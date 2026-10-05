# Copyright (c) 2026 Gil Rodrigues
r"""Compile the stock prefill attention kernels to PTX for bend/err_prefill_diff.py.

Usage (inside the engine image, which has Triton 3.6.0; no GPU and no network needed):
    python3 -I -B stock_prefill_ptx.py STOCK_PACKAGE_DIR OUT_DIR

STOCK_PACKAGE_DIR is OUT/stock of bend/engine_trees.py (stock ExLlamaV3 355c6ee). The
script requires its modules/attention_fn/triton_paged.py to have the stock SHA-256.
OUT_DIR must be an empty directory. The script writes:
- stock_prefill_sm86.ptx and stock_prefill_sm86.ttgir: _paged_attn_prefill_kernel, the
  staged fp16 path that ext 3022 replaces, at the served staged prefill launch
  (QCK = QCV = 0, NEW_KV 0, causal, no window / softcap / sinks, head_dim 256,
  n_q 24 / n_kv 4, BLOCK_M 64, BLOCK_N 32, 8 warps, 2 stages).
- stock_combine_sm86.ptx: _paged_attn_prefill_combine_kernel (8 warps, 1 stage).
The target is sm_86 (GPUTarget("cuda", 86, 32)).

Example with the elpis engine image (read-only mounts, no network). Mount the stock
package at /stock/exllamav3: the PTX and TTGIR embed the source path, and the files
that bend/err_prefill_diff.py was checked against used that path.
    docker run --rm --network none --user 0:0 --entrypoint /opt/venv/bin/python \
        -v "$PWD/bend/gen:/gen:ro" -v "$OUT/stock:/stock/exllamav3:ro" -v "$PTX:/out" \
        IMAGE -I -B /gen/stock_prefill_ptx.py /stock/exllamav3 /out

Origin: the stock_ptx.py and combine_ptx.py scripts of the 3022 prefill work. Only the
paths, the stock hash check and the removal of the diagnostic prints changed.
"""

import hashlib
import importlib
import sys
import types
from pathlib import Path
from typing import NoReturn

import triton
from triton.backends.compiler import GPUTarget
from triton.compiler import ASTSource
from triton.runtime.jit import JITFunction

STOCK_TRITON_PAGED = "910379b663acb08711c3be207cd3e9ed96658527cc110a6ce39c793f997836d9"
TARGET = GPUTarget("cuda", 86, 32)
ARGC = 3


def fail(message: str) -> NoReturn:
    """Stop with an error.

    Args:
        message: The failure description.

    Raises:
        SystemExit: Always.

    """
    text = f"stock_prefill_ptx: FAIL: {message}"
    raise SystemExit(text)


def asm_text(asm: object, key: str) -> str:
    """Return one text artifact of a compiled kernel.

    Args:
        asm: The compiled kernel's asm mapping.
        key: The artifact name (ptx, ttgir).

    Returns:
        The artifact text.

    """
    if not isinstance(asm, dict):
        fail("the compiled kernel has no asm mapping")
    text = asm.get(key)
    if not isinstance(text, str):
        fail(f"the compiled kernel has no {key} text")
    return text


class AttnArgs:
    """Stand-in for exllamav3's AttnArgs; only used in annotations at import time."""


def get_non_causal_span_arglist(_args: AttnArgs) -> list[dict[str, object]]:
    """Stand-in for exllamav3's span splitter; the compiled kernels never call it.

    Raises:
        RuntimeError: Always.

    """
    msg = "get_non_causal_span_arglist is a stub"
    raise RuntimeError(msg)


def load_stock(stock: Path) -> types.ModuleType:
    """Import the pinned stock triton_paged.py with stub parent packages.

    Returns:
        The module.

    """
    attention_fn = stock / "modules/attention_fn"
    path = attention_fn / "triton_paged.py"
    if hashlib.sha256(path.read_bytes()).hexdigest() != STOCK_TRITON_PAGED:
        fail(f"{path} is not the stock 355c6ee file")
    for name, directory in (
        ("exllamav3", stock),
        ("exllamav3.modules", stock / "modules"),
        ("exllamav3.modules.attention_fn", attention_fn),
    ):
        package = types.ModuleType(name)
        package.__path__ = [str(directory)]
        sys.modules[name] = package
    common = types.ModuleType("exllamav3.modules.attention_fn.common")
    common.__dict__.update(
        AttnArgs=AttnArgs, get_non_causal_span_arglist=get_non_causal_span_arglist
    )
    sys.modules[common.__name__] = common
    return importlib.import_module("exllamav3.modules.attention_fn.triton_paged")


def prefill(mod: types.ModuleType) -> tuple[str, str]:
    """Compile the staged prefill kernel.

    Returns:
        (ptx, ttgir).

    """
    fn: object = mod.__dict__.get("_paged_attn_prefill_kernel")
    if not isinstance(fn, JITFunction):
        fail("_paged_attn_prefill_kernel is not a Triton kernel")
    names = fn.arg_names
    scale = 1.0 / 16.0  # head_dim 256: softmax scale 1/sqrt(256)
    const = {
        "IS_SPLIT": False,
        "NEW_KV": 0,
        "QCK": 0,
        "QCV": 0,
        "n_q_heads": 24,
        "n_kv_heads": 4,
        "page_size": 256,
        "head_dim": 256,
        "HD_PAD": 256,
        "scale": scale,
        "CAUSAL": True,
        "HAS_WINDOW_LEFT": False,
        "HAS_WINDOW_RIGHT": False,
        "SOFTCAP": 0.0,
        "HAS_SINKS": False,
        "WIDE_INDEX": False,
        "BLOCK_M": 64,
        "BLOCK_N": 32,
    }
    ptrs = {
        "q": "*fp16",
        "k_cache": "*fp16",
        "v_cache": "*fp16",
        "block_table": "*i32",
        "cache_seqlens": "*i32",
        "out": "*fp16",
        "partial_o": "*fp32",
        "partial_ml": "*fp32",
        "k_scales": "*fp16",
        "v_scales": "*fp16",
        "h32": "*fp16",
        "k_new": "*fp16",
        "v_new": "*fp16",
        "sinks": "*fp16",
    }
    ints = {
        "num_splits": "i32",
        "q_len": "i32",
        "kv_append_len": "i32",
        "num_pages_per_seq": "i32",
        "WINDOW_LEFT": "i32",
        "WINDOW_RIGHT": "i32",
    }
    sig, cx = {}, {}
    for n in names:
        if n in const:
            sig[n] = "constexpr"
            cx[n] = const[n]
        elif n in ptrs:
            sig[n] = ptrs[n]
        elif n in ints:
            sig[n] = ints[n]
        else:
            fail(f"unmapped arg {n}")
    src = ASTSource(fn, sig, constexprs={(names.index(k),): v for k, v in cx.items()})
    k = triton.compile(src, target=TARGET, options={"num_warps": 8, "num_stages": 2})
    return asm_text(k.asm, "ptx"), asm_text(k.asm, "ttgir")


def combine(mod: types.ModuleType) -> str:
    """Compile the split combine kernel.

    Returns:
        The PTX.

    """
    fn: object = mod.__dict__.get("_paged_attn_prefill_combine_kernel")
    if not isinstance(fn, JITFunction):
        fail("_paged_attn_prefill_combine_kernel is not a Triton kernel")
    names = fn.arg_names
    const = {
        "QCV": 0,
        "HAS_SINKS": False,
        "n_q_heads": 24,
        "head_dim": 256,
        "HD_PAD": 256,
        "WIDE_INDEX": False,
        "BLOCK_M": 64,
    }
    types_ = {
        "partial_o": "*fp32",
        "partial_ml": "*fp32",
        "out": "*fp16",
        "h32": "*fp16",
        "sinks": "*fp16",
        "num_splits": "i32",
        "q_len": "i32",
    }
    sig = {n: ("constexpr" if n in const else types_[n]) for n in names}
    k = triton.compile(
        ASTSource(fn, sig, constexprs={(names.index(a),): v for a, v in const.items()}),
        target=TARGET,
        options={"num_warps": 8, "num_stages": 1},
    )
    return asm_text(k.asm, "ptx")


def main(argv: list[str]) -> None:
    """Write the three files into OUT_DIR."""
    if len(argv) != ARGC:
        fail(__doc__ or "usage: STOCK_PACKAGE_DIR OUT_DIR")
    stock, out = Path(argv[1]), Path(argv[2])
    if not out.is_dir() or any(out.iterdir()):
        fail(f"{out} is not an empty directory")
    mod = load_stock(stock)
    ptx, ttgir = prefill(mod)
    (out / "stock_prefill_sm86.ptx").write_text(ptx, encoding="utf-8")
    (out / "stock_prefill_sm86.ttgir").write_text(ttgir, encoding="utf-8")
    (out / "stock_combine_sm86.ptx").write_text(combine(mod), encoding="utf-8")


if __name__ == "__main__":
    main(sys.argv)

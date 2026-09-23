"""Offline, fail-closed admission of an original Bend scalar leaf and SM86 cubin.

This module has no torch or CUDA-driver dependency. The CPU proof/plan stages do
not import it. NVRTC is used only by the explicit compile-native build stage.
"""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import re
from dataclasses import dataclass
from pathlib import Path

from bend import adapter

OPTIONS = (
    "--gpu-architecture=sm_86",
    "-DCUBE_LOG=7",
    "--fmad=false",
    "-default-device",
)
FILES = (
    "binding.json",
    "probe.c",
    "probe",
    "probe.ll",
    "acceptance.cu",
    "acceptance.cubin",
    "nvrtc.json",
    "clang.json",
    "compile.json",
    "ir.json",
    "parity.json",
)
TYPES = {"Term", "u32", "u64", "Nat"}
TOKEN = re.compile(r"\s*(==|!=|[A-Za-z_][A-Za-z_0-9]*|[0-9]+(?:ull|u)?|[{}()\[\];,=+])")
SIGNATURE = re.compile(
    r"INLINE Term (spin_[0-9]+)\(Env e, THR Term\* o((?:, (?:u32|Term) r[0-9]+)*)\) \{"
)


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class Scalar:
    name: str
    arguments: tuple[str, ...]
    text: str
    outputs: int
    calls: tuple[str, ...]


class Admission:
    """Accept only the emitted, bounded scalar sublanguage; never sanitize C.

    The actual source is compiled unchanged. This parser only rejects it. No
    pointers, arbitrary calls, dynamic indexing, globals, recursion, or repeated
    polling are admitted. Nat overflow and exact results are additionally checked
    by all-domain constant LLVM bodies and actual original-C execution.
    """

    def __init__(self, text: str, arguments: tuple[str, ...]) -> None:
        self.tokens: list[str] = []
        offset = 0
        while text[offset:].strip():
            match = TOKEN.match(text, offset)
            if match is None:
                adapter.fail("Unadmitted token in scalar leaf")
            self.tokens.append(match.group(1))
            offset = match.end()
        self.at = 0
        self.variables = {f"r{i}" for i in range(len(arguments))}
        self.arrays: dict[str, int] = {}
        self.initialized: set[str] = set()
        self.calls: list[str] = []
        self.call_outputs: list[tuple[str, int]] = []

    def peek(self) -> str:
        return self.tokens[self.at] if self.at < len(self.tokens) else ""

    def take(self, expected: str | None = None) -> str:
        token = self.peek()
        if not token or (expected is not None and token != expected):
            adapter.fail(
                f"Unadmitted scalar syntax: expected {expected}, found {token}"
            )
        self.at += 1
        return token

    def number(self) -> int:
        token = self.take()
        if re.fullmatch(r"[0-9]+(?:ull|u)?", token) is None:
            adapter.fail("Scalar array index/extent must be a literal")
        value = int(token.rstrip("ul"))
        if value > 8:
            adapter.fail("Scalar literal exceeds the admitted block8 domain")
        return value

    def expression(self) -> None:
        self.atom()
        while self.peek() in ("+", "==", "!="):
            self.take()
            self.atom()

    def atom(self) -> None:
        token = self.peek()
        if token == "(":
            self.take("(")
            if self.peek() in TYPES:
                self.take()
                self.take(")")
                self.atom()
            else:
                self.expression()
                self.take(")")
        elif token and token[0].isdigit():
            self.number()
        elif token == "nat_chk":
            self.take()
            self.take("(")
            self.take("e")
            self.take(",")
            self.expression()
            self.take(")")
        elif re.fullmatch(r"spin_[0-9]+", token):
            name = self.take()
            self.calls.append(name)
            self.take("(")
            self.take("e")
            self.take(",")
            array = self.take()
            if array not in self.arrays:
                adapter.fail("Scalar call must use bounded local output storage")
            self.call_outputs.append((name, self.arrays[array]))
            while self.peek() == ",":
                self.take(",")
                self.expression()
            self.take(")")
            self.initialized.add(array)
        elif token in self.arrays:
            name = self.take()
            self.take("[")
            index = self.number()
            self.take("]")
            if name not in self.initialized or index >= self.arrays[name]:
                adapter.fail("Uninitialized or out-of-range scalar local output")
        elif token in self.variables and token != "wpoll":
            self.take()
        else:
            adapter.fail(f"Unadmitted scalar expression: {token}")

    def statements(self, end: str) -> None:
        while self.peek() != end:
            token = self.peek()
            if token in TYPES:
                kind = self.take()
                name = self.take()
                # Bend 2.0.26 comp.ts:name_local strips leading underscores
                # from the cleaned base, then emits "_" + base + "_" + n.
                # ABI names (e, o, rN, wpoll) are not generated locals.
                if (
                    re.fullmatch(
                        r"_(?:[A-Za-z0-9][A-Za-z0-9_]*)?_(?:0|[1-9][0-9]*)", name
                    )
                    is None
                    or name in self.variables
                    or name in self.arrays
                    or name in ("e", "o", "wpoll")
                ):
                    adapter.fail("Ambiguous scalar local")
                if self.peek() == "[":
                    self.take("[")
                    extent = self.number()
                    self.take("]")
                    if kind != "Term" or not 1 <= extent <= 4:
                        adapter.fail("Scalar local output is not bounded")
                    self.arrays[name] = extent
                else:
                    self.take("=")
                    self.expression()
                    self.variables.add(name)
                self.take(";")
            elif token == "if":
                self.take("if")
                self.take("(")
                self.expression()
                self.take(")")
                self.take("{")
                self.statements("}")
                self.take("}")
                if self.peek() == "else":
                    self.take("else")
                    self.take("{")
                    self.statements("}")
                    self.take("}")
            elif token == "return":
                self.take("return")
                self.take("0")
                self.take(";")
            elif token in self.variables and token != "wpoll":
                self.take()
                self.take("=")
                self.expression()
                self.take(";")
            else:
                adapter.fail(f"Unadmitted scalar statement: {token}")

    def body(self) -> int:
        for token in ("u32", "wpoll", "=", "0", ";"):
            self.take(token)
        self.statements("WL_SPIN")
        self.take("WL_SPIN")
        self.statements("break")
        self.take("break")
        self.take(";")
        self.take("}")
        outputs = 0
        while self.peek() == "o":
            self.take("o")
            self.take("[")
            if self.number() != outputs or outputs >= 4:
                adapter.fail("Scalar result layout is not a bounded ordered flat tuple")
            self.take("]")
            self.take("=")
            self.expression()
            self.take(";")
            outputs += 1
        self.take("return")
        self.take("1")
        self.take(";")
        if self.peek() or not outputs:
            adapter.fail("Unexpected scalar result epilogue")
        return outputs


def emitted_binding(text: str) -> dict[str, object]:
    """Identify the sole seven-discriminant ABI and admit its complete call closure."""
    required = (
        "#define WL_SPIN     for (;;) { if (err_spun(e.mem, &wpoll)) { return 0; }",
        "#define err_seen(H)    (DEVICE && a32_load(a32_at(H, H_ERROR_CODE)) != 0)",
        "#define err_spun(H, n) ((++*(n) & 4095) == 0 && err_seen(H))",
        "typedef u64 Term;",
        "typedef Term Nat;",
        "#define NAT_IMM ((1ull << 48) - 1)",
        "INLINE Nat nat_chk(Env e, Nat n) {\n  if (n > NAT_IMM) {\n    err_post(e.mem, ERR_NATS);\n    return NAT_IMM;\n  }\n  return n;\n}",
    )
    if any(text.count(item) != 1 for item in required):
        adapter.fail("Original runtime scalar/polling ABI is not established")
    raw: dict[str, tuple[tuple[str, ...], str, str]] = {}
    for match in SIGNATURE.finditer(text):
        # WL_SPIN contributes an opening brace through a macro. The original
        # emitter ends each function at column zero; inner/poll braces are indented.
        start = match.end()
        closing = re.search(r"^}", text[start:], re.MULTILINE)
        if closing is None:
            adapter.fail("Incomplete emitted scalar definition")
        end = start + closing.end()
        arguments = tuple(re.findall(r", (u32|Term) r[0-9]+", match.group(2)))
        if match.group(2) != "".join(
            f", {kind} r{i}" for i, kind in enumerate(arguments)
        ):
            adapter.fail("Unestablished scalar argument ordering")
        if match.group(1) in raw:
            adapter.fail("Duplicate emitted scalar identity")
        raw[match.group(1)] = (
            arguments,
            text[start : end - 1],
            text[match.start() : end],
        )
    candidates = [
        name for name, (arguments, _, _) in raw.items() if arguments == ("u32",) * 7
    ]
    if len(candidates) != 1:
        adapter.fail("Expected one unambiguous seven-Bool emitted scalar leaf")
    active: set[str] = set()
    admitted: dict[str, Scalar] = {}

    def visit(name: str) -> Scalar:
        if name in active or name not in raw:
            adapter.fail("Recursive or unknown scalar dependency")
        if name in admitted:
            return admitted[name]
        active.add(name)
        arguments, body, original = raw[name]
        parser = Admission(body, arguments)
        outputs = parser.body()
        for callee, extent in parser.call_outputs:
            if visit(callee).outputs != extent:
                adapter.fail("Scalar caller/callee output storage mismatch")
        active.remove(name)
        result = Scalar(name, arguments, original, outputs, tuple(parser.calls))
        admitted[name] = result
        return result

    leaf = visit(candidates[0])
    if leaf.outputs != 4:
        adapter.fail("Seven-Bool leaf must return exactly four flat words")
    return {
        "leaf": leaf.name,
        "arguments": list(leaf.arguments),
        "outputs": leaf.outputs,
        "functions": {
            name: sha(value.text) for name, value in sorted(admitted.items())
        },
        "admission": "acyclic scalar grammar; one poll/call; bounded outputs; all-domain original-C/LLVM parity",
        "parameter_order": "r0..r6 correspond to CPU mask bits 0..6",
        "bool_binding": "unique parity match across both zero/one encodings and all 128 ordered flags",
    }


def probe_source(leaf: str) -> str:
    parts = [
        '#define main litos_original_main\n#include "../speculate.c"\n#undef main\n'
        '_Static_assert(sizeof(Term) == 8 && sizeof(u32) == 4, "Bend scalar ABI changed");\n'
    ]
    for encoding in range(2):
        for mask in range(128):
            args = ", ".join(str(((mask >> bit) & 1) ^ encoding) for bit in range(7))
            for field in range(5):
                value = "ok" if field == 4 else f"words[{field}]"
                parts.append(
                    f"u64 litos_proof_{encoding}_{mask}_{field}(void) {{ Env env = {{0,0}}; Term words[4]; Term ok = {leaf}(env, words, {args}); return {value}; }}\n"
                )
    parts.append(f"""
int main(void) {{
  for (u32 encoding = 0; encoding < 2; ++encoding) {{
    for (u32 mask = 0; mask < 128; ++mask) {{
      Env env = {{0,0}};
      Term words[4];
      Term ok = {leaf}(env, words,
        ((mask >> 0) & 1) ^ encoding, ((mask >> 1) & 1) ^ encoding,
        ((mask >> 2) & 1) ^ encoding, ((mask >> 3) & 1) ^ encoding,
        ((mask >> 4) & 1) ^ encoding, ((mask >> 5) & 1) ^ encoding,
        ((mask >> 6) & 1) ^ encoding);
      if (ok != 1) return 2;
      printf("%llu %llu %llu %llu\\n", (unsigned long long)words[0],
        (unsigned long long)words[1], (unsigned long long)words[2], (unsigned long long)words[3]);
    }}
  }}
  return 0;
}}
""")
    return "".join(parts)


def parity(text: str, ir: str, policy: adapter.SpeculationPolicy) -> int:
    """Require all specialized original-C functions to be literal safe returns."""
    lines = text.splitlines()
    if len(lines) != 256 or text != "\n".join(lines) + "\n":
        adapter.fail("Incomplete scalar finite-domain execution")
    rows: list[tuple[int, ...]] = []
    for line in lines:
        if re.fullmatch(r"[0-9]+ [0-9]+ [0-9]+ [0-9]+", line) is None:
            adapter.fail("Malformed scalar finite-domain output")
        rows.append(tuple(map(int, line.split(" "))))
    constants: dict[tuple[int, int, int], int] = {}
    for match in re.finditer(
        r"^define [^\n]*@litos_proof_([01])_([0-9]+)_([0-4])\(\)[^\n]*\{\n([^}]+)\}",
        ir,
        re.MULTILINE,
    ):
        body = re.sub(r";[^\n]*", "", match.group(4)).strip()
        literal = re.fullmatch(r"ret i64 ([0-9]+)", body)
        if literal is None:
            adapter.fail("Scalar domain has nonconstant/unsafe LLVM dependency")
        key = (int(match.group(1)), int(match.group(2)), int(match.group(3)))
        if key in constants:
            adapter.fail("Duplicate scalar LLVM witness")
        constants[key] = int(literal.group(1))
    if len(constants) != 2 * 128 * 5:
        adapter.fail("Incomplete all-domain LLVM constant witness")
    for encoding in range(2):
        for mask in range(128):
            if (
                constants.get((encoding, mask, 4)) != 1
                or tuple(constants.get((encoding, mask, field)) for field in range(4))
                != rows[encoding * 128 + mask]
            ):
                adapter.fail("Original-C execution and bounded LLVM witness disagree")
    matches = [
        encoding
        for encoding in range(2)
        if tuple(rows[encoding * 128 : (encoding + 1) * 128]) == policy.decisions
    ]
    if len(matches) != 1:
        adapter.fail("No unique Bool ABI agrees with checked CPU enumeration")
    return matches[0]


def checked_result(result: object, operation: str) -> None:
    if not isinstance(result, int) or result != 0:
        adapter.fail(f"{operation} failed: {result}")


def compile_nvrtc(source: str, library: Path, output: Path) -> dict[str, object]:
    """Use the real NVRTC device dialect offline, without a CUDA driver/context."""
    library = library.resolve(strict=True)
    before = adapter.digest(library)
    lib = ctypes.CDLL(str(library))
    major, minor = ctypes.c_int(), ctypes.c_int()
    version = ctypes.CFUNCTYPE(
        ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int)
    )(("nvrtcVersion", lib))
    checked_result(version(ctypes.byref(major), ctypes.byref(minor)), "nvrtcVersion")
    program = ctypes.c_void_p()
    create = ctypes.CFUNCTYPE(
        ctypes.c_int,
        ctypes.POINTER(ctypes.c_void_p),
        ctypes.c_char_p,
        ctypes.c_char_p,
        ctypes.c_int,
        ctypes.c_void_p,
        ctypes.c_void_p,
    )(("nvrtcCreateProgram", lib))
    checked_result(
        create(ctypes.byref(program), source.encode(), b"acceptance.cu", 0, None, None),
        "nvrtcCreateProgram",
    )
    destroy = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.POINTER(ctypes.c_void_p))((
        "nvrtcDestroyProgram",
        lib,
    ))
    try:
        compile_program = ctypes.CFUNCTYPE(
            ctypes.c_int, ctypes.c_void_p, ctypes.c_int, ctypes.POINTER(ctypes.c_char_p)
        )(("nvrtcCompileProgram", lib))
        options = (ctypes.c_char_p * len(OPTIONS))(
            *(option.encode() for option in OPTIONS)
        )
        result = compile_program(program, len(OPTIONS), options)
        log_size = ctypes.c_size_t()
        size_log = ctypes.CFUNCTYPE(
            ctypes.c_int, ctypes.c_void_p, ctypes.POINTER(ctypes.c_size_t)
        )(("nvrtcGetProgramLogSize", lib))
        get_log = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p)((
            "nvrtcGetProgramLog",
            lib,
        ))
        checked_result(
            size_log(program, ctypes.byref(log_size)), "nvrtcGetProgramLogSize"
        )
        log = ctypes.create_string_buffer(log_size.value)
        checked_result(get_log(program, log), "nvrtcGetProgramLog")
        diagnostics = log.value.decode("utf-8", errors="strict")
        if result != 0:
            adapter.fail(f"NVRTC compilation failed ({result}): {diagnostics}")
        size_cubin = ctypes.CFUNCTYPE(
            ctypes.c_int, ctypes.c_void_p, ctypes.POINTER(ctypes.c_size_t)
        )(("nvrtcGetCUBINSize", lib))
        get_cubin = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p)((
            "nvrtcGetCUBIN",
            lib,
        ))
        size = ctypes.c_size_t()
        checked_result(size_cubin(program, ctypes.byref(size)), "nvrtcGetCUBINSize")
        if not size.value:
            adapter.fail("NVRTC returned an empty SM86 cubin")
        cubin = ctypes.create_string_buffer(size.value)
        checked_result(get_cubin(program, cubin), "nvrtcGetCUBIN")
        with output.open("xb") as stream:
            stream.write(cubin.raw)
        builtins = {
            Path(line.split()[-1]).resolve(strict=True)
            for line in Path("/proc/self/maps").read_text(encoding="utf-8").splitlines()
            if "/libnvrtc-builtins.so" in line
        }
        if len(builtins) != 1 or adapter.digest(library) != before:
            adapter.fail("NVRTC compiler/builtins identity is not established")
        builtin = builtins.pop()
        return {
            "library": str(library),
            "sha256": before,
            "version": [major.value, minor.value],
            "builtins": str(builtin),
            "builtins_sha256": adapter.digest(builtin),
            "options": list(OPTIONS),
            "log": diagnostics,
        }
    finally:
        checked_result(destroy(ctypes.byref(program)), "nvrtcDestroyProgram")


def cuda_source(directory: Path, binding: dict[str, object], encoding: int) -> str:
    leaf = binding.get("leaf")
    if not isinstance(leaf, str) or re.fullmatch(r"spin_[0-9]+", leaf) is None:
        adapter.fail("Invalid admitted scalar symbol")
    original = (directory / "speculate.c").read_text(encoding="utf-8")
    glue = (directory / "sources/bend/native.cu").read_text(encoding="utf-8")
    return (
        original
        + f"\n#define LITOS_LEAF {leaf}\n#define LITOS_FALSE {encoding}\n#define LITOS_TRUE {1 ^ encoding}\n"
        + glue
    )


def commands(compiler: str) -> tuple[list[str], list[str], list[str]]:
    common = [compiler, "-std=c11", "-O3", "native/probe.c"]
    return (
        [compiler, "--version"],
        common + ["-lpthread", "-lm", "-o", "native/probe"],
        common + ["-S", "-emit-llvm", "-o", "native/probe.ll"],
    )


def compile_native(directory: Path, cc: str, nvrtc: Path) -> None:
    _, _, policy = adapter.retained_execution(directory)
    native = directory / "native"
    native.mkdir(exist_ok=False)
    compiler = adapter.executable(cc)
    compiler_sha = adapter.digest(compiler)
    version_command, compile_command, ir_command = commands(str(compiler))
    version = adapter.successful_output(
        adapter.run(version_command, cwd=directory, record=native / "clang.json"),
        version_command,
    )
    if re.search(r"clang version (?:1[4-9]|[2-9][0-9])\.", version) is None:
        adapter.fail("Native scalar admission requires clang 14 or newer")
    binding = emitted_binding((directory / "speculate.c").read_text(encoding="utf-8"))
    leaf = binding["leaf"]
    if not isinstance(leaf, str):
        adapter.fail("Missing scalar symbol")
    with (native / "probe.c").open("x", encoding="utf-8") as stream:
        stream.write(probe_source(leaf))
    for command, log in ((compile_command, "compile.json"), (ir_command, "ir.json")):
        if adapter.successful_output(
            adapter.run(command, cwd=directory, record=native / log),
            command,
            quiet=False,
        ):
            adapter.fail("Unexpected scalar compiler stdout")
    execution = adapter.run(
        ["./native/probe"], cwd=directory, record=native / "parity.json"
    )
    encoding = parity(
        adapter.successful_output(execution, ["./native/probe"]),
        (native / "probe.ll").read_text(encoding="utf-8"),
        policy,
    )
    binding["false"] = encoding
    binding["true"] = 1 ^ encoding
    adapter.write_json(native / "binding.json", binding)
    source = cuda_source(directory, binding, encoding)
    with (native / "acceptance.cu").open("x", encoding="utf-8") as stream:
        stream.write(source)
    nvrtc_identity = compile_nvrtc(source, nvrtc, native / "acceptance.cubin")
    adapter.write_json(native / "nvrtc.json", nvrtc_identity)
    if adapter.digest(compiler) != compiler_sha:
        adapter.fail("Native CPU compiler changed during admission")
    adapter.retained_execution(directory)
    adapter.write_json(
        native / "identity.json",
        {
            "schema": 1,
            "verified_sha256": adapter.digest(directory / "verified.json"),
            "source_sha256": adapter.digest(directory / "source.json"),
            "build_sha256": adapter.digest(directory / "build.json"),
            "generated_c_sha256": adapter.digest(directory / "speculate.c"),
            "compiler": {
                "path": str(compiler),
                "sha256": compiler_sha,
                "version": version,
            },
            "files": {name: adapter.digest(native / name) for name in FILES},
        },
    )
    native_identity(directory)


def native_identity(directory: Path) -> Path:
    """Reuse full retained proof/build/execution identity; never run a subprocess."""
    _, _, policy = adapter.retained_execution(directory)
    native = directory / "native"
    identity = adapter.object_file(native / "identity.json")
    expected_keys = {
        "schema",
        "verified_sha256",
        "source_sha256",
        "build_sha256",
        "generated_c_sha256",
        "compiler",
        "files",
    }
    if (
        set(identity) != expected_keys
        or type(identity.get("schema")) is not int
        or identity["schema"] != 1
    ):
        adapter.fail("Malformed native artifact identity")
    for key, name in (
        ("verified_sha256", "verified.json"),
        ("source_sha256", "source.json"),
        ("build_sha256", "build.json"),
        ("generated_c_sha256", "speculate.c"),
    ):
        if identity.get(key) != adapter.digest(directory / name):
            adapter.fail("Native module differs from checked Bend generation")
    if adapter.check_hashes(native, identity.get("files")) != set(
        FILES
    ) or adapter.tree_files(native) != set(FILES) | {"identity.json"}:
        adapter.fail("Incomplete or unexpected native artifact closure")
    compiler = identity.get("compiler")
    if not adapter.is_object(compiler) or set(compiler) != {
        "path",
        "sha256",
        "version",
    }:
        adapter.fail("Missing native compiler identity")
    path, compiler_hash, version = (
        compiler.get("path"),
        compiler.get("sha256"),
        compiler.get("version"),
    )
    if (
        not isinstance(path, str)
        or not Path(path).is_absolute()
        or not isinstance(compiler_hash, str)
        or re.fullmatch(r"[0-9a-f]{64}", compiler_hash) is None
        or not isinstance(version, str)
    ):
        adapter.fail("Malformed native compiler identity")
    version_command, compile_command, ir_command = commands(path)
    if (
        adapter.successful_output(
            adapter.object_file(native / "clang.json"), version_command
        )
        != version
    ):
        adapter.fail("Native compiler version evidence changed")
    for command, log in ((compile_command, "compile.json"), (ir_command, "ir.json")):
        if adapter.successful_output(
            adapter.object_file(native / log), command, quiet=False
        ):
            adapter.fail("Changed native compilation evidence")
    binding = emitted_binding((directory / "speculate.c").read_text(encoding="utf-8"))
    encoding = parity(
        adapter.successful_output(
            adapter.object_file(native / "parity.json"), ["./native/probe"]
        ),
        (native / "probe.ll").read_text(encoding="utf-8"),
        policy,
    )
    binding.update({"false": encoding, "true": 1 ^ encoding})
    if adapter.object_file(native / "binding.json") != binding:
        adapter.fail("Native scalar ABI binding changed")
    leaf = binding["leaf"]
    if not isinstance(leaf, str) or (native / "probe.c").read_text(
        encoding="utf-8"
    ) != probe_source(leaf):
        adapter.fail("Native scalar probe does not call the admitted original leaf")
    if (native / "acceptance.cu").read_text(encoding="utf-8") != cuda_source(
        directory, binding, encoding
    ):
        adapter.fail(
            "Native CUDA input is not unchanged generated C plus retained glue"
        )
    nvrtc = adapter.object_file(native / "nvrtc.json")
    if set(nvrtc) != {
        "library",
        "sha256",
        "version",
        "builtins",
        "builtins_sha256",
        "options",
        "log",
    } or nvrtc.get("options") != list(OPTIONS):
        adapter.fail("Malformed native NVRTC identity")
    for key in ("sha256", "builtins_sha256"):
        value = nvrtc.get(key)
        if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
            adapter.fail("Missing retained NVRTC compiler digest")
    for key in ("library", "builtins"):
        value = nvrtc.get(key)
        if not isinstance(value, str) or not Path(value).is_absolute():
            adapter.fail("Missing retained NVRTC compiler path")
    version = nvrtc.get("version")
    if (
        not isinstance(nvrtc.get("log"), str)
        or not isinstance(version, list)
        or len(version) != 2
        or any(type(value) is not int for value in version)
        or adapter.exact_int(version[0], "NVRTC major") < 11
        or adapter.exact_int(version[1], "NVRTC minor") > 99
    ):
        adapter.fail("Missing retained NVRTC version/diagnostics")
    return native / "acceptance.cubin"


class Arguments(argparse.Namespace):
    """Explicit offline native stage; no implicit build on import or launch."""

    directory: Path = Path()
    cc: str = "clang"
    nvrtc: Path = Path()


def main() -> None:
    """Compile an admitted scalar consumer after adapter generate/compile/verify."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("--directory", type=Path, required=True)
    _ = parser.add_argument("--cc", default="clang")
    _ = parser.add_argument("--nvrtc", type=Path, required=True)
    args = Arguments()
    _ = parser.parse_args(namespace=args)
    compile_native(args.directory.resolve(strict=True), args.cc, args.nvrtc)


if __name__ == "__main__":
    main()

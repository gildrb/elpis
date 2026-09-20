"""In-process, caller-stream launch of the proof-bound original Bend scalar leaf.

A worker constructs AcceptanceKernel before capture and owns the runner for its
serving lifetime. Successfully loaded CUDA modules belong to the existing CUDA
context until that context is destroyed, independently of Python object life.
There is no successful-module unload/finalizer: graphs may outlive the runner.
Only failed construction unloads its not-yet-exposed module. The worker must keep
the owning CUDA context alive until all its launches and graphs are finished.
"""

from __future__ import annotations

import ctypes
from collections.abc import Callable
from pathlib import Path
from typing import TYPE_CHECKING

from . import adapter
from .native_build import native_identity

if TYPE_CHECKING:
    import torch


class _Driver:
    """Every driver symbol has its complete native signature and checked status."""

    def __init__(self) -> None:
        self.library = ctypes.CDLL("libcuda.so.1")
        lib = self.library
        self.error_name: Callable[[object, object], object] = ctypes.CFUNCTYPE(
            ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_char_p)
        )(("cuGetErrorName", lib))
        self.error_string: Callable[[object, object], object] = ctypes.CFUNCTYPE(
            ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_char_p)
        )(("cuGetErrorString", lib))
        self.ctx_current: Callable[[object], object] = ctypes.CFUNCTYPE(
            ctypes.c_int, ctypes.POINTER(ctypes.c_void_p)
        )(("cuCtxGetCurrent", lib))
        self.ctx_device: Callable[[object], object] = ctypes.CFUNCTYPE(
            ctypes.c_int, ctypes.POINTER(ctypes.c_int)
        )(("cuCtxGetDevice", lib))
        self.module_load: Callable[[object, object, object, object, object], object] = (
            ctypes.CFUNCTYPE(
                ctypes.c_int,
                ctypes.POINTER(ctypes.c_void_p),
                ctypes.c_void_p,
                ctypes.c_uint,
                ctypes.c_void_p,
                ctypes.c_void_p,
            )(("cuModuleLoadDataEx", lib))
        )
        self.module_unload: Callable[[object], object] = ctypes.CFUNCTYPE(
            ctypes.c_int, ctypes.c_void_p
        )(("cuModuleUnload", lib))
        self.module_function: Callable[[object, object, object], object] = (
            ctypes.CFUNCTYPE(
                ctypes.c_int,
                ctypes.POINTER(ctypes.c_void_p),
                ctypes.c_void_p,
                ctypes.c_char_p,
            )(("cuModuleGetFunction", lib))
        )
        # Explicit eager function loading, including under CUDA_MODULE_LOADING=LAZY.
        # Requiring this driver API is preferable to first-use loading in capture.
        self.function_load: Callable[[object], object] = ctypes.CFUNCTYPE(
            ctypes.c_int, ctypes.c_void_p
        )(("cuFuncLoad", lib))
        self.launch: Callable[
            [
                object,
                object,
                object,
                object,
                object,
                object,
                object,
                object,
                object,
                object,
                object,
            ],
            object,
        ] = ctypes.CFUNCTYPE(
            ctypes.c_int,
            ctypes.c_void_p,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_void_p,
            ctypes.POINTER(ctypes.c_void_p),
            ctypes.c_void_p,
        )(("cuLaunchKernel", lib))

    def check(self, result: object, operation: str) -> None:
        if not isinstance(result, int):
            adapter.fail(f"Invalid CUDA driver status from {operation}")
        if result == 0:
            return
        name, message = ctypes.c_char_p(), ctypes.c_char_p()
        name_status = self.error_name(result, ctypes.byref(name))
        message_status = self.error_string(result, ctypes.byref(message))
        if name_status != 0 or message_status != 0:
            adapter.fail(f"{operation}: CUDA status {result}; error lookup failed")
        label = name.value.decode("utf-8") if name.value is not None else "unknown"
        detail = (
            message.value.decode("utf-8") if message.value is not None else "unknown"
        )
        adapter.fail(f"{operation}: {label} ({result}): {detail}")

    def context(self) -> int:
        context = ctypes.c_void_p()
        self.check(self.ctx_current(ctypes.byref(context)), "cuCtxGetCurrent")
        if context.value is None:
            adapter.fail("AcceptanceKernel requires the worker's existing CUDA context")
        return context.value


class AcceptanceKernel:
    """Worker-owned runner; successful module lifetime is the owning CUDA context.

    Construct outside capture. No successful module is unloaded when this Python
    object dies; the worker owns context/graph teardown ordering.

    launch writes only caller-owned tensors. The caller must maintain their
    storage lifetime and normal stream/event ordering, including graph replay.
    All output storage must be disjoint from each other and from input storage.
    Prefix input alone may be strided (including zero stride). No tokens or
    lengths are read back to the host and no tensor is allocated by this class.
    """

    def __init__(self, directory: Path, device: torch.device) -> None:
        import torch

        self._torch = torch
        if not isinstance(device, torch.device) or device.type != "cuda":
            adapter.fail("AcceptanceKernel requires an explicit CUDA device")
        index = torch.cuda.current_device() if device.index is None else device.index
        if torch.cuda.current_device() != index:
            adapter.fail(
                "Construct AcceptanceKernel on the worker's current CUDA device"
            )
        self.device = torch.device("cuda", index)
        # Initialize the worker's ordinary torch stream before observing its
        # existing context. Never use driver primary-context retain/set APIs.
        torch.cuda.current_stream(self.device)
        if torch.cuda.is_current_stream_capturing():
            adapter.fail("AcceptanceKernel must be loaded before CUDA graph capture")
        if torch.cuda.get_device_capability(self.device) != (8, 6):
            adapter.fail("AcceptanceKernel artifact is compiled specifically for SM86")
        cubin_path = native_identity(directory.resolve(strict=True))
        self._driver = _Driver()
        self._context = self._driver.context()
        current = ctypes.c_int()
        self._driver.check(
            self._driver.ctx_device(ctypes.byref(current)), "cuCtxGetDevice"
        )
        if current.value != index:
            adapter.fail("Torch device and current CUDA driver context disagree")
        image = ctypes.create_string_buffer(cubin_path.read_bytes())
        self._module = ctypes.c_void_p()
        self._function = ctypes.c_void_p()
        self._driver.check(
            self._driver.module_load(ctypes.byref(self._module), image, 0, None, None),
            "cuModuleLoadDataEx",
        )
        try:
            self._driver.check(
                self._driver.module_function(
                    ctypes.byref(self._function), self._module, b"litos_acceptance"
                ),
                "cuModuleGetFunction",
            )
            self._driver.check(self._driver.function_load(self._function), "cuFuncLoad")
        except BaseException as construction_error:
            # Construction has not returned and no graph/launch can reference
            # this module. This is the only safe early-unload boundary.
            try:
                self._driver.check(
                    self._driver.module_unload(self._module), "cuModuleUnload"
                )
            except BaseException as cleanup_error:
                raise BaseExceptionGroup(
                    "Native acceptance construction and module cleanup failed",
                    [construction_error, cleanup_error],
                )
            raise

    def launch(
        self,
        candidates: torch.Tensor,
        target_top1: torch.Tensor,
        accept_lens_out: torch.Tensor,
        commit_lens_out: torch.Tensor,
        bonus_ids_out: torch.Tensor,
        out_tokens_out: torch.Tensor,
        prefix_lens: torch.Tensor,
        new_seq_lens_out: torch.Tensor,
    ) -> None:
        torch = self._torch
        tensors = (
            candidates,
            target_top1,
            accept_lens_out,
            commit_lens_out,
            bonus_ids_out,
            out_tokens_out,
            prefix_lens,
            new_seq_lens_out,
        )
        if not isinstance(candidates, torch.Tensor) or candidates.ndim != 2:
            adapter.fail("Native acceptance candidates must have shape [batch,8]")
        batch = candidates.shape[0]
        if batch > (2**31 - 1) * 128:
            adapter.fail("Native acceptance batch exceeds CUDA launch geometry")
        widths = 0
        for index, tensor in enumerate(tensors):
            if not isinstance(tensor, torch.Tensor):
                adapter.fail("Native acceptance requires torch tensors")
            if tensor.device != self.device or tensor.layout != torch.strided:
                adapter.fail(
                    "Native acceptance tensors must share the worker CUDA device"
                )
            if tensor.dtype not in (torch.int32, torch.int64):
                adapter.fail("Native acceptance supports only int32/int64 tensors")
            expected = (batch, 8) if index in (0, 1, 5) else (batch,)
            if tuple(tensor.shape) != expected:
                adapter.fail("Native acceptance tensor shape mismatch")
            if index != 6 and not tensor.is_contiguous():
                adapter.fail(
                    "Native acceptance token/output tensors must be contiguous"
                )
            if tensor.requires_grad or tensor.is_conj() or tensor.is_neg():
                adapter.fail(
                    "Native acceptance requires ordinary unaliased tensor values"
                )
            widths |= int(tensor.dtype == torch.int64) << index
        prefix_stride = prefix_lens.stride(0)
        if prefix_stride < 0 or prefix_stride > 2**64 - 1:
            adapter.fail("Native acceptance prefix stride exceeds the native ABI")
        if not batch:
            return
        # Pointer interval checks are metadata-only, never a device read. Strided
        # prefix holes remain conservatively owned by that input for this check.
        spans: list[tuple[int, int]] = []
        for index, tensor in enumerate(tensors):
            start = tensor.data_ptr()
            elements = (batch - 1) * prefix_stride + 1 if index == 6 else tensor.numel()
            size = elements * tensor.element_size()
            if start == 0 or start + size > 2**64 - 1:
                adapter.fail("Invalid native acceptance storage extent")
            spans.append((start, start + size))
        for output in (2, 3, 4, 5, 7):
            begin, end = spans[output]
            for other, (other_begin, other_end) in enumerate(spans):
                if other != output and begin < other_end and other_begin < end:
                    adapter.fail(
                        "Native acceptance output storage overlaps another tensor"
                    )
        if self._driver.context() != self._context:
            adapter.fail("AcceptanceKernel cannot launch in a different CUDA context")
        stream = torch.cuda.current_stream(self.device)
        # One compact host parameter slab. CUDA copies launch parameters before
        # this call returns, including capture; no tensor/device allocations.
        values = (ctypes.c_uint64 * 10)(
            *(tensor.data_ptr() for tensor in tensors), batch, prefix_stride
        )
        width_value = ctypes.c_uint(widths)
        address = ctypes.addressof(values)
        parameters = (ctypes.c_void_p * 11)(
            *(address + index * ctypes.sizeof(ctypes.c_uint64) for index in range(10)),
            ctypes.addressof(width_value),
        )
        self._driver.check(
            self._driver.launch(
                self._function,
                (batch + 127) // 128,
                1,
                1,
                128,
                1,
                1,
                0,
                ctypes.c_void_p(stream.cuda_stream),
                parameters,
                None,
            ),
            "cuLaunchKernel(litos_acceptance)",
        )

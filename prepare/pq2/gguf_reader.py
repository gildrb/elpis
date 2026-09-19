"""Strict, minimal GGUF v3 reader pinned to the PrismML fork release
prism-b10683-d8f26ee.

Scope and invariants:

- Little-endian only: the GGUF specification fixes little-endian byte order.
- Version 3 only. Other versions are rejected, never downgraded.
- Tensor data offsets are relative to the data section base, which is the
  first ``general.alignment``-aligned offset after the metadata section
  (alignment default 32, must be a power of two).
- Tensor type ids come from the pinned fork table. PQ2_0 (142) is its own
  type with geometry (128 elements, 34 bytes) and its fp16 scale stored
  first; it never aliases TQ2_0 (35, geometry (256, 66), scale stored
  after the codes).
- Only tensor types with geometry pinned from the fork's ``ggml-common.h``
  are byte-readable. Other known ids are still parsed into the tensor
  table but fail loudly on ``read_tensor_bytes``. Unknown ids are rejected
  at parse time. Nothing is silently skipped or approximated.
- All bounds, alignment, duplicate-key, duplicate-name and short-read
  violations raise; there are no silent fallbacks in this module.
"""

from __future__ import annotations

import os
import struct
from enum import IntEnum
from typing import Dict, List, Optional, Tuple, Union

import numpy as np
from numpy.typing import NDArray

_MAGIC = b"GGUF"
_VERSION = 3
_HEADER = struct.Struct("<4sIQQ")  # magic, version(u32), tensor_count(u64), kv_count(u64)
_U32 = struct.Struct("<I")
_U64 = struct.Struct("<Q")
_KEY_MAX_BYTES = 4096
_MAX_ARRAY_NESTING = 64
_DEFAULT_ALIGNMENT = 32


class GgufError(Exception):
    """Base class for every GGUF parsing or reading failure."""


class GgufFormatError(GgufError):
    """The byte stream is not a well-formed GGUF v3 file."""


class GgufBoundsError(GgufError):
    """A structure claims more bytes than the file physically contains."""


class GgufUnsupportedError(GgufError):
    """The file uses a value or tensor type outside the pinned geometry."""


class GgufMetadataType(IntEnum):
    """GGUF metadata value types (gguf.h ``gguf_metadata_value_type``)."""

    UINT8 = 0
    INT8 = 1
    UINT16 = 2
    INT16 = 3
    UINT32 = 4
    INT32 = 5
    FLOAT32 = 6
    BOOL = 7
    STRING = 8
    ARRAY = 9
    UINT64 = 10
    INT64 = 11
    FLOAT64 = 12


class GGMLType(IntEnum):
    """ggml tensor type ids pinned from the PrismML fork prism-b10683-d8f26ee."""

    F32 = 0
    F16 = 1
    Q4_0 = 2
    Q4_1 = 3
    Q5_0 = 6
    Q5_1 = 7
    Q8_0 = 8
    Q8_1 = 9
    Q2_K = 10
    Q3_K = 11
    Q4_K = 12
    Q5_K = 13
    Q6_K = 14
    Q8_K = 15
    IQ2_XXS = 16
    IQ2_XS = 17
    IQ3_XXS = 18
    IQ1_S = 19
    IQ4_NL = 20
    IQ3_S = 21
    IQ2_S = 22
    IQ4_XS = 23
    I8 = 24
    I16 = 25
    I32 = 26
    I64 = 27
    F64 = 28
    IQ1_M = 29
    BF16 = 30
    TQ1_0 = 34
    TQ2_0 = 35
    MXFP4 = 39
    NVFP4 = 40
    Q1_0 = 41
    Q2_0 = 42
    PQ2_0 = 142
    PTQ1_0 = 143


# (elements per block, bytes per block), pinned from the fork's
# ggml-common.h / ggml-quants.h. Scalar types store one element per block.
_GEOMETRY: Dict[int, Tuple[int, int]] = {
    GGMLType.F32: (1, 4),
    GGMLType.F16: (1, 2),
    GGMLType.BF16: (1, 2),
    GGMLType.F64: (1, 8),
    GGMLType.I8: (1, 1),
    GGMLType.I16: (1, 2),
    GGMLType.I32: (1, 4),
    GGMLType.I64: (1, 8),
    GGMLType.PQ2_0: (128, 34),
    GGMLType.TQ2_0: (256, 66),
}

MetadataScalar = Union[int, float, bool, str]
# Recursive alias: a metadata value is a scalar or a (possibly nested) array.
MetadataValue = Union[MetadataScalar, List["MetadataValue"]]

# value type id -> (struct for inline scalars, numpy dtype for bulk arrays)
_FIXED_VALUE_TYPES: Dict[int, Tuple[struct.Struct, np.dtype]] = {
    GgufMetadataType.UINT8.value: (struct.Struct("<B"), np.dtype(np.uint8)),
    GgufMetadataType.INT8.value: (struct.Struct("<b"), np.dtype(np.int8)),
    GgufMetadataType.UINT16.value: (struct.Struct("<H"), np.dtype(np.uint16)),
    GgufMetadataType.INT16.value: (struct.Struct("<h"), np.dtype(np.int16)),
    GgufMetadataType.UINT32.value: (struct.Struct("<I"), np.dtype(np.uint32)),
    GgufMetadataType.INT32.value: (struct.Struct("<i"), np.dtype(np.int32)),
    GgufMetadataType.FLOAT32.value: (struct.Struct("<f"), np.dtype(np.float32)),
    GgufMetadataType.UINT64.value: (struct.Struct("<Q"), np.dtype(np.uint64)),
    GgufMetadataType.INT64.value: (struct.Struct("<q"), np.dtype(np.int64)),
    GgufMetadataType.FLOAT64.value: (struct.Struct("<d"), np.dtype(np.float64)),
}

_INT_VALUE_TYPES = frozenset(
    (
        GgufMetadataType.UINT8.value,
        GgufMetadataType.INT8.value,
        GgufMetadataType.UINT16.value,
        GgufMetadataType.INT16.value,
        GgufMetadataType.UINT32.value,
        GgufMetadataType.INT32.value,
        GgufMetadataType.UINT64.value,
        GgufMetadataType.INT64.value,
    )
)


def ggml_type(value: int) -> GGMLType:
    """Resolve a raw tensor type id against the pinned table."""
    try:
        return GGMLType(value)
    except ValueError as exc:
        raise GgufFormatError(
            f"unknown ggml tensor type id {value}: this reader is pinned to the "
            "prism fork type table and rejects unknown ids"
        ) from exc


def ggml_geometry(type_: GGMLType) -> Optional[Tuple[int, int]]:
    """Return (elements per block, bytes per block) or None when not pinned."""
    return _GEOMETRY.get(type_)


def ggml_nbytes(type_: GGMLType, dims: Tuple[int, ...]) -> Optional[int]:
    """Packed byte size of a tensor, or None when geometry is not pinned.

    Row bytes follow ggml_row_size: the first dimension must tile the block
    size exactly for block types.
    """
    geom = _GEOMETRY.get(type_)
    if geom is None:
        return None
    blck, blk_bytes = geom
    if dims[0] % blck != 0:
        raise GgufFormatError(
            f"{type_.name}: first dimension {dims[0]} is not a multiple of "
            f"block size {blck}"
        )
    row_bytes = (dims[0] // blck) * blk_bytes
    rest = 1
    for d in dims[1:]:
        rest *= d
    return row_bytes * rest


def bf16_bytes_to_f32(raw: NDArray[np.uint8]) -> NDArray[np.float32]:
    """Reinterpret bfloat16 bytes as float32 by bit shifting, never int casting.

    Historical defect this guards against: int-casting raw bf16 bytes yields
    [16256, 16384, -16512] where the values are [1.0, 2.0, -1.0].
    """
    if raw.dtype != np.uint8:
        raise ValueError("bf16 raw bytes must have dtype uint8")
    if raw.shape[-1] % 2 != 0:
        raise ValueError("bf16 raw bytes must have an even last dimension")
    flat = np.ascontiguousarray(raw).reshape(-1, 2)
    u16 = flat[:, 0].astype(np.uint16) | (flat[:, 1].astype(np.uint16) << 8)
    f32 = (u16.astype(np.uint32) << 16).view(np.float32)
    return f32.reshape(raw.shape[:-1] + (raw.shape[-1] // 2,))


class TensorInfo:
    """One entry of the GGUF tensor table."""

    __slots__ = ("name", "dims", "type", "offset", "absolute_offset", "nbytes")

    def __init__(
        self,
        name: str,
        dims: Tuple[int, ...],
        type_: GGMLType,
        offset: int,
        absolute_offset: int,
        nbytes: Optional[int],
    ) -> None:
        self.name = name
        self.dims = dims
        self.type = type_
        self.offset = offset
        self.absolute_offset = absolute_offset
        self.nbytes = nbytes

    def __repr__(self) -> str:
        return (
            f"TensorInfo(name={self.name!r}, dims={self.dims}, "
            f"type={self.type.name}, offset={self.offset}, nbytes={self.nbytes})"
        )


class GgufReader:
    """Parses one GGUF v3 file: header, metadata and tensor table.

    The handle stays open for ``read_tensor_bytes``; use the context manager
    protocol or ``close``.
    """

    def __init__(self, path: str) -> None:
        self._path = os.fspath(path)
        try:
            self._file = open(self._path, "rb")
        except OSError as exc:
            raise GgufBoundsError(f"cannot open {self._path!r}: {exc}") from exc
        try:
            self._size: int = os.fstat(self._file.fileno()).st_size
            self._pos: int = 0
            self._parse()
        except BaseException:
            self._file.close()
            raise

    def __enter__(self) -> "GgufReader":
        return self

    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        self.close()

    def close(self) -> None:
        self._file.close()

    @property
    def path(self) -> str:
        return self._path

    @property
    def file_size(self) -> int:
        return self._size

    @property
    def version(self) -> int:
        return self._version

    @property
    def alignment(self) -> int:
        return self._alignment

    @property
    def data_offset(self) -> int:
        return self._data_offset

    @property
    def metadata(self) -> Dict[str, MetadataValue]:
        return self._metadata

    @property
    def kv_types(self) -> Dict[str, GgufMetadataType]:
        return self._kv_types

    @property
    def tensors(self) -> Dict[str, TensorInfo]:
        return self._tensors

    @property
    def tensor_order(self) -> List[str]:
        return self._tensor_order

    # -- low-level reads ---------------------------------------------------

    def _read(self, nbytes: int) -> bytes:
        if nbytes < 0:
            raise GgufBoundsError(f"negative read size {nbytes}")
        if self._pos + nbytes > self._size:
            raise GgufBoundsError(
                f"short read: need {nbytes} bytes at offset {self._pos}, "
                f"file holds {self._size - self._pos} bytes"
            )
        data = self._file.read(nbytes)
        if len(data) != nbytes:
            raise GgufBoundsError(
                f"underlying read returned {len(data)} of {nbytes} bytes "
                f"at offset {self._pos}"
            )
        self._pos += nbytes
        return data

    def _read_gguf_string(self, what: str) -> str:
        (length,) = _U64.unpack(self._read(8))
        raw = self._read(length)
        try:
            return raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise GgufFormatError(f"{what} is not valid utf-8: {exc}") from exc

    # -- metadata ----------------------------------------------------------

    def _read_array_element(self, elem_type: int, what: str, depth: int) -> MetadataValue:
        if elem_type == GgufMetadataType.STRING.value:
            return self._read_gguf_string(what)
        if elem_type == GgufMetadataType.ARRAY.value:
            if depth >= _MAX_ARRAY_NESTING:
                raise GgufFormatError("metadata array nesting exceeds depth limit")
            (inner_type,) = _U32.unpack(self._read(4))
            (inner_count,) = _U64.unpack(self._read(8))
            return [
                self._read_array_element(inner_type, what, depth + 1)
                for _ in range(inner_count)
            ]
        if elem_type == GgufMetadataType.BOOL.value:
            raw = self._read(1)
            if raw[0] not in (0, 1):
                raise GgufFormatError(f"{what}: bool byte must be 0 or 1, got {raw[0]}")
            return raw[0] == 1
        if elem_type not in _FIXED_VALUE_TYPES:
            raise GgufUnsupportedError(
                f"unsupported metadata value type {elem_type} for {what}"
            )
        fixed, _ = _FIXED_VALUE_TYPES[elem_type]
        (value,) = fixed.unpack(self._read(fixed.size))
        if elem_type in _INT_VALUE_TYPES:
            return int(value)
        return float(value)

    def _read_value(self, value_type: int, what: str, depth: int) -> MetadataValue:
        if value_type != GgufMetadataType.ARRAY.value:
            return self._read_array_element(value_type, what, depth)
        if depth >= _MAX_ARRAY_NESTING:
            raise GgufFormatError("metadata array nesting exceeds depth limit")
        (elem_type,) = _U32.unpack(self._read(4))
        (count,) = _U64.unpack(self._read(8))
        return [
            self._read_array_element(elem_type, what, depth + 1) for _ in range(count)
        ]

    def _parse(self) -> None:
        magic, version, tensor_count, kv_count = _HEADER.unpack(self._read(_HEADER.size))
        if magic != _MAGIC:
            raise GgufFormatError(f"bad magic {magic!r}, expected {_MAGIC!r}")
        if version != _VERSION:
            raise GgufFormatError(
                f"unsupported GGUF version {version}: this reader requires "
                f"version {_VERSION}"
            )
        self._version: int = version

        self._metadata: Dict[str, MetadataValue] = {}
        self._kv_types: Dict[str, GgufMetadataType] = {}
        for _ in range(kv_count):
            key = self._read_gguf_string("metadata key")
            key_len = len(key.encode("utf-8"))
            if not 0 < key_len <= _KEY_MAX_BYTES:
                raise GgufFormatError(
                    f"metadata key byte length {key_len} outside (0, {_KEY_MAX_BYTES}]"
                )
            if key in self._metadata:
                raise GgufFormatError(f"duplicate metadata key {key!r}")
            (value_type,) = _U32.unpack(self._read(4))
            self._metadata[key] = self._read_value(value_type, key, 0)
            self._kv_types[key] = GgufMetadataType(value_type)

        self._tensors: Dict[str, TensorInfo] = {}
        self._tensor_order: List[str] = []
        for _ in range(tensor_count):
            name = self._read_gguf_string("tensor name")
            if not name:
                raise GgufFormatError("tensor name is empty")
            if len(name.encode("utf-8")) > _KEY_MAX_BYTES:
                raise GgufFormatError("tensor name exceeds 4096 bytes")
            if name in self._tensors:
                raise GgufFormatError(f"duplicate tensor name {name!r}")
            (n_dims,) = _U32.unpack(self._read(4))
            if not 1 <= n_dims <= 4:
                raise GgufFormatError(f"tensor {name!r}: n_dims {n_dims} outside [1, 4]")
            ne: List[int] = []
            for _ in range(n_dims):
                (d,) = _U64.unpack(self._read(8))
                if d == 0:
                    raise GgufFormatError(f"tensor {name!r} has a zero dimension")
                ne.append(d)
            dims = tuple(ne)
            (raw_type,) = _U32.unpack(self._read(4))
            type_ = ggml_type(raw_type)
            (rel_offset,) = _U64.unpack(self._read(8))
            nbytes = ggml_nbytes(type_, dims)
            info = TensorInfo(
                name=name,
                dims=dims,
                type_=type_,
                offset=rel_offset,
                absolute_offset=0,  # fixed below once the data base is known
                nbytes=nbytes,
            )
            self._tensors[name] = info
            self._tensor_order.append(name)

        alignment_raw = self._metadata.get("general.alignment", None)
        if alignment_raw is not None and (
            type(alignment_raw) is bool or not isinstance(alignment_raw, int)
        ):
            raise GgufFormatError("general.alignment must be a UINT32 integer")
        self._alignment: int = (
            _DEFAULT_ALIGNMENT if alignment_raw is None else int(alignment_raw)
        )
        if self._alignment <= 0 or (self._alignment & (self._alignment - 1)) != 0:
            raise GgufFormatError(
                f"general.alignment {self._alignment} must be a positive power of two"
            )

        self._data_offset: int = (
            (self._pos + self._alignment - 1) // self._alignment
        ) * self._alignment
        if self._size < self._data_offset:
            raise GgufBoundsError(
                f"data section base {self._data_offset} exceeds file size {self._size}"
            )

        prev_end = 0
        prev_name = ""
        for name in self._tensor_order:
            info = self._tensors[name]
            if info.nbytes is None:
                continue  # geometry not pinned; read_tensor_bytes fails loudly
            if info.offset % self._alignment != 0:
                raise GgufFormatError(
                    f"tensor {name!r} offset {info.offset} is not aligned "
                    f"to {self._alignment}"
                )
            info.absolute_offset = self._data_offset + info.offset
            if info.absolute_offset + info.nbytes > self._size:
                raise GgufBoundsError(
                    f"tensor {name!r} data [{info.absolute_offset}, "
                    f"{info.absolute_offset + info.nbytes}) exceeds file "
                    f"size {self._size}"
                )
            if info.absolute_offset < prev_end:
                raise GgufFormatError(
                    f"tensor {name!r} overlaps tensor {prev_name!r}"
                )
            prev_end = info.absolute_offset + info.nbytes
            prev_name = name

    # -- tensor data ---------------------------------------------------------

    def read_tensor_bytes(self, name: str) -> bytes:
        """Read the exact packed bytes of one tensor, with bounds validation."""
        info = self._tensors.get(name)
        if info is None:
            raise GgufFormatError(f"unknown tensor {name!r}")
        if info.nbytes is None:
            raise GgufUnsupportedError(
                f"tensor {name!r} has type {info.type.name} with no pinned "
                "geometry; this reader refuses to guess a byte layout"
            )
        self._file.seek(info.absolute_offset)
        data = self._file.read(info.nbytes)
        if len(data) != info.nbytes:
            raise GgufBoundsError(
                f"short tensor read for {name!r}: got {len(data)} of "
                f"{info.nbytes} bytes"
            )
        return data

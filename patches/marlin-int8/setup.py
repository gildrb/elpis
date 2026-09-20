# SPDX-License-Identifier: Apache-2.0
"""Build with the image's existing Torch/CUDA: pip install --no-build-isolation --no-deps ."""
import os
from pathlib import Path
import re
import subprocess
import sys

from setuptools import setup
import torch
from torch.utils.cpp_extension import BuildExtension, CUDAExtension, CUDA_HOME

ROOT = Path(__file__).resolve().parent
KERNELS = ROOT / "csrc" / "quantization" / "gptq_marlin"
if CUDA_HOME is None:
    raise RuntimeError("CUDA toolkit (nvcc) is required; a visible GPU is not")
if not hasattr(torch, "float8_e8m0fnu"):
    raise RuntimeError("The pinned upstream host dispatcher requires Torch >=2.8")
# Never infer targets from visible GPUs, and never silently build another arch.
os.environ["TORCH_CUDA_ARCH_LIST"] = "8.6"
nvcc_version = subprocess.check_output(
    [str(Path(CUDA_HOME) / "bin" / "nvcc"), "--version"], text=True
)
match = re.search(r"release (\d+)\.(\d+)", nvcc_version)
if match is None:
    raise RuntimeError("Cannot identify the installed CUDA compiler version")
cuda_version = tuple(map(int, match.groups()))
if cuda_version < (12, 0):
    raise RuntimeError("The upstream cuda_fp8.h dependency requires CUDA >=12.0")
subprocess.run([sys.executable, str(KERNELS / "generate_kernels.py"), "8.6"], check=True)

nvcc_flags = ["-O3", "-std=c++17", "--expt-relaxed-constexpr",
              "--expt-extended-lambda", "-Xcompiler=-fvisibility=hidden"]
# Upstream uses cross-TU explicit kernel instantiations. CUDA >=12.8 changed
# the template stub default; retaining this upstream flag is essential to link.
if cuda_version >= (12, 8):
    nvcc_flags.append("-static-global-template-stub=false")

setup(
    name="litos-marlin-int8",
    version="0.1.0",
    packages=["litos_marlin_int8"],
    package_data={"litos_marlin_int8": ["py.typed"]},
    data_files=[("share/litos-marlin-int8", ["source-manifest.json", "NOTICE", "LICENSE"])],
    python_requires=">=3.10",
    install_requires=["torch>=2.8", "triton>=3.4"],
    ext_modules=[CUDAExtension(
        "litos_marlin_int8._litos_marlin_int8",
        sources=["csrc/bindings.cpp",
                 "csrc/quantization/gptq_marlin/gptq_marlin.cu",
                 "csrc/quantization/gptq_marlin/gptq_marlin_repack.cu",
                 "csrc/quantization/gptq_marlin/sm80_kernel_s8_u4b8_float16.cu",
                 "csrc/quantization/gptq_marlin/sm80_kernel_s8_u4b8_bfloat16.cu"],
        include_dirs=[str(ROOT / "csrc"), str(KERNELS)],
        extra_compile_args={"cxx": ["-O3", "-std=c++17", "-fvisibility=hidden"],
                            "nvcc": nvcc_flags},
    )],
    cmdclass={"build_ext": BuildExtension},
)

// SPDX-License-Identifier: Apache-2.0
// Schemas derived from vLLM torch_bindings.cpp at the source-manifest pin.
#include <torch/library.h>
#include "core/registration.h"
#include "core/scalar_type.hpp"

TORCH_LIBRARY_EXPAND(TORCH_EXTENSION_NAME, ops) {
  ops.def("uint4b8_id() -> int", []() { return vllm::kU4B8.id(); });
  // Unlike upstream, truthfully declare mutations and the optional output alias.
  ops.def(
      "gptq_marlin_gemm(Tensor a, Tensor(a!)? c_or_none, Tensor b_q_weight, "
      "Tensor? b_bias_or_none, Tensor b_scales, Tensor? a_scales, "
      "Tensor? global_scale, Tensor? b_zeros_or_none, Tensor? g_idx_or_none, "
      "Tensor? perm_or_none, Tensor(b!) workspace, int b_type_id, "
      "int size_m, int size_n, int size_k, bool is_k_full, "
      "bool use_atomic_add, bool use_fp32_reduce, bool is_zp_float) -> Tensor(a!)");
  ops.def(
      "gptq_marlin_repack(Tensor b_q_weight, Tensor perm, "
      "int size_k, int size_n, int num_bits, bool is_a_8bit) -> Tensor");
}

REGISTER_EXTENSION(TORCH_EXTENSION_NAME)

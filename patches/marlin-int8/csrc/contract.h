// SPDX-License-Identifier: Apache-2.0
// Local standalone ABI admission checks; no device arithmetic is defined here.
#pragma once

#include <ATen/MemoryOverlap.h>
#include <ATen/cuda/CUDAContext.h>
#include <torch/all.h>
#include <cuda_runtime.h>
#include <limits>
#include "core/scalar_type.hpp"

namespace litos_marlin_int8 {
inline void check_nk(int64_t n, int64_t k) {
  TORCH_CHECK(n > 0 && n % 64 == 0, "N must be positive and divisible by 64");
  // At K=128 upstream infers channelwise scales, a different representation.
  TORCH_CHECK(k >= 256 && k % 128 == 0,
              "K must be >=256 and divisible by 128 (group128 only)");
  TORCH_CHECK(n <= std::numeric_limits<int>::max() / k,
              "N*K exceeds upstream 32-bit indexing range");
}

inline void check_device(const torch::Tensor& t) {
  TORCH_CHECK(t.is_cuda(), "expected a CUDA tensor");
  const auto* properties = at::cuda::getDeviceProperties(t.get_device());
  TORCH_CHECK(properties->major == 8 && properties->minor == 6,
              "this extension supports SM86 only");
}

inline void check_tensor(const torch::Tensor& t, const torch::Tensor& reference,
                         at::ScalarType dtype, const char* name) {
  TORCH_CHECK(t.device() == reference.device(), name, " must share the CUDA device");
  TORCH_CHECK(t.scalar_type() == dtype, name, " has unsupported dtype");
  TORCH_CHECK(t.is_contiguous(), name, " must be contiguous");
  TORCH_CHECK(!t.requires_grad(), name, " is inference-only");
  TORCH_CHECK(t.numel() == 0 || reinterpret_cast<uintptr_t>(t.data_ptr()) % 16 == 0,
              name, " must be 16-byte aligned");
}

inline void check_empty(const std::optional<torch::Tensor>& t,
                        const torch::Tensor& reference, const char* name) {
  if (t.has_value()) {
    check_tensor(*t, reference, at::kInt, name);
    TORCH_CHECK(t->dim() == 1 && t->numel() == 0, name, " must be None or empty int32");
  }
}

inline void check_repack(const torch::Tensor& w, const torch::Tensor& perm,
                         int64_t k, int64_t n, int64_t bits, bool a8) {
  check_nk(n, k);
  check_device(w);
  check_tensor(w, w, at::kInt, "b_q_weight");
  check_tensor(perm, w, at::kInt, "perm");
  TORCH_CHECK(w.dim() == 2 && w.size(0) == k / 8 && w.size(1) == n,
              "GPTQ input must have int32 shape [K/8,N]");
  TORCH_CHECK(perm.dim() == 1 && perm.numel() == 0, "activation ordering is unsupported");
  TORCH_CHECK(bits == 4 && a8, "only num_bits=4, is_a_8bit=True is supported");
}

inline void check_gemm(
    const torch::Tensor& a, const std::optional<torch::Tensor>& c,
    const torch::Tensor& w, const std::optional<torch::Tensor>& bias,
    const torch::Tensor& scales, const std::optional<torch::Tensor>& a_scales,
    const std::optional<torch::Tensor>& global_scale,
    const std::optional<torch::Tensor>& zeros,
    const std::optional<torch::Tensor>& g_idx,
    const std::optional<torch::Tensor>& perm, const torch::Tensor& workspace,
    int64_t type, int64_t m, int64_t n, int64_t k, bool k_full,
    bool atomic_add, bool zp_float) {
  check_nk(n, k);
  TORCH_CHECK(m >= 0 && m <= std::numeric_limits<int>::max() / std::max(n, k),
              "M exceeds upstream 32-bit indexing range");
  check_device(a);
  check_tensor(a, a, at::kChar, "a");
  TORCH_CHECK(a.dim() == 2 && a.size(0) == m && a.size(1) == k,
              "a must have int8 shape [M,K]");
  TORCH_CHECK(type == vllm::kU4B8.id(), "only uint4b8 symmetric weights are supported");
  TORCH_CHECK(k_full && !zp_float, "requires is_k_full=True, is_zp_float=False");
  TORCH_CHECK(!global_scale.has_value(),
              "global_scale is NVFP4-only; multiply a_scales by input_global_scale instead");
  check_empty(zeros, a, "b_zeros");
  check_empty(g_idx, a, "g_idx");
  check_empty(perm, a, "perm");
  check_tensor(w, a, at::kInt, "b_q_weight");
  TORCH_CHECK(w.dim() == 2 && w.size(0) == k / 16 && w.size(1) == n * 2,
              "repacked weight must have int32 shape [K/16,2*N]");
  TORCH_CHECK(scales.scalar_type() == at::kHalf || scales.scalar_type() == at::kBFloat16,
              "b_scales must carry packed signed-int16 bits in an fp16/bf16 tensor");
  check_tensor(scales, a, scales.scalar_type(), "b_scales");
  TORCH_CHECK(scales.dim() == 2 && scales.size(0) == k / 128 && scales.size(1) == n,
              "b_scales must have group128 shape [K/128,N]");
  TORCH_CHECK(!atomic_add || scales.scalar_type() == at::kHalf,
              "BF16 atomic reduction is unsupported on SM86");
  TORCH_CHECK(a_scales.has_value(), "a_scales is required for INT8 activations");
  check_tensor(*a_scales, a, at::kFloat, "a_scales");
  TORCH_CHECK((a_scales->dim() == 1 && a_scales->size(0) == m) ||
              (a_scales->dim() == 2 && a_scales->size(0) == m && a_scales->size(1) == 1),
              "a_scales must have float32 shape [M] or [M,1]");
  check_tensor(workspace, a, at::kInt, "workspace");
  TORCH_CHECK(workspace.dim() == 1, "workspace must be a one-dimensional int32 lock buffer");
  at::assert_no_overlap(workspace, a);
  at::assert_no_overlap(workspace, w);
  at::assert_no_overlap(workspace, scales);
  at::assert_no_overlap(workspace, *a_scales);
  if (bias.has_value()) {
    check_tensor(*bias, a, scales.scalar_type(), "b_bias");
    TORCH_CHECK(bias->dim() == 1 && bias->size(0) == n,
                "b_bias must have shape [N] and Marlin's single permutation");
    at::assert_no_overlap(workspace, *bias);
  }
  if (c.has_value()) {
    check_tensor(*c, a, scales.scalar_type(), "c");
    TORCH_CHECK(c->dim() == 2 && c->size(0) == m && c->size(1) == n,
                "c must have shape [M,N] and match b_scales' carrier dtype");
    at::assert_no_overlap(*c, a);
    at::assert_no_overlap(*c, w);
    at::assert_no_overlap(*c, scales);
    at::assert_no_overlap(*c, *a_scales);
    at::assert_no_overlap(*c, workspace);
    if (bias.has_value()) at::assert_no_overlap(*c, *bias);
  }
}
}  // namespace litos_marlin_int8

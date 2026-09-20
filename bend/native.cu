// Appended verbatim to the original Bend-generated C by native_build.py.
// LITOS_LEAF and Bool discriminants are bound by retained finite-domain evidence.
// No acceptance algebra, VM, allocation, or policy table lives in this glue.
static_assert(sizeof(Term) == 8 && sizeof(u32) == 4 &&
                  sizeof(int) == 4 && sizeof(long long) == 8,
              "Bend scalar word/discriminant ABI changed");

static __device__ __forceinline__ long long litos_read(
    const void* data, unsigned int wide, unsigned long long index) {
  return wide ? ((const long long*)data)[index] : ((const int*)data)[index];
}

static __device__ __forceinline__ void litos_write(
    void* data, unsigned int wide, unsigned long long index,
    unsigned long long bits) {
  // Corresponding unsigned types preserve the exact signed tensor bit pattern.
  if (wide) ((unsigned long long*)data)[index] = bits;
  else ((unsigned int*)data)[index] = (unsigned int)bits;
}

extern "C" __global__ void litos_acceptance(
    const void* __restrict__ candidates, const void* __restrict__ target_top1,
    void* __restrict__ accept_lens, void* __restrict__ commit_lens,
    void* __restrict__ bonus_ids, void* __restrict__ out_tokens,
    const void* __restrict__ prefix_lens, void* __restrict__ new_seq_lens,
    unsigned long long batch, unsigned long long prefix_stride,
    unsigned int widths) {
  const unsigned long long row =
      (unsigned long long)blockIdx.x * blockDim.x + threadIdx.x;
  if (row >= batch) return;
  const unsigned long long base = row * 8;
  const unsigned int cw = widths & 1, tw = (widths >> 1) & 1;
  // Exactly seven scalar registers, not a Bend collection or an acceptance mask.
  const u32 m0 = litos_read(candidates, cw, base + 1) == litos_read(target_top1, tw, base + 0) ? LITOS_TRUE : LITOS_FALSE;
  const u32 m1 = litos_read(candidates, cw, base + 2) == litos_read(target_top1, tw, base + 1) ? LITOS_TRUE : LITOS_FALSE;
  const u32 m2 = litos_read(candidates, cw, base + 3) == litos_read(target_top1, tw, base + 2) ? LITOS_TRUE : LITOS_FALSE;
  const u32 m3 = litos_read(candidates, cw, base + 4) == litos_read(target_top1, tw, base + 3) ? LITOS_TRUE : LITOS_FALSE;
  const u32 m4 = litos_read(candidates, cw, base + 5) == litos_read(target_top1, tw, base + 4) ? LITOS_TRUE : LITOS_FALSE;
  const u32 m5 = litos_read(candidates, cw, base + 6) == litos_read(target_top1, tw, base + 5) ? LITOS_TRUE : LITOS_FALSE;
  const u32 m6 = litos_read(candidates, cw, base + 7) == litos_read(target_top1, tw, base + 6) ? LITOS_TRUE : LITOS_FALSE;
  Term words[4];
  Env env = {0, 0};
  if (!LITOS_LEAF(env, words, m0, m1, m2, m3, m4, m5, m6)) {
    asm volatile("trap;");
    return;
  }
  const unsigned int ow = (widths >> 5) & 1;
  const long long bonus = litos_read(target_top1, tw, base + words[2]);
  for (unsigned int j = 0; j < 8; ++j) {
    const long long value = j == words[0] ? bonus :
        (j < 7 ? litos_read(candidates, cw, base + j + 1) : 0);
    litos_write(out_tokens, ow, base + j, value);
  }
  litos_write(accept_lens, (widths >> 2) & 1, row, words[0]);
  litos_write(commit_lens, (widths >> 3) & 1, row, words[1]);
  litos_write(bonus_ids, (widths >> 4) & 1, row, bonus);
  // Match the original int32 delta's promotion to the prefix input width:
  // int32 addition wraps before a possible int64 output conversion.
  const unsigned int pw = (widths >> 6) & 1;
  const unsigned long long prefix =
      litos_read(prefix_lens, pw, row * prefix_stride);
  const unsigned long long sum = prefix + words[3];
  const unsigned int low = (unsigned int)sum;
  const unsigned long long next = pw ? sum :
      ((low & 0x80000000u) ? (0xffffffff00000000ull | low) : low);
  litos_write(new_seq_lens, (widths >> 7) & 1, row, next);
}

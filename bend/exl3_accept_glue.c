// Appended after the UNCHANGED Bend-emitted C of bend/EXL3_ACCEPT.bend
// (its main renamed by the including translation unit). exl3_build.py binds
// ETA_EXL3_LEAF to the admitted emitted leaf of exl3_accept.accept. This
// glue holds no acceptance logic: it validates the served domain, narrows
// ids, calls the leaf once with Env{0, 0} and checks its output range.
_Static_assert(sizeof(Term) == 8 && sizeof(u32) == 4,
               "Bend scalar word ABI changed");

#define ETA_EXL3_ID_LIMIT 4294967296LL
#define ETA_EXL3_BUDGET_LIMIT ((int64_t)NAT_IMM)

// cells: [0] k (1..7), [1] budget (1..2^48-1), [2] checkpoint (0..k),
// [3] stop count (0..4), [4..7] stop slots, [8..15] verify ids t0..t7,
// [16..22] proposals p0..p6. Result r >= 2: count = r >> 1, eos = r & 1.
// Errors: -1 k, -2 stop count, -3 budget, -4 checkpoint, -5 id range,
// -6 leaf failure or output outside 1..k+1 / {0, 1}.
__attribute__((visibility("default"))) int32_t eta_exl3_accept(
    const int64_t* cells) {
  const int64_t k = cells[0];
  const int64_t budget = cells[1];
  const int64_t checkpoint = cells[2];
  const int64_t stops = cells[3];
  if (k < 1 || k > 7) return -1;
  if (stops < 0 || stops > 4) return -2;
  if (budget < 1 || budget > ETA_EXL3_BUDGET_LIMIT) return -3;
  if (checkpoint < 0 || checkpoint > k) return -4;
  for (int64_t i = 0; i < stops; ++i) {
    if (cells[4 + i] < 0 || cells[4 + i] >= ETA_EXL3_ID_LIMIT) return -5;
  }
  for (int64_t i = 0; i <= k; ++i) {
    if (cells[8 + i] < 0 || cells[8 + i] >= ETA_EXL3_ID_LIMIT) return -5;
  }
  for (int64_t i = 0; i < k; ++i) {
    if (cells[16 + i] < 0 || cells[16 + i] >= ETA_EXL3_ID_LIMIT) return -5;
  }
  Term out[2];
  Env env = {0, 0};
  if (!ETA_EXL3_LEAF(env, out, (Term)k, (Term)budget, (Term)checkpoint,
                       (Term)stops, (u32)cells[4], (u32)cells[5],
                       (u32)cells[6], (u32)cells[7], (u32)cells[8],
                       (u32)cells[9], (u32)cells[10], (u32)cells[11],
                       (u32)cells[12], (u32)cells[13], (u32)cells[14],
                       (u32)cells[15], (u32)cells[16], (u32)cells[17],
                       (u32)cells[18], (u32)cells[19], (u32)cells[20],
                       (u32)cells[21], (u32)cells[22])) {
    return -6;
  }
  const Term count = out[0];
  const Term eos = out[1];
  if (count < 1 || count > (Term)k + 1 || eos > 1) return -6;
  return (int32_t)(count * 2 + eos);
}

// Appended after the UNCHANGED Bend-emitted C of bend/EXL3_TREE_ACCEPT.bend
// (its main renamed by the including translation unit). exl3_build.py binds
// ELPIS_EXL3_TREE_LEAF and ELPIS_EXL3_TREE_DERIVE to the admitted emitted leaves
// of exl3_tree_accept.accept_tree and exl3_tree_accept.derive. This glue holds
// no acceptance or derivation logic: it validates the served domain, narrows
// ids, calls a leaf once with Env{0, 0} and checks its output range.
_Static_assert(sizeof(Term) == 8 && sizeof(u32) == 4,
               "Bend scalar word ABI changed");

#define ELPIS_EXL3_ID_LIMIT 4294967296LL
#define ELPIS_EXL3_BUDGET_LIMIT ((int64_t)NAT_IMM)

// Parents of an 8-row tree: row 0 is -1, row r in 0..r-1.
static int elpis_exl3_tree_parents(const int64_t* parent) {
  if (parent[0] != -1) return 0;
  for (int64_t r = 1; r < 8; ++r) {
    if (parent[r] < 0 || parent[r] >= r) return 0;
  }
  return 1;
}

// cells: [0] budget (1..2^48-1), [1] checkpoint (0..7), [2] stop count
// (0..4), [3..6] stop slots, [7..14] verify ids of rows 0..7, [15..22]
// tokens of rows 0..7 (row 0 = anchor, range-checked only), [23..30]
// parents (row 0 = -1, else 0..r-1). Result r >= 2: last = r >> 5,
// count = (r >> 1) & 15, eos = r & 1. Errors: -1 parents, -2 stop count,
// -3 budget, -4 checkpoint, -5 id range, -6 leaf failure or output outside
// count 1..8 / eos {0, 1} / last 0..7.
__attribute__((visibility("default"))) int32_t elpis_exl3_tree_accept(
    const int64_t* cells) {
  const int64_t budget = cells[0];
  const int64_t checkpoint = cells[1];
  const int64_t stops = cells[2];
  if (!elpis_exl3_tree_parents(cells + 23)) return -1;
  if (stops < 0 || stops > 4) return -2;
  if (budget < 1 || budget > ELPIS_EXL3_BUDGET_LIMIT) return -3;
  if (checkpoint < 0 || checkpoint > 7) return -4;
  for (int64_t i = 0; i < stops; ++i) {
    if (cells[3 + i] < 0 || cells[3 + i] >= ELPIS_EXL3_ID_LIMIT) return -5;
  }
  for (int64_t i = 7; i < 23; ++i) {
    if (cells[i] < 0 || cells[i] >= ELPIS_EXL3_ID_LIMIT) return -5;
  }
  Term out[3];
  Env env = {0, 0};
  if (!ELPIS_EXL3_TREE_LEAF(env, out, (Term)budget, (Term)checkpoint,
                          (Term)stops, (u32)cells[3], (u32)cells[4],
                          (u32)cells[5], (u32)cells[6], (u32)cells[7],
                          (u32)cells[8], (u32)cells[9], (u32)cells[10],
                          (u32)cells[11], (u32)cells[12], (u32)cells[13],
                          (u32)cells[14], (u32)cells[16], (u32)cells[17],
                          (u32)cells[18], (u32)cells[19], (u32)cells[20],
                          (u32)cells[21], (u32)cells[22], (Term)cells[24],
                          (Term)cells[25], (Term)cells[26], (Term)cells[27],
                          (Term)cells[28], (Term)cells[29], (Term)cells[30])) {
    return -6;
  }
  const Term count = out[0];
  const Term eos = out[1];
  const Term last = out[2];
  if (count < 1 || count > 8 || eos > 1 || last > 7) return -6;
  return (int32_t)(last * 32 + count * 2 + eos);
}

// parent: 8 cells as above; out: the 128 TreeDesc bytes. Returns 0, or -1
// for invalid parents, -6 for a leaf failure or a value outside 0..255.
__attribute__((visibility("default"))) int32_t elpis_exl3_tree_derive(
    const int64_t* parent, uint8_t* out) {
  if (!elpis_exl3_tree_parents(parent)) return -1;
  Term bytes[128];
  Env env = {0, 0};
  if (!ELPIS_EXL3_TREE_DERIVE(env, bytes, (Term)parent[1], (Term)parent[2],
                            (Term)parent[3], (Term)parent[4], (Term)parent[5],
                            (Term)parent[6], (Term)parent[7])) {
    return -6;
  }
  for (int i = 0; i < 128; ++i) {
    if (bytes[i] > 255) return -6;
  }
  for (int i = 0; i < 128; ++i) out[i] = (uint8_t)bytes[i];
  return 0;
}

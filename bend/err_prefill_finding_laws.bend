# FINDING (not contract): refutations of the prefill-attention domination law for ext 3022 v4 against stock
# ExLlamaV3 355c6ee, on the model err_prefill.bend (causes summarized in its header). Each law states that elpis's
# worst leaf of a concrete row is dominated by NO stock leaf / composite of that row (at exchange rate 128), i.e. the
# contract law "elpis path dom stock worst-leaf path" is FALSE there. Proven by computation in
# err_prefill_finding_proof.bend; same named hypotheses as err_prefill_laws.bend. These record the current state of
# 3022 v4; they are expected to stop holding once the kernel is fixed, and then belong deleted, not re-pinned.
# SCOPE: they describe ext 3022 v4 as it was BEFORE ext 3031 (patches/exl3-ext/3031-prefill-pattn-dominate.patch),
# which replaces that arithmetic (tree denominator, chains of E tiles + combine; contract now err_pfix_laws.bend).
# The finding is kept until the GPU gates of 3031 pass, and then retired.
import Base
import ./err_bound.bend as Eb
import ./err_prefill.bend as Ep

# 1. vs unsplit stock (served when the job's block table spans < 8192 keys), rows seeing n = 1 or 2 key tiles
# (absolute position < 64): elpis's worst leaf (tile 0, first half) is dominated by no stock leaf of the row (all
# tiles, both halves); common segment: the worst masked score segments of the numerator and denominator keys.
# Cause: elpis's denominator is 7 sequential f_add + 2 quad f_add (9 r32), stock's tl.sum is a depth-5 tree.
law pv_unsplit_false:
  {Ep.none_dom(128n, Eb.add(Eb.add(Ep.score_s(False{}, 0n), Ep.score_s(False{}, 0n)), Ep.elpis_leaf(0n, 0n, False{})),
    Ep.add_all(Eb.add(Ep.score_s(False{}, 0n), Ep.score_s(False{}, 0n)), Ep.unsplit_leaves(1n))) == True{} : Bool} &
  {Ep.none_dom(128n, Eb.add(Eb.add(Ep.score_s(False{}, 0n), Ep.score_s(False{}, 0n)), Ep.elpis_leaf(0n, 1n, False{})),
    Ep.add_all(Eb.add(Ep.score_s(False{}, 0n), Ep.score_s(False{}, 0n)), Ep.unsplit_leaves(2n))) == True{} : Bool}

# 2. vs the served split stock (num_splits = 2 for block tables >= 8192 keys): no stock composite (numerator key in
# either split, any tile, either half; denominator worst key of either split) dominates elpis's worst leaf, for
#   row 63 at prefix 0 (splits of 1 + 1 tiles: r32 tier),
#   row 127 at prefix 0 (2 + 2 tiles: ex2 kind),
#   row 2047 at prefix 0 (32 + 32 tiles, the last row of a 2048 chunk: ex2 kind).
# Cause (ex2): elpis's leaf passes one online-softmax rescale (alpha = ex2) per later tile of the whole row (2 (n - 1)
# with the denominator); stock's split chains are half as long and the combine adds one exp2 weight.
law pv_split_false:
  {Ep.none_dom(128n, Eb.add(Eb.add(Ep.score_s(False{}, 0n), Ep.score_s(False{}, 0n)), Ep.elpis_leaf(0n, 1n, False{})),
    Ep.add_all(Eb.add(Ep.score_s(False{}, 0n), Ep.score_s(False{}, 0n)), Ep.split_leaves(1n, 1n))) == True{} : Bool} &
  {Ep.none_dom(128n, Eb.add(Eb.add(Ep.score_s(False{}, 0n), Ep.score_s(False{}, 0n)), Ep.elpis_leaf(0n, 3n, False{})),
    Ep.add_all(Eb.add(Ep.score_s(False{}, 0n), Ep.score_s(False{}, 0n)), Ep.split_leaves(2n, 2n))) == True{} : Bool} &
  {Ep.none_dom(128n, Eb.add(Eb.add(Ep.score_s(True{}, 0n), Ep.score_s(True{}, 0n)), Ep.elpis_leaf(0n, 63n, False{})),
    Ep.add_all(Eb.add(Ep.score_s(True{}, 0n), Ep.score_s(True{}, 0n)), Ep.split_leaves(32n, 32n))) == True{} : Bool}

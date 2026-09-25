# Ext 8204 deferred phase-1 publish (knob defer_pub = 1, the default) of the ext 8201 fused MLP
# (exl3_mlp_m16_kernel.cuh) and of the ext 8202 layer tail, whose phases 1/2 are 8201's
# (exl3_tail_m16_kernel.cuh). Append-only extension of bend/mlp_m16_sched.bend: the tables, the
# partition and every counter event of 8201 are unchanged; only the POSITION of the phase-1 counter
# signals in a block's program moves.
# - 8201 (defer_pub = 0): after flushing group g, each warp fences and adds 1 to cnt1[g] (Sig{C1{g}}
#   right after Flush{g}, mlp_m16_sched's sigs1).
# - 8204 (defer_pub = 1): a flush in the middle of the slice (a group crossing) neither fences nor
#   signals; after the slice's last flush one fence, then each warp adds 1 to cnt1 of every group of
#   its slice (lane i publishes group s1 / KT1 + i). So a block's program is: its whole phase-1 main
#   loop, then exactly 8201's counter events of the block in 8201's order.
# start_order (8204's other knob) only moves the input-transform LOADS ahead of the ring prologue:
# no main-loop, table or counter event changes, so every law of this module and of mlp_m16_sched /
# tail_m16_sched holds for either value. The model is the default vperm = 0 (block b runs its own
# slice); vperm = 1 is a diagnostic knob that runs virtual block (b + G / 2) mod G on CTA b.
# Laws: bend/mlp_m16_defer_laws.bend.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./mlp_m16_defer_spec.bend as Spec

def tag_work(evs: List<&2, PSpec.Ev>, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match evs:
    case Nil{}:
      rest
    case ev <> more:
      Spec.Work{ev} <> tag_work(more, rest)

def tag_sync(evs: List<&2, MSpec.Ev>, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match evs:
    case Nil{}:
      rest
    case ev <> more:
      Spec.Sync{ev} <> tag_sync(more, rest)

# Block b's phase-1 main loop over its table slice [s1, e1) (8201's, unchanged).
def mainloop1(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> List<&2, PSpec.Ev>:
  Part.mainloop(Mlp.s1(G, H, I, b), Mlp.e1(G, H, I, b), Mlp.kt1(H))

# 8204 (deferred): the whole phase-1 main loop, then 8201's counter events of the block.
def events(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> List<&2, Spec.Ev>:
  tag_work(mainloop1(G, H, I, b), tag_sync(Mlp.events(G, H, I, b), Nil{}))

# 8201 (per-flush publish), the reference order: the phase-1 main loop with Sig{C1{g}} right after
# each Flush{g}, then 8201's finish and phase-2 events.
def eager.go(+evs: List<&2, PSpec.Ev>, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match evs:
    case Nil{}:
      rest
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          Spec.Work{PSpec.Tile{g, it}} <> eager.go(more, rest)
        case PSpec.Flush{g}:
          Spec.Work{PSpec.Flush{g}} <> Spec.Sync{MSpec.Sig{MSpec.C1{g}, 8n, 0n}} <> eager.go(more, rest)

def eager(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> List<&2, Spec.Ev>:
  eager.go(mainloop1(G, H, I, b), tag_sync(Mlp.finish(Mlp.pairs(I), Mlp.fin_pair(G, H, I, b),
    Mlp.waits2(Mlp.waits(G, H, I, b))), Nil{}))

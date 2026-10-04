# The decode table of /tmp/kernel-work/Int8Linear/decacc/work/partA.md (analyze_a.py over the stock sources
# and the persisted autotune cache), transcribed: the stock class of every served (op, m), in k-values.
# lm_head's entry is a placeholder (never used: law stock_table_partA excludes it through not_head).
# Used by bend/precision_laws.bend (law stock_table_partA) and printed by bend/PRECISION_TABLE.bend.
import Base
import ./precision_order.bend as Ord
import ./precision_stock.bend as S

def part_a(op: S.Op, +m: Nat) -> Ord.Acc:
  match op:
    case S.AttnQG{}:
      Ord.Runs{2560n, 2560n, False{}}
    case S.AttnK{}:
      Ord.Runs{2560n, 2560n, False{}}
    case S.AttnV{}:
      Ord.Runs{2560n, 2560n, False{}}
    case S.GdnQkv{}:
      Ord.Runs{1024n, 2048n, True{}}
    case S.GdnZ{}:
      Ord.Runs{1024n, 2048n, True{}}
    case S.AttnO{}:
      S.acc_pick(Nat.is_le(m, 2n), Ord.Int8{}, Ord.Runs{64n, 64n, True{}})
    case S.GdnOut{}:
      S.acc_pick(Nat.is_le(m, 2n), Ord.Int8{}, Ord.Runs{64n, 64n, True{}})
    case S.MlpGate{}:
      S.acc_pick(Nat.is_le(m, 2n), Ord.Int8{}, Ord.Runs{112n, 2128n, False{}})
    case S.MlpUp{}:
      S.acc_pick(Nat.is_le(m, 2n), Ord.Int8{}, Ord.Runs{112n, 2128n, False{}})
    case S.MlpDown{}:
      S.acc_pick(Nat.is_le(m, 2n), Ord.Int8{}, Ord.Runs{64n, 64n, True{}})
    case S.LmHead{}:
      Ord.Fp32{}

def not_head(op: S.Op) -> Bool:
  match op:
    case S.LmHead{}:
      False{}
    case S.AttnQG{}:
      True{}
    case S.AttnK{}:
      True{}
    case S.AttnV{}:
      True{}
    case S.AttnO{}:
      True{}
    case S.GdnQkv{}:
      True{}
    case S.GdnZ{}:
      True{}
    case S.GdnOut{}:
      True{}
    case S.MlpGate{}:
      True{}
    case S.MlpUp{}:
      True{}
    case S.MlpDown{}:
      True{}

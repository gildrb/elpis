# elpis decode GEMM routes and accumulation schedules: elpis 4cc1429's ext series, which the planned
# p9501x2 series (15a6d4a) keeps for decode (it drops 3021c, a prefill attention kernel, and adds 5110g,
# a prefill-only 4096-row merge in generator/job.py + modules/gated_delta_net.py, and 9501b, the
# persistent prefix cache in generator/). Nat model of accumulation SCHEDULES, no floating-point values.
#
# The m16 side is DERIVED from the proven schedule models, not restated: the fold schedule is the one of
# the DIET traces of bend/m16_diet.bend (served EXL3_M16_DIET modes 1 / 2; mode 2 has mode 1's loop trace,
# bend/m16_diet2_laws.bend) and bend/m16_diet_spec.bend (mode 0), which m16_diet_laws.bend proves equal
# for the m16g, 8201 and 8202 kernels over the v2 skeleton of bend/gemm_m16_partition.bend; the fold
# cadence is their fold cadence FO (m16_diet.bend cfg_fold = 2 k16 tiles: ext 3023 fold-32, the served
# EXL3_M16_FOLD32 = 1 instance). Law fold_runs_* in
# bend/precision_laws.bend shows every fp16 run of those traces is at most FOLD tiles; the class below
# uses exactly that bound. Cross-block partials are the fp32 split-K slots of the same kernels
# (gemm_m16_partition_spec.bend Sum / reduction_order, gemm_m16_wpart, tail_m16_sched, mlp_m16_sched).
#
# Where elpis runs a stock kernel unchanged it runs the stock model's kernel (bend/precision_stock.bend):
# no series patch touches the stock GEMM / GEMV / int8 GEMV sources (see that module's header).
import Base
import ./precision_order.bend as Ord
import ./precision_stock.bend as Stock
import ./m16_diet.bend as Diet
import ./m16_diet_spec.bend as DSpec

# The kernel elpis runs for a served (op, m).
#   M16g:   exl3_gemm_m16g_kernel (ext 2102 / 2105): patches/exl3-ext/2102-proj-m16-grouped-v2-on3003-5101.patch
#           g_routes (2102:262-268, rows amended by 9003b-draft-proj-m16g.patch:143-147):
#           { GDN_QKVZ 5120 { 10240, 6144 } m 2..8 } and { ATTN_QKV 5120 { 12288, 1024, 1024 } m 2..8 };
#           m 1 is M16G_OLD, the site's own sliced exl3_mgemm (2102:283-295, 2102:424).
#   Tail:   exl3_tail_m16_kernel (ext 8202, with 8201's MLP phases): the attention / GDN output projection
#           (6144 -> 5120), residual, RMSNorm and gate / up / down in one launch for m 1..8
#           (8202-layer-tail-on2102.patch:618-621, :807-831 exl3_tail_m16_supported: size_m 1 ..
#           EXL3_TAIL_M16_ROWS = 8, :1056).
#   StockK: the unchanged stock kernel (lm_head: exl3_gemm_gr; projections outside the route rows).
type Route is Data:
  M16g{}
  Tail{}
  StockK{}

def rpick(c: Bool, t: Route, f: Route) -> Route:
  match c:
    case True{}:
      t
    case False{}:
      f

def in_rows(+m: Nat, +lo: Nat, +hi: Nat) -> Bool:
  Bool.and(Nat.is_le(lo, m), Nat.is_le(m, hi))

def route(op: Stock.Op, +m: Nat) -> Route:
  match op:
    case Stock.AttnQG{}:
      rpick(in_rows(m, 2n, 8n), M16g{}, StockK{})
    case Stock.AttnK{}:
      rpick(in_rows(m, 2n, 8n), M16g{}, StockK{})
    case Stock.AttnV{}:
      rpick(in_rows(m, 2n, 8n), M16g{}, StockK{})
    case Stock.GdnQkv{}:
      rpick(in_rows(m, 2n, 8n), M16g{}, StockK{})
    case Stock.GdnZ{}:
      rpick(in_rows(m, 2n, 8n), M16g{}, StockK{})
    case Stock.AttnO{}:
      rpick(in_rows(m, 1n, 8n), Tail{}, StockK{})
    case Stock.GdnOut{}:
      rpick(in_rows(m, 1n, 8n), Tail{}, StockK{})
    case Stock.MlpGate{}:
      rpick(in_rows(m, 1n, 8n), Tail{}, StockK{})
    case Stock.MlpUp{}:
      rpick(in_rows(m, 1n, 8n), Tail{}, StockK{})
    case Stock.MlpDown{}:
      rpick(in_rows(m, 1n, 8n), Tail{}, StockK{})
    case Stock.LmHead{}:
      StockK{}

# ---- fp16 run bookkeeping over a DIET trace (m16_diet_spec.bend Ev) ----
# It{.., fold} = one k16-tile MMA into the fp16 accumulators, then fold() into fp32 when `fold`;
# Seg = fold() + flush(g) at a segment end; Pro / Exit move no accumulator.

def rsel(c: Bool, +t: Nat, +f: Nat) -> Nat:
  match c:
    case True{}:
      t
    case False{}:
      f

# Every fp16 run is at most `lim` tiles: every tile keeps the open run within lim.
def runs_ok(evs: List<&2, DSpec.Ev>, +open: Nat, +lim: Nat) -> Bool:
  match evs:
    case Nil{}:
      Nat.is_le(open, lim)
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, r, xo, fold}:
          Bool.and(Nat.is_le(1n+open, lim), runs_ok(rest, rsel(fold, 0n, 1n+open), lim))
        case DSpec.Seg{g}:
          Bool.and(Nat.is_le(open, lim), runs_ok(rest, 0n, lim))
        case DSpec.Pro{w}:
          runs_ok(rest, open, lim)
        case DSpec.Exit{st}:
          runs_ok(rest, open, lim)

# The open run (tiles) after a trace.
def closed(evs: List<&2, DSpec.Ev>, +open: Nat) -> Nat:
  match evs:
    case Nil{}:
      open
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, r, xo, fold}:
          closed(rest, rsel(fold, 0n, 1n+open))
        case DSpec.Seg{g}:
          closed(rest, 0n)
        case DSpec.Pro{w}:
          closed(rest, open)
        case DSpec.Exit{st}:
          closed(rest, open)

# The longest fp16 run (tiles) of a trace.
def max_run(evs: List<&2, DSpec.Ev>, +open: Nat, +best: Nat) -> Nat:
  match evs:
    case Nil{}:
      Nat.max(best, open)
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, r, xo, fold}:
          max_run(rest, rsel(fold, 0n, 1n+open), Nat.max(best, 1n+open))
        case DSpec.Seg{g}:
          max_run(rest, 0n, Nat.max(best, open))
        case DSpec.Pro{w}:
          max_run(rest, open, best)
        case DSpec.Exit{st}:
          max_run(rest, open, best)

# ---- the served m16 configuration (Exl3M16Cfg<1>, m <= 8: MT = 1) ----
def fold() -> Nat:
  Diet.cfg_fold()

def pf() -> Nat:
  Diet.cfg_pf()

def xr() -> Nat:
  Diet.cfg_xr()

def ws() -> Nat:
  Diet.cfg_ws()

def xi() -> Nat:
  Diet.cfg_xi(1n)

# m16g / tail class: fp16 runs of at most FOLD k16 tiles (16 FOLD = 32 k-values, law fold_runs_*), at
# least one tile, fp32 split-K partials.
def m16_acc() -> Ord.Acc:
  Ord.Runs{16n, Nat.mul(16n, fold()), True{}}

def route_acc(r: Route, op: Stock.Op, +m: Nat, +e: Stock.Env, +ts: Stock.Tunes) -> Ord.Acc:
  match r:
    case M16g{}:
      m16_acc()
    case Tail{}:
      m16_acc()
    case StockK{}:
      Stock.acc(op, m, e, ts)

# The elpis class of every served (op, m); where elpis runs the stock kernel it is that kernel under the
# same runtime outcomes and autotune records (e, ts) as stock.
def acc(+op: Stock.Op, +m: Nat, +e: Stock.Env, +ts: Stock.Tunes) -> Ord.Acc:
  route_acc(route(op, m), op, m, e, ts)

def is_stock.of(r: Route) -> Bool:
  match r:
    case M16g{}:
      False{}
    case Tail{}:
      False{}
    case StockK{}:
      True{}

# elpis runs the unchanged stock kernel at (op, m).
def is_stock(+op: Stock.Op, +m: Nat) -> Bool:
  is_stock.of(route(op, m))

# Roofline ceiling and loss tables for the committed g7n engine, printed from
# the proven byte model (roofline.bend == roofline_spec.bend, laws in
# roofline_laws.bend). Run: bend bend/ROOFLINE_TABLE.bend (compiled IO main).
# Units: bytes; bandwidth bw in bytes per 10 ns (875.6 GB/s = 8756, 936 GB/s =
# 9360); time in 10 ns; tokens per round in milli-tokens; rates in deci-tok/s.
# The laws' u = 1 and s = 10^6 (r * T <= tm * 10^6 for these units).
# MEASURED inputs (not proven), cited:
#  - kernel-trace-3/trace.log (image g7n): per-case decode tok/s (lines 5-7),
#    unprofiled median round wall (lines 11, 86, 161), bucket ms/round
#    (lines 17-36, 92-111, 167-186).
#  - ar/run-g7n-2/logs/tiny-math.stdout: the benchmark's three calls
#    (prompt, completion tokens, model duration): (162, 1991, 12.16505742 s),
#    (304, 18544, 158.86636114 s), (296, 2628, 16.30052114 s).
# DERIVED (labelled in the output): tokens per round = tok/s x round wall;
# per-call rounds = call time / mean round time, the mean taken over the
# call's depth range on the piecewise-linear round-time curve through the
# three trace points.
import Base
import ./roofline_bin.bend as N
import ./roofline.bend as Impl

def bw875() -> Nat:
  8756n

def bw936() -> Nat:
  9360n

def S() -> Nat:
  U32.to_nat(1000000)

# ---- formatting ----
def drop1(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      t

def pow10(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.mul(10n, pow10(p))

# x / 10^k with k decimals.
def fix(+x: Nat, +k: Nat) -> String:
  Nat.show(Nat.div(x, pow10(k))) ++ "." ++ drop1(Nat.show(Nat.add(pow10(k), Nat.mod(x, pow10(k)))))

def mb(+b: Nat) -> String:
  fix(Nat.div(b, 100000n), 1n)

# 10 ns units -> ms with 3 decimals.
def ms(+t: Nat) -> String:
  fix(Nat.div(t, 100n), 3n)

# ---- model evaluation (runtime) ----
def f_c0(f: N.Form) -> N.Bin:
  match f:
    case N.Form{a, b, c, d}:
      a

def f_kd(f: N.Form) -> N.Bin:
  match f:
    case N.Form{a, b, c, d}:
      b

def f_kc(f: N.Form) -> N.Bin:
  match f:
    case N.Form{a, b, c, d}:
      c

def f_kw(f: N.Form) -> N.Bin:
  match f:
    case N.Form{a, b, c, d}:
      d

def lin() -> N.Lin:
  N.Form.lin(Impl.round())

# bytes at depth d with cm milli committed tokens per round, window read w.
def bytes_at(l: N.Lin, +d: Nat, +cm: Nat, +w: Nat) -> Nat:
  match l:
    case N.Lin{l0, ld, lc, lw}:
      Nat.add(l0, Nat.add(Nat.mul(d, ld), Nat.add(Nat.div(Nat.mul(cm, lc), 1000n), Nat.mul(w, lw))))

def round_bytes(+d: Nat, +cm: Nat) -> Nat:
  bytes_at(lin(), d, cm, N.Lin.win(d))

# Smallest time (10 ns) moving b bytes at bw: ceil(b / bw).
def floor_t(+b: Nat, +bw: Nat) -> Nat:
  Nat.div(Nat.add(b, Nat.sub(bw, 1n)), bw)

def ceil_rate(+tm: Nat, +bw: Nat, +b: Nat) -> Nat:
  N.Ceil.rate(tm, S(), bw, b, 1n)

# ---- round-time curve (trace unprofiled medians, 10 ns) ----
def t_lo(lt: Bool, +d: Nat) -> Nat:
  match lt:
    case True{}:
      Nat.sub(U32.to_nat(3089800), Nat.div(Nat.mul(Nat.sub(107n, d), U32.to_nat(175000)), U32.to_nat(8083)))
    case False{}:
      Nat.add(U32.to_nat(3089800), Nat.div(Nat.mul(Nat.sub(d, 107n), U32.to_nat(175000)), U32.to_nat(8083)))

def t_pick(lt: Bool, +d: Nat) -> Nat:
  match lt:
    case True{}:
      t_lo(Nat.is_lt(d, 107n), d)
    case False{}:
      Nat.add(U32.to_nat(3264800), Nat.div(Nat.mul(Nat.sub(d, U32.to_nat(8190)), U32.to_nat(406000)), U32.to_nat(24538)))

def t_at(+d: Nat) -> Nat:
  t_pick(Nat.is_lt(d, U32.to_nat(8190)), d)

# sums over d = p .. p + n - 1 of the round-time curve and of the window read.
def sum_t(n: Nat, +d: Nat, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+k:
      sum_t(k, 1n+d, Nat.add(acc, t_at(d)))

def sum_w(n: Nat, +d: Nat, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+k:
      sum_w(k, 1n+d, Nat.add(acc, N.Lin.win(d)))

# ---- per-depth ceiling rows ----
def depth_row(name: String, +d: Nat, +tm: Nat, meas: String) -> String:
  +b = round_bytes(d, tm)
  "depth " ++ Nat.show(d) ++ " (" ++ name ++ ") tokens/round " ++ fix(tm, 3n) ++
    " bytes " ++ Nat.show(b) ++ " (" ++ mb(b) ++ " MB)" ++
    " floor_ms@875.6 " ++ ms(floor_t(b, bw875())) ++ " floor_ms@936 " ++ ms(floor_t(b, bw936())) ++
    " ceiling_tok_s@875.6 " ++ fix(ceil_rate(tm, bw875(), b), 1n) ++
    " ceiling_tok_s@936 " ++ fix(ceil_rate(tm, bw936(), b), 1n) ++ " measured_tok_s " ++ meas ++ "\n"

# tokens per round (milli) = tok/s (milli) x round wall (10 ns) / 10^8.
def tpr(+mtoks: Nat, +wall: Nat) -> Nat:
  Nat.div(Nat.mul(mtoks, wall), U32.to_nat(100000000))

# ---- per-call ceilings ----
# mean bytes of a call's rounds: d2 = twice the mean depth.
def mean_bytes(l: N.Lin, +d2: Nat, +tm: Nat, +w: Nat) -> Nat:
  match l:
    case N.Lin{l0, ld, lc, lw}:
      Nat.add(l0, Nat.add(Nat.div(Nat.mul(d2, ld), 2n),
        Nat.add(Nat.div(Nat.mul(tm, lc), 1000n), Nat.mul(w, lw))))

# p prompt, n completion tokens, t call time (10 ns).
def call_row(name: String, +p: Nat, +n: Nat, +t: Nat) -> String:
  +mean_t = Nat.div(sum_t(n, p, 0n), n)
  +tm = Nat.div(Nat.mul(Nat.mul(n, 1000n), mean_t), t)
  +mean_w = Nat.div(sum_w(n, p, 0n), n)
  +mean_d2 = Nat.add(Nat.mul(2n, p), n)
  +b = mean_bytes(lin(), mean_d2, tm, mean_w)
  "call " ++ name ++ " prompt " ++ Nat.show(p) ++ " tokens " ++ Nat.show(n) ++
    " time_s " ++ fix(Nat.div(t, 10000n), 4n) ++
    " measured_tok_s " ++ fix(Nat.div(Nat.mul(n, U32.to_nat(1000000000)), t), 1n) ++
    " derived_rounds " ++ fix(Nat.div(Nat.mul(t, 10n), mean_t), 1n) ++
    " derived_tokens/round " ++ fix(tm, 3n) ++ " mean_round_bytes " ++ Nat.show(b) ++
    " ceiling_tok_s@875.6 " ++ fix(ceil_rate(tm, bw875(), b), 1n) ++
    " ceiling_tok_s@936 " ++ fix(ceil_rate(tm, bw936(), b), 1n) ++ "\n"

# ---- loss ledger ----
def names() -> List<&2, String>:
  ["target_mlp_gemm", "target_mlp_other", "gdn_gemm", "gdn_small", "attn_proj_gemm",
    "attention(split+combine+other)", "norms_residual", "lm_head", "sampler", "draft_forward",
    "draft_sample_head", "draft_sample_topk", "draft_sample_walk", "draft_sample_other",
    "rewind_replay", "draft_kv_refresh", "memcpy", "idle(wall-busy)"]

def phase_bytes(fs: List<&2, N.Form>, +d: Nat, +cm: Nat) -> List<&2, Nat>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, rest}:
      bytes_at(N.Form.lin(f), d, cm, N.Lin.win(d)) <> phase_bytes(rest, d, cm)

def rows(bs: List<&2, Nat>, ms_: List<&2, Nat>, +bw: Nat) -> List<&2, N.Row>:
  match bs ms_:
    case Con{b, br} Con{m, mr}:
      N.Row{m, floor_t(b, bw)} <> rows(br, mr, bw)
    case _ _:
      Nil{}

def ledger_lines(ns: List<&2, String>, bs: List<&2, Nat>, rs: List<&2, N.Row>) -> String:
  match ns bs rs:
    case Con{name, nr} Con{+b, br} Con{N.Row{+m, +f}, rr}:
      "  " ++ name ++ " bytes " ++ Nat.show(b) ++ " measured_ms " ++ ms(m) ++ " floor_ms " ++
        ms(f) ++ " loss_ms " ++ ms(Nat.sub(m, f)) ++ "\n" ++ ledger_lines(nr, br, rr)
    case _ _ _:
      ""

def sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      Nat.add(x, sum(rest))

# Measured bucket times (10 ns); the last entry is idle = wall - sum(buckets).
def with_idle(+xs: List<&2, Nat>, +wall: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, xs, [Nat.sub(wall, sum(xs))])

def ledger(name: String, +d: Nat, +tm: Nat, +wall: Nat, +meas: List<&2, Nat>, +bw: Nat, bwn: String) -> String:
  +bs = phase_bytes(Impl.phases(), d, tm)
  +rs = rows(bs, with_idle(meas, wall), bw)
  "ledger " ++ name ++ " depth " ++ Nat.show(d) ++ " bw " ++ bwn ++ " wall_ms " ++ ms(wall) ++
    " valid " ++ Bool.show(N.Ledger.valid(rs)) ++ "\n" ++ ledger_lines(names(), bs, rs) ++
    "  total bytes " ++ Nat.show(sum(bs)) ++ " measured_ms " ++ ms(N.Ledger.meas(rs)) ++
    " floor_ms " ++ ms(N.Ledger.floor(rs)) ++ " sum_loss_ms " ++ ms(N.Ledger.loss(rs)) ++
    " measured-floor_ms " ++ ms(Nat.sub(N.Ledger.meas(rs), N.Ledger.floor(rs))) ++ "\n"

def m(+ms1000: Nat) -> Nat:
  Nat.mul(ms1000, 100n)

def aime_meas() -> List<&2, Nat>:
  [m(12665n), m(122n), m(5952n), m(1616n), m(2194n), m(1014n), m(589n), m(1273n), m(18n),
    m(1908n), m(1278n), m(70n), m(22n), m(4n), m(421n), m(355n), m(28n)]

def c8k_meas() -> List<&2, Nat>:
  [m(12637n), m(123n), m(6004n), m(1625n), m(2221n), m(2770n), m(593n), m(1286n), m(18n),
    m(2007n), m(1297n), m(74n), m(22n), m(4n), m(413n), m(356n), m(27n)]

def c32k_meas() -> List<&2, Nat>:
  [m(12768n), m(122n), m(5837n), m(1603n), m(2158n), m(7247n), m(578n), m(1245n), m(18n),
    m(1986n), m(1256n), m(71n), m(21n), m(4n), m(398n), m(338n), m(27n)]

def big(+hi: Nat, +lo: Nat) -> Nat:
  Nat.add(Nat.mul(hi, S()), lo)

def report() -> String:
  +tm107 = tpr(U32.to_nat(170796), U32.to_nat(3089800))
  +tm8k = tpr(U32.to_nat(148422), U32.to_nat(3264800))
  +tm32k = tpr(U32.to_nat(115190), U32.to_nat(3670800))
  +aime_t = big(15886n, U32.to_nat(636114))
  +aime_mt = Nat.div(sum_t(U32.to_nat(18544), 304n, 0n), U32.to_nat(18544))
  +tm_aime = Nat.div(Nat.mul(U32.to_nat(18544000), aime_mt), aime_t)
  "== differential anchors (bytes)\n" ++
  "target_weight_gemm_bytes " ++ Nat.show(N.Bin.val(Impl.trace_target_gemm_bytes())) ++ "\n" ++
  "draft_forward_linear_bytes " ++ Nat.show(N.Bin.val(Impl.trace_draft_linears())) ++ "\n" ++
  "lm_head_bytes " ++ Nat.show(N.Bin.val(Impl.head())) ++ "\n" ++
  "target_weight_bytes " ++ Nat.show(N.Bin.val(Impl.target_weights())) ++ "\n" ++
  "draft_side_weight_bytes " ++ Nat.show(N.Bin.val(Impl.draft_weights())) ++ "\n" ++
  "round_form c0 " ++ Nat.show(N.Bin.val(f_c0(Impl.round()))) ++ " kd " ++
    Nat.show(N.Bin.val(f_kd(Impl.round()))) ++ " kc " ++ Nat.show(N.Bin.val(f_kc(Impl.round()))) ++
    " kw " ++ Nat.show(N.Bin.val(f_kw(Impl.round()))) ++ "\n" ++
  "== ceiling by depth (tokens/round DERIVED = trace decode tok/s x round wall; 18600 uses the AIME call's derived value)\n" ++
  depth_row("aime-think trace", 107n, tm107, "170.796") ++
  depth_row("ctx-8192 trace", U32.to_nat(8190), tm8k, "148.422") ++
  depth_row("AIME call mid-depth", U32.to_nat(18600), tm_aime, "n/a") ++
  depth_row("ctx-32768 trace", U32.to_nat(32728), tm32k, "115.19") ++
  "== ceiling per benchmark call (run-g7n-2; rounds DERIVED from the trace round-time curve)\n" ++
  call_row("c1", 162n, U32.to_nat(1991), big(1216n, U32.to_nat(505742))) ++
  call_row("aime", 304n, U32.to_nat(18544), aime_t) ++
  call_row("c3", 296n, U32.to_nat(2628), big(1630n, U32.to_nat(52114))) ++
  "== loss ledger (kernel-trace-3 buckets, ms/round; floor = ceil(phase bytes / bw))\n" ++
  ledger("aime-think", 107n, tm107, U32.to_nat(3089800), aime_meas(), bw875(), "875.6") ++
  ledger("ctx-8192", U32.to_nat(8190), tm8k, U32.to_nat(3264800), c8k_meas(), bw875(), "875.6") ++
  ledger("ctx-32768", U32.to_nat(32728), tm32k, U32.to_nat(3670800), c32k_meas(), bw875(), "875.6") ++
  ledger("aime-think", 107n, tm107, U32.to_nat(3089800), aime_meas(), bw936(), "936") ++
  ledger("ctx-8192", U32.to_nat(8190), tm8k, U32.to_nat(3264800), c8k_meas(), bw936(), "936") ++
  ledger("ctx-32768", U32.to_nat(32728), tm32k, U32.to_nat(3670800), c32k_meas(), bw936(), "936")

def main() -> IO(Unit):
  IO.print(report())

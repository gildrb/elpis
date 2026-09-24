# Exact binary naturals and linear byte forms for the DRAM roofline model
# (roofline.bend, roofline_spec.bend). The checker evaluates Nat in unary, so the
# 10^10-byte round totals are computed on this little-endian bit list instead:
# every constructor path yields the canonical form (no high zero bit), so two
# values are equal exactly when their terms are identical and the concrete
# floor_exact law is checked by {==}. Bin.val maps to Nat for the compiled
# table program (native Nat at runtime, < 2^48).
import Base

type Bin is Data:
  BE{}
  B0{rest: Bin}
  B1{rest: Bin}

# 2x, canonical (0 stays BE).
def Bin.dbl(x: Bin) -> Bin:
  match x:
    case BE{}:
      BE{}
    case B0{r}:
      B0{B0{r}}
    case B1{r}:
      B0{B1{r}}

def Bin.inc(x: Bin) -> Bin:
  match x:
    case BE{}:
      B1{BE{}}
    case B0{r}:
      B1{r}
    case B1{r}:
      B0{Bin.inc(r)}

def Bin.add(a: Bin, b: Bin) -> Bin:
  match a b:
    case BE{} _:
      b
    case B0{x} BE{}:
      B0{x}
    case B1{x} BE{}:
      B1{x}
    case B0{x} B0{y}:
      Bin.dbl(Bin.add(x, y))
    case B0{x} B1{y}:
      B1{Bin.add(x, y)}
    case B1{x} B0{y}:
      B1{Bin.add(x, y)}
    case B1{x} B1{y}:
      B0{Bin.inc(Bin.add(x, y))}

def Bin.mul(a: Bin, +b: Bin) -> Bin:
  match a:
    case BE{}:
      BE{}
    case B0{x}:
      Bin.dbl(Bin.mul(x, b))
    case B1{x}:
      Bin.add(b, Bin.dbl(Bin.mul(x, b)))

# floor(x / 2).
def Bin.half(x: Bin) -> Bin:
  match x:
    case BE{}:
      BE{}
    case B0{r}:
      r
    case B1{r}:
      r

# floor(x / 8): packed-bit byte counts (bits * elements / 8).
def Bin.div8(x: Bin) -> Bin:
  Bin.half(Bin.half(Bin.half(x)))

def Bin.small(n: Nat) -> Bin:
  match n:
    case 0n:
      BE{}
    case 1n+p:
      Bin.inc(Bin.small(p))

def Bin.dec.go(ds: List<&2, Nat>, acc: Bin) -> Bin:
  match ds:
    case Nil{}:
      acc
    case Con{d, rest}:
      Bin.dec.go(rest, Bin.add(Bin.mul(acc, Bin.small(10n)), Bin.small(d)))

# Decimal literal, most significant digit first: Bin.dec([4n, 4n, 8n]) = 448.
def Bin.dec(ds: List<&2, Nat>) -> Bin:
  Bin.dec.go(ds, BE{})

def Bin.val(x: Bin) -> Nat:
  match x:
    case BE{}:
      0n
    case B0{r}:
      Nat.double(Bin.val(r))
    case B1{r}:
      1n+Nat.double(Bin.val(r))

# Bytes one round moves as a function of the committed depth d (tokens in the
# target cache before the round) and the committed count c of that round:
#   bytes(d, c) = c0 + kd * d + kc * c + kw * min(d + 8, 2056)
# (kw: the draft's sliding-window KV read, window 2048 left of the 8-row block).
type Form is Data:
  Form{c0: Bin, kd: Bin, kc: Bin, kw: Bin}

def Form.zero() -> Form:
  Form{BE{}, BE{}, BE{}, BE{}}

def Form.const(b: Bin) -> Form:
  Form{b, BE{}, BE{}, BE{}}

def Form.add(a: Form, b: Form) -> Form:
  match a b:
    case Form{a0, ad, ac, aw} Form{b0, bd, bc, bw}:
      Form{Bin.add(a0, b0), Bin.add(ad, bd), Bin.add(ac, bc), Bin.add(aw, bw)}

def Form.scale(+n: Bin, f: Form) -> Form:
  match f:
    case Form{f0, fd, fc, fw}:
      Form{Bin.mul(n, f0), Bin.mul(n, fd), Bin.mul(n, fc), Bin.mul(n, fw)}

def Form.sum(fs: List<&2, Form>) -> Form:
  match fs:
    case Nil{}:
      Form.zero()
    case Con{f, rest}:
      Form.add(f, Form.sum(rest))

# bytes(d, c) with symbolic Bin arguments (the floor_exact statement); w is
# the draft window read length min(d + 8, 2056), left free here.
def Form.at(f: Form, +d: Bin, +c: Bin, +w: Bin) -> Bin:
  match f:
    case Form{f0, fd, fc, fw}:
      Bin.add(f0, Bin.add(Bin.mul(d, fd), Bin.add(Bin.mul(c, fc), Bin.mul(w, fw))))

# Nat image of a form (runtime only: never evaluated by the checker on a
# concrete form, whose values are far past the unary range).
type Lin is Data:
  Lin{c0: Nat, kd: Nat, kc: Nat, kw: Nat}

def Form.lin(f: Form) -> Lin:
  match f:
    case Form{f0, fd, fc, fw}:
      Lin{Bin.val(f0), Bin.val(fd), Bin.val(fc), Bin.val(fw)}

# Draft window: 2048 left + the 8-row block (triton_paged.py:279-286, 3002 L184).
def Lin.win(+d: Nat) -> Nat:
  Nat.min(Nat.add(d, 8n), U32.to_nat(2056))

def Lin.eval(l: Lin, +d: Nat, +c: Nat) -> Nat:
  match l:
    case Lin{l0, ld, lc, lw}:
      Nat.add(l0, Nat.add(Nat.mul(d, ld), Nat.add(Nat.mul(c, lc), Nat.mul(Lin.win(d), lw))))

# ---- schedules and loss ledgers (Nat; units chosen by the caller) ----
# A phase of a round moves `bytes` in `time`.
type Phase is Data:
  Phase{bytes: Nat, time: Nat}

def Sched.bytes(ps: List<&2, Phase>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case Con{Phase{b, t}, rest}:
      Nat.add(b, Sched.bytes(rest))

def Sched.time(ps: List<&2, Phase>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case Con{Phase{b, t}, rest}:
      Nat.add(t, Sched.time(rest))

# Every phase respects the bandwidth: bytes * u <= time * bw (u converts the
# time unit, e.g. bytes * 1000 <= ns * (bytes per us)).
def Sched.fits(ps: List<&2, Phase>, +bw: Nat, +u: Nat) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{Phase{b, t}, rest}:
      Bool.and(Nat.is_le(Nat.mul(b, u), Nat.mul(t, bw)), Sched.fits(rest, bw, u))

# One ledger row: measured time and floor time of a phase.
type Row is Data:
  Row{meas: Nat, floor: Nat}

def Ledger.meas(rs: List<&2, Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{Row{m, f}, rest}:
      Nat.add(m, Ledger.meas(rest))

def Ledger.floor(rs: List<&2, Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{Row{m, f}, rest}:
      Nat.add(f, Ledger.floor(rest))

def Ledger.loss(rs: List<&2, Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{Row{m, f}, rest}:
      Nat.add(Nat.sub(m, f), Ledger.loss(rest))

# Every row's floor is at most its measurement (else the byte model is refuted).
def Ledger.valid(rs: List<&2, Row>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{Row{+m, +f}, rest}:
      Bool.and(Nat.is_le(f, m), Ledger.valid(rest))

# Printed ceiling (rounded DOWN): floor(tm * s * bw / (B * u)), the largest
# rate a round of B bytes at bandwidth bw can sustain for tm tokens per round.
def Ceil.rate(tm: Nat, +s: Nat, +bw: Nat, B: Nat, +u: Nat) -> Nat:
  Nat.div(Nat.mul(Nat.mul(tm, s), bw), Nat.mul(B, u))

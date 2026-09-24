# Independent reference for the roofline byte model (roofline.bend): the same
# round enumerated tensor by tensor, layer by layer, from the model CONFIG
# (shapes, bit widths, layer pattern) instead of the safetensors byte counts.
# Sources: /models/qwen38-27b-exl3/config.json text_config (hidden 5120,
# intermediate 17408, 64 layers, full_attention_interval 4, linear 16 x 128 key
# / 48 x 128 value heads, conv kernel 4, 24 q / 4 kv heads x 256, output gate),
# its quantization_config (bits 4, head_bits 6), vocab 248320 (lm_head.svh),
# /models/dflash2-exl3/config.json (5 layers, 32 / 8 heads x 128, block 8,
# sliding_window 2048, selector rank 256, top_k 16, 5 target taps), draft conv
# kernel_projection [1280, 5120] and base_kernel [2, 2, 5120] (header shapes).
# Formats: EXL3 linear in x out at b bits = trellis in*out*b/8 + suh 2*in +
# svh 2*out bytes; CQ3 cache token of D values = D*3/8 + 2*D/32 bytes.
import Base
import ./roofline_bin.bend as N

def n(ds: List<&2, Nat>) -> N.Bin:
  N.Bin.dec(ds)

def s(x: Nat) -> N.Bin:
  N.Bin.small(x)

def mul(a: N.Bin, +b: N.Bin) -> N.Bin:
  N.Bin.mul(a, b)

def add(a: N.Bin, b: N.Bin) -> N.Bin:
  N.Bin.add(a, b)

def fixed(b: N.Bin) -> N.Form:
  N.Form.const(b)

# ---- configuration ----
def hidden() -> N.Bin:
  n([5n, 1n, 2n, 0n])

def inter() -> N.Bin:
  n([1n, 7n, 4n, 0n, 8n])

def vocab() -> N.Bin:
  n([2n, 4n, 8n, 3n, 2n, 0n])

def head_dim() -> N.Bin:
  s(128n)

def key_dim() -> N.Bin:
  mul(s(16n), s(128n))

def value_dim() -> N.Bin:
  mul(s(48n), s(128n))

def conv_dim() -> N.Bin:
  add(mul(s(2n), key_dim()), value_dim())

# M = window + 1 target rows per round (max_history 7).
def rows() -> N.Bin:
  s(8n)

# ---- formats ----
def exl3(+i: N.Bin, +o: N.Bin, bits: Nat) -> N.Bin:
  add(N.Bin.div8(mul(mul(i, o), s(bits))), add(mul(s(2n), i), mul(s(2n), o)))

def f16(elems: N.Bin) -> N.Bin:
  mul(s(2n), elems)

def f32(elems: N.Bin) -> N.Bin:
  mul(s(4n), elems)

# CQ3 K + V bytes per token of D = heads * head_dim values.
def cq3_kv(+D: N.Bin) -> N.Bin:
  mul(s(2n), add(N.Bin.div8(mul(D, s(3n))), f16(N.Bin.half(N.Bin.half(N.Bin.half(N.Bin.half(N.Bin.half(D))))))))

def sum(xs: List<&2, N.Bin>) -> N.Bin:
  match xs:
    case Nil{}:
      N.BE{}
    case Con{x, rest}:
      add(x, sum(rest))

# ---- target layers ----
def mlp() -> N.Form:
  fixed(sum([exl3(hidden(), inter(), 4n), exl3(hidden(), inter(), 4n),
    exl3(inter(), hidden(), 4n), f16(hidden()), f16(hidden())]))

def gdn() -> N.Form:
  +state = f32(mul(s(48n), mul(s(128n), s(128n))))
  +cread = f16(mul(conv_dim(), s(4n)))
  +static_row = sum([f16(conv_dim()), f32(s(48n)), f16(s(48n))])
  N.Form{sum([exl3(hidden(), add(mul(s(2n), key_dim()), value_dim()), 4n),
      exl3(hidden(), value_dim(), 4n), exl3(value_dim(), hidden(), 4n),
      f16(mul(s(48n), hidden())), f16(mul(s(48n), hidden())), f16(mul(conv_dim(), s(4n))),
      f16(s(48n)), f16(s(48n)), f16(head_dim()),
      state, state, state,
      cread, f16(mul(conv_dim(), add(s(4n), s(7n)))), cread, cread,
      mul(rows(), static_row)]),
    N.BE{}, static_row, N.BE{}}

def attention() -> N.Form:
  +tok = cq3_kv(mul(s(4n), s(256n)))
  N.Form{sum([exl3(hidden(), mul(s(2n), mul(s(24n), s(256n))), 4n),
      exl3(hidden(), mul(s(4n), s(256n)), 4n), exl3(hidden(), mul(s(4n), s(256n)), 4n),
      exl3(mul(s(24n), s(256n)), hidden(), 4n), f16(s(256n)), f16(s(256n)),
      mul(rows(), tok), mul(rows(), tok)]),
    tok, N.BE{}, N.BE{}}

def mixer(r: Nat) -> N.Form:
  match r:
    case 0n:
      attention()
    case 1n+p:
      gdn()

# Layer i is full attention iff (i + 1) % full_attention_interval == 0.
def layer(i: Nat) -> N.Form:
  N.Form.add(mlp(), mixer(Nat.mod(1n+i, 4n)))

def layers(left: Nat, +i: Nat) -> List<&2, N.Form>:
  match left:
    case 0n:
      Nil{}
    case 1n+p:
      layer(i) <> layers(p, 1n+i)

# ---- target top: final norm, head read by verify, logits, embed upload, taps ----
def target_top() -> N.Form:
  fixed(sum([f16(hidden()), exl3(hidden(), vocab(), 6n), f16(mul(rows(), vocab())),
    f16(mul(rows(), hidden())), f16(mul(s(5n), mul(rows(), hidden())))]))

# ---- draft ----
def draft_tok() -> N.Bin:
  mul(s(5n), cq3_kv(mul(s(8n), s(128n))))

def draft_layer() -> N.Form:
  +q = mul(s(32n), s(128n))
  +kv = mul(s(8n), s(128n))
  fixed(sum([exl3(hidden(), q, 4n), exl3(hidden(), kv, 4n), exl3(hidden(), kv, 4n),
    exl3(q, hidden(), 4n), exl3(hidden(), inter(), 4n), exl3(hidden(), inter(), 4n),
    exl3(inter(), hidden(), 4n), f16(mul(n([1n, 2n, 8n, 0n]), hidden())),
    f16(mul(n([1n, 2n, 8n, 0n]), hidden())), f16(mul(s(4n), hidden())),
    f16(mul(s(4n), hidden())), f16(hidden()), f16(hidden()), f16(s(128n)), f16(s(128n))]))

def draft_layers(left: Nat) -> List<&2, N.Form>:
  match left:
    case 0n:
      Nil{}
    case 1n+p:
      draft_layer() <> draft_layers(p)

# Draft forward top: final norm, embed upload, 8 block tokens written, window read.
def draft_top() -> N.Form:
  N.Form{sum([f16(hidden()), f16(mul(rows(), hidden())), mul(rows(), draft_tok())]),
    N.BE{}, N.BE{}, draft_tok()}

# Draft sampling: full target head on 8 rows, logits, hidden_projection, and
# 7 rows x (1 + top_k 16) codebook rows of rank 256 fp16.
def draft_sample() -> N.Form:
  fixed(sum([exl3(hidden(), vocab(), 6n), f16(mul(rows(), vocab())),
    f16(mul(s(256n), hidden())), f16(mul(mul(s(7n), s(17n)), s(256n)))]))

# update_kv_from_target: fc (5 taps x hidden -> hidden), hidden_norm, k/v/k_norm
# of each draft layer; per committed token one tap row read, one token written.
def draft_refresh_layer() -> N.Bin:
  +kv = mul(s(8n), s(128n))
  sum([exl3(hidden(), kv, 4n), exl3(hidden(), kv, 4n), f16(s(128n))])

def draft_refresh() -> N.Form:
  N.Form{sum([exl3(mul(s(5n), hidden()), hidden(), 4n), f16(hidden()),
      mul(s(5n), draft_refresh_layer())]),
    N.BE{}, add(f16(mul(s(5n), hidden())), draft_tok()), N.BE{}}

def round() -> N.Form:
  N.Form.add(N.Form.sum(layers(64n, 0n)),
    N.Form.sum([target_top(), draft_top(), draft_sample(), draft_refresh(),
      N.Form.sum(draft_layers(5n))]))

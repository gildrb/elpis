# Compositional proofs over arbitrary bit lists and arbitrary Nat indices.
# Finite Slot cases establish the complete block8 projection, not sampled runs.
# No theorem here authenticates native C, pointer truth, or asynchronous storage.
import Base
import ./abi.bend as Impl
import ./abi_spec.bend as Spec
import ./abi_laws.bend as Laws

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(n: Nat, -m: Nat)
  -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

def slot_nil(n: Nat) -> {None{} == Spec.slot_at(n, Nil{}) : Maybe<&2, Spec.Slot>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.index_refinement(n):
  match n:
    case 0n:
      {==}
    case 1n+n0:
      match n0:
        case 0n:
          {==}
        case 1n+n1:
          match n1:
            case 0n:
              {==}
            case 1n+n2:
              match n2:
                case 0n:
                  {==}
                case 1n+n3:
                  match n3:
                    case 0n:
                      {==}
                    case 1n+n4:
                      match n4:
                        case 0n:
                          {==}
                        case 1n+n5:
                          match n5:
                            case 0n:
                              {==}
                            case 1n+n6:
                              match n6:
                                case 0n:
                                  {==}
                                case 1n+n7:
                                  slot_nil(n7)

def Laws.index_progress(slot):
  match slot:
    case Spec.S0{}:
      {==}
    case Spec.S1{}:
      {==}
    case Spec.S2{}:
      {==}
    case Spec.S3{}:
      {==}
    case Spec.S4{}:
      {==}
    case Spec.S5{}:
      {==}
    case Spec.S6{}:
      {==}
    case Spec.S7{}:
      {==}

def Laws.index_bound(slot):
  match slot:
    case Spec.S0{}:
      {==}
    case Spec.S1{}:
      {==}
    case Spec.S2{}:
      {==}
    case Spec.S3{}:
      {==}
    case Spec.S4{}:
      {==}
    case Spec.S5{}:
      {==}
    case Spec.S6{}:
      {==}
    case Spec.S7{}:
      {==}

def Laws.word_scalar_bounds(slot):
  match slot:
    case Spec.S0{}:
      ({==}, {==})
    case Spec.S1{}:
      ({==}, {==})
    case Spec.S2{}:
      ({==}, {==})
    case Spec.S3{}:
      ({==}, {==})
    case Spec.S4{}:
      ({==}, {==})
    case Spec.S5{}:
      ({==}, {==})
    case Spec.S6{}:
      ({==}, {==})
    case Spec.S7{}:
      ({==}, {==})

def Laws.index_rejected(n):
  {==}

def inputs_length(count: Nat, start: Nat)
  -> {List.length(&2, Nat, Spec.inputs(count, start)) == count : Nat}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      %inputs_length(p, 1n+start) :
        {1n+List.length(&2, Nat, Spec.inputs(p, 1n+start)) == 1n+_ : Nat}
      {==}

def Laws.four_word_refinement(accepted):
  %inputs_length(Spec.index(accepted), 1n) :
    {[Spec.index(accepted), 1n+_, Spec.index(accepted), 1n+Spec.index(accepted)] ==
      Spec.words(accepted) : List<&2, Nat>}
  %inputs_length(1n+Spec.index(accepted), 0n) :
    {[Spec.index(accepted), 1n+List.length(&2, Nat, Spec.inputs(Spec.index(accepted), 1n)),
      Spec.index(accepted), _] == Spec.words(accepted) : List<&2, Nat>}
  {==}

def Laws.four_word_arity(accepted):
  {==}

def Laws.four_word_projection(accepted):
  ({==}, {==}, {==}, {==})

def at_nil(n: Nat) -> {Spec.at(n, Nil{}) == None{} : Maybe<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.word_out_of_range(accepted, n):
  at_nil(n)

# 64 constructor cases are the exact finite domain, with no token-value cases.
def Laws.transport_refinement(accepted, slot):
  match accepted:
    case Spec.S0{}:
      match slot:
        case Spec.S0{}:
          {==}
        case Spec.S1{}:
          {==}
        case Spec.S2{}:
          {==}
        case Spec.S3{}:
          {==}
        case Spec.S4{}:
          {==}
        case Spec.S5{}:
          {==}
        case Spec.S6{}:
          {==}
        case Spec.S7{}:
          {==}
    case Spec.S1{}:
      match slot:
        case Spec.S0{}:
          {==}
        case Spec.S1{}:
          {==}
        case Spec.S2{}:
          {==}
        case Spec.S3{}:
          {==}
        case Spec.S4{}:
          {==}
        case Spec.S5{}:
          {==}
        case Spec.S6{}:
          {==}
        case Spec.S7{}:
          {==}
    case Spec.S2{}:
      match slot:
        case Spec.S0{}:
          {==}
        case Spec.S1{}:
          {==}
        case Spec.S2{}:
          {==}
        case Spec.S3{}:
          {==}
        case Spec.S4{}:
          {==}
        case Spec.S5{}:
          {==}
        case Spec.S6{}:
          {==}
        case Spec.S7{}:
          {==}
    case Spec.S3{}:
      match slot:
        case Spec.S0{}:
          {==}
        case Spec.S1{}:
          {==}
        case Spec.S2{}:
          {==}
        case Spec.S3{}:
          {==}
        case Spec.S4{}:
          {==}
        case Spec.S5{}:
          {==}
        case Spec.S6{}:
          {==}
        case Spec.S7{}:
          {==}
    case Spec.S4{}:
      match slot:
        case Spec.S0{}:
          {==}
        case Spec.S1{}:
          {==}
        case Spec.S2{}:
          {==}
        case Spec.S3{}:
          {==}
        case Spec.S4{}:
          {==}
        case Spec.S5{}:
          {==}
        case Spec.S6{}:
          {==}
        case Spec.S7{}:
          {==}
    case Spec.S5{}:
      match slot:
        case Spec.S0{}:
          {==}
        case Spec.S1{}:
          {==}
        case Spec.S2{}:
          {==}
        case Spec.S3{}:
          {==}
        case Spec.S4{}:
          {==}
        case Spec.S5{}:
          {==}
        case Spec.S6{}:
          {==}
        case Spec.S7{}:
          {==}
    case Spec.S6{}:
      match slot:
        case Spec.S0{}:
          {==}
        case Spec.S1{}:
          {==}
        case Spec.S2{}:
          {==}
        case Spec.S3{}:
          {==}
        case Spec.S4{}:
          {==}
        case Spec.S5{}:
          {==}
        case Spec.S6{}:
          {==}
        case Spec.S7{}:
          {==}
    case Spec.S7{}:
      match slot:
        case Spec.S0{}:
          {==}
        case Spec.S1{}:
          {==}
        case Spec.S2{}:
          {==}
        case Spec.S3{}:
          {==}
        case Spec.S4{}:
          {==}
        case Spec.S5{}:
          {==}
        case Spec.S6{}:
          {==}
        case Spec.S7{}:
          {==}

def eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def Laws.bonus_provenance(accepted):
  %Equal.sym(Bool, Nat.is_eq(Spec.index(accepted), Spec.index(accepted)), True{},
    eq_refl(Spec.index(accepted))) :
    {Impl.overwrite(_, accepted, accepted) == Spec.TargetBonus{Spec.index(accepted)} : Spec.Source}
  {==}

def Laws.committed_count(accepted):
  %inputs_length(Spec.index(accepted), 1n) :
    {1n+List.length(&2, Nat, Spec.inputs(Spec.index(accepted), 1n)) == 1n+_ : Nat}
  {==}

def lt_shift(base: Nat, +a: Nat, +b: Nat)
  -> {Nat.is_lt(Nat.add(base, a), Nat.add(base, b)) == Nat.is_lt(a, b) : Bool}:
  match base:
    case 0n:
      {==}
    case 1n+p:
      lt_shift(p, a, b)

def Laws.address_within_row(row, slot):
  Equal.trans(Bool,
    Nat.is_lt(Nat.add(Nat.mul(row, 8n), Spec.index(slot)), Nat.add(Nat.mul(row, 8n), 8n)),
    Nat.is_lt(Spec.index(slot), 8n), True{},
    lt_shift(Nat.mul(row, 8n), Spec.index(slot), 8n), Laws.index_bound(slot))

def Laws.prefix_stride_units(width, row, stride):
  ({==}, {==})

def mul_zero(n: Nat) -> {Nat.mul(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

def Laws.broadcast_stride(width, row):
  %Equal.sym(Nat, Nat.mul(row, 0n), 0n, mul_zero(row)) :
    {Spec.Bytes{Nat.mul(_, Spec.bytes(width))} == Spec.Bytes{0n} : Spec.ByteOffset}
  {==}

# A symbolic surplus of padding avoids normalizing concrete 32/64-bit words.
def resize_reference(n: Nat, +extra: Nat, +fill: Bool, +xs: List<&2, Bool>)
  -> {Impl.resize(n, fill, xs) == Spec.take(n,
    List.append(&2, Bool, xs, List.replicate(Bool, Nat.add(n, extra), fill))) : List<&2, Bool>}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match xs:
        case Nil{}:
          %resize_reference(p, extra, fill, Nil{}) :
            {fill <> Impl.resize(p, fill, Nil{}) == fill <> _ : List<&2, Bool>}
          {==}
        case h <> t:
          %add_succ(p, extra) :
            {h <> Impl.resize(p, fill, t) == h <> Spec.take(p,
              List.append(&2, Bool, t, List.replicate(Bool, _, fill))) : List<&2, Bool>}
          %resize_reference(p, 1n+extra, fill, t) :
            {h <> Impl.resize(p, fill, t) == h <> _ : List<&2, Bool>}
          {==}

def converted_reference(+dest: Spec.Width, +xs: List<&2, Bool>)
  -> {Impl.converted(dest, xs) == Spec.resize(Spec.bits(dest), xs) : List<&2, Bool>}:
  %add_zero(Spec.bits(dest)) :
    {Impl.converted(dest, xs) == Spec.take(Spec.bits(dest),
      List.append(&2, Bool, xs, List.replicate(Bool, _, Spec.sign(xs)))) : List<&2, Bool>}
  resize_reference(Spec.bits(dest), 0n, Spec.sign(xs), xs)

def transfer_valid_reference(+ok: Bool, +dest: Spec.Width, +xs: List<&2, Bool>)
  -> {Impl.transfer_valid(ok, dest, xs) == Spec.transfer_valid(ok, dest, xs) : Spec.Transfer}:
  match ok:
    case False{}:
      {==}
    case True{}:
      Equal.cong(List<&2, Bool>, Spec.Transfer, value => Spec.Value{value},
        Impl.converted(dest, xs), Spec.resize(Spec.bits(dest), xs), converted_reference(dest, xs))

def Laws.signed_transport(source, dest, raw):
  match raw:
    case Spec.Missing{}:
      {==}
    case Spec.Cancelled{}:
      {==}
    case Spec.Bits{value}:
      transfer_valid_reference(Spec.valid_width(source, value), dest, value)

def resize_length(n: Nat, +fill: Bool, xs: List<&2, Bool>)
  -> {List.length(&2, Bool, Impl.resize(n, fill, xs)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match xs:
        case Nil{}:
          %resize_length(p, fill, Nil{}) :
            {1n+List.length(&2, Bool, Impl.resize(p, fill, Nil{})) == 1n+_ : Nat}
          {==}
        case h <> t:
          %resize_length(p, fill, t) :
            {1n+List.length(&2, Bool, Impl.resize(p, fill, t)) == 1n+_ : Nat}
          {==}

def Laws.converted_width(dest, xs):
  resize_length(Spec.bits(dest), Spec.sign(xs), xs)

def resize_prefix(+low: List<&2, Bool>, high: List<&2, Bool>, +fill: Bool)
  -> {Impl.resize(List.length(&2, Bool, low), fill,
    List.append(&2, Bool, low, high)) == low : List<&2, Bool>}:
  match low:
    case Nil{}:
      {==}
    case h <> t:
      %resize_prefix(t, high, fill) :
        {h <> Impl.resize(List.length(&2, Bool, t), fill,
          List.append(&2, Bool, t, high)) == h <> _ : List<&2, Bool>}
      {==}

def Laws.narrow_low_bits(low, high, exact):
  %exact :
    {Impl.resize(_, Spec.sign(List.append(&2, Bool, low, high)),
      List.append(&2, Bool, low, high)) == low : List<&2, Bool>}
  resize_prefix(low, high, Spec.sign(List.append(&2, Bool, low, high)))

def sign_nonempty(+xs: List<&2, Bool>, h: Bool, +last: Bool)
  -> {Spec.sign(h <> List.append(&2, Bool, xs, [last])) == last : Bool}:
  match xs:
    case Nil{}:
      {==}
    case k <> t:
      sign_nonempty(t, k, last)

def sign_append(+xs: List<&2, Bool>, +last: Bool)
  -> {Spec.sign(List.append(&2, Bool, xs, [last])) == last : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      sign_nonempty(t, h, last)

def resize_empty(n: Nat, +fill: Bool)
  -> {Impl.resize(n, fill, Nil{}) == List.replicate(Bool, n, fill) : List<&2, Bool>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %resize_empty(p, fill) :
        {fill <> Impl.resize(p, fill, Nil{}) == fill <> _ : List<&2, Bool>}
      {==}

def resize_extend(+low: List<&2, Bool>, +n: Nat, +fill: Bool)
  -> {Impl.resize(Nat.add(List.length(&2, Bool, low), 1n+n), fill,
    List.append(&2, Bool, low, [fill])) ==
    List.append(&2, Bool, low, List.replicate(Bool, 1n+n, fill)) : List<&2, Bool>}:
  match low:
    case Nil{}:
      %resize_empty(n, fill) :
        {fill <> Impl.resize(n, fill, Nil{}) == fill <> _ : List<&2, Bool>}
      {==}
    case h <> t:
      %resize_extend(t, n, fill) :
        {h <> Impl.resize(Nat.add(List.length(&2, Bool, t), 1n+n), fill,
          List.append(&2, Bool, t, [fill])) == h <> _ : List<&2, Bool>}
      {==}

def Laws.signed_widen(low, negative, exact):
  %Equal.sym(Bool, Spec.sign(List.append(&2, Bool, low, [negative])), negative,
    sign_append(low, negative)) :
    {Impl.resize(64n, _, List.append(&2, Bool, low, [negative])) ==
      List.append(&2, Bool, low, List.replicate(Bool, 33n, negative)) : List<&2, Bool>}
  %exact :
    {Impl.resize(Nat.add(_, 33n), negative, List.append(&2, Bool, low, [negative])) ==
      List.append(&2, Bool, low, List.replicate(Bool, 33n, negative)) : List<&2, Bool>}
  resize_extend(low, 32n, negative)

def carry_zero(+xs: List<&2, Bool>)
  -> {Impl.carry(xs, False{}) == xs : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %carry_zero(t) : {h <> Impl.carry(t, False{}) == h <> _ : List<&2, Bool>}
      {==}

def Laws.ripple_reference(xs):
  match xs:
    case Nil{}:
      {==}
    case False{} <> t:
      %carry_zero(t) : {True{} <> Impl.carry(t, False{}) == True{} <> _ : List<&2, Bool>}
      {==}
    case True{} <> t:
      %Laws.ripple_reference(t) :
        {False{} <> Impl.carry(t, True{}) == False{} <> _ : List<&2, Bool>}
      {==}

def Laws.advance_reference(delta, xs):
  match delta:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(List<&2, Bool>, Impl.advance(p, Impl.carry(xs, True{})),
        Impl.advance(p, Spec.bump(xs)), Spec.advance(p, Spec.bump(xs)),
        Equal.cong(List<&2, Bool>, List<&2, Bool>, value => Impl.advance(p, value),
          Impl.carry(xs, True{}), Spec.bump(xs), Laws.ripple_reference(xs)),
        Laws.advance_reference(p, Spec.bump(xs)))

def carry_length(+xs: List<&2, Bool>, +c: Bool)
  -> {List.length(&2, Bool, Impl.carry(xs, c)) == List.length(&2, Bool, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %carry_length(t, Bool.and(c, h)) :
        {1n+List.length(&2, Bool, Impl.carry(t, Bool.and(c, h))) == 1n+_ : Nat}
      {==}

def Laws.advance_width(delta, xs):
  match delta:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, List.length(&2, Bool, Impl.advance(p, Impl.carry(xs, True{}))),
        List.length(&2, Bool, Impl.carry(xs, True{})), List.length(&2, Bool, xs),
        Laws.advance_width(p, Impl.carry(xs, True{})), carry_length(xs, True{}))

def sequence_valid_reference(+ok: Bool, +dest: Spec.Width, +delta: Nat, +xs: List<&2, Bool>)
  -> {Impl.sequence_valid(ok, dest, delta, xs) == Spec.sequence_valid(ok, dest, delta, xs) : Spec.Transfer}:
  match ok:
    case False{}:
      {==}
    case True{}:
      %Laws.advance_reference(delta, xs) :
        {Spec.Value{Impl.converted(dest, Impl.advance(delta, xs))} ==
          Spec.Value{Spec.resize(Spec.bits(dest), _)} : Spec.Transfer}
      Equal.cong(List<&2, Bool>, Spec.Transfer, value => Spec.Value{value},
        Impl.converted(dest, Impl.advance(delta, xs)),
        Spec.resize(Spec.bits(dest), Impl.advance(delta, xs)),
        converted_reference(dest, Impl.advance(delta, xs)))

def Laws.wrapping_sequence(source, dest, delta, raw):
  match raw:
    case Spec.Missing{}:
      {==}
    case Spec.Cancelled{}:
      {==}
    case Spec.Bits{value}:
      sequence_valid_reference(Spec.valid_width(source, value), dest, delta, value)

# Only a genuine no-carry witness permits interpreting binary succession as
# Nat succession. This is deliberately not inferred from a bounded delta alone.
def unsigned_bump(+xs: List<&2, Bool>, room: Spec.CarryRoom(xs))
  -> {Spec.unsigned(Spec.bump(xs)) == 1n+Spec.unsigned(xs) : Nat}:
  match xs:
    case Nil{}:
      match room:
    case False{} <> t:
      {==}
    case True{} <> t:
      %unsigned_bump(t, room) :
        {Nat.double(Spec.unsigned(Spec.bump(t))) == Nat.double(_) : Nat}
      {==}

def safe_reference(delta: Nat, +xs: List<&2, Bool>, safe: Spec.SafeAdvance(delta, xs))
  -> {Spec.unsigned(Spec.advance(delta, xs)) == Nat.add(delta, Spec.unsigned(xs)) : Nat}:
  match delta:
    case 0n:
      {==}
    case 1n++p:
      (nonnegative, room, rest) = safe
      Equal.trans(Nat, Spec.unsigned(Spec.advance(p, Spec.bump(xs))),
        Nat.add(p, Spec.unsigned(Spec.bump(xs))), 1n+Nat.add(p, Spec.unsigned(xs)),
        safe_reference(p, Spec.bump(xs), rest),
        Equal.trans(Nat, Nat.add(p, Spec.unsigned(Spec.bump(xs))),
          Nat.add(p, 1n+Spec.unsigned(xs)), 1n+Nat.add(p, Spec.unsigned(xs)),
          Equal.cong(Nat, Nat, value => Nat.add(p, value),
            Spec.unsigned(Spec.bump(xs)), 1n+Spec.unsigned(xs), unsigned_bump(xs, room)),
          add_succ(p, Spec.unsigned(xs))))

def Laws.semantic_advance(delta, xs, safe):
  Equal.trans(Nat, Spec.unsigned(Impl.advance(delta, xs)),
    Spec.unsigned(Spec.advance(delta, xs)), Nat.add(delta, Spec.unsigned(xs)),
    Equal.cong(List<&2, Bool>, Nat, Spec.unsigned,
      Impl.advance(delta, xs), Spec.advance(delta, xs), Laws.advance_reference(delta, xs)),
    safe_reference(delta, xs, safe))

def safe_sign(delta: Nat, +xs: List<&2, Bool>, safe: Spec.SafeAdvance(delta, xs))
  -> {Spec.sign(Spec.advance(delta, xs)) == False{} : Bool}:
  match delta:
    case 0n:
      safe
    case 1n+p:
      (nonnegative, room, rest) = safe
      safe_sign(p, Spec.bump(xs), rest)

def Laws.nonnegative_advance(delta, xs, safe):
  Equal.trans(Bool, Spec.sign(Impl.advance(delta, xs)),
    Spec.sign(Spec.advance(delta, xs)), False{},
    Equal.cong(List<&2, Bool>, Bool, Spec.sign,
      Impl.advance(delta, xs), Spec.advance(delta, xs), Laws.advance_reference(delta, xs)),
    safe_sign(delta, xs, safe))

def Laws.admission_refinement(observations):
  match observations:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case Spec.Unknown{check}:
          {==}
        case Spec.Failed{check}:
          {==}
        case Spec.Passed{check}:
          Laws.admission_refinement(t)
        case Spec.Stopped{}:
          {==}

def Laws.invalid_classification(check, rest):
  ({==}, {==}, {==})

def Laws.passed_progress(check, rest):
  {==}

def Laws.sequence_progress():
  {==}

def Laws.signed_overflow_preserved():
  {==}

def Laws.comparison_refinement(slot):
  match slot:
    case Spec.S0{}:
      {==}
    case Spec.S1{}:
      {==}
    case Spec.S2{}:
      {==}
    case Spec.S3{}:
      {==}
    case Spec.S4{}:
      {==}
    case Spec.S5{}:
      {==}
    case Spec.S6{}:
      {==}
    case Spec.S7{}:
      {==}

def Laws.prefix_broadcast_extent(batch_predecessor):
  %mul_zero(batch_predecessor) :
    {1n+Nat.mul(batch_predecessor, 0n) == 1n+_ : Nat}
  {==}

def Laws.missing_cancelled(source, dest, delta):
  ({==}, {==})

def Laws.malformed_classification(source, dest, delta, xs, invalid):
  %Equal.sym(Bool, Spec.valid_width(source, xs), False{}, invalid) :
    {Impl.sequence_valid(_, dest, delta, xs) == Spec.Malformed{} : Spec.Transfer}
  {==}

def unsigned_zeros(n: Nat)
  -> {Spec.unsigned(List.replicate(Bool, n, False{})) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %unsigned_zeros(p) :
        {Nat.double(Spec.unsigned(List.replicate(Bool, p, False{}))) == Nat.double(_) : Nat}
      {==}

def unsigned_padding(+xs: List<&2, Bool>, +padding: Nat)
  -> {Spec.unsigned(List.append(&2, Bool, xs, List.replicate(Bool, padding, False{}))) ==
    Spec.unsigned(xs) : Nat}:
  match xs:
    case Nil{}:
      unsigned_zeros(padding)
    case False{} <> t:
      %unsigned_padding(t, padding) :
        {Nat.double(Spec.unsigned(List.append(&2, Bool, t,
          List.replicate(Bool, padding, False{})))) == Nat.double(_) : Nat}
      {==}
    case True{} <> t:
      %unsigned_padding(t, padding) :
        {1n+Nat.double(Spec.unsigned(List.append(&2, Bool, t,
          List.replicate(Bool, padding, False{})))) == 1n+Nat.double(_) : Nat}
      {==}

def Laws.logical_narrow(low, padding, exact, nonnegative):
  %Equal.sym(List<&2, Bool>,
    Impl.converted(Spec.I32{}, List.append(&2, Bool, low, List.replicate(Bool, padding, False{}))),
    low, Laws.narrow_low_bits(low, List.replicate(Bool, padding, False{}), exact)) :
    {Spec.unsigned(_) ==
      Spec.unsigned(List.append(&2, Bool, low, List.replicate(Bool, padding, False{}))) : Nat} &
    {Spec.sign(_) == False{} : Bool}
  (Equal.sym(Nat,
    Spec.unsigned(List.append(&2, Bool, low, List.replicate(Bool, padding, False{}))),
    Spec.unsigned(low), unsigned_padding(low, padding)), nonnegative)

def Laws.logical_widen(low, exact):
  %Equal.sym(List<&2, Bool>,
    Impl.converted(Spec.I64{}, List.append(&2, Bool, low, [False{}])),
    List.append(&2, Bool, low, List.replicate(Bool, 33n, False{})),
    Laws.signed_widen(low, False{}, exact)) :
    {Spec.unsigned(_) == Spec.unsigned(List.append(&2, Bool, low, [False{}])) : Nat}
  Equal.trans(Nat,
    Spec.unsigned(List.append(&2, Bool, low, List.replicate(Bool, 33n, False{}))),
    Spec.unsigned(low), Spec.unsigned(List.append(&2, Bool, low, [False{}])),
    unsigned_padding(low, 33n),
    Equal.sym(Nat, Spec.unsigned(List.append(&2, Bool, low, [False{}])),
      Spec.unsigned(low), unsigned_padding(low, 1n)))

def Laws.native_safe_progress():
  ({==}, Unit{},
    ({==}, Unit{},
      ({==}, Unit{},
        ({==}, Unit{},
          ({==}, Unit{},
            ({==}, Unit{},
              ({==}, Unit{},
                ({==}, Unit{}, {==}))))))))

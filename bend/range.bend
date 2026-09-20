# Balanced CPU fork/join allocation sequence. Nat arithmetic has no wraparound.
# The split annotation is explicit; both children contain exactly 2^p leaves.
import Base

def width(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      +h = width(p)
      Nat.add(h, h)

def tree(d: Nat, +start: Nat) -> List<&2, Nat>:
  match d:
    case 0n:
      [start]
    case 1n++p:
      left right = tree(p, start) tree(p, Nat.add(width(p), start))
      List.append(&2, Nat, left, right)

# 2048 and 8 are deliberately NOT paired in one unbalanced parallel call.
# Page zero stays reserved. The engine removes its dummy from this list once.
def native() -> List<&2, Nat>:
  main_pages = tree(11n, 1n)
  headroom_pages = tree(3n, 2049n)
  List.append(&2, Nat, main_pages, headroom_pages)

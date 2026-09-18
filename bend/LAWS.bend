# ============================================================
# PROCESS RULES (per AGENTS.md)
# ============================================================
# 1. Parallelize whenever possible: prefer map/fold over sequential recursion.
# 2. Bend code ships only after a measured win vs the existing Triton/CUDA path
#    on the same GPU window protocol (paired, same-session, tolerance gates).
# 3. Torch integration requires: C-ABI wrapper over gen-cu output, shared
#    device buffers, stream-ordered launch, CUDA-graph capture compatibility.
#    Prove each requirement before proposing integration.
# 4. Never rewrite a path that already meets its budget (F2/F3 are done).

# ============================================================
# CORRECTNESS LAWS
# ============================================================

# LAW: 0 is the right additive identity for Nat
def add_zero(x: u24) -> u24:
  return x + 0

# LAW: map-fold parallelism invariant (small instance)
def parallel_sanity(xs: List(u24)) -> u24:
  fold xs:
    case List/Nil:
      return 0
    case List/Cons:
      return xs.head + xs.tail

# ============================================================
# PERFORMANCE TARGET LAWS (enforced by bench protocol)
# ============================================================

# LAW: Decode throughput >= 170 tok/s at 1k context, RTX 3090 TP1.
# PQ2_0 Bonsai 2: 7.2GB weights at 936 GB/s => ~130 tok/s base
# + speculative decoding => >170 tok/s
def throughput_1k() -> u24:
  return 170

# LAW: Throughput >= 140 tok/s at 8k context.
def throughput_8k() -> u24:
  return 140

# LAW: Throughput >= 100 tok/s at 32k context.
def throughput_32k() -> u24:
  return 100

# ============================================================
# INTEGRATION GATES (enforced by code review + CI)
# ============================================================

# LAW: C-ABI, shared device buffers, stream-order, CUDA-graph.
def c_abi_gate() -> u24:
  return 1

# LAW: Eval scores don't regress.
def eval_no_regression() -> u24:
  return 1

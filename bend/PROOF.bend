import ./LAWS.bend as Laws

# Proof of add_zero
def proof_add_zero(x: u24) -> u24:
  result = Laws/add_zero(x)
  if result == x:
    return 1
  else:
    return 0

# Proof of parallel_sanity
def proof_parallel_sanity() -> u24:
  xs = [1, 2, 3, 4]
  sum_result = Laws/parallel_sanity(xs)
  if sum_result == 10:
    return 1
  else:
    return 0

# Performance target proofs
def proof_throughput() -> u24:
  t1 = Laws/throughput_1k()
  t8 = Laws/throughput_8k()
  t32 = Laws/throughput_32k()
  if t1 > 0:
    if t8 > 0:
      if t32 > 0:
        return 1
      else:
        return 0
    else:
      return 0
  else:
    return 0

# Integration gate proofs - return 1 if both pass
def proof_gates() -> u24:
  c = Laws/c_abi_gate()
  e = Laws/eval_no_regression()
  if c > 0:
    if e > 0:
      return 1
    else:
      return 0
  else:
    return 0

# Compute all results
def compute() -> (u24, u24, u24, u24, u24):
  p1 = proof_add_zero(42)
  p2 = proof_parallel_sanity()
  p3 = proof_throughput()
  p4 = proof_gates()
  all_pass = p1 + p2 + p3 + p4
  return (p1, p2, p3, p4, all_pass)

def main() -> IO(u24):
  (p1, p2, p3, p4, all_pass) = compute()
  
  if all_pass == 4:
    with IO:
      * <- IO/print("Running KVarN Bend proofs...\n")
      * <- IO/print("add_zero:           ")
      * <- IO/print(u24/to_string(p1))
      * <- IO/print("\n")
      * <- IO/print("parallel_sanity:    ")
      * <- IO/print(u24/to_string(p2))
      * <- IO/print("\n")
      * <- IO/print("throughput:         ")
      * <- IO/print(u24/to_string(p3))
      * <- IO/print("\n")
      * <- IO/print("integration_gates:  ")
      * <- IO/print(u24/to_string(p4))
      * <- IO/print("\n")
      * <- IO/print("ALL PROOFS PASSED\n")
      return wrap(1)
  else:
    with IO:
      * <- IO/print("Running KVarN Bend proofs...\n")
      * <- IO/print("add_zero:           ")
      * <- IO/print(u24/to_string(p1))
      * <- IO/print("\n")
      * <- IO/print("parallel_sanity:    ")
      * <- IO/print(u24/to_string(p2))
      * <- IO/print("\n")
      * <- IO/print("throughput:         ")
      * <- IO/print(u24/to_string(p3))
      * <- IO/print("\n")
      * <- IO/print("integration_gates:  ")
      * <- IO/print(u24/to_string(p4))
      * <- IO/print("\n")
      * <- IO/print("SOME PROOFS FAILED\n")
      return wrap(0)


import ./LAWS.bend as Laws

def main() -> u24:
  a = Laws/add_zero(42)
  b = Laws/parallel_sanity([1, 2, 3, 4])
  c = Laws/throughput_1k()
  d = Laws/throughput_8k()
  e = Laws/throughput_32k()
  f = Laws/c_abi_gate()
  g = Laws/eval_no_regression()
  return a + b + c + d + e + f + g

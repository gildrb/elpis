# ============================================================
# PQ2_0 Ternary Dequant Kernel (Bend CUDA implementation)
# ============================================================

import ./LAWS.bend as Laws

# Core: decode one 2-bit value to float
def decode_to_float(code: u24) -> f24:
  if code == 0:
    return -1.0
  else:
    if code == 1:
      return 0.0
    else:
      if code == 2:
        return 1.0
      else:
        return 0.0

# Apply scale factor
def apply_scale(val: f24, scale: f24) -> f24:
  return val * scale

# Sanity test
def sanity_check() -> u24:
  tern = decode_to_float(0)
  result = apply_scale(tern, 1.0)
  if result < -0.5:
    if result > -1.5:
      return 1
    else:
      return 0
  else:
    return 0

# Minimal main (pure function, fits 64 CUDA nodes)
def main() -> u24:
  return sanity_check()
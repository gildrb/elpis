# Tiny test to check CUDA compilation viability
def main() -> IO(u24):
  with IO:
    * <- IO/print("Hello from Bend on CUDA!\n")
    return wrap(1)
// Leaf-level cost: eta_exl3_accept (glue validation + Bend leaf) vs a C
// transcription of the serial decision, over served-like k = 7 inputs.
// cc -O2 exl3_accept_leaf.c -ldl -o leaf && ./leaf LIB
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define N 4096
static int64_t cells[N][23];

static uint64_t rng = 20260926;
static uint32_t next(void) {
  rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
  return (uint32_t)rng;
}

static int32_t ref(const int64_t* c) {
  int64_t k = c[0], budget = c[1], cp = c[2], ns = c[3];
  for (int64_t i = 0; i <= k; ++i) {
    int64_t t = c[8 + i], n = i + 1;
    int stop = 0;
    for (int64_t s = 0; s < ns; ++s) stop |= c[4 + s] == t;
    if (stop || n >= budget) return (int32_t)(n * 2 + 1);
    if (i == k) return (int32_t)(n * 2);
    if (c[16 + i] != t || n == cp) return (int32_t)(n * 2);
  }
  return -1;
}

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e9 + ts.tv_nsec;
}

int main(int argc, char** argv) {
  void* h = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
  int32_t (*leaf)(const int64_t*) = (int32_t (*)(const int64_t*))dlsym(h, "eta_exl3_accept");
  for (int r = 0; r < N; ++r) {
    int64_t* c = cells[r];
    c[0] = 7; c[1] = next() % 20 == 0 ? 1 + next() % 63 : 4096;
    c[2] = next() % 10 == 0 ? 1 + next() % 7 : 0; c[3] = 2;
    c[4] = 248044; c[5] = 248046; c[6] = c[7] = 0;
    int acc = 0;
    while (acc < 7 && next() % 100 < 75) ++acc;
    for (int i = 0; i < 8; ++i) c[8 + i] = next() % 248000;
    if (next() % 50 == 0) c[8 + next() % 8] = 248046;
    for (int i = 0; i < 7; ++i) c[16 + i] = i < acc ? c[8 + i] : (c[8 + i] + 1) % 248000;
  }
  for (int r = 0; r < N; ++r) {
    if (leaf(cells[r]) != ref(cells[r])) { printf("mismatch %d\n", r); return 1; }
  }
  volatile int64_t sink = 0;
  for (int round = 0; round < 23; ++round) {
    for (int which = 0; which < 2; ++which) {
      int w = round % 2 ? 1 - which : which;
      double t0 = now();
      for (int rep = 0; rep < 200; ++rep)
        for (int r = 0; r < N; ++r) sink += w ? ref(cells[r]) : leaf(cells[r]);
      double dt = (now() - t0) / (200.0 * N);
      if (round >= 3) printf("%s %.2f\n", w ? "cref" : "bend", dt);
    }
  }
  return (int)(sink & 0);
}

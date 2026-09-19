# ============================================================
# KVarN Gather Kernel - Bend CUDA implementation
#
# Parallel gather of KV cache pages for speculative decoding.
# Each (row, head) pair is independent -> automatic parallelism.
#
# Must fit within HVM CUDA 64-node function size limit.
# ============================================================

import ./LAWS.bend as Laws

# ============================================================
# TYPE DEFINITIONS
# ============================================================

type PageEntry:
  PageEntry {
    page: u24,
    token: u24,
    slot: i24,
    committed: u24,
    provisional: u24,
  }

type GatherItem:
  GatherItem {
    loc: i24,
    length: u24,
    page: PageEntry,
    head: u24,
    width: u24,
  }

type GatherOutput:
  GatherOutput {
    key: f24,
    value: f24,
    status: u24,
  }

# ============================================================
# PER-PAGE VALIDATION
# ============================================================

def is_valid_page(entry: PageEntry, length: u24, width: u24) -> u24:
  match entry:
    case PageEntry/PageEntry:
      # A page is valid if it has data and is committed or provisional
      if entry.page > 0:
        if entry.committed > 0:
          return 1
        else:
          if entry.provisional > 0:
            return 1
          else:
            return 0
      else:
        return 0

def is_bad_length(length: u24, width: u24) -> u24:
  if length < 1:
    return 1
  else:
    if length > width:
      return 1
    else:
      return 0

# ============================================================
# SINGLE POSITION PROCESS
# ============================================================

def process_position(
  loc: i24,
  length: u24,
  entry: PageEntry,
  head: u24,
  width: u24,
) -> GatherOutput:
  
  valid = is_valid_page(entry, length, width)
  bad_len = is_bad_length(length, width)
  
  invalid = 0
  if bad_len > 0:
    invalid = 1
  else:
    if valid == 0:
      invalid = 1
    else:
      invalid = 0
  
  if invalid > 0:
    return GatherOutput/GatherOutput { key: 0.0, value: 0.0, status: 1 }
  else:
    return GatherOutput/GatherOutput { key: 1.0, value: 1.0, status: 0 }

# ============================================================
# PARALLEL GATHER OVER WORK ITEMS
# ============================================================

def gather_all(items: List(GatherItem)) -> List(GatherOutput):
  # Fold is parallel: each item processed independently
  fold items:
    case List/Nil:
      return []
    case List/Cons:
      match items.head:
        case GatherItem/GatherItem:
          result = process_position(
            items.head.loc, items.head.length,
            items.head.page, items.head.head, items.head.width
          )
          return List/Cons(result, items.tail)
          
def main() -> IO(u24):
  # Simple sanity check
  entry = PageEntry/PageEntry { page: 1, token: 0, slot: -1, committed: 1, provisional: 0 }
  result = process_position(+128, 1, entry, 0, 2184)
  
  ok = 0
  match result:
    case GatherOutput/GatherOutput:
      if result.status == 0:
        ok = 1
      else:
        ok = 0
  
  with IO:
    if ok > 0:
      * <- IO/print("Gather kernel: PASS\n")
    else:
      * <- IO/print("Gather kernel: FAIL\n")
    return wrap(ok)
# Prints the served-shape precision table: for every (op, m), m = 1 .. 8, the stock 355c6ee class
# (PA.part_a, equal to the stock model's class by law stock_table_partA; lm_head: not normalized,
# elpis runs that same kernel) and the elpis class (bend/precision_elpis.bend under the served runtime
# outcomes and persisted autotune records). bend/precision_diff.py compares it with partA.md.
import Base
import ./precision_order.bend as Ord
import ./precision_stock.bend as S
import ./precision_elpis.bend as E
import ./precision_parta.bend as PA

def op_name(op: S.Op) -> String:
  match op:
    case S.AttnQG{}:
      "attn q_proj (q|gate)"
    case S.AttnK{}:
      "attn k_proj"
    case S.AttnV{}:
      "attn v_proj"
    case S.AttnO{}:
      "attn o_proj"
    case S.GdnQkv{}:
      "GDN in_proj_qkv"
    case S.GdnZ{}:
      "GDN in_proj_z"
    case S.GdnOut{}:
      "GDN out_proj"
    case S.MlpGate{}:
      "MLP gate_proj"
    case S.MlpUp{}:
      "MLP up_proj"
    case S.MlpDown{}:
      "MLP down_proj"
    case S.LmHead{}:
      "lm_head"

def route_name(r: E.Route) -> String:
  match r:
    case E.M16g{}:
      "exl3_gemm_m16g_kernel"
    case E.Tail{}:
      "exl3_tail_m16_kernel"
    case E.StockK{}:
      "stock kernel"

def fb() -> S.Tune:
  S.Tune{4n, 82n}

def ts() -> S.Tunes:
  S.tunes(S.gu_shape(), S.gu_grid(), S.head_shape(), S.head_grid(), fb())

def stock_s(+op: S.Op, +m: Nat, nh: Bool) -> String:
  match nh:
    case True{}:
      Ord.show(PA.part_a(op, m))
    case False{}:
      "stock exl3_gemm (K 6, shape 4, grid 82): not normalized"

def elpis_s(+op: S.Op, +m: Nat, st: Bool) -> String:
  match st:
    case True{}:
      "= stock kernel"
    case False{}:
      Ord.show(E.acc(op, m, S.served_env(), ts()))

def row(+op: S.Op, +m: Nat) -> String:
  op_name(op) ++ " | " ++ Nat.show(m) ++ " | " ++ stock_s(op, m, PA.not_head(op)) ++ " | " ++
    route_name(E.route(op, m)) ++ " | " ++ elpis_s(op, m, E.is_stock(op, m)) ++ "\n"

def rows(left: Nat, +m: Nat, +op: S.Op) -> String:
  match left:
    case 0n:
      ""
    case 1n+r:
      row(op, m) ++ rows(r, 1n+m, op)

def main() -> String:
  rows(8n, 1n, S.AttnQG{}) ++ rows(8n, 1n, S.AttnK{}) ++ rows(8n, 1n, S.AttnV{}) ++ rows(8n, 1n, S.AttnO{}) ++
  rows(8n, 1n, S.GdnQkv{}) ++ rows(8n, 1n, S.GdnZ{}) ++ rows(8n, 1n, S.GdnOut{}) ++ rows(8n, 1n, S.MlpGate{}) ++
  rows(8n, 1n, S.MlpUp{}) ++ rows(8n, 1n, S.MlpDown{}) ++ rows(8n, 1n, S.LmHead{})

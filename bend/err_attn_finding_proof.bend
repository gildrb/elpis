# Proofs of bend/err_attn_finding_laws.bend (the current kernel's gap): case analysis, computation
# and rewriting only. No @unsafe definitions, axioms, holes or foreign code; every def precedes its
# uses. The enumerations over the Q.K^T k-step ks (0 .. 15, then every ks >= 16, where
# Nat.sub(16n, ks) = 0) and the rotation half make every case a closed computation of Eb.dom.
import Base
import ./err_bound.bend as Eb
import ./err_attn.bend as Ea
import ./err_attn_finding_laws.bend as Laws

def Laws.elpis_worst2_path():
  {==}

def Laws.stock_worst2_path():
  {==}

def Laws.attn_gap_rotation():
  {==}

# ---- AQ / AW: kh in {0, 1, 2 + q}, ks enumerated ----
def aq_t_0(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), 0n, ks, True{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aq_t_1(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), 1n, ks, True{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aq_t_2(q: Nat, +ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), 1n+1n+q, ks, True{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aq_t(+kh: Nat, +ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), kh, ks, True{})) == False{} : Bool}:
  match kh:
    case 0n:
      aq_t_0(ks)
    case 1n+p:
      match p:
        case 0n:
          aq_t_1(ks)
        case 1n+q:
          aq_t_2(q, ks)
def aq_f_0(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), 0n, ks, False{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aq_f_1(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), 1n, ks, False{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aq_f_2(q: Nat, +ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), 1n+1n+q, ks, False{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aq_f(+kh: Nat, +ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), kh, ks, False{})) == False{} : Bool}:
  match kh:
    case 0n:
      aq_f_0(ks)
    case 1n+p:
      match p:
        case 0n:
          aq_f_1(ks)
        case 1n+q:
          aq_f_2(q, ks)
def aq_gen(+kh: Nat, +ks: Nat, +i: Nat, c: Bool, e: {c == Nat.is_lt(i, 16n) : Bool})
  -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.stock_leaf(Ea.geo_s2(), Ea.AQ{kh, ks, i})) == False{} : Bool}:
  match c:
    case True{}:
      %e : {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), kh, ks, _)) == False{} : Bool}
      aq_t(kh, ks)
    case False{}:
      %e : {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aq(Ea.geo_s2(), kh, ks, _)) == False{} : Bool}
      aq_f(kh, ks)
def aw_t_0(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), 0n, ks, True{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aw_t_1(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), 1n, ks, True{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aw_t_2(q: Nat, +ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), 1n+1n+q, ks, True{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aw_t(+kh: Nat, +ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), kh, ks, True{})) == False{} : Bool}:
  match kh:
    case 0n:
      aw_t_0(ks)
    case 1n+p:
      match p:
        case 0n:
          aw_t_1(ks)
        case 1n+q:
          aw_t_2(q, ks)
def aw_f_0(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), 0n, ks, False{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aw_f_1(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), 1n, ks, False{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aw_f_2(q: Nat, +ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), 1n+1n+q, ks, False{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def aw_f(+kh: Nat, +ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), kh, ks, False{})) == False{} : Bool}:
  match kh:
    case 0n:
      aw_f_0(ks)
    case 1n+p:
      match p:
        case 0n:
          aw_f_1(ks)
        case 1n+q:
          aw_f_2(q, ks)
def aw_gen(+kh: Nat, +ks: Nat, +i: Nat, c: Bool, e: {c == Nat.is_lt(i, 16n) : Bool})
  -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.stock_leaf(Ea.geo_s2(), Ea.AW{kh, ks, i})) == False{} : Bool}:
  match c:
    case True{}:
      %e : {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), kh, ks, _)) == False{} : Bool}
      aw_t(kh, ks)
    case False{}:
      %e : {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_aw(Ea.geo_s2(), kh, ks, _)) == False{} : Bool}
      aw_f(kh, ks)

# ---- AK: ks enumerated ----
def ak_t(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_ak(Ea.geo_s2(), ks, True{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def ak_f(+ks: Nat) -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_ak(Ea.geo_s2(), ks, False{})) == False{} : Bool}:
  match ks:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  {==}
def ak_gen(+ks: Nat, +i: Nat, c: Bool, e: {c == Nat.is_lt(i, 16n) : Bool})
  -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.stock_leaf(Ea.geo_s2(), Ea.AK{ks, i})) == False{} : Bool}:
  match c:
    case True{}:
      %e : {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_ak(Ea.geo_s2(), ks, _)) == False{} : Bool}
      ak_t(ks)
    case False{}:
      %e : {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_ak(Ea.geo_s2(), ks, _)) == False{} : Bool}
      ak_f(ks)

def av_gen(+i: Nat, c: Bool, e: {c == Nat.is_lt(i, 16n) : Bool})
  -> {Eb.dom(128n, Ea.elpis_worst2(), Ea.stock_leaf(Ea.geo_s2(), Ea.AV{i})) == False{} : Bool}:
  match c:
    case True{}:
      %e : {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_av(Ea.geo_s2(), _)) == False{} : Bool}
      {==}
    case False{}:
      %e : {Eb.dom(128n, Ea.elpis_worst2(), Ea.s_av(Ea.geo_s2(), _)) == False{} : Bool}
      {==}

def Laws.attn_not_dom(l):
  match l:
    case Ea.AQ{+kh, +ks, +i}:
      aq_gen(kh, ks, i, Nat.is_lt(i, 16n), {==})
    case Ea.AK{+ks, +i}:
      ak_gen(ks, i, Nat.is_lt(i, 16n), {==})
    case Ea.AV{+i}:
      av_gen(i, Nat.is_lt(i, 16n), {==})
    case Ea.AW{+kh, +ks, +i}:
      aw_gen(kh, ks, i, Nat.is_lt(i, 16n), {==})
    case Ea.AG{}:
      {==}

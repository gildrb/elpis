# Pruned int4 draft head of ext patch 9005c (9005c-eta-draft-q4-head-pruned-n896.patch), transcribed over Nat and
# lists from the patched sources (tree q4p/c_eta):
#   S: modules/arch_specific/dflash2_head_blocks.py   (constants, DRAFT_HEAD_BLOCK_ORDER, kept_blocks, PrunedHeadPolicy)
#   Q: modules/arch_specific/dflash2_q4_head.py       (Q4DraftHead: kept-block check, keep_cols, id_map, topk slicing)
#   D: exllamav3_ext/dflash2_head.cu                   (better(), the epilogue's column -> token id, HEAD_TOPK)
# Model boundaries (not proven here): Python / torch / CUDA semantics and int32 ranges; the kernel's fp32 values are
# modelled by Nat values under their total order (assumed never NaN: the proofs need a total order); lists are the
# model's representation of the host tables and candidate lists, not a production data structure;
# the per-column values of the permuted copy equal the full head's for the same token (packing is column-local; checked
# on the CPU by DraftProj's smoke_layout.py, not here); the warp / block / grid merge network is modelled by its
# contract, the top-16 by better() of all columns (bend/draft_head_partition.bend covers "every tile once"); every
# column id < vocab (vocab = 248320 and 128 N are multiples of 16, so the epilogue's padding branch never runs).
# The policy's statistics counters (rounds_pruned, rounds_full, fallbacks) do not influence any choice and are not
# modelled; the window is kept newest-first (sum and the last-32 cut do not depend on the order).
# Reference: draft_head_idmap_spec.bend; laws: draft_head_idmap_laws.bend; proof: draft_head_idmap_proof.bend.
import Base
import ./draft_head_idmap_spec.bend as Spec

# ==== constants ====

# S: DRAFT_HEAD_VOCAB = 248320
def idm_vocab() -> Nat:
  248320n

# S: DRAFT_HEAD_BLOCK = 128
def idm_block() -> Nat:
  128n

# S: DRAFT_HEAD_BLOCKS_DEFAULT = 896
def idm_n_default() -> Nat:
  896n

# S: DRAFT_HEAD_BLOCKS_ALLOWED = (896, 1024): the other selectable N
def idm_n_alt() -> Nat:
  1024n

# S: FALLBACK_WINDOW = 32
def idm_window() -> Nat:
  32n

# S: FALLBACK_TRIGGER = 2
def idm_trigger() -> Nat:
  2n

# S: FALLBACK_HOLD = 128
def idm_hold_len() -> Nat:
  128n

# D: #define HEAD_TOPK 16
def idm_topk_k() -> Nat:
  16n

# S: DRAFT_HEAD_BLOCK_ORDER = ( ... ): the first 1024 entries of the block order (1940 blocks of 128 ids)
def idm_order() -> List<&2, Nat>:
  [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 16n, 17n, 18n, 19n, 20n, 21n, 22n, 23n, 24n,
    25n, 26n, 27n, 28n, 29n, 30n, 31n, 32n, 33n, 34n, 35n, 36n, 37n, 38n, 39n, 40n, 41n, 42n, 43n, 44n, 45n, 46n, 47n,
    48n, 49n, 50n, 51n, 52n, 53n, 54n, 55n, 56n, 57n, 58n, 59n, 60n, 61n, 62n, 63n, 64n, 65n, 66n, 67n, 68n, 69n, 70n,
    71n, 72n, 73n, 74n, 75n, 76n, 77n, 78n, 79n, 80n, 81n, 82n, 83n, 84n, 85n, 86n, 87n, 88n, 89n, 90n, 91n, 92n, 93n,
    94n, 95n, 96n, 97n, 98n, 99n, 100n, 101n, 102n, 103n, 104n, 105n, 106n, 107n, 108n, 109n, 110n, 111n, 112n, 113n,
    114n, 115n, 116n, 117n, 118n, 119n, 120n, 121n, 122n, 123n, 124n, 125n, 126n, 127n, 1937n, 1938n, 133n, 143n,
    144n, 153n, 163n, 183n, 187n, 197n, 208n, 222n, 224n, 227n, 234n, 240n, 248n, 250n, 251n, 252n, 270n, 274n, 279n,
    281n, 287n, 290n, 299n, 312n, 316n, 317n, 325n, 326n, 331n, 344n, 350n, 358n, 360n, 364n, 365n, 385n, 386n, 390n,
    403n, 408n, 412n, 429n, 443n, 446n, 448n, 449n, 468n, 469n, 474n, 508n, 523n, 540n, 542n, 550n, 551n, 558n, 559n,
    575n, 585n, 587n, 596n, 599n, 612n, 619n, 635n, 641n, 644n, 667n, 672n, 676n, 711n, 725n, 738n, 744n, 1163n,
    1164n, 1165n, 1168n, 1170n, 1172n, 1173n, 1174n, 1180n, 1182n, 1183n, 1195n, 1196n, 1202n, 1206n, 1209n, 1213n,
    1218n, 1225n, 1228n, 1233n, 1240n, 1244n, 1259n, 1268n, 1282n, 1319n, 1320n, 1321n, 1322n, 1323n, 1324n, 1325n,
    1326n, 1340n, 1361n, 1372n, 1377n, 1393n, 1407n, 1454n, 1627n, 1648n, 1653n, 1657n, 1862n, 241n, 335n, 210n, 171n,
    140n, 149n, 162n, 695n, 136n, 130n, 229n, 137n, 141n, 135n, 682n, 191n, 150n, 371n, 147n, 201n, 151n, 132n, 159n,
    200n, 134n, 138n, 576n, 232n, 216n, 145n, 185n, 131n, 155n, 244n, 189n, 158n, 139n, 174n, 164n, 148n, 182n, 583n,
    152n, 129n, 217n, 202n, 204n, 146n, 173n, 205n, 165n, 157n, 128n, 401n, 334n, 233n, 199n, 142n, 223n, 179n, 336n,
    196n, 212n, 243n, 177n, 207n, 487n, 175n, 168n, 235n, 193n, 288n, 203n, 178n, 176n, 192n, 167n, 213n, 156n, 186n,
    209n, 190n, 161n, 289n, 549n, 379n, 195n, 188n, 423n, 263n, 154n, 170n, 172n, 247n, 272n, 198n, 219n, 306n, 169n,
    230n, 269n, 166n, 397n, 160n, 228n, 285n, 215n, 259n, 296n, 238n, 440n, 266n, 218n, 211n, 181n, 260n, 543n, 305n,
    242n, 237n, 286n, 420n, 180n, 332n, 314n, 414n, 184n, 214n, 280n, 194n, 373n, 236n, 321n, 292n, 245n, 278n, 424n,
    231n, 226n, 337n, 435n, 262n, 239n, 351n, 295n, 413n, 265n, 246n, 391n, 297n, 298n, 457n, 277n, 465n, 206n, 249n,
    453n, 301n, 268n, 220n, 411n, 345n, 318n, 450n, 372n, 271n, 313n, 221n, 419n, 225n, 343n, 359n, 282n, 643n, 311n,
    273n, 291n, 355n, 294n, 422n, 712n, 300n, 257n, 254n, 324n, 418n, 347n, 256n, 394n, 315n, 495n, 261n, 567n, 253n,
    405n, 387n, 492n, 511n, 356n, 264n, 404n, 328n, 276n, 396n, 409n, 283n, 255n, 307n, 455n, 376n, 258n, 441n, 319n,
    389n, 377n, 436n, 354n, 417n, 349n, 267n, 1636n, 320n, 309n, 504n, 303n, 426n, 329n, 304n, 275n, 357n, 348n, 352n,
    322n, 649n, 375n, 430n, 338n, 512n, 368n, 527n, 388n, 369n, 327n, 362n, 383n, 410n, 400n, 302n, 353n, 330n, 398n,
    284n, 628n, 496n, 685n, 342n, 402n, 565n, 514n, 503n, 560n, 310n, 479n, 490n, 406n, 680n, 534n, 341n, 363n, 489n,
    483n, 361n, 673n, 478n, 382n, 370n, 671n, 415n, 339n, 340n, 333n, 466n, 293n, 473n, 603n, 393n, 588n, 374n, 608n,
    421n, 670n, 323n, 384n, 434n, 367n, 392n, 499n, 459n, 438n, 507n, 439n, 445n, 532n, 454n, 498n, 718n, 684n, 407n,
    544n, 378n, 563n, 602n, 462n, 548n, 509n, 346n, 484n, 472n, 399n, 451n, 538n, 581n, 442n, 520n, 547n, 506n, 460n,
    425n, 444n, 431n, 632n, 702n, 381n, 416n, 519n, 1158n, 594n, 480n, 562n, 517n, 1771n, 308n, 427n, 475n, 433n,
    463n, 497n, 481n, 545n, 723n, 366n, 456n, 536n, 477n, 655n, 701n, 580n, 533n, 1621n, 525n, 687n, 546n, 529n, 500n,
    571n, 610n, 518n, 724n, 553n, 502n, 572n, 589n, 586n, 663n, 557n, 494n, 630n, 609n, 706n, 432n, 528n, 720n, 674n,
    713n, 564n, 627n, 555n, 486n, 659n, 510n, 613n, 633n, 521n, 692n, 566n, 488n, 485n, 611n, 631n, 690n, 616n, 622n,
    458n, 606n, 696n, 428n, 505n, 515n, 541n, 726n, 526n, 691n, 729n, 660n, 650n, 464n, 493n, 617n, 614n, 561n, 524n,
    625n, 537n, 593n, 452n, 535n, 747n, 395n, 741n, 615n, 597n, 470n, 491n, 636n, 467n, 666n, 447n, 591n, 590n, 607n,
    501n, 657n, 437n, 736n, 668n, 574n, 569n, 624n, 707n, 745n, 482n, 598n, 604n, 530n, 471n, 708n, 573n, 669n, 531n,
    556n, 626n, 522n, 662n, 579n, 461n, 568n, 577n, 689n, 647n, 735n, 742n, 743n, 678n, 704n, 697n, 380n, 654n, 731n,
    637n, 1515n, 584n, 727n, 698n, 652n, 683n, 621n, 675n, 634n, 623n, 737n, 618n, 539n, 595n, 601n, 715n, 699n, 661n,
    686n, 714n, 656n, 746n, 1159n, 710n, 578n, 677n, 516n, 703n, 719n, 642n, 552n, 688n, 705n, 605n, 694n, 645n, 582n,
    1161n, 513n, 653n, 570n, 592n, 700n, 600n, 554n, 658n, 638n, 728n, 679n, 639n, 620n, 1160n, 681n, 693n, 722n,
    646n, 733n, 716n, 1169n, 640n, 665n, 476n, 739n, 648n, 629n, 651n, 1162n, 740n, 721n, 717n, 732n, 664n, 730n,
    734n, 1171n, 1344n, 709n, 1166n, 1761n, 1194n, 1343n, 1205n, 1349n, 1351n, 1211n, 1210n, 1318n, 1246n, 1353n,
    1406n, 1167n, 1280n, 1204n, 1264n, 1212n, 1222n, 1176n, 1198n, 1242n, 1188n, 1252n, 1179n, 752n, 1502n, 1352n,
    1581n, 1562n, 1345n, 748n, 1175n, 1860n, 1285n, 1178n, 1197n, 1384n, 1243n, 1248n, 1586n, 1736n, 1513n, 1516n,
    1332n, 1640n, 1330n, 1554n, 1734n, 1363n, 1793n, 1201n, 1187n, 1263n, 1517n, 1388n, 1395n, 1549n, 1878n, 1245n,
    1442n, 1189n, 1177n, 1732n, 1378n, 1544n, 1396n, 1239n, 1777n, 1615n, 751n, 1453n, 1260n, 1181n, 1369n, 1419n,
    1334n, 1241n, 1610n, 1737n, 1400n, 1845n, 1844n, 1540n, 1191n, 1421n, 1247n, 1446n, 1287n, 1362n, 1628n, 1397n,
    1503n, 1743n, 1467n, 1251n, 1350n, 1728n, 1565n, 1418n, 750n, 1827n, 1782n, 1273n, 1214n, 1768n, 1471n, 1392n,
    1256n, 1683n, 759n, 1249n, 1491n, 1483n, 1376n, 1472n, 1336n, 1445n, 1481n, 1354n, 1822n, 1726n, 1776n, 1250n,
    1261n, 1272n, 1764n, 1231n, 1414n, 1591n, 1801n, 1192n, 1639n, 1464n, 1420n, 753n, 1283n, 762n, 1333n, 1538n,
    1327n, 1459n, 1217n, 1190n, 1389n, 1717n, 1422n, 1267n, 1184n, 1613n, 1348n, 1383n, 1655n, 1834n, 1405n, 1506n,
    1774n, 1588n, 1359n, 1338n, 1200n, 1886n, 1431n, 1450n, 1356n, 1599n, 1632n, 1561n, 1461n, 1842n, 1342n, 1800n,
    1535n, 1692n, 1394n, 1443n, 1216n, 1638n, 1883n, 1876n, 1534n, 1337n, 1866n, 1265n, 1221n, 1521n, 1656n, 1370n,
    1399n, 1258n, 1271n, 1329n, 1865n, 1277n, 1413n, 1720n, 1417n, 1255n, 1207n, 1292n, 1611n, 1537n, 1477n, 1346n,
    1788n, 1510n, 1341n, 1186n, 1462n, 1199n, 1533n, 786n, 1536n, 1301n, 1364n, 1711n]

# ==== kept blocks (S: kept_blocks) ====

def idm_sort.sel(go: Bool, +x: Nat, +y: Nat, +rest: List<&2, Nat>, deeper: List<&2, Nat>) -> List<&2, Nat>:
  match go:
    case True{}:
      x <> y <> rest
    case False{}:
      y <> deeper

# Insert x into an ascending list (before the first entry >= x).
def idm_sort.ins(ys: List<&2, Nat>, +x: Nat) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      x <> Nil{}
    case +y <> +rest:
      idm_sort.sel(Nat.is_le(x, y), x, y, rest, idm_sort.ins(rest, x))

# Python sorted() of a list of ints: ascending.
def idm_sort(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      idm_sort.ins(idm_sort(rest), x)

# S: blocks = sorted(DRAFT_HEAD_BLOCK_ORDER[:n])
def idm_kept_blocks(+order: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  idm_sort(List.take(&2, Nat, order, n))

# len(set(xs)): the entries that do not occur again later.
def idm_card(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +y <> +rest:
      Nat.add(Spec.ids_bit(Bool.not(Spec.ids_member(rest, y))), idm_card(rest))

# S: (blocks[-1] + 1) * DRAFT_HEAD_BLOCK > vocab  rejects; an empty list has no blocks[0] / blocks[-1] (IndexError,
# also a rejection). Q: 128 * (kb[-1] + 1) > vocab is the same product.
def idm_last_fits(xs: List<&2, Nat>, +vocab: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +y <> +rest:
      match rest:
        case Nil{}:
          Nat.is_le(Nat.mul(1n+y, idm_block()), vocab)
        case _:
          idm_last_fits(rest, vocab)

# S: if len(set(blocks)) != n or blocks[0] < 0 or (blocks[-1] + 1) * DRAFT_HEAD_BLOCK > vocab: raise ValueError
# (blocks[0] < 0 is vacuous over Nat). True = accepted.
def idm_kept_ok(+order: List<&2, Nat>, +n: Nat, +vocab: Nat) -> Bool:
  +blocks = idm_kept_blocks(order, n)
  Bool.and(Nat.is_eq(idm_card(blocks), n), idm_last_fits(blocks, vocab))

# Q: any(b1 <= b0 for b0, b1 in zip(kb, kb[1:])) rejects; True = no such pair.
def idm_adj_incr(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +y <> +rest:
      match rest:
        case Nil{}:
          True{}
        case +z <> _:
          Bool.and(Nat.is_lt(y, z), idm_adj_incr(rest))

# Q: if (vocab % 128 or not kb or len(kb) * 128 < HEAD_TOP_K or kb[0] < 0 or 128 * (kb[-1] + 1) > vocab
# Q:         or any(b1 <= b0 for b0, b1 in zip(kb, kb[1:]))): raise ValueError      True = accepted.
def idm_head_ok(+kb: List<&2, Nat>, +vocab: Nat) -> Bool:
  +len = List.length(&2, Nat, kb)
  Bool.and(Nat.is_eq(Nat.mod(vocab, 128n), 0n),
    Bool.and(Nat.is_lt(0n, len),
      Bool.and(Nat.is_le(idm_topk_k(), Nat.mul(len, 128n)),
        Bool.and(idm_last_fits(kb, vocab), idm_adj_incr(kb)))))

# ==== column -> token id map (Q: Q4DraftHead.__init__) ====

# [x, x + 1, ..., x + len - 1]
def idm_row(len: Nat, +x: Nat) -> List<&2, Nat>:
  match len:
    case 0n:
      Nil{}
    case 1n+rest:
      x <> idm_row(rest, 1n+x)

def idm_mask_pick(want: Bool, value: Bool) -> Bool:
  match want:
    case True{}:
      value
    case False{}:
      Bool.not(value)

def idm_rows.cons(keep: Bool, +row: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match keep:
    case True{}:
      List.append(&2, Nat, row, rest)
    case False{}:
      rest

# Q: ids = torch.arange(vocab, dtype = torch.int64).view(-1, 128)     (row b = ids 128 b .. 128 b + 127)
# Q: mask = torch.zeros(vocab // 128, dtype = torch.bool)
# Q: mask[torch.tensor(self.kept_blocks)] = True                     (mask[b] = b is a kept block)
# ids[mask] (want) / ids[~mask] (not want), flattened: the rows b, b + 1, ..., b + cnt - 1 selected, in order.
def idm_rows(cnt: Nat, +want: Bool, +kept: List<&2, Nat>, +b: Nat) -> List<&2, Nat>:
  match cnt:
    case 0n:
      Nil{}
    case 1n+rest:
      idm_rows.cons(idm_mask_pick(want, Spec.ids_member(kept, b)), idm_row(128n, Nat.mul(b, 128n)),
        idm_rows(rest, want, kept, 1n+b))

# Q: self.id_map = torch.cat((ids[mask].flatten(), ids[~mask].flatten())).to(device = dev, dtype = torch.int32)
# for a vocabulary of vocab = 128 nb ids (Q checks vocab % 128 == 0).
def idm_id_map(+kept: List<&2, Nat>, +nb: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, idm_rows(nb, True{}, kept, 0n), idm_rows(nb, False{}, kept, 0n))

# Q: self.keep_cols = vocab if kept is None else 128 * len(kept)      (kept = set(kb))
def idm_keep_cols(+kept: List<&2, Nat>) -> Nat:
  Nat.mul(128n, idm_card(kept))

# ==== the kernel's ranking (D: dflash2_q4_head_topk_kernel) ====

# D: return av > bv || (av == bv && ai < bi);
def idm_better(+a: Spec.IdmCand, +b: Spec.IdmCand) -> Bool:
  Bool.or(Nat.is_gt(Spec.ids_v(a), Spec.ids_v(b)),
    Bool.and(Nat.is_eq(Spec.ids_v(a), Spec.ids_v(b)), Nat.is_lt(Spec.ids_t(a), Spec.ids_t(b))))

def idm_ins.sel(go: Bool, +c: Spec.IdmCand, +y: Spec.IdmCand, +rest: List<&2, Spec.IdmCand>,
    deeper: List<&2, Spec.IdmCand>) -> List<&2, Spec.IdmCand>:
  match go:
    case True{}:
      c <> y <> rest
    case False{}:
      y <> deeper

# A candidate entering a running list kept best-first by better().
def idm_ins(ys: List<&2, Spec.IdmCand>, +c: Spec.IdmCand) -> List<&2, Spec.IdmCand>:
  match ys:
    case Nil{}:
      c <> Nil{}
    case +y <> +rest:
      idm_ins.sel(idm_better(c, y), c, y, rest, idm_ins(rest, c))

# The running top-k list over the columns (the contract of the kernel's rv / ri lists and merges): every candidate
# enters the list, which is cut back to its best k.
def idm_topk(+k: Nat, xs: List<&2, Spec.IdmCand>) -> List<&2, Spec.IdmCand>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      List.take(&2, Spec.IdmCand, idm_ins(idm_topk(k, rest), x), k)

# Per-token values of one row (the head's softcap(scale * logit) for every token): a binary tree read along the
# token id's bits, least significant first. Values are Nat under the kernel's order (larger is better).
type IdmVals is Data:
  IdmLeaf{v: Nat}
  IdmNode{lo: IdmVals, hi: IdmVals}

def idm_value.go(vals: IdmVals, bit: Nat, +q: Nat) -> Nat:
  match vals:
    case IdmLeaf{v}:
      v
    case IdmNode{lo, hi}:
      match bit:
        case 0n:
          idm_value.go(lo, Nat.mod(q, 2n), Nat.div(q, 2n))
        case 1n+b:
          idm_value.go(hi, Nat.mod(q, 2n), Nat.div(q, 2n))

def idm_value(vals: IdmVals, +t: Nat) -> Nat:
  idm_value.go(vals, Nat.mod(t, 2n), Nat.div(t, 2n))

# D: ti[e] = id < vocab ? (id_map ? id_map[id] : id) : INT_MAX;   for the columns id = 0 .. vocab - 1 in order
# (the host checks id_map.size(0) == vocab, so column id carries token id_map[id], or id without a map).
def idm_tokens(im: Maybe<&2, List<&2, Nat>>, +vocab: Nat) -> List<&2, Nat>:
  match im:
    case None{}:
      idm_row(vocab, 0n)
    case Some{m}:
      m

# D: tv[e] = value of the column, ti[e] = its token: column id holds the head column of token ti (Q packs token
# id_map[id]'s weights at column id), so its value is that token's value.
def idm_cols(+vals: IdmVals, toks: List<&2, Nat>) -> List<&2, Spec.IdmCand>:
  match toks:
    case Nil{}:
      Nil{}
    case +t <> rest:
      Spec.IdmCand{idm_value(vals, t), t} <> idm_cols(vals, rest)

# One call of dflash2_q4_head_topk over `vocab` columns: the top-k by better().
def idm_call(+k: Nat, +vals: IdmVals, im: Maybe<&2, List<&2, Nat>>, +vocab: Nat) -> List<&2, Spec.IdmCand>:
  idm_topk(k, idm_cols(vals, idm_tokens(im, vocab)))

def idm_slice(full: Bool, +m: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  match full:
    case True{}:
      m
    case False{}:
      List.take(&2, Nat, m, n)

def idm_ncols(pruned: Bool, +kept: List<&2, Nat>, +nb: Nat) -> Nat:
  match pruned:
    case True{}:
      idm_keep_cols(kept)
    case False{}:
      Nat.mul(nb, 128n)

# Q (Q4DraftHead.topk on the kept-first copy, vocab = 128 nb):
# Q:   n = self.keep_cols if pruned else self.vocab
# Q:   if n != self.vocab: wq, sc, im = wq[: n // 16], sc[: n // 16], im[:n]
# Q:   ext.dflash2_q4_head_topk(xr, wq, sc, n, ..., im)
def idm_head_call(+k: Nat, +vals: IdmVals, +kept: List<&2, Nat>, +nb: Nat, +pruned: Bool) -> List<&2, Spec.IdmCand>:
  +n = idm_ncols(pruned, kept, nb)
  +im = idm_slice(Nat.is_eq(n, Nat.mul(nb, 128n)), idm_id_map(kept, nb), n)
  idm_call(k, vals, Some{im}, n)

# ==== switch-back policy (S: PrunedHeadPolicy) ====

# An anchor token: a token id t >= 0, or the negative integer -(m + 1).
type IdmTok is Data:
  IdmPos{t: Nat}
  IdmNeg{m: Nat}

# One call on the policy: observe_anchor(token) or reset() (DFlash2Model.begin_job at each job's prefill).
type IdmEv is Data:
  IdmObs{tok: IdmTok}
  IdmReset{}

# S (__init__): self.recent = []; self.hold = 0; self.use_pruned = True
def idm_init() -> Spec.IdmPol:
  Spec.IdmPol{Nil{}, 0n, True{}}

# S (reset): self.recent = []; self.hold = 0; self.use_pruned = True
def idm_reset(st: Spec.IdmPol) -> Spec.IdmPol:
  Spec.IdmPol{Nil{}, 0n, True{}}

# S: b = token // DRAFT_HEAD_BLOCK; flag = 0 <= b < len(self.kept) and not self.kept[b]
# (len(self.kept) = vocab // 128 = nb; kept[b] = b is a kept block; a negative token has b < 0)
def idm_oos(+kept: List<&2, Nat>, +nb: Nat, tok: IdmTok) -> Bool:
  match tok:
    case IdmPos{t}:
      +b = Nat.div(t, idm_block())
      Bool.and(Nat.is_lt(b, nb), Bool.not(Spec.ids_member(kept, b)))
    case IdmNeg{m}:
      False{}

# S: if sum(self.recent) >= FALLBACK_TRIGGER: self.hold, self.use_pruned, self.recent = FALLBACK_HOLD, False, []
# S: else: self.use_pruned = True
def idm_fire(fire: Bool, +recent: List<&2, Bool>) -> Spec.IdmPol:
  match fire:
    case True{}:
      Spec.IdmPol{Nil{}, idm_hold_len(), False{}}
    case False{}:
      Spec.IdmPol{recent, 0n, True{}}

# S: self.recent.append(flag); del self.recent[:-FALLBACK_WINDOW]   (newest first: prepend, keep the first 32)
def idm_push(flag: Bool, recent: List<&2, Bool>) -> List<&2, Bool>:
  List.take(&2, Bool, flag <> recent, idm_window())

def idm_window_step(+recent: List<&2, Bool>) -> Spec.IdmPol:
  idm_fire(Nat.is_le(idm_trigger(), Spec.ids_trues(recent)), recent)

# S: observe_anchor(token):
# S:   if not self.adaptive: self.use_pruned = True
# S:   elif self.hold > 0: self.hold -= 1; self.use_pruned = self.hold == 0
# S:   else: (append the flag, trim, fire or not)
def idm_observe(adaptive: Bool, +kept: List<&2, Nat>, +nb: Nat, st: Spec.IdmPol, tok: IdmTok) -> Spec.IdmPol:
  match adaptive:
    case False{}:
      match st:
        case Spec.IdmPol{recent, hold, use}:
          Spec.IdmPol{recent, hold, True{}}
    case True{}:
      match st:
        case Spec.IdmPol{recent, hold, use}:
          match hold:
            case 1n+h:
              +left = h
              Spec.IdmPol{recent, left, Spec.ids_is_zero(left)}
            case 0n:
              idm_window_step(idm_push(idm_oos(kept, nb, tok), recent))

def idm_event(+adaptive: Bool, +kept: List<&2, Nat>, +nb: Nat, st: Spec.IdmPol, ev: IdmEv) -> Spec.IdmPol:
  match ev:
    case IdmObs{tok}:
      idm_observe(adaptive, kept, nb, st, tok)
    case IdmReset{}:
      idm_reset(st)

# The state after a sequence of calls, from st.
def idm_run(evs: List<&2, IdmEv>, +adaptive: Bool, +kept: List<&2, Nat>, +nb: Nat, st: Spec.IdmPol) -> Spec.IdmPol:
  match evs:
    case Nil{}:
      st
    case ev <> rest:
      idm_run(rest, adaptive, kept, nb, idm_event(adaptive, kept, nb, st, ev))

def idm_use(st: Spec.IdmPol) -> Bool:
  match st:
    case Spec.IdmPol{recent, hold, use}:
      use

def idm_hold(st: Spec.IdmPol) -> Nat:
  match st:
    case Spec.IdmPol{recent, hold, use}:
      hold

def idm_recent(st: Spec.IdmPol) -> List<&2, Bool>:
  match st:
    case Spec.IdmPol{recent, hold, use}:
      recent

# The head chosen in each round of an anchor sequence (True = pruned), from st.
def idm_uses(toks: List<&2, IdmTok>, +adaptive: Bool, +kept: List<&2, Nat>, +nb: Nat, st: Spec.IdmPol) -> List<&2, Bool>:
  match toks:
    case Nil{}:
      Nil{}
    case tok <> rest:
      +next = idm_observe(adaptive, kept, nb, st, tok)
      idm_use(next) <> idm_uses(rest, adaptive, kept, nb, next)

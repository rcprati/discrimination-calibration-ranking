"""
Running example of the paper: n = 4 examples, m = 3 labels (A, B, C).

Computes every number quoted in the running-example boxes and in the appendix,
exactly (fractions) where the quantity is rational and to six decimals for the
nDCG family (which involves log2 3). Writes data/running_example.json and prints
a readable summary.

Conventions: scores are pairwise distinct within every row and column, so ranks
are unambiguous; hard predictions use the threshold 0.5 (no score equals 0.5);
w(r) = 1/log2(r+1); AUC concordance gives half credit to ties (none occur).
"""
import json
import math
import os
from fractions import Fraction as F

LABELS = ["A", "B", "C"]
Y = [[1, 1, 0], [1, 0, 1], [0, 1, 0], [0, 1, 0]]
P = [[F(7, 10), F(6, 10), F(1, 10)],
     [F(6, 10), F(1, 10), F(4, 10)],
     [F(8, 10), F(2, 10), F(7, 10)],
     [F(4, 10), F(3, 10), F(2, 10)]]
# Companion predictor with the same Brier score but different rankings.
P_SAME_BRIER = [[F(8, 10), F(7, 10), F(2, 10)],
                [F(9, 10), F(4, 10), F(1, 10)],
                [F(4, 10), F(2, 10), F(3, 10)],
                [F(2, 10), F(1, 10), F(6, 10)]]
THRESHOLD = F(1, 2)
M_LABELS = len(Y[0])


def w(r):
    return 1.0 / math.log2(r + 1)


def col(M, j):
    return [row[j] for row in M]


def row_rank(Pm, i, j):
    return 1 + sum(Pm[i][jj] > Pm[i][j] for jj in range(len(Pm[i])))


def conc(Ym, Pm, i, j):
    neg = [ii for ii in range(len(Ym)) if Ym[ii][j] == 0]
    s = sum(F(1) if Pm[i][j] > Pm[ii][j] else F(1, 2) if Pm[i][j] == Pm[ii][j] else F(0) for ii in neg)
    return s / len(neg)


def confusion(Ym, Pm):
    n, m = len(Ym), len(Ym[0])
    H = [[1 if Pm[i][j] > THRESHOLD else 0 for j in range(m)] for i in range(n)]
    per = []
    for j in range(m):
        tp = sum(H[i][j] * Ym[i][j] for i in range(n))
        fp = sum(H[i][j] * (1 - Ym[i][j]) for i in range(n))
        fn = sum((1 - H[i][j]) * Ym[i][j] for i in range(n))
        tn = sum((1 - H[i][j]) * (1 - Ym[i][j]) for i in range(n))
        per.append((tp, fp, fn, tn))
    tot = tuple(sum(c[k] for c in per) for k in range(4))
    prec = [F(c[0], c[0] + c[1]) for c in per]
    rec = [F(c[0], c[0] + c[2]) for c in per]
    return H, per, tot, prec, rec


def brier(Ym, Pm):
    n, m = len(Ym), len(Ym[0])
    cells = [[(Ym[i][j] - Pm[i][j]) ** 2 for j in range(m)] for i in range(n)]
    bs_class = [sum(col(cells, j)) / n for j in range(m)]
    bs_ex = [sum(cells[i]) / m for i in range(n)]
    micro = sum(map(sum, cells)) / (n * m)
    alpha = [sum(cells[i][j] for i in range(n) if Ym[i][j]) / sum(col(Ym, j)) for j in range(m)]
    beta = [sum(cells[i][j] for i in range(n) if not Ym[i][j]) / (n - sum(col(Ym, j))) for j in range(m)]
    return cells, micro, bs_class, bs_ex, alpha, beta


def ranking(Ym, Pm):
    n, m = len(Ym), len(Ym[0])
    R = [[row_rank(Pm, i, j) for j in range(m)] for i in range(n)]
    D = [[Ym[i][j] * w(R[i][j]) for j in range(m)] for i in range(n)]
    k = [sum(Ym[i]) for i in range(n)]
    npos = [sum(col(Ym, j)) for j in range(m)]
    idcg = [sum(w(r) for r in range(1, k[i] + 1)) for i in range(n)]
    dcg = {"micro": sum(map(sum, D)) / (n * m),
           "class_mean": sum(sum(col(D, j)) / n for j in range(m)) / m,
           "exemplar_mean": sum(sum(D[i]) / m for i in range(n)) / n}
    ndcg_class = [sum(col(D, j)) / (npos[j] * w(1)) for j in range(m)]
    ndcg_ex = [sum(D[i]) / idcg[i] for i in range(n)]
    ndcg = {"micro": sum(map(sum, D)) / sum(idcg), "class": ndcg_class,
            "class_mean": sum(ndcg_class) / m, "exemplar": ndcg_ex, "exemplar_mean": sum(ndcg_ex) / n}
    A = [[conc(Ym, Pm, i, j) if Ym[i][j] else F(0) for j in range(m)] for i in range(n)]
    auc = [sum(col(A, j)) / npos[j] for j in range(m)]
    auc_ex = [sum(A[i]) / k[i] for i in range(n)]
    aucs = {"class": auc, "macro": sum(auc) / m,
            "micro": sum(npos[j] * auc[j] for j in range(m)) / sum(npos),
            "exemplar": auc_ex, "exemplar_mean": sum(auc_ex) / n,
            "raw": sum(map(sum, A)) / (n * m)}
    pos = [Pm[i][j] for i in range(n) for j in range(m) if Ym[i][j]]
    neg = [Pm[i][j] for i in range(n) for j in range(m) if not Ym[i][j]]
    pooled = sum(F(1) if a > b else F(1, 2) if a == b else F(0) for a in pos for b in neg) / (len(pos) * len(neg))
    top1 = [max(range(m), key=lambda j: Pm[i][j]) for i in range(n)]
    p_at_1 = F(sum(Ym[i][top1[i]] for i in range(n)), n)
    return R, D, A, dcg, ndcg, aucs, pooled, top1, p_at_1


def skew_per_class(j, factor):
    """Per-class convention: scale the positives of class j by `factor`, other classes unchanged."""
    n, m = len(Y), len(Y[0])
    _, per, _, _, _ = confusion(Y, P)
    tp, fp, fn, tn = per[j]
    _, _, _, _, alpha, beta = brier(Y, P)
    npos = [sum(col(Y, jj)) for jj in range(m)]
    _, _, _, _, _, aucs, _, _, _ = ranking(Y, P)
    auc = aucs["class"]
    npos2 = list(npos)
    npos2[j] *= factor
    pi = F(npos[j], n)
    pi2 = F(npos2[j], npos2[j] + (n - npos[j]))
    return {
        "pi": (pi, pi2),
        "precision": (F(tp, tp + fp), F(factor * tp, factor * tp + fp)),
        "recall": (F(tp, tp + fn), F(tp, tp + fn)),
        "specificity": (F(tn, tn + fp), F(tn, tn + fp)),
        "BS_j": (pi * alpha[j] + (1 - pi) * beta[j], pi2 * alpha[j] + (1 - pi2) * beta[j]),
        "alpha_beta": ((alpha[j], beta[j]), (alpha[j], beta[j])),
        "AUC_j": (auc[j], auc[j]),
        "micro_AUC": (sum(npos[jj] * auc[jj] for jj in range(m)) / sum(npos),
                      sum(npos2[jj] * auc[jj] for jj in range(m)) / sum(npos2)),
        "macro_AUC": (sum(auc) / m, sum(auc) / m),
    }


def replicate_rows(rows):
    Y2 = Y + [Y[i] for i in rows]
    P2 = P + [P[i] for i in rows]
    return Y2, P2


def fmt(x):
    if isinstance(x, F):
        return str(x) if x.denominator != 1 else str(x.numerator)
    if isinstance(x, float):
        return round(x, 6)
    if isinstance(x, (list, tuple)):
        return [fmt(v) for v in x]
    if isinstance(x, dict):
        return {k: fmt(v) for k, v in x.items()}
    return x


def main():
    n, m = len(Y), len(Y[0])
    out = {}
    H, per, tot, prec, rec = confusion(Y, P)
    out["hard_predictions"] = H
    out["confusion_per_class_tp_fp_fn_tn"] = per
    out["confusion_total"] = tot
    out["precision"] = {"class": prec, "macro": sum(prec) / m, "micro": F(tot[0], tot[0] + tot[1])}
    out["recall"] = {"class": rec, "macro": sum(rec) / m, "micro": F(tot[0], tot[0] + tot[2])}
    out["soft_TP_product_tnorm"] = [[Y[i][j] * P[i][j] for j in range(m)] for i in range(n)]
    cells, bmicro, bclass, bex, alpha, beta = brier(Y, P)
    out["brier"] = {"cells": cells, "micro": bmicro, "class": bclass, "macro": sum(bclass) / m,
                    "exemplar": bex, "exemplar_mean": sum(bex) / n, "alpha": alpha, "beta": beta}
    R, D, A, dcg, ndcg, aucs, pooled, top1, p1 = ranking(Y, P)
    out["row_ranks"] = R
    out["dcg_cells"] = D
    out["dcg_raw"] = dcg
    out["ndcg"] = ndcg
    out["auc_cells"] = A
    out["auc"] = aucs
    out["pooled_roc_auc"] = pooled
    out["top1_labels"] = [LABELS[j] for j in top1]
    out["precision_at_1"] = p1
    # companion 1: squared scores (same rankings everywhere)
    Psq = [[P[i][j] ** 2 for j in range(m)] for i in range(n)]
    _, _, _, _, _, aucs_sq, _, _, _ = ranking(Y, Psq)
    out["companion_squared_scores"] = {"brier": brier(Y, Psq)[1], "auc_class": aucs_sq["class"],
                                       "ndcg_class": ranking(Y, Psq)[4]["class"]}
    # companion 2: same Brier score, different rankings
    _, _, _, _, _, aucs2, _, _, _ = ranking(Y, P_SAME_BRIER)
    out["companion_same_brier"] = {"P": P_SAME_BRIER, "brier": brier(Y, P_SAME_BRIER)[1],
                                   "auc_class": aucs2["class"], "auc_macro": aucs2["macro"]}
    # skew: per-class convention, positives of A doubled
    out["skew_per_class_A_x2"] = skew_per_class(0, 2)
    # skew: whole rows where A is relevant duplicated
    Y2, P2 = replicate_rows([0, 1])
    _, _, _, _, ndcg2, aucs2r, _, _, _ = ranking(Y2, P2)
    out["skew_rows_of_A_duplicated"] = {"ndcg_class": ndcg2["class"], "ndcg_micro": ndcg2["micro"],
                                        "ndcg_exemplar_mean": ndcg2["exemplar_mean"],
                                        "auc_class": aucs2r["class"], "auc_micro": aucs2r["micro"]}
    os.makedirs(os.path.join(os.path.dirname(__file__), "data"), exist_ok=True)
    path = os.path.join(os.path.dirname(__file__), "data", "running_example.json")
    with open(path, "w") as fh:
        json.dump(fmt(out), fh, indent=1)
    print(json.dumps(fmt(out), indent=1))


if __name__ == "__main__":
    main()

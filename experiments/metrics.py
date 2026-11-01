"""
metrics.py — Implementation of the three cell-operator frameworks.

Reference
---------
"A Generalised Confusion Matrix Framework: Calibration, Ranking, and
Unification", Ronaldo C. Prati (extending prati2026unified).

Frameworks
----------
Discrimination  : coincidence (t-norm) operators
Calibration     : deviation (φ(y-ŷ)) operators
Ranking         : positional (Y · w(rank)) operators

Each function takes numpy arrays:
    Y     : np.ndarray, shape (n, m), binary true labels  ∈ {0, 1}
    Yhat  : np.ndarray, shape (n, m), predicted probabilities ∈ [0, 1]
    Yhard : np.ndarray, shape (n, m), thresholded predictions ∈ {0, 1}
"""

import numpy as np
from sklearn.metrics import roc_auc_score, f1_score


# ── Internal helpers ──────────────────────────────────────────────────────────

def _rank_matrix(Yhat: np.ndarray) -> np.ndarray:
    """
    Row-rank matrix: R[i, j] = rank of label j for example i
    (rank 1 = highest predicted score).
    """
    n, m = Yhat.shape
    order = np.argsort(-Yhat, axis=1)          # descending sort, per row
    R = np.empty_like(order)
    R[np.arange(n)[:, None], order] = np.arange(1, m + 1)[None, :]
    return R


def _col_rank_matrix(Yhat: np.ndarray) -> np.ndarray:
    """
    Column-rank matrix: R[i, j] = rank of example i for class j
    (rank 1 = highest predicted score for that class).
    Used for AUC's column-dependent operator.
    """
    n, m = Yhat.shape
    order = np.argsort(-Yhat, axis=0)          # descending sort, per column
    R = np.empty_like(order)
    R[order, np.arange(m)[None, :]] = np.arange(1, n + 1)[:, None]
    return R


def _log_weight(r: np.ndarray) -> np.ndarray:
    """Logarithmic positional weight: w(r) = 1 / log2(r + 1)."""
    return 1.0 / np.log2(np.asarray(r, dtype=float) + 1.0)


# ── Discrimination Framework (coincidence / t-norm operators) ─────────────────

def f1_micro(Y: np.ndarray, Yhard: np.ndarray) -> float:
    """Micro-F1 on hard (thresholded) predictions."""
    return float(f1_score(Y, Yhard, average="micro", zero_division=0))


def f1_macro(Y: np.ndarray, Yhard: np.ndarray) -> float:
    """Macro-F1 on hard (thresholded) predictions."""
    return float(f1_score(Y, Yhard, average="macro", zero_division=0))


def hamming_loss(Y: np.ndarray, Yhard: np.ndarray) -> float:
    """Hamming loss = micro Brier score for hard predictions (Theorem bridge)."""
    return float(np.mean(Y != Yhard))


# ── Calibration Framework (deviation / squared-error operators) ───────────────

def brier_micro(Y: np.ndarray, Yhat: np.ndarray) -> float:
    """
    Micro Brier score = (1/nm) Σ_{i,j} (Y_ij − Ŷ_ij)².
    Theorem: equals brier_macro = brier_exemplar (collapse theorem).
    """
    return float(np.mean((Y - Yhat) ** 2))


def brier_macro(Y: np.ndarray, Yhat: np.ndarray) -> float:
    """Macro (per-class) Brier score = (1/m) Σ_j [(1/n) Σ_i (Y_ij − Ŷ_ij)²]."""
    return float(np.mean(np.mean((Y - Yhat) ** 2, axis=0)))


def brier_exemplar(Y: np.ndarray, Yhat: np.ndarray) -> float:
    """Exemplar Brier score = (1/n) Σ_i [(1/m) Σ_j (Y_ij − Ŷ_ij)²]."""
    return float(np.mean(np.mean((Y - Yhat) ** 2, axis=1)))


def brier_class(Y: np.ndarray, Yhat: np.ndarray) -> np.ndarray:
    """Per-class Brier scores BS_j, shape (m,)."""
    return np.mean((Y - Yhat) ** 2, axis=0)


def mae_class(Y: np.ndarray, Yhat: np.ndarray) -> np.ndarray:
    """
    Per-class mean absolute error (the phi(t)=|t| deviation operator, Remark
    rem:mae_nonproper): a member of the Calibration Framework's structural family
    (micro=macro=exemplar collapse still holds) but NOT a proper scoring rule.
    """
    return np.mean(np.abs(Y - Yhat), axis=0)


def murphy_decomposition(
    Y: np.ndarray, Yhat: np.ndarray, n_bins: int = 10
):
    """
    Per-class Murphy decomposition of the BINNED (discretised) predictor:
    BS_hat_j = UNC_j − RES_j + REL_j, exactly (Proposition prop:murphy_binned).

        UNC_j = π_j (1 − π_j)                              (climatological variance)
        RES_j = Σ_k (n_k/n)(o_k − π_j)²                   (resolution)
        REL_j = Σ_k (n_k/n)(o_k − p̄_k)²                  (reliability / calibration)

    Uses equal-width bins on [0, 1].

    NOTE: the returned BS is the Brier score of the predictor obtained by
    replacing each Yhat_ij with its own bin mean p̄_k -- it equals UNC-RES+REL
    exactly by construction, but is generally NOT equal to brier_class(Y, Yhat)
    (the true Brier score of the original, continuous Yhat). The gap between
    the two is not simply a "within-bin variance" residual and is not
    sign-definite (Remark rem:binning_gap); it shrinks as n_bins grows. Use
    brier_class(Y, Yhat) for the true per-class Brier score.

    Parameters
    ----------
    Y      : (n, m) binary true labels
    Yhat   : (n, m) predicted probabilities
    n_bins : number of equal-width calibration bins

    Returns
    -------
    BS, UNC, RES, REL : np.ndarray of shape (m,) -- BS is the BINNED Brier
                         score (see NOTE above), not brier_class(Y, Yhat)
    """
    n, m = Y.shape
    UNC = np.zeros(m)
    RES = np.zeros(m)
    REL = np.zeros(m)

    edges = np.linspace(0.0, 1.0 + 1e-9, n_bins + 1)

    for j in range(m):
        y_j = Y[:, j].astype(float)
        p_j = np.clip(Yhat[:, j], 0.0, 1.0)
        pi_j = y_j.mean()
        UNC[j] = pi_j * (1.0 - pi_j)

        bin_idx = np.clip(np.digitize(p_j, edges) - 1, 0, n_bins - 1)
        for k in range(n_bins):
            mask = bin_idx == k
            n_k = int(mask.sum())
            if n_k == 0:
                continue
            o_k = y_j[mask].mean()     # observed frequency in bin k
            p_k = p_j[mask].mean()     # mean predicted probability in bin k
            w = n_k / n
            RES[j] += w * (o_k - pi_j) ** 2
            REL[j] += w * (o_k - p_k) ** 2

    BS = UNC - RES + REL
    return BS, UNC, RES, REL


def brier_exemplar_decomposition(Y: np.ndarray, Yhat: np.ndarray):
    """
    Per-exemplar Brier decomposition (row-axis analogue of Murphy).

    BS_i^ex = (k_i/m) * alpha_i  +  ((m - k_i)/m) * beta_i

    where k_i = sum_j Y_ij (label cardinality of example i), and

        alpha_i = mean_{j: Y_ij=1} (1 - Yhat_ij)^2   miss-calibration on positives
        beta_i  = mean_{j: Y_ij=0}      Yhat_ij^2    false-alarm calibration

    alpha_i is nan when k_i = 0 (no positive labels).
    beta_i  is nan when k_i = m (all labels positive).

    Returns
    -------
    BS_ex : np.ndarray (n,)   per-exemplar Brier score
    alpha : np.ndarray (n,)   miss-calibration component (nan if k_i=0)
    beta  : np.ndarray (n,)   false-alarm component      (nan if k_i=m)
    k     : np.ndarray (n,)   label cardinality
    """
    n, m = Y.shape
    k     = Y.sum(axis=1).astype(int)
    BS_ex = np.mean((Y - Yhat) ** 2, axis=1)
    alpha = np.full(n, np.nan)
    beta  = np.full(n, np.nan)

    for i in range(n):
        pos = Y[i] == 1
        neg = Y[i] == 0
        if pos.any():
            alpha[i] = np.mean((1.0 - Yhat[i, pos]) ** 2)
        if neg.any():
            beta[i]  = np.mean(Yhat[i, neg] ** 2)

    return BS_ex, alpha, beta, k


# ── Ranking Framework (positional operators) ──────────────────────────────────

def _dcg_cell_matrix(Y: np.ndarray, Yhat: np.ndarray) -> np.ndarray:
    """
    DCG cell matrix: D[i,j] = Y[i,j] · w(rank_i(j)).
    This is the fundamental cell-level object of the Ranking Framework.
    """
    R = _rank_matrix(Yhat)
    W = _log_weight(R)
    return Y.astype(float) * W


# — Row-dependent family (nDCG) ————————————————————————————————————————————

def dcg_micro(Y: np.ndarray, Yhat: np.ndarray) -> float:
    """Micro DCG = (1/nm) Σ_{i,j} Y_ij · w(rank_i(j))."""
    return float(np.mean(_dcg_cell_matrix(Y, Yhat)))


def dcg_class(Y: np.ndarray, Yhat: np.ndarray) -> np.ndarray:
    """Per-class DCG_j^class = (1/n) Σ_i Y_ij · w(rank_i(j)), shape (m,)."""
    return np.mean(_dcg_cell_matrix(Y, Yhat), axis=0)


def dcg_exemplar(Y: np.ndarray, Yhat: np.ndarray) -> np.ndarray:
    """Per-example DCG_i^ex = (1/m) Σ_j Y_ij · w(rank_i(j)), shape (n,)."""
    return np.mean(_dcg_cell_matrix(Y, Yhat), axis=1)


def ndcg_class(Y: np.ndarray, Yhat: np.ndarray) -> np.ndarray:
    """
    Per-class nDCG_j^class = DCG_j^class / (π_j · w(1)).
    Skew-invariant ranking measure (Proposition prop:ndcg_class_skew).
    """
    pi = Y.mean(axis=0)
    w1 = _log_weight(np.array([1]))[0]          # w(1) = 1/log2(2) = 1.0
    IDCG = pi * w1
    DCG = dcg_class(Y, Yhat)
    return np.where(IDCG > 0, DCG / IDCG, 0.0)


def ndcg_exemplar(Y: np.ndarray, Yhat: np.ndarray) -> np.ndarray:
    """
    Per-example nDCG_i = m · DCG_i^ex / IDCG_i,
    where IDCG_i = Σ_{r=1}^{k_i} w(r) and k_i = |{j : Y_ij=1}|.
    """
    n, m = Y.shape
    k = Y.sum(axis=1).astype(int)
    IDCG_i = np.array([
        float(np.sum(_log_weight(np.arange(1, ki + 1)))) if ki > 0 else 0.0
        for ki in k
    ])
    DCG_ex = dcg_exemplar(Y, Yhat)              # shape (n,), mean over m labels
    # nDCG_i = m * DCG_ex[i] / IDCG_i  (undo the 1/m in dcg_exemplar)
    return np.where(IDCG_i > 0, m * DCG_ex / IDCG_i, 0.0)


def ndcg_micro(Y: np.ndarray, Yhat: np.ndarray) -> float:
    """
    Micro nDCG = DCG_micro / IDCḠ, where IDCḠ = mean_i(IDCG_i) / m.
    Not skew-invariant.
    """
    n, m = Y.shape
    k = Y.sum(axis=1).astype(int)
    IDCG_i = np.array([
        float(np.sum(_log_weight(np.arange(1, ki + 1)))) if ki > 0 else 0.0
        for ki in k
    ])
    IDCG_bar = IDCG_i.mean() / m
    dcg = dcg_micro(Y, Yhat)
    return float(dcg / IDCG_bar) if IDCG_bar > 0 else 0.0


# — Column-dependent family (AUC) ────────────────────────────────────────────

def auc_class(Y: np.ndarray, Yhat: np.ndarray) -> np.ndarray:
    """
    Per-class AUC_j = P(score of positive > score of negative).
    Skew-invariant ranking measure (Proposition prop:auc_skew).
    Returns nan for classes with a single label value in Y.
    """
    m = Y.shape[1]
    AUC = np.full(m, np.nan)
    for j in range(m):
        if Y[:, j].sum() > 0 and (1 - Y[:, j]).sum() > 0:
            AUC[j] = float(roc_auc_score(Y[:, j], Yhat[:, j]))
    return AUC


def auc_macro(Y: np.ndarray, Yhat: np.ndarray) -> float:
    """Macro AUC = mean of per-class AUC_j (nan-safe)."""
    return float(np.nanmean(auc_class(Y, Yhat)))


def auc_micro(Y: np.ndarray, Yhat: np.ndarray) -> float:
    """
    Micro AUC = prevalence-weighted average of per-class AUCs (Equation
    eq:auc_micro):  AUC^micro = Σ_j n_j^+ AUC_j / Σ_j n_j^+.
    Not skew-invariant: the weights n_j^+ change under prevalence rescaling.

    NOTE: this is deliberately NOT sklearn's roc_auc_score(..., average=
    "micro"), which pools scores across *all* classes into one global
    ranking (comparing a positive cell of one class against a negative cell
    of another). That pooled ranking is a different statistic from
    Σ_1(A)/Σ_1(Y) (Equation eq:auc_micro). The two can differ when the
    classes' score distributions are on different scales (typical under
    binary relevance, one sub-classifier per class), but a difference of
    scale neither forces nor is required for a gap (Remark 80).
    """
    auc_j = auc_class(Y, Yhat)
    n_pos = Y.sum(axis=0)
    valid = ~np.isnan(auc_j)
    if not valid.any() or n_pos[valid].sum() == 0:
        return float("nan")
    return float(np.sum(n_pos[valid] * auc_j[valid]) / np.sum(n_pos[valid]))


def mean_rank_class(Y: np.ndarray, Yhat: np.ndarray) -> np.ndarray:
    """
    Raw column-rank operator M_j: the mean descending column rank
    (rank 1 = highest score) of the positive examples of class j.

    This is the fixed-weight column positional operator with weight
    v(r) = r, *before* normalisation. It is skew-SENSITIVE: adding
    negatives interleaves them among the positives and shifts the ranks.
    AUC_j is its affine Wilcoxon-Mann-Whitney normalisation
    (Proposition prop:auc_meanrank):
        AUC_j = (n - (n_j^+ - 1)/2 - M_j) / n_j^-.
    Returns nan for classes lacking both positives and negatives.
    """
    R = _col_rank_matrix(Yhat)            # R[i,j] = descending column rank
    m = Y.shape[1]
    M = np.full(m, np.nan)
    for j in range(m):
        pos = Y[:, j] == 1
        if pos.sum() > 0 and (~pos).sum() > 0:
            M[j] = float(R[pos, j].mean())
    return M


def auc_from_mean_rank(M_j: float, n: int, n_pos: int) -> float:
    """
    Recover AUC_j from the mean positive rank via the WMW affine map
    (Proposition prop:auc_meanrank). Exact for distinct scores.
    """
    n_neg = n - n_pos
    return (n - 0.5 * (n_pos - 1) - M_j) / n_neg

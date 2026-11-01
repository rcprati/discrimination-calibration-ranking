"""
run_experiments.py — Empirical illustrations for the paper.

"A Generalised Confusion Matrix Framework: Calibration, Ranking, and Unification"
Ronaldo C. Prati, UFABC

Datasets
--------
Experiments 1–3 use the Emotions dataset (593 examples, 72 features, 6 labels).
Experiment  4   uses the Yeast    dataset (2417 examples, 103 features, 14 labels).
Both are downloaded as ARFF files from OpenML and cached in experiments/data/.

Experiments
-----------
1. Classifier ranking disagreement across the three frameworks.
   Shows that F1, Brier, nDCG, and AUC induce different orderings
   over the same set of classifiers on the same dataset.

2. Aggregation collapse (Calibration) vs split (Ranking).
   Verifies micro-BS = macro-BS = exemplar-BS (collapse theorem)
   and micro-nDCG ≠ macro-nDCG ≠ exemplar-nDCG.

3. Skew-invariance under class-prevalence variation.
   Varies the prevalence of one class by subsampling; shows
   AUC_j and nDCG_j^class are stable, micro-AUC and macro-BS are not.

4. Per-class Murphy decomposition heatmap.
   Plots REL_j, RES_j, UNC_j for each classifier × class pair,
   illustrating BS_j = UNC_j − RES_j + REL_j.

Usage
-----
    pip install scikit-multilearn
    cd experiments/
    python run_experiments.py

Figures are saved to experiments/figs/ as PDF files ready for LaTeX inclusion.
The numbers behind each figure are saved to experiments/data/*.csv.

Dependencies
------------
    pip install numpy scipy scikit-learn matplotlib pandas
    (No extra dataset library needed — ARFF files are fetched from OpenML.)
"""

import os
import sys
import warnings

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import pandas as pd
from scipy.stats import kendalltau

from sklearn.model_selection import train_test_split
from sklearn.multioutput import MultiOutputClassifier
from sklearn.linear_model import LogisticRegression
from sklearn.ensemble import RandomForestClassifier, GradientBoostingClassifier
from sklearn.neural_network import MLPClassifier
from sklearn.calibration import CalibratedClassifierCV
from sklearn.preprocessing import MinMaxScaler

# Import our framework metrics
sys.path.insert(0, os.path.dirname(__file__))
from metrics import (
    f1_micro, f1_macro, hamming_loss,
    brier_micro, brier_macro, brier_exemplar, brier_class, mae_class,
    murphy_decomposition, brier_exemplar_decomposition,
    dcg_micro, dcg_class, dcg_exemplar,
    ndcg_micro, ndcg_class, ndcg_exemplar,
    auc_class, auc_macro, auc_micro,
    mean_rank_class, auc_from_mean_rank,
)

warnings.filterwarnings("ignore")

# ── Global settings ───────────────────────────────────────────────────────────

SEED = 42
OUT_DIR = os.path.join(os.path.dirname(__file__), "figs")
DATA_DIR = os.path.join(os.path.dirname(__file__), "data")


def _save(name, df):
    """Write the numbers behind a figure to experiments/data/<name>.csv."""
    os.makedirs(DATA_DIR, exist_ok=True)
    path = os.path.join(DATA_DIR, f"{name}.csv")
    df.to_csv(path, index=True, float_format="%.10g")
    print(f"  saved {path}")
os.makedirs(OUT_DIR, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 10,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "figure.dpi": 150,
    "savefig.dpi": 200,
    "text.usetex": False,          # set True if LaTeX is available
})

COLORS = {
    "disc":  "#2166ac",   # Discrimination (blue)
    "cal":   "#d6604d",   # Calibration (red)
    "rank":  "#1a9850",   # Ranking (green)
    "extra": "#762a83",   # extra (purple)
}


# ── Data loading ──────────────────────────────────────────────────────────────
#
# Datasets are downloaded from OpenML via the `openml` Python package and
# cached locally in ~/openml/org/openml/www/datasets/ (openml default cache).
#
# OpenML dataset identifiers:
#   Emotions : ID 40589  —  593 ex., 72 features, 6 labels
#   Yeast    : ID 40597  —  2417 ex., 103 features, 14 labels
#
# MULAN convention: feature columns first, label columns at the right end.
# n_labels is the count of label columns.
#
# Install:  pip install openml

_OPENML_IDS = {
    "emotions": {"id": 40589, "n_labels": 6},
    "yeast":    {"id": 40597, "n_labels": 14},
}


def _load_openml(name: str, seed: int = SEED):
    """
    Download a multilabel dataset from OpenML and return a train/test split.
    Data is cached locally after the first download.
    """
    try:
        import openml
    except ImportError:
        raise ImportError(
            "The `openml` package is required for dataset loading.\n"
            "Install with:  pip install openml"
        )

    cfg   = _OPENML_IDS[name]
    ds    = openml.datasets.get_dataset(
        cfg["id"],
        download_data=True,
        download_qualities=False,
        download_features_meta_data=False,
    )
    # Retrieve all columns as a DataFrame (openml handles type conversion)
    df, _, _, _ = ds.get_data(dataset_format="dataframe", target=None)

    # MULAN convention: last n_labels columns are binary label attributes
    n_labels = cfg["n_labels"]
    arr = df.values
    X   = arr[:, :-n_labels].astype(float)

    # Label columns may be returned as bool, int, or strings
    # ('True'/'False', '0'/'1', b'0'/b'1') depending on the ARFF encoding.
    def _to_binary(v):
        s = str(v).strip("b'\"").lower()
        if s in ("true",  "1", "1.0", "yes"): return 1
        if s in ("false", "0", "0.0", "no"):  return 0
        raise ValueError(f"Unexpected label value: {v!r}")

    raw_Y = arr[:, -n_labels:]
    Y = np.vectorize(_to_binary)(raw_Y).astype(int)

    # Preserve label column names for use in figure axes
    label_names = list(df.columns[-n_labels:])

    X = MinMaxScaler().fit_transform(X)
    X_tr, X_te, Y_tr, Y_te = train_test_split(X, Y, test_size=0.3, random_state=seed)
    return X_tr, X_te, Y_tr, Y_te, label_names


def load_emotions(seed: int = SEED):
    """
    Emotions dataset — OpenML ID 40589.
    593 examples, 72 features, 6 labels.
    Labels: amazed-suprised, happy-pleased, relaxing-calm,
            quiet-still, sad-lonely, angry-aggresive
    Used for Experiments 1–3.
    Returns X_tr, X_te, Y_tr, Y_te, label_names.
    """
    print("  Loading 'emotions' (OpenML ID 40589) ...")
    return _load_openml("emotions", seed)


def load_yeast(seed: int = SEED):
    """
    Yeast dataset — OpenML ID 40597.
    2417 examples, 103 features, 14 labels (Class1–Class14).
    Used for Experiment 4 (Murphy heatmap).
    Returns X_tr, X_te, Y_tr, Y_te, label_names.
    """
    print("  Loading 'yeast' (OpenML ID 40597) ...")
    return _load_openml("yeast", seed)


# ── Classifiers ───────────────────────────────────────────────────────────────

CLASSIFIERS = {
    "LR":             LogisticRegression(max_iter=500, random_state=SEED),
    "RF":             RandomForestClassifier(n_estimators=100, random_state=SEED),
    "GBT":            GradientBoostingClassifier(n_estimators=100, random_state=SEED),
    "MLP (uncal.)":   MLPClassifier(hidden_layer_sizes=(64,), max_iter=300,
                                    random_state=SEED),
    "MLP (cal.)":     CalibratedClassifierCV(
                          MLPClassifier(hidden_layer_sizes=(64,), max_iter=300,
                                        random_state=SEED),
                          cv=3, method="sigmoid"),
}


def build_classifiers():
    return {
        name: MultiOutputClassifier(clf, n_jobs=1)
        for name, clf in CLASSIFIERS.items()
    }


def get_proba(clf, X):
    """Stack positive-class probabilities from a fitted MultiOutputClassifier."""
    return np.column_stack([p[:, 1] for p in clf.predict_proba(X)])


def threshold(Yhat, t=0.5):
    return (Yhat >= t).astype(int)


def train_all(X_tr, X_te, Y_tr, Y_te):
    """Fit all classifiers and return (proba, hard) predictions on the test set."""
    clfs   = build_classifiers()
    probas = {}
    hards  = {}
    print("  Training classifiers ...")
    for name, clf in clfs.items():
        clf.fit(X_tr, Y_tr)
        p = get_proba(clf, X_te)
        probas[name] = p
        hards[name]  = threshold(p)
        print(f"    {name} done.")
    return probas, hards


# ═════════════════════════════════════════════════════════════════════════════
# Experiment 1 — Classifier ranking disagreement
# ═════════════════════════════════════════════════════════════════════════════

def exp1_ranking_disagreement(Y_te, probas, hards):
    """
    Compute macro-F1 (Discrimination), macro-Brier (Calibration),
    macro-nDCG_j^class (Ranking), and macro-AUC (Ranking) for each
    classifier, then plot rank matrices to show framework disagreement.
    """
    print("\n--- Exp 1: Classifier ranking disagreement ---")
    rows = {}
    for name in probas:
        Yhat  = probas[name]
        Yhard = hards[name]
        rows[name] = {
            "F1 (macro)":       f1_macro(Y_te, Yhard),
            # Invert Brier so higher = better, consistent with other metrics
            "1-BS (macro)":     1.0 - brier_macro(Y_te, Yhat),
            "nDCG (macro)":     float(ndcg_class(Y_te, Yhat).mean()),
            "AUC (macro)":      auc_macro(Y_te, Yhat),
        }

    df = pd.DataFrame(rows).T
    _save("exp1_scores", df)
    ranks = df.rank(ascending=False).astype(int)
    metrics = list(df.columns)
    names   = list(df.index)

    # Kendall τ
    print("  Kendall τ between framework rankings:")
    for i, m1 in enumerate(metrics):
        for j, m2 in enumerate(metrics):
            if j > i:
                tau, p = kendalltau(ranks[m1].values, ranks[m2].values)
                print(f"    {m1} vs {m2}: τ = {tau:.3f} (p = {p:.3f})")

    # Figure
    fig, axes = plt.subplots(1, 2, figsize=(12, 4.5))

    # (a) Raw scores
    ax = axes[0]
    x = np.arange(len(names))
    w = 0.18
    palette = [COLORS["disc"], COLORS["cal"], COLORS["rank"], COLORS["extra"]]
    for i, (metric, color) in enumerate(zip(metrics, palette)):
        ax.bar(x + i * w, df[metric].values, w, label=metric, color=color, alpha=0.85)
    ax.set_xticks(x + 1.5 * w)
    ax.set_xticklabels(names, rotation=20, ha="right", fontsize=9)
    ax.set_ylabel("Score")
    ax.set_title("(a) Scores across frameworks")
    ax.legend(fontsize=8)

    # (b) Rank heatmap
    ax = axes[1]
    rank_mat = ranks.T.values          # shape (n_metrics, n_classifiers)
    im = ax.imshow(rank_mat, cmap="RdYlGn_r", aspect="auto",
                   vmin=1, vmax=len(names))
    ax.set_xticks(range(len(names)))
    ax.set_xticklabels(names, rotation=20, ha="right", fontsize=9)
    ax.set_yticks(range(len(metrics)))
    ax.set_yticklabels(metrics, fontsize=9)
    ax.set_title("(b) Classifier ranks per metric\n(green = 1st, red = last)")
    for i in range(len(metrics)):
        for j in range(len(names)):
            ax.text(j, i, str(rank_mat[i, j]), ha="center", va="center",
                    fontsize=11, fontweight="bold", color="black")
    plt.colorbar(im, ax=ax, label="Rank")

    plt.tight_layout()
    path = os.path.join(OUT_DIR, "exp1_ranking_disagreement.pdf")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved {path}")
    return df, ranks


# ═════════════════════════════════════════════════════════════════════════════
# Experiment 2 — Aggregation collapse (Brier) vs split (nDCG)
# ═════════════════════════════════════════════════════════════════════════════

def exp2_collapse(Y_te, probas):
    """
    Verify the collapse theorem: micro-BS = macro-BS = exemplar-BS.
    Verify that micro-nDCG ≠ macro-nDCG ≠ exemplar-nDCG.
    """
    print("\n--- Exp 2: Aggregation collapse ---")
    names = list(probas)
    bs   = {agg: [] for agg in ("micro", "macro", "exemplar")}
    ndcg = {agg: [] for agg in ("micro", "macro", "exemplar")}

    for name in names:
        Yhat = probas[name]
        bs["micro"].append(brier_micro(Y_te, Yhat))
        bs["macro"].append(brier_macro(Y_te, Yhat))
        bs["exemplar"].append(brier_exemplar(Y_te, Yhat))
        ndcg["micro"].append(ndcg_micro(Y_te, Yhat))
        ndcg["macro"].append(float(ndcg_class(Y_te, Yhat).mean()))
        ndcg["exemplar"].append(float(ndcg_exemplar(Y_te, Yhat).mean()))

    # Numerical verification of collapse
    print("  Brier collapse (|micro − macro|, |micro − exemplar|):")
    for i, name in enumerate(names):
        d_mm = abs(bs["micro"][i] - bs["macro"][i])
        d_me = abs(bs["micro"][i] - bs["exemplar"][i])
        print(f"    {name}: |micro-macro| = {d_mm:.2e}, |micro-exemplar| = {d_me:.2e}")

    _save("exp2_aggregations", pd.DataFrame(
        {**{f"BS_{k}": v for k, v in bs.items()},
         **{f"nDCG_{k}": v for k, v in ndcg.items()}}, index=names))

    x = np.arange(len(names))
    w = 0.25
    agg_labels = ["micro", "macro", "exemplar"]
    agg_colors = [COLORS["disc"], COLORS["cal"], COLORS["rank"]]

    fig, axes = plt.subplots(1, 2, figsize=(12, 4.5))

    for ax, data, title, ylabel in [
        (axes[0], bs,   "(a) Brier score (lower = better)\n[collapse: micro = macro = exemplar]",
         "Brier score"),
        (axes[1], ndcg, "(b) nDCG (higher = better)\n[split: micro ≈ exemplar ≠ macro]",
         "nDCG"),
    ]:
        bars_per_agg = {}
        for i, (agg, color) in enumerate(zip(agg_labels, agg_colors)):
            bars_per_agg[agg] = ax.bar(
                x + i * w, data[agg], w, label=agg, color=color, alpha=0.85)
        # Value labels above every bar
        for i, (agg, color) in enumerate(zip(agg_labels, agg_colors)):
            for xi, val in zip(x, data[agg]):
                ax.text(xi + i * w, val + 0.001, f"{val:.4f}",
                        ha="center", va="bottom", fontsize=5.5,
                        color="black", rotation=90)
        ax.set_xticks(x + w)
        ax.set_xticklabels(names, rotation=20, ha="right", fontsize=9)
        ax.set_ylabel(ylabel)
        ax.set_title(title, fontsize=9)
        ax.legend(fontsize=8)
        # Extra vertical space for the value labels
        ylo, yhi = ax.get_ylim()
        ax.set_ylim(ylo, yhi * 1.12)

    plt.tight_layout()
    path = os.path.join(OUT_DIR, "exp2_collapse.pdf")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved {path}")


# ═════════════════════════════════════════════════════════════════════════════
# Experiment 3 — Skew-invariance under prevalence variation
# ═════════════════════════════════════════════════════════════════════════════

def exp3_skew_invariance(X_tr, X_te, Y_tr, Y_te, label_names=None):
    """
    Vary class-0 prevalence by subsampling the test set.
    Shows AUC_0 and nDCG_0^class are stable; micro-AUC and macro-BS are not.
    """
    print("\n--- Exp 3: Skew-invariance ---")

    # Use LR (well-calibrated) for this illustration
    clf = MultiOutputClassifier(
        LogisticRegression(max_iter=500, random_state=SEED), n_jobs=1
    )
    clf.fit(X_tr, Y_tr)
    Yhat_full = get_proba(clf, X_te)

    # Label name for class 0; OpenML sometimes replaces hyphens with dots
    raw_lname = label_names[0] if label_names else "class 0"
    lname = raw_lname.replace(".", "-")   # restore hyphen for display

    # Cap at π=0.80 to avoid AUC instability when negatives become very scarce
    rng = np.random.default_rng(SEED)
    target_prevs = np.linspace(0.1, 0.80, 10)
    N_TRIALS     = 10    # repeated subsamples for confidence bands

    pos_idx = np.where(Y_te[:, 0] == 1)[0]
    neg_idx = np.where(Y_te[:, 0] == 0)[0]
    n_pos   = len(pos_idx)
    n_neg   = len(neg_idx)

    # Collect N_TRIALS realisations at each target prevalence
    all_auc0       = {pi: [] for pi in target_prevs}
    all_ndcg0      = {pi: [] for pi in target_prevs}
    all_micro_auc  = {pi: [] for pi in target_prevs}
    all_macro_bs   = {pi: [] for pi in target_prevs}
    all_meanrank0  = {pi: [] for pi in target_prevs}   # raw mean rank M_0
    actual_prevs   = []
    max_auc_identity_err = 0.0   # machine-precision check of prop:auc_meanrank

    for pi_target in target_prevs:
        n_neg_target = max(5, int(round(n_pos * (1.0 - pi_target) / pi_target)))
        n_neg_sample = min(n_neg_target, n_neg)
        prev_trials  = []

        for _ in range(N_TRIALS):
            sampled_neg = rng.choice(neg_idx, size=n_neg_sample, replace=False)
            idx = np.concatenate([pos_idx, sampled_neg])
            rng.shuffle(idx)

            Y_sub    = Y_te[idx]
            Yhat_sub = Yhat_full[idx]
            prev_trials.append(float(Y_sub[:, 0].mean()))

            auc_j = auc_class(Y_sub, Yhat_sub)
            all_auc0[pi_target].append(
                float(auc_j[0]) if not np.isnan(auc_j[0]) else np.nan)
            all_ndcg0[pi_target].append(
                float(ndcg_class(Y_sub, Yhat_sub)[0]))
            all_micro_auc[pi_target].append(auc_micro(Y_sub, Yhat_sub))
            all_macro_bs[pi_target].append(brier_macro(Y_sub, Yhat_sub))

            # Raw mean rank M_0 of the positives (skew-sensitive foil), and a
            # machine-precision check that AUC_0 = affine(M_0) (prop:auc_meanrank)
            M0 = float(mean_rank_class(Y_sub, Yhat_sub)[0])
            all_meanrank0[pi_target].append(M0)
            if not np.isnan(auc_j[0]):
                n_sub  = Y_sub.shape[0]
                npos_0 = int(Y_sub[:, 0].sum())
                auc_rec = auc_from_mean_rank(M0, n_sub, npos_0)
                max_auc_identity_err = max(
                    max_auc_identity_err, abs(auc_rec - float(auc_j[0])))

        actual_prevs.append(float(np.mean(prev_trials)))

    print(f"  Identity AUC_0 = affine(M_0) max error over all trials: "
          f"{max_auc_identity_err:.2e}  (Proposition prop:auc_meanrank)")

    def _mean_std(d):
        means = np.array([np.nanmean(d[pi]) for pi in target_prevs])
        stds  = np.array([np.nanstd(d[pi])  for pi in target_prevs])
        return means, stds

    auc0_m,      auc0_s      = _mean_std(all_auc0)
    ndcg0_m,     ndcg0_s     = _mean_std(all_ndcg0)
    micro_auc_m, micro_auc_s = _mean_std(all_micro_auc)
    macro_bs_m,  macro_bs_s  = _mean_std(all_macro_bs)
    meanrank0_m, meanrank0_s = _mean_std(all_meanrank0)

    # Per-class-summary convention (Definition def:cal_skew of the paper): only class 0's counts
    # change and the summaries of the other classes are held at their full-test-set values.
    # Subsampling whole rows, as above, also changes the other classes' columns (their positives
    # and the composition of their negatives), which this convention does not do.
    _auc_full = auc_class(Y_te, Yhat_full)
    _npos_full = Y_te.sum(axis=0).astype(float)
    _n_te, _m = Y_te.shape
    _pos0, _neg0 = Y_te[:, 0] == 1, Y_te[:, 0] == 0
    _alpha0 = float(np.mean((1.0 - Yhat_full[_pos0, 0]) ** 2))
    _beta0 = float(np.mean(Yhat_full[_neg0, 0] ** 2))
    _bs_full = brier_class(Y_te, Yhat_full)
    _others = [l for l in range(_m) if l != 0 and not np.isnan(_auc_full[l])]
    _num_o = float(np.sum(_npos_full[_others] * _auc_full[_others]))
    _den_o = float(np.sum(_npos_full[_others]))
    _grid = np.linspace(float(Y_te[:, 0].mean()), 0.81, 30)
    _n_pos0, _n_neg0 = float(_pos0.sum()), float(_neg0.sum())
    _lam = (_grid / (1.0 - _grid)) * (_n_neg0 / _n_pos0)      # positive scaling reaching each prevalence
    _micro_neg = (_n_pos0 * _auc_full[0] + _num_o) / (_n_pos0 + _den_o)   # scaling negatives: n+ unchanged
    _micro_pos = (_lam * _n_pos0 * _auc_full[0] + _num_o) / (_lam * _n_pos0 + _den_o)
    _macro_bs_conv = (_grid * _alpha0 + (1.0 - _grid) * _beta0
                      + float(np.sum(_bs_full[1:]))) / _m
    _save("exp3_per_class_convention", pd.DataFrame({
        "prevalence": _grid, "micro_auc_scaling_negatives": _micro_neg,
        "micro_auc_scaling_positives": _micro_pos, "macro_bs": _macro_bs_conv,
        "AUC0": _auc_full[0], "alpha0": _alpha0, "beta0": _beta0}))
    _save("exp3_prevalence_sweep", pd.DataFrame({
        "target_prevalence": target_prevs, "actual_prevalence": actual_prevs,
        "auc0_mean": auc0_m, "auc0_std": auc0_s,
        "ndcg0_mean": ndcg0_m, "ndcg0_std": ndcg0_s,
        "micro_auc_mean": micro_auc_m, "micro_auc_std": micro_auc_s,
        "macro_bs_mean": macro_bs_m, "macro_bs_std": macro_bs_s,
        "meanrank0_mean": meanrank0_m, "meanrank0_std": meanrank0_s}))

    xlabel = f"Prevalence of '{lname}' ($\\pi_j$)"

    fig, axes = plt.subplots(1, 2, figsize=(11, 4))

    ax = axes[0]
    l_auc, = ax.plot(actual_prevs, auc0_m, "o-", color=COLORS["rank"],
            label=f"AUC ({lname}) — normalised, skew-inv.", linewidth=2)
    ax.fill_between(actual_prevs, auc0_m - auc0_s, auc0_m + auc0_s,
                    color=COLORS["rank"], alpha=0.15)
    l_ndcg, = ax.plot(actual_prevs, ndcg0_m, "s--", color=COLORS["disc"],
            label=f"nDCG$^{{\\mathrm{{class}}}}$ ({lname}) — normalised, skew-inv.", linewidth=2)
    ax.fill_between(actual_prevs, ndcg0_m - ndcg0_s, ndcg0_m + ndcg0_s,
                    color=COLORS["disc"], alpha=0.15)
    ax.set_xlabel(xlabel)
    ax.set_ylabel("Normalised score (AUC, nDCG$^{\\mathrm{class}}$)")
    ax.set_title("(a) AUC is the normalisation of a drifting raw rank")
    ax.set_ylim(0, 1.05)

    # Twin axis: the RAW mean rank M_0 (skew-sensitive) whose affine
    # normalisation is the flat AUC_0 above (Proposition prop:auc_meanrank).
    axb = ax.twinx()
    axb.spines["right"].set_visible(True)
    l_mr, = axb.plot(actual_prevs, meanrank0_m, "^:", color=COLORS["extra"],
            label=f"mean rank $M_0$ ({lname}) — raw, skew-sensitive", linewidth=2)
    axb.fill_between(actual_prevs, meanrank0_m - meanrank0_s,
                     meanrank0_m + meanrank0_s, color=COLORS["extra"], alpha=0.15)
    axb.set_ylabel("Raw mean rank $M_0$", color=COLORS["extra"])
    axb.tick_params(axis="y", labelcolor=COLORS["extra"])
    ax.legend(handles=[l_auc, l_ndcg, l_mr], fontsize=7, loc="upper center",
              bbox_to_anchor=(0.5, -0.2), frameon=False)

    ax = axes[1]
    ax2 = ax.twinx()
    l1, = ax.plot(actual_prevs, micro_auc_m, "D:", color=COLORS["cal"],
                  label="Micro-AUC, row subsampling", linewidth=2)
    ax.fill_between(actual_prevs,
                    micro_auc_m - micro_auc_s, micro_auc_m + micro_auc_s,
                    color=COLORS["cal"], alpha=0.15)
    l2, = ax2.plot(actual_prevs, macro_bs_m, "v-.", color=COLORS["extra"],
                   label="Macro-BS, row subsampling", linewidth=2)
    l3, = ax.plot(_grid, _micro_pos, "--", color=COLORS["cal"], linewidth=1.4,
                  label="Micro-AUC, per-class convention (scaling positives)")
    l4, = ax2.plot(_grid, _macro_bs_conv, "--", color=COLORS["extra"], linewidth=1.4,
                   label="Macro-BS, per-class convention")
    ax2.fill_between(actual_prevs,
                     macro_bs_m - macro_bs_s, macro_bs_m + macro_bs_s,
                     color=COLORS["extra"], alpha=0.15)
    ax.set_xlabel(xlabel)
    ax.set_ylabel("Micro-AUC", color=COLORS["cal"])
    ax2.set_ylabel("Macro-BS", color=COLORS["extra"])
    ax.set_title("(b) Aggregate measures vary with prevalence")
    ax.tick_params(axis="y", labelcolor=COLORS["cal"])
    ax2.tick_params(axis="y", labelcolor=COLORS["extra"])
    # Legend below the panel: inside the axes it covers the subsampling bands.
    ax.legend(handles=[l1, l2, l3, l4], fontsize=6.5, loc="upper center",
              bbox_to_anchor=(0.5, -0.2), ncol=2, frameon=False)

    plt.tight_layout()
    path = os.path.join(OUT_DIR, "exp3_skew_invariance.pdf")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved {path}")


# ═════════════════════════════════════════════════════════════════════════════
# Experiment 4 — Per-class Murphy decomposition heatmap
# ═════════════════════════════════════════════════════════════════════════════

def exp4_murphy_heatmap(Y_te, probas, label_names=None):
    """
    Per-class Murphy decomposition: BS_j = UNC_j - RES_j + REL_j.

    Layout (GridSpec):
      Top row   : REL_j heatmap (classifiers × labels)
                  RES_j heatmap (classifiers × labels)
      Bottom row: UNC_j bar chart (labels only — identical across classifiers,
                  because UNC_j = pi_j(1-pi_j) is a data property).
    """
    print("\n--- Exp 4: Murphy decomposition ---")

    names  = list(probas)
    n_clf  = len(names)
    m      = Y_te.shape[1]
    labels = label_names if label_names else [f"L{j}" for j in range(m)]

    BS_mat  = np.zeros((n_clf, m))
    UNC_mat = np.zeros((n_clf, m))
    RES_mat = np.zeros((n_clf, m))
    REL_mat = np.zeros((n_clf, m))

    for i, name in enumerate(names):
        BS, UNC, RES, REL = murphy_decomposition(Y_te, probas[name], n_bins=10)
        BS_mat[i]  = BS
        UNC_mat[i] = UNC
        RES_mat[i] = RES
        REL_mat[i] = REL

    residual = np.abs(BS_mat - (UNC_mat - RES_mat + REL_mat))
    print(f"  Max |BS - (UNC - RES + REL)|: {residual.max():.2e}  (should be ~0)")

    _lab = label_names if label_names else [f"L{j}" for j in range(m)]
    _rows = []
    for _i, _name in enumerate(probas):
        for _j in range(m):
            _rows.append({"classifier": _name, "label": _lab[_j], "BS": BS_mat[_i, _j],
                          "UNC": UNC_mat[_i, _j], "RES": RES_mat[_i, _j],
                          "REL": REL_mat[_i, _j]})
    _save("exp5_murphy_per_class", pd.DataFrame(_rows))

    # UNC is the same for every classifier — take row 0
    unc_j = UNC_mat[0]

    # ── Layout ───────────────────────────────────────────────────────────────
    fig = plt.figure(figsize=(16, 7))
    gs  = fig.add_gridspec(2, 2, height_ratios=[3, 1.2],
                           hspace=0.55, wspace=0.3)

    ax_rel = fig.add_subplot(gs[0, 0])
    ax_res = fig.add_subplot(gs[0, 1])
    ax_unc = fig.add_subplot(gs[1, :])   # spans both columns

    x = np.arange(m)

    # ── REL and RES heatmaps ─────────────────────────────────────────────────
    for ax, mat, title, cmap in [
        (ax_rel, REL_mat, r"(a) Reliability ($\widehat{\mathrm{REL}}_j$)  $\downarrow$", "Reds"),
        (ax_res, RES_mat, r"(b) Resolution ($\widehat{\mathrm{RES}}_j$)  $\uparrow$",   "Greens"),
    ]:
        vmax = mat.max() if mat.max() > 0 else 1.0
        im   = ax.imshow(mat, cmap=cmap, aspect="auto", vmin=0, vmax=vmax)
        ax.set_xticks(range(m))
        ax.set_xticklabels(labels, fontsize=7, rotation=60, ha="right")
        ax.set_yticks(range(n_clf))
        ax.set_yticklabels(names, fontsize=9)
        ax.set_title(title, fontsize=10)
        plt.colorbar(im, ax=ax, shrink=0.80, pad=0.02)

    # ── UNC bar chart ────────────────────────────────────────────────────────
    ax_unc.bar(x, unc_j, color=COLORS["disc"], alpha=0.75, width=0.6)
    ax_unc.set_xticks(x)
    ax_unc.set_xticklabels(labels, fontsize=7, rotation=60, ha="right")
    ax_unc.set_ylabel(r"UNC$_j$", fontsize=9)
    ax_unc.set_title(
        r"(c) Uncertainty (UNC$_j$ = $\pi_j(1-\pi_j)$) — "
        "data property, identical for all classifiers",
        fontsize=10
    )
    ax_unc.set_xlim(-0.5, m - 0.5)

    fig.suptitle(
        r"Per-class Murphy decomposition (binned): "
        r"$\widehat{\mathrm{BS}}_j$ = UNC$_j$ $-$ $\widehat{\mathrm{RES}}_j$ + $\widehat{\mathrm{REL}}_j$",
        fontsize=12, y=1.01
    )
    fig.savefig(os.path.join(OUT_DIR, "exp4_murphy_heatmap.pdf"),
                bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved exp4_murphy_heatmap.pdf")


# ═════════════════════════════════════════════════════════════════════════════
# Experiment 5 — Per-exemplar Brier decomposition
# ═════════════════════════════════════════════════════════════════════════════

def exp5_exemplar_decomposition(Y_te_emo, probas_emo,
                                Y_te_yeast, probas_yeast):
    """
    Per-exemplar Brier decomposition.

    Panel (a): mean alpha_i / beta_i by label cardinality k_i, using
               the Yeast dataset (14 labels → k ranges 1–8+, richer curve).
               One line per classifier; solid = alpha, dashed = beta.

    Panel (b): Empirical CDFs of BS_i^ex per classifier on Emotions.
               All means are identical (collapse theorem) but CDFs diverge,
               showing that calibrated classifiers concentrate mass near 0.
    """
    print("\n--- Exp 5: Per-exemplar Brier decomposition ---")

    clf_names = list(probas_emo)
    palette   = [COLORS["disc"], COLORS["cal"], COLORS["rank"],
                 COLORS["extra"], "#4d4d4d"]

    # ── (a) alpha / beta by cardinality — Yeast ───────────────────────────────
    m_yeast = Y_te_yeast.shape[1]
    all_alpha_y = {}
    all_beta_y  = {}
    all_k_y     = None

    for name in clf_names:
        _, alpha, beta, k = brier_exemplar_decomposition(Y_te_yeast,
                                                          probas_yeast[name])
        all_alpha_y[name] = alpha
        all_beta_y[name]  = beta
        if all_k_y is None:
            all_k_y = k

    # Keep cardinalities with at least 15 examples for stable means
    cardinalities = [ki for ki in sorted(set(all_k_y))
                     if (all_k_y == ki).sum() >= 15
                     and 0 < ki < m_yeast]
    card_counts   = [(all_k_y == ki).sum() for ki in cardinalities]

    # ── (b) CDFs of BS_i^ex — Emotions ───────────────────────────────────────
    all_BS_emo = {}
    for name in clf_names:
        BS_ex, _, _, _ = brier_exemplar_decomposition(Y_te_emo, probas_emo[name])
        all_BS_emo[name] = np.sort(BS_ex)

    # ── Figure ────────────────────────────────────────────────────────────────
    _rows = []
    for _name in clf_names:
        for _k, _c in zip(cardinalities, card_counts):
            _rows.append({"classifier": _name, "cardinality": _k, "n_examples": int(_c),
                          "mean_alpha": float(np.nanmean(all_alpha_y[_name][all_k_y == _k])),
                          "mean_beta": float(np.nanmean(all_beta_y[_name][all_k_y == _k]))})
    _save("exp6_alpha_beta_by_cardinality", pd.DataFrame(_rows))
    _save("exp6_bs_example_quantiles", pd.DataFrame(
        {_name: np.quantile(all_BS_emo[_name], [0.05, 0.25, 0.5, 0.75, 0.95, 1.0])
         for _name in clf_names},
        index=["q05", "q25", "q50", "q75", "q95", "max"]).assign(
            **{}).T.assign(mean=[float(np.mean(all_BS_emo[_n])) for _n in clf_names]))

    fig, axes = plt.subplots(1, 2, figsize=(13, 4.5))

    # Panel (a)
    ax = axes[0]
    x  = np.arange(len(cardinalities))
    for name, color in zip(clf_names, palette):
        mean_alpha = [np.nanmean(all_alpha_y[name][all_k_y == ki])
                      for ki in cardinalities]
        mean_beta  = [np.nanmean(all_beta_y[name] [all_k_y == ki])
                      for ki in cardinalities]
        ax.plot(x, mean_alpha, "o-",  color=color, linewidth=1.8, alpha=0.9)
        ax.plot(x, mean_beta,  "s--", color=color, linewidth=1.8, alpha=0.55)

    ax.set_xticks(x)
    ax.set_xticklabels(
        [f"$k={ki}$\n(n={n})" for ki, n in zip(cardinalities, card_counts)],
        fontsize=8)
    ax.set_xlabel("Label cardinality $k_i$  (Yeast, $m=14$)")
    ax.set_ylabel("Mean squared error component")
    ax.set_title(
        "(a) $\\alpha_i$ (solid) and $\\beta_i$ (dashed) by cardinality\n"
        r"$\mathrm{BS}_i^{\mathrm{ex}} = \frac{k_i}{m}\,\alpha_i"
        r" + \frac{m-k_i}{m}\,\beta_i$"
    )
    # Legend: one proxy per classifier, style note in title
    from matplotlib.lines import Line2D
    proxies = [Line2D([0], [0], color=c, linewidth=1.8)
               for c in palette[:len(clf_names)]]
    ax.legend(proxies, clf_names, fontsize=7,
              title="solid = $\\alpha_i$,  dashed = $\\beta_i$",
              title_fontsize=7)

    # Panel (b)
    ax = axes[1]
    for name, color in zip(clf_names, palette):
        bs_sorted = all_BS_emo[name]
        cdf = np.arange(1, len(bs_sorted) + 1) / len(bs_sorted)
        mu  = bs_sorted.mean()
        ax.plot(bs_sorted, cdf, color=color, linewidth=1.8,
                label=f"{name}  (mean={mu:.4f})")
        ax.axvline(mu, color=color, linewidth=0.8, linestyle=":")

    ax.set_xlabel(r"$\mathrm{BS}_i^{\mathrm{ex}}$  (Emotions)")
    ax.set_ylabel("Empirical CDF")
    ax.set_title(
        "(b) CDFs of per-exemplar Brier scores\n"
        "Means are close across classifiers; CDFs reveal distributional differences"
    )
    ax.legend(fontsize=7)

    plt.tight_layout()
    path = os.path.join(OUT_DIR, "exp5_exemplar_decomposition.pdf")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved {path}")


# ═════════════════════════════════════════════════════════════════════════════
# Experiment 6 — Per-class nDCG as a novel measure
# ═════════════════════════════════════════════════════════════════════════════

def exp6_ndcg_class_novel(Y_te, probas, label_names=None, Y_tr=None):
    """
    Empirical illustration of nDCG_j^class as a novel per-class ranking measure.

    AUC_j  = E[f(i,j) | Y_ij=1]             column-rank quality
    nDCG_j^class = E[w(rank_i(j)) | Y_ij=1] row-rank quality

    Panel (a): Scatter of mean-across-classifiers AUC_j vs nDCG_j^class,
               one annotated point per label.  Diagonal y=x for reference;
               per-classifier background dots show spread.

    Panel (b): Horizontal grouped bar chart (RF and MLP cal.) for each label,
               sorted by descending AUC_j.  The visible gap between the two
               bars per label is the key diagnostic: labels where nDCG_j^class
               falls well short of AUC_j compete with many co-occurring labels
               for the top row-rank position.
    """
    print("\n--- Exp 6: Per-class nDCG as a novel measure ---")

    clf_names = list(probas)
    n_clf     = len(clf_names)
    m         = Y_te.shape[1]
    labels    = label_names if label_names else [f"L{j}" for j in range(m)]
    # Shorten label names for readability (keep up to 8 chars)
    short_labels = [lb[:8] for lb in labels]

    palette  = [COLORS["disc"], COLORS["cal"], COLORS["rank"],
                COLORS["extra"], "#4d4d4d"]
    markers  = ['o', 's', '^', 'D', 'v']

    # ── Compute AUC_j and nDCG_j^class for every classifier ──────────────────
    auc_mat  = np.full((n_clf, m), np.nan)
    ndcg_mat = np.full((n_clf, m), np.nan)

    for ci, name in enumerate(clf_names):
        Yhat = probas[name]
        auc_mat[ci]  = np.where(
            np.isnan(auc_class(Y_te, Yhat)), np.nan, auc_class(Y_te, Yhat))
        ndcg_mat[ci] = ndcg_class(Y_te, Yhat)

    mean_auc  = np.nanmean(auc_mat,  axis=0)   # shape (m,)
    mean_ndcg = np.nanmean(ndcg_mat, axis=0)   # shape (m,)
    gap_mean  = mean_auc - mean_ndcg
    _rows = []
    for _ci, _name in enumerate(clf_names):
        for _j in range(m):
            _rows.append({"classifier": _name, "label": labels[_j],
                          "AUC": auc_mat[_ci, _j], "nDCG_class": ndcg_mat[_ci, _j]})
    _save("exp7_auc_vs_ndcg_per_class", pd.DataFrame(_rows))
    _save("exp7_label_means", pd.DataFrame(
        {"label": labels, "prevalence": Y_te.mean(axis=0), "mean_AUC": mean_auc,
         "mean_nDCG_class": mean_ndcg, "gap": gap_mean}))

    print(f"  Mean AUC_j:            {np.nanmean(mean_auc):.3f}")
    print(f"  Mean nDCG_j^class:     {np.nanmean(mean_ndcg):.3f}")
    print(f"  Mean gap (AUC-nDCG):   {np.nanmean(gap_mean):.3f}")

    # ── Mechanism tests for the dependence of nDCG_j^class on label prevalence ──
    # Hypothesis: nDCG_j^class varies across labels mainly through the SCALE of label j's
    # scores relative to the other labels (which follows the base rate), not through how well
    # label j separates its positives from its negatives.
    #   Test 1 (prior-only): every example gets the same score pi_j for label j (training
    #          prevalence). AUC_j = 0.5 by construction; only the scale is left.
    #   Test 2 (column-wise normalisation): replace each column by its mid-rank percentile.
    #          A strictly increasing map within a column leaves AUC_j exactly unchanged but
    #          gives all labels the same score distribution, removing the scale.
    from scipy.stats import rankdata, spearmanr
    prev = Y_te.mean(axis=0)
    prior = (Y_tr if Y_tr is not None else Y_te).mean(axis=0)
    Yprior = np.tile(prior, (Y_te.shape[0], 1))
    ndcg_prior = ndcg_class(Y_te, Yprior)
    auc_prior = auc_class(Y_te, Yprior)

    # Oracle ceiling: scores equal to the labels (random tie-breaks). nDCG_j^class = 1 cannot be
    # attained for all labels at once in multilabel data, since only one label per example is first.
    _rng_or = np.random.default_rng(SEED)
    ndcg_oracle = np.mean([ndcg_class(Y_te, Y_te + _rng_or.uniform(0.0, 1e-6, size=Y_te.shape))
                           for _ in range(20)], axis=0)

    n_te = Y_te.shape[0]
    N_JIT = 20
    rng_mech = np.random.default_rng(SEED)
    ndcg_norm = np.zeros((n_clf, m))
    max_auc_change = 0.0
    for ci, name in enumerate(clf_names):
        P = probas[name]
        U = np.column_stack([(rankdata(P[:, j], method="average") - 0.5) / n_te
                             for j in range(m)])
        acc = np.zeros(m)
        for _ in range(N_JIT):
            # a tiny constant per column breaks cross-label ties at random and leaves
            # every within-column comparison, hence AUC_j, untouched
            Uj = U + rng_mech.uniform(0.0, 1e-9, size=m)[None, :]
            acc += ndcg_class(Y_te, Uj)
            a_new = auc_class(Y_te, Uj)
            max_auc_change = max(max_auc_change,
                                 float(np.nanmax(np.abs(a_new - auc_mat[ci]))))
        ndcg_norm[ci] = acc / N_JIT

    mean_ndcg_norm = ndcg_norm.mean(axis=0)
    rho = lambda a, b: float(spearmanr(a, b)[0])
    summary = pd.DataFrame({
        "quantity": ["nDCG_model", "nDCG_prior_only", "nDCG_normalised",
                     "AUC_model", "gap_model (AUC-nDCG)", "gap_normalised (AUC-nDCG)"],
        "spearman_with_prevalence": [
            rho(prev, mean_ndcg), rho(prev, ndcg_prior), rho(prev, mean_ndcg_norm),
            rho(prev, mean_auc), rho(prev, mean_auc - mean_ndcg),
            rho(prev, mean_auc - mean_ndcg_norm)],
        "mean_over_labels": [np.nanmean(mean_ndcg), np.nanmean(ndcg_prior),
                             np.nanmean(mean_ndcg_norm), np.nanmean(mean_auc),
                             np.nanmean(mean_auc - mean_ndcg),
                             np.nanmean(mean_auc - mean_ndcg_norm)]})
    summary.loc[len(summary)] = ["spearman(nDCG_model, nDCG_prior_only)",
                                 rho(mean_ndcg, ndcg_prior), np.nan]
    summary.loc[len(summary)] = ["spearman(nDCG_model, nDCG_normalised)",
                                 rho(mean_ndcg, mean_ndcg_norm), np.nan]
    summary.loc[len(summary)] = ["spearman(nDCG_normalised, AUC_model)",
                                 rho(mean_ndcg_norm, mean_auc), np.nan]
    summary.loc[len(summary)] = ["spearman(nDCG_model, AUC_model)",
                                 rho(mean_ndcg, mean_auc), np.nan]
    summary.loc[len(summary)] = ["nDCG_oracle (mean over labels)", float(np.mean(ndcg_oracle)), np.nan]
    summary.loc[len(summary)] = ["spearman(nDCG_oracle, prevalence)", rho(prev, ndcg_oracle), np.nan]
    summary.loc[len(summary)] = ["spearman(nDCG_model / nDCG_oracle, prevalence)",
                                 rho(prev, mean_ndcg / ndcg_oracle), np.nan]
    summary.loc[len(summary)] = ["max |AUC change| under normalisation", max_auc_change, np.nan]
    summary.loc[len(summary)] = ["AUC of the prior-only predictor (mean over labels)",
                                 float(np.nanmean(auc_prior)), np.nan]
    _save("exp7_mechanism_summary", summary)
    _rows = []
    for _j in range(m):
        _rows.append({"label": labels[_j], "prevalence": prev[_j], "AUC_model": mean_auc[_j],
                      "nDCG_model": mean_ndcg[_j], "nDCG_oracle": ndcg_oracle[_j],
                      "nDCG_prior_only": ndcg_prior[_j],
                      "nDCG_normalised": mean_ndcg_norm[_j]})
    _save("exp7_mechanism_per_label", pd.DataFrame(_rows))
    print("  Mechanism tests (Spearman with prevalence):")
    print(summary.to_string(index=False))

    # ── Figure ────────────────────────────────────────────────────────────────
    fig, axes = plt.subplots(1, 2, figsize=(15, 5.5))

    # ── Panel (a): annotated scatter (mean per label) ─────────────────────────
    ax = axes[0]

    # Background: per-classifier dots (small, light)
    for ci, (name, color, mk) in enumerate(zip(clf_names, palette, markers)):
        valid = ~np.isnan(auc_mat[ci]) & ~np.isnan(ndcg_mat[ci])
        ax.scatter(auc_mat[ci, valid], ndcg_mat[ci, valid],
                   color=color, marker=mk, s=30, alpha=0.30,
                   linewidths=0, zorder=2)

    # Foreground: mean per label, annotated
    for j in range(m):
        if np.isnan(mean_auc[j]) or np.isnan(mean_ndcg[j]):
            continue
        ax.scatter(mean_auc[j], mean_ndcg[j],
                   color='black', s=55, zorder=4, linewidths=0)
        ax.annotate(short_labels[j],
                    xy=(mean_auc[j], mean_ndcg[j]),
                    xytext=(4, 2), textcoords='offset points',
                    fontsize=6.5, color='#333333', zorder=5)

    # Diagonal y = x
    ax.plot([0, 1], [0, 1], 'k--', linewidth=1, alpha=0.45)

    # Classifier legend (small dots)
    from matplotlib.lines import Line2D
    clf_proxies = [Line2D([0], [0], marker=mk, color=c, linestyle='None',
                          markersize=6, alpha=0.6, label=name)
                   for mk, c, name in zip(markers, palette, clf_names)]
    clf_proxies.append(Line2D([0], [0], marker='o', color='black',
                              linestyle='None', markersize=6, label='Label mean'))
    ax.legend(handles=clf_proxies, fontsize=7, loc='upper left',
              title='Classifier', title_fontsize=7)

    ax.set_xlabel(r'$\mathrm{AUC}_j$  (column-rank)', fontsize=10)
    ax.set_ylabel(r'$\mathrm{nDCG}_j^{\mathrm{class}}$  (row-rank)', fontsize=10)
    ax.set_title(
        r'(a) $\mathrm{AUC}_j$ vs.\ $\mathrm{nDCG}_j^{\mathrm{class}}$ per label'
        '\nBlack dots = mean across classifiers;  light = per-classifier',
        fontsize=9
    )
    ax.set_xlim(-0.02, 1.05)
    ax.set_ylim(-0.02, 1.05)

    # ── Panel (b): dumbbell plot — RF only, AUC vs nDCG per label ───────────
    ax = axes[1]

    rf_idx    = clf_names.index("RF")
    rf_auc_j  = auc_mat[rf_idx]
    rf_ndcg_j = ndcg_mat[rf_idx]

    # Sort by mean AUC_j descending (consistent with panel (a))
    sort_order  = np.argsort(
        np.where(np.isnan(mean_auc), -np.inf, mean_auc))[::-1]
    y_pos       = np.arange(m)
    auc_sorted  = rf_auc_j[sort_order]
    ndcg_sorted = rf_ndcg_j[sort_order]

    col_auc  = COLORS["disc"]
    col_ndcg = COLORS["rank"]

    # Connecting line
    for yi, (a, n) in enumerate(zip(auc_sorted, ndcg_sorted)):
        if not (np.isnan(a) or np.isnan(n)):
            ax.plot([n, a], [yi, yi], color='#aaaaaa', linewidth=1.2,
                    zorder=1, solid_capstyle='round')

    # Dots
    ax.scatter(auc_sorted, y_pos, color=col_auc, s=45, zorder=3,
               label=r'AUC$_j$  (column-rank)', linewidths=0)
    ax.scatter(ndcg_sorted, y_pos, color=col_ndcg, s=45, zorder=3,
               marker='D',
               label=r'nDCG$_j^{\mathrm{class}}$  (row-rank)', linewidths=0)

    ax.set_yticks(y_pos)
    ax.set_yticklabels([short_labels[j] for j in sort_order], fontsize=8)
    ax.set_xlabel('Score  (RF)', fontsize=10)
    ax.set_title(
        r'(b) Per-label AUC$_j$ vs.\ nDCG$_j^{\mathrm{class}}$  (RF)'
        '\nSorted by mean AUC$_j$;  circle = AUC, diamond = nDCG',
        fontsize=9
    )
    ax.set_xlim(0, 1.05)
    ax.axvline(0, color='gray', linewidth=0.5)
    ax.grid(axis='x', linewidth=0.4, alpha=0.4)
    ax.legend(fontsize=8, loc='upper left')

    plt.tight_layout()
    path = os.path.join(OUT_DIR, "exp6_ndcg_class_novel.pdf")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved {path}")


# ═════════════════════════════════════════════════════════════════════════════
# Experiment 7 — Properness: order-preserving distortion and its limits
# ═════════════════════════════════════════════════════════════════════════════

def exp7_properness_distortion(Y_te, probas):
    """
    Propositions prop:disc_improper / prop:auc_improper: positional operators are
    proper but never strictly proper -- any order-preserving distortion of the
    predicted probabilities attains the same score. Remark rem:mae_nonproper: MAE
    (unlike Brier) is not a proper scoring rule.

    Apply Yhat -> Yhat^gamma elementwise for a sweep of gamma > 0. Since x -> x^gamma
    is strictly increasing on [0,1], it preserves the rank of every entry within any
    row and within any column, so AUC_j and nDCG_j^class -- which depend only on
    ranks -- must be EXACTLY unchanged for every gamma. Brier score and MAE, which
    depend on the actual values, are not: Brier (strictly proper) should be
    minimised at gamma=1 (the untouched, calibrated probabilities); MAE (not
    proper) need not be.
    """
    print("\n--- Exp 7: Properness -- order-preserving distortion ---")
    Yhat0 = probas["LR"]
    gammas = np.sort(np.unique(np.concatenate([np.geomspace(0.2, 5.0, 24), [1.0]])))

    auc_macro_g, ndcg_macro_g, bs_macro_g, mae_macro_g = [], [], [], []
    for g in gammas:
        Yhat_g = Yhat0 ** g
        auc_macro_g.append(float(np.nanmean(auc_class(Y_te, Yhat_g))))
        ndcg_macro_g.append(float(ndcg_class(Y_te, Yhat_g).mean()))
        bs_macro_g.append(float(brier_class(Y_te, Yhat_g).mean()))
        mae_macro_g.append(float(mae_class(Y_te, Yhat_g).mean()))

    auc_macro_g = np.array(auc_macro_g)
    ndcg_macro_g = np.array(ndcg_macro_g)
    bs_macro_g = np.array(bs_macro_g)
    mae_macro_g = np.array(mae_macro_g)

    i1 = int(np.argmin(np.abs(gammas - 1.0)))
    ibs = int(np.argmin(bs_macro_g))
    imae = int(np.argmin(mae_macro_g))
    _save("exp4_properness_distortion", pd.DataFrame({
        "gamma": gammas, "macro_AUC": auc_macro_g, "macro_nDCG_class": ndcg_macro_g,
        "macro_Brier": np.array(bs_macro_g), "macro_MAE": mae_macro_g}))
    print(f"  macro-AUC   spread over gamma in [{gammas.min():.2f},{gammas.max():.2f}]: "
          f"{auc_macro_g.max() - auc_macro_g.min():.2e} "
          f"(values [{auc_macro_g.min():.6f}, {auc_macro_g.max():.6f}])")
    print(f"  macro-nDCG  spread: {ndcg_macro_g.max() - ndcg_macro_g.min():.2e} "
          f"(values [{ndcg_macro_g.min():.6f}, {ndcg_macro_g.max():.6f}])")
    print(f"  macro-Brier: minimum at gamma={gammas[ibs]:.3f} (value {bs_macro_g[ibs]:.4f}); "
          f"gamma=1.0 value {bs_macro_g[i1]:.4f} "
          f"({'coincide' if ibs == i1 else 'DO NOT coincide'})")
    print(f"  macro-MAE:   minimum at gamma={gammas[imae]:.3f} (value {mae_macro_g[imae]:.4f}); "
          f"gamma=1.0 value {mae_macro_g[i1]:.4f} "
          f"({'coincide' if imae == i1 else 'DO NOT coincide'})")

    fig, axes = plt.subplots(1, 3, figsize=(15, 4))

    ax = axes[0]
    ax.plot(gammas, auc_macro_g, "o-", color=COLORS["rank"], label="macro-AUC", linewidth=2)
    ax.plot(gammas, ndcg_macro_g, "s--", color=COLORS["extra"], label="macro-nDCG", linewidth=2)
    ax.axvline(1.0, color="gray", ls=":", lw=1)
    ax.set_xlabel(r"distortion exponent $\gamma$ ($\hat{P}\to\hat{P}^{\gamma}$)")
    ax.set_ylabel("score (higher = better)")
    ax.set_title("(a) Ranking measures: exactly flat\n[order-preserving, not strictly proper]",
                 fontsize=9)
    ax.legend(fontsize=8)

    ax = axes[1]
    ax.plot(gammas, bs_macro_g, "D-", color=COLORS["cal"], linewidth=2)
    ax.axvline(1.0, color="gray", ls=":", lw=1, label=r"$\gamma=1$ (untouched)")
    ax.axvline(gammas[ibs], color="black", ls="--", lw=1,
               label=f"minimum ($\\gamma={gammas[ibs]:.2f}$)")
    ax.set_xlabel(r"distortion exponent $\gamma$")
    ax.set_ylabel("macro-Brier score (lower = better)")
    ax.set_title("(b) Brier score penalises the distortion\n[strictly proper scoring rule]",
                 fontsize=9)
    ax.legend(fontsize=8)

    ax = axes[2]
    ax.plot(gammas, mae_macro_g, "v-", color=COLORS["disc"], linewidth=2)
    ax.axvline(1.0, color="gray", ls=":", lw=1, label=r"$\gamma=1$ (untouched)")
    ax.axvline(gammas[imae], color="black", ls="--", lw=1,
               label=f"minimum ($\\gamma={gammas[imae]:.2f}$)")
    ax.set_xlabel(r"distortion exponent $\gamma$")
    ax.set_ylabel("macro-MAE (lower = better)")
    ax.set_title("(c) MAE minimised away from $\\gamma=1$\n[not a proper scoring rule]", fontsize=9)
    ax.legend(fontsize=8)

    plt.tight_layout()
    path = os.path.join(OUT_DIR, "exp7_properness_distortion.pdf")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved {path}")


# ═════════════════════════════════════════════════════════════════════════════
# Supplementary: Collapse table (for LaTeX)
# ═════════════════════════════════════════════════════════════════════════════

def tie_sensitivity(Y_te, probas, tag):
    """Macro-nDCG^class and macro-AUC under different tie conventions.

    metrics.py ranks with np.argsort (ties in a row broken by label index) and AUC with
    sklearn (ties count 1/2). The paper's Definition of the rank is min-rank and its concordance
    fraction counts ties as 0. Random forests output many tied scores, so the conventions differ.
    """
    from scipy.stats import rankdata
    n, m = Y_te.shape
    w1 = 1.0
    pi = Y_te.mean(axis=0)

    def ndcg_from_ranks(R):
        W = 1.0 / np.log2(R + 1.0)
        return (Y_te * W).sum(axis=0) / n / (pi * w1)

    rows = []
    rng = np.random.default_rng(SEED)
    for name, P in probas.items():
        code = float(np.mean(ndcg_class(Y_te, P)))
        minr = float(np.mean(ndcg_from_ranks(rankdata(-P, method="min", axis=1))))
        rnd = float(np.mean([np.mean(ndcg_from_ranks(
            rankdata(-(P + rng.uniform(0, 1e-9, size=P.shape)), method="min", axis=1)))
            for _ in range(20)]))
        auc_sk = float(np.nanmean(auc_class(Y_te, P)))
        strict = []
        for j in range(m):
            pos, neg = P[Y_te[:, j] == 1, j], P[Y_te[:, j] == 0, j]
            strict.append(np.nan if len(pos) == 0 or len(neg) == 0
                          else float(np.mean(pos[:, None] > neg[None, :])))
        ties_rows = int(np.sum([len(set(r)) < len(r) for r in P]))
        ties_cols = int(np.sum([len(set(P[:, j])) < n for j in range(m)]))
        rows.append({"classifier": name, "macro_nDCG_code": code, "macro_nDCG_minrank": minr,
                     "macro_nDCG_random_ties": rnd, "macro_AUC_sklearn": auc_sk,
                     "macro_AUC_strict": float(np.nanmean(strict)),
                     "rows_with_ties": ties_rows, "columns_with_ties": ties_cols})
    # Oracle ceiling: scores equal to the labels (random tie-breaks); nDCG_j^class = 1 is not
    # attainable for all labels at once when examples have several relevant labels.
    orc = float(np.mean([np.mean(ndcg_from_ranks(rankdata(
        -(Y_te + rng.uniform(0, 1e-6, size=Y_te.shape)), method="min", axis=1)))
        for _ in range(20)]))
    rows.append({"classifier": "oracle (scores = labels)", "macro_nDCG_code": np.nan,
                 "macro_nDCG_minrank": np.nan, "macro_nDCG_random_ties": orc,
                 "macro_AUC_sklearn": 1.0, "macro_AUC_strict": np.nan,
                 "rows_with_ties": np.nan, "columns_with_ties": np.nan})
    _save(f"tie_sensitivity_{tag}", pd.DataFrame(rows).set_index("classifier"))


def print_collapse_table(Y_te, probas):
    """Print a LaTeX-ready table for the collapse theorem verification."""
    print("\n--- Supplementary: Collapse table ---")
    rows = []
    for name, Yhat in probas.items():
        rows.append({
            "Classifier": name,
            "BS micro":    brier_micro(Y_te, Yhat),
            "BS macro":    brier_macro(Y_te, Yhat),
            "BS exemplar": brier_exemplar(Y_te, Yhat),
            "nDCG micro":    ndcg_micro(Y_te, Yhat),
            "nDCG macro":    float(ndcg_class(Y_te, Yhat).mean()),
            "nDCG exemplar": float(ndcg_exemplar(Y_te, Yhat).mean()),
        })
    df = pd.DataFrame(rows).set_index("Classifier")
    print(df.round(4).to_string())


# ═════════════════════════════════════════════════════════════════════════════
# Main
# ═════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("=" * 60)
    print("Experiments for the Generalised Confusion Matrix paper")
    print("=" * 60)

    # ── Experiments 1–3: Emotions (small, 6 labels) ───────────────────────────
    print("\n[Dataset: Emotions — Experiments 1–3]")
    X_tr, X_te, Y_tr, Y_te, emo_labels = load_emotions()
    n_tr, n_te, m = X_tr.shape[0], X_te.shape[0], Y_te.shape[1]
    print(f"  Train: {n_tr}  Test: {n_te}  Labels: {m}")
    print(f"  Label names: {emo_labels}")
    print(f"  Mean class prevalence: {Y_te.mean(axis=0).round(3)}")

    print("\nTraining classifiers ...")
    probas, hards = train_all(X_tr, X_te, Y_tr, Y_te)

    exp1_ranking_disagreement(Y_te, probas, hards)
    exp2_collapse(Y_te, probas)
    exp3_skew_invariance(X_tr, X_te, Y_tr, Y_te, label_names=emo_labels)
    exp7_properness_distortion(Y_te, probas)
    print_collapse_table(Y_te, probas)
    tie_sensitivity(Y_te, probas, "emotions")

    # ── Experiment 4: Yeast (14 labels — richer heatmap) ─────────────────────
    print("\n[Dataset: Yeast — Experiment 4]")
    X_tr4, X_te4, Y_tr4, Y_te4, yeast_labels = load_yeast()
    n_tr4, n_te4, m4 = X_tr4.shape[0], X_te4.shape[0], Y_te4.shape[1]
    print(f"  Train: {n_tr4}  Test: {n_te4}  Labels: {m4}")
    print(f"  Label names: {yeast_labels}")
    print(f"  Mean class prevalence: {Y_te4.mean(axis=0).round(3)}")

    print("\nTraining classifiers (Yeast) ...")
    probas4, hards4 = train_all(X_tr4, X_te4, Y_tr4, Y_te4)

    tie_sensitivity(Y_te4, probas4, "yeast")
    exp4_murphy_heatmap(Y_te4, probas4, label_names=yeast_labels)
    exp5_exemplar_decomposition(Y_te, probas, Y_te4, probas4)
    exp6_ndcg_class_novel(Y_te4, probas4, label_names=yeast_labels, Y_tr=Y_tr4)

    print(f"\nAll figures saved to: {OUT_DIR}/")
    print("Done.")

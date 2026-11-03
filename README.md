# Discrimination, Calibration, and Ranking: Lean proofs and experiments

Code accompanying *Discrimination, Calibration, and Ranking: A Unified Matrix Framework*
(R. C. Prati and F. Johari). The measures are implemented in the
[aggmetrics](https://github.com/rcprati/aggmetrics) package.

| Directory | Contents |
|---|---|
| `lean/` | Lean 4 / Mathlib formalisation of the theorems of the paper |
| `experiments/` | Python scripts, the numbers behind every figure (`data/`) and the figures (`figs/`) |

## Lean

Toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (pinned in `lean/lake-manifest.json`).

```bash
cd lean
lake exe cache get   # prebuilt Mathlib
lake build
```

Statements are grouped by paper section:

| Topic | Files |
|---|---|
| Base results (indicator matrices, aggregation operators) | `Basic`, `Mixture`, `TNorm` |
| Calibration: Brier collapse, class-conditional errors, Murphy decomposition, Savage representation | `Calibration`, `Savage`, `CalSkew`, `MurphySkew` |
| Ranking: DCG collapse, nDCG and AUC aggregation, duality, properness, AUC ties | `Ranking`, `AUCTies` |
| Worked examples of the background section | `BackgroundExamples` |

Scope notes. The ranks in the hard-prediction remark are an abstract rank function. The
perturbation to distinct marginals in the dependent-AUC counterexample is proved on paper only. The
isotonic (CORP) terms and the numerical running example are not formalised. Where a Lean
statement is narrower than its counterpart in the paper, the paper states the restriction.

## Experiments

```bash
cd experiments
pip install -r requirements.txt
python run_experiments.py        # Experiments 1-7; downloads Emotions and Yeast from OpenML
python running_example.py        # six-part running example -> data/running_example.json
python pooled_vs_micro_auc.py    # pooled ROC-AUC against micro-AUC -> data/pooled_vs_micro_auc.csv
python exp_isotonic_murphy.py    # isotonic Murphy terms (needs aggmetrics >= 0.3)
```

| Result in the paper | Command (in `experiments/`) | Output |
|---|---|---|
| Experiments 1 to 7 (Section 8), including the tie-sensitivity values quoted in Sections 8.1 and 8.2 | `python run_experiments.py` | `figs/exp*.pdf`, `data/exp*.csv`, `data/tie_sensitivity_{emotions,yeast}.csv` |
| Six-part running example (Section 2 and Appendix A) | `python running_example.py` | `data/running_example.json` |
| Pooled ROC-AUC against micro-AUC (Section 6.10) | `python pooled_vs_micro_auc.py` | `data/pooled_vs_micro_auc.csv` |
| Dependent-label AUC counterexample search (Proposition on AUC properness) | `python auc_dependence_search.py` | counts printed to the terminal |
| Isotonic Murphy terms (Section 8.6) | `python exp_isotonic_murphy.py` (aggmetrics >= 0.3) | `data/exp5b_isotonic_murphy.csv` |

Runtimes on an Apple M3 (8 cores, 8 GB), Python 3.13.9, scikit-learn 1.7.2, NumPy 2.5.2, SciPy 1.16.3,
pandas 2.3.3, matplotlib 3.10.6: `run_experiments.py` about 100 s, `exp_isotonic_murphy.py` about 85 s, the
other scripts a few seconds. Rerunning them on 3 November 2026 regenerated every CSV in `data/`
identically to the stored files (maximum absolute difference 0).

`metrics.py` holds independent numpy implementations of every measure used, so the experiments
do not depend on the package. Figures are written to `figs/` and the underlying numbers to `data/`.

## Citation

See `CITATION.cff`. Code is released under the BSD 3-Clause licence.

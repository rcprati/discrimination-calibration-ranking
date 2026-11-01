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

`metrics.py` holds independent numpy implementations of every measure used, so the experiments
do not depend on the package. Figures are written to `figs/` and the underlying numbers to `data/`.

## Citation

See `CITATION.cff`. Code is released under the BSD 3-Clause licence.

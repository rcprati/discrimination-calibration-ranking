import Mathlib

/-!
# Worked examples for the background section

Formalization of the two Section 2 examples of the paper on generalised confusion matrices
(`future_generalised_confusion`), now in its Appendix B.

* `squared_recall_micro`, `squared_recall_weighted`, `squared_recall_not_decomposable` — Theorem
  ("Micro = denominator-weighted macro") needs additive numerators and denominators: for
  `M = recall²` and the count vectors `v₁ = (1,0,1,2)`, `v₂ = (3,0,1,0)` (order `tp, fp, fn, tn`),
  pooling gives `4/9` while the denominator-weighted mean of the per-label values gives `1/2`.
* `micro_ba_cancellation`, `pooled_recall_varies`, `micro_ba_invariant_without_equal_rates` —
  Corollary ("Macro- and micro-averaging under skew"): equal per-class rates are sufficient but not
  necessary for micro skew-invariance. With two mutually exclusive labels of prevalences `p`,
  `1 − p` and class rates `rec₁ = spec₁ = c`, `rec₂ = spec₂ = d`, the pooled recall and
  specificity are `p c + (1 − p) d` and `(1 − p) c + p d`; their mean (micro balanced accuracy) is
  `(c + d)/2` for every `p`, although the pooled recall changes with `p` whenever `c ≠ d`.
-/

namespace Aggmetrics.BackgroundExamples

/-- Pooled squared recall: `((1 + 3)/((1 + 1) + (3 + 1)))² = 4/9`. -/
theorem squared_recall_micro : ((1 + 3 : ℝ) / ((1 + 1) + (3 + 1))) ^ 2 = 4 / 9 := by norm_num

/-- Denominator-weighted mean of the per-label squared recalls `1/4` and `9/16`, with the
denominators `(tp + fn)² = 4` and `16`: `(4 · 1/4 + 16 · 9/16)/(4 + 16) = 1/2`. -/
theorem squared_recall_weighted :
    ((2 : ℝ) ^ 2 * ((1 : ℝ) / 2) ^ 2 + (4 : ℝ) ^ 2 * ((3 : ℝ) / 4) ^ 2)
        / ((2 : ℝ) ^ 2 + (4 : ℝ) ^ 2) = 1 / 2 := by norm_num

theorem squared_recall_not_decomposable :
    ((1 + 3 : ℝ) / ((1 + 1) + (3 + 1))) ^ 2
      ≠ ((2 : ℝ) ^ 2 * ((1 : ℝ) / 2) ^ 2 + (4 : ℝ) ^ 2 * ((3 : ℝ) / 4) ^ 2)
          / ((2 : ℝ) ^ 2 + (4 : ℝ) ^ 2) := by
  rw [squared_recall_micro, squared_recall_weighted]; norm_num

/-- Micro balanced accuracy with positive-class weights `(p, 1 − p)` and negative-class weights
`(1 − p, p)` does not depend on `p`. -/
theorem micro_ba_cancellation (c d p : ℝ) :
    ((p * c + (1 - p) * d) + ((1 - p) * c + p * d)) / 2 = (c + d) / 2 := by ring

/-- The pooled recall itself changes with the prevalence when the class rates differ. -/
theorem pooled_recall_varies {c d p p' : ℝ} (hcd : c ≠ d) (hp : p ≠ p') :
    p * c + (1 - p) * d ≠ p' * c + (1 - p') * d := by
  intro h
  have : (p - p') * (c - d) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact hp (sub_eq_zero.mp h')
  · exact hcd (sub_eq_zero.mp h')

/-- Equal per-class rates are not necessary for micro skew-invariance: with `c = 0.9`, `d = 0.1`
the micro balanced accuracy is `1/2` at every prevalence, while the pooled recall is `0.3` at
`p = 1/4` and `0.7` at `p = 3/4`. -/
theorem micro_ba_invariant_without_equal_rates :
    (∀ p : ℝ, ((p * (9 / 10) + (1 - p) * (1 / 10)) + ((1 - p) * (9 / 10) + p * (1 / 10))) / 2
        = 1 / 2)
      ∧ (1 / 4 : ℝ) * (9 / 10) + (1 - 1 / 4) * (1 / 10) = 3 / 10
      ∧ (3 / 4 : ℝ) * (9 / 10) + (1 - 3 / 4) * (1 / 10) = 7 / 10 := by
  refine ⟨fun p => ?_, by norm_num, by norm_num⟩
  rw [micro_ba_cancellation]; norm_num

end Aggmetrics.BackgroundExamples

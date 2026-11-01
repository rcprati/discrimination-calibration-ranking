import Mathlib

/-!
# Skew-sensitivity of the Murphy terms

Formalization of Corollary ("Skew-sensitivity of Murphy terms") of Section 4 of the paper on
generalised confusion matrices (`future_generalised_confusion`).

Model. For one class, `a`, `b : Fin s → ℝ` are the probability distributions of the `s` score bins
on the positive and on the negative examples, and the prevalence `π` mixes them: the bin `p` has
probability `P(p) = π a_p + (1 − π) b_p`, calibration map `f(p) = π a_p / P(p)` (Bayes' rule), and
`v p` is the predicted value attached to the bin.

* `unc_not_const` — part (a): `UNC = π (1 − π)` depends on the prevalence alone.
* `res_closed`, `res_pos_of_ne`, `res_eq_zero_of_eq`, `res_le_unc`, `res_not_const` — part (b): the
  resolution term has the exact form
  `RES(π) = π² (1 − π)² ∑_p (a_p − b_p)² / (π a_p + (1 − π) b_p)`, so `RES ≡ 0` iff `a = b` and
  `RES > 0` on `(0,1)` otherwise; since `RES ≤ UNC = π (1 − π)` vanishes at the endpoints, `RES` is
  then not constant in `π`. This replaces the Jensen argument of the paper by an exact formula.
* `rel_eq_zero_iff`, `rel_zero_two_prevalences`, `rel_zero_of_extreme`, `calibration_survives_iff` —
  part (c), exact form: a classifier is perfectly calibrated (`REL = 0`) at two different
  prevalences iff every predicted value is attained by one class alone and equals `1` (positives
  only) or `0` (negatives only). The concrete witness is in `Aggmetrics.Calibration`
  (`rel_calibrated`, `rel_after_skew`).
* `rel_separated`, `rel_separated_invariant_iff` — the corollary's closing sentence on degenerate
  exceptions: if every predicted value is attained by one class alone, `REL = π α + (1 − π) β`, which
  takes equal values at two prevalences iff `α = β`.
-/

namespace Aggmetrics.MurphySkew

variable {s : ℕ}

/-- Probability of the predicted value `p` when the positive class has weight `π`:
`π a_p + (1 − π) b_p`, where `a`, `b` are the score distributions on the positives and negatives. -/
def mix (a b : Fin s → ℝ) (π : ℝ) (p : Fin s) : ℝ := π * a p + (1 - π) * b p

/-- The resolution term `RES = ∑_p P(p) (f(p) − π)²` with `f(p) = π a_p / P(p)` the calibration map. -/
noncomputable def res (a b : Fin s → ℝ) (π : ℝ) : ℝ :=
  ∑ p, mix a b π p * (π * a p / mix a b π p - π) ^ 2

theorem res_term (a b : Fin s → ℝ) (π : ℝ) (p : Fin s) (h : 0 < mix a b π p) :
    mix a b π p * (π * a p / mix a b π p - π) ^ 2
      = π ^ 2 * (1 - π) ^ 2 * ((a p - b p) ^ 2 / mix a b π p) := by
  have hm := h.ne'
  unfold mix at hm h ⊢
  field_simp
  ring

/-- Exact form of the resolution term: `RES(π) = π² (1 − π)² ∑_p (a_p − b_p)² / (π a_p + (1 − π) b_p)`. -/
theorem res_closed (a b : Fin s → ℝ) (π : ℝ) (h : ∀ p, 0 < mix a b π p) :
    res a b π = π ^ 2 * (1 - π) ^ 2 * ∑ p, (a p - b p) ^ 2 / mix a b π p := by
  unfold res
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => res_term a b π p (h p))

theorem mix_pos (a b : Fin s → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (hab : ∀ p, 0 < a p + b p) {π : ℝ} (h0 : 0 < π) (h1 : π < 1) (p : Fin s) :
    0 < mix a b π p := by
  unfold mix
  have hm : 0 < min π (1 - π) := lt_min h0 (by linarith)
  have e1 : min π (1 - π) * a p ≤ π * a p :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (ha p)
  have e2 : min π (1 - π) * b p ≤ (1 - π) * b p :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (hb p)
  nlinarith [mul_pos hm (hab p)]

/-- `RES` vanishes identically iff the score distributions on positives and negatives coincide, and is
strictly positive otherwise (for every prevalence in `(0,1)`). -/
theorem res_pos_of_ne (a b : Fin s → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (hab : ∀ p, 0 < a p + b p) {π : ℝ} (h0 : 0 < π) (h1 : π < 1) (hne : ∃ p, a p ≠ b p) :
    0 < res a b π := by
  rw [res_closed a b π (mix_pos a b ha hb hab h0 h1)]
  have hpi : 0 < π ^ 2 * (1 - π) ^ 2 := by
    have : 0 < 1 - π := by linarith
    positivity
  refine mul_pos hpi ?_
  obtain ⟨q, hq⟩ := hne
  refine Finset.sum_pos' (fun p _ => ?_) ⟨q, Finset.mem_univ q, ?_⟩
  · exact div_nonneg (sq_nonneg _) (mix_pos a b ha hb hab h0 h1 p).le
  · exact div_pos (by positivity) (mix_pos a b ha hb hab h0 h1 q)

theorem res_eq_zero_of_eq (a b : Fin s → ℝ) (π : ℝ) (h : ∀ p, a p = b p) : res a b π = 0 := by
  unfold res
  refine Finset.sum_eq_zero (fun p _ => ?_)
  have hm : mix a b π p = a p := by unfold mix; rw [← h p]; ring
  rw [hm]
  by_cases hz : a p = 0
  · simp [hz]
  · have : π * a p / a p = π := by field_simp
    rw [this]; ring

/-- `RES ≤ UNC = π (1 − π)`. -/
theorem res_le_unc (a b : Fin s → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (hab : ∀ p, 0 < a p + b p) (hsa : ∑ p, a p = 1) (hsb : ∑ p, b p = 1) {π : ℝ} (h0 : 0 < π)
    (h1 : π < 1) : res a b π ≤ π * (1 - π) := by
  have hmp := mix_pos a b ha hb hab h0 h1
  have key : ∀ p, mix a b π p * (π * a p / mix a b π p - π) ^ 2
      ≤ π * a p - 2 * π * (π * a p) + π ^ 2 * mix a b π p := by
    intro p
    have hm := hmp p
    have e : mix a b π p * (π * a p / mix a b π p - π) ^ 2
        = (π * a p) ^ 2 / mix a b π p - 2 * π * (π * a p) + π ^ 2 * mix a b π p := by
      field_simp
      ring
    rw [e]
    have hle : π * a p ≤ mix a b π p := by
      unfold mix
      nlinarith [mul_nonneg (sub_nonneg.2 h1.le) (hb p)]
    have : (π * a p) ^ 2 / mix a b π p ≤ π * a p := by
      rw [div_le_iff₀ hm]
      nlinarith [mul_nonneg h0.le (ha p)]
    linarith
  calc res a b π ≤ ∑ p, (π * a p - 2 * π * (π * a p) + π ^ 2 * mix a b π p) :=
        Finset.sum_le_sum (fun p _ => key p)
    _ = π * (∑ p, a p) - 2 * π * (π * ∑ p, a p) + π ^ 2 * ∑ p, mix a b π p := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
    _ = π * (1 - π) := by
        have hsm : ∑ p, mix a b π p = 1 := by
          unfold mix
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsa, hsb]
          ring
        rw [hsm, hsa]; ring

/-- Theorem ("Skew-sensitivity of Murphy terms"), part (b): the resolution term is skew-sensitive
exactly when the score distributions on positives and negatives differ: it then takes different
values at two prevalences, since it is positive at `π = 1/2` but bounded by `π (1 − π)`. -/
theorem res_not_const (a b : Fin s → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (hab : ∀ p, 0 < a p + b p) (hsa : ∑ p, a p = 1) (hsb : ∑ p, b p = 1)
    (hne : ∃ p, a p ≠ b p) :
    ∃ π π' : ℝ, 0 < π ∧ π < 1 ∧ 0 < π' ∧ π' < 1 ∧ res a b π ≠ res a b π' := by
  have hc : 0 < res a b (1 / 2) := res_pos_of_ne a b ha hb hab (by norm_num) (by norm_num) hne
  set c := res a b (1 / 2) with hc_def
  have h0 : 0 < min (1 / 4) (c / 2) := lt_min (by norm_num) (by linarith)
  have h1 : min (1 / 4) (c / 2) < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨min (1 / 4) (c / 2), 1 / 2, h0, h1, by norm_num, by norm_num, ?_⟩
  have hle := res_le_unc a b ha hb hab hsa hsb h0 h1
  have hm : min (1 / 4) (c / 2) ≤ c / 2 := min_le_right _ _
  intro heq
  nlinarith [mul_pos h0 h0]

/-- Part (a): `UNC = π (1 − π)` is skew-sensitive (it depends on the prevalence alone). -/
theorem unc_not_const : ∃ π π' : ℝ, 0 < π ∧ π < 1 ∧ 0 < π' ∧ π' < 1 ∧ π * (1 - π) ≠ π' * (1 - π') :=
  ⟨1 / 2, 1 / 4, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The reliability term at prevalence `π`, with `v p` the predicted value attached to the score bin `p`
and `f(p) = π a_p / P(p)` the calibration map. -/
noncomputable def rel (a b v : Fin s → ℝ) (π : ℝ) : ℝ :=
  ∑ p, mix a b π p * (v p - π * a p / mix a b π p) ^ 2

theorem rel_eq_zero_iff (a b v : Fin s → ℝ) (π : ℝ) (h : ∀ p, 0 < mix a b π p) :
    rel a b v π = 0 ↔ ∀ p, v p = π * a p / mix a b π p := by
  unfold rel
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => mul_nonneg (h p).le (sq_nonneg _))]
  constructor
  · intro H p
    have h0 := H p (Finset.mem_univ p)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (h p).ne'
    · have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      linarith
  · intro H p _
    simp [H p]

/-- A classifier calibrated at two different prevalences: every predicted value must be attained by
one class alone, and equal `1` if by positives only, `0` if by negatives only. -/
theorem rel_zero_two_prevalences (a b v : Fin s → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (hab : ∀ p, 0 < a p + b p) {π π' : ℝ} (h0 : 0 < π) (h1 : π < 1) (h0' : 0 < π')
    (h1' : π' < 1) (hne : π ≠ π') (hr : rel a b v π = 0) (hr' : rel a b v π' = 0) :
    ∀ p, (b p = 0 ∧ v p = 1) ∨ (a p = 0 ∧ v p = 0) := by
  intro p
  have e1 := (rel_eq_zero_iff a b v π (mix_pos a b ha hb hab h0 h1)).mp hr p
  have e2 := (rel_eq_zero_iff a b v π' (mix_pos a b ha hb hab h0' h1')).mp hr' p
  have hm := mix_pos a b ha hb hab h0 h1 p
  have hm' := mix_pos a b ha hb hab h0' h1' p
  rcases (ha p).eq_or_lt with hA | hA
  · right
    refine ⟨hA.symm, ?_⟩
    rw [e1, ← hA]; simp
  · rcases (hb p).eq_or_lt with hB | hB
    · left
      refine ⟨hB.symm, ?_⟩
      rw [e1]
      unfold mix
      rw [← hB, mul_zero, add_zero]
      exact div_self (mul_pos h0 hA).ne'
    · exfalso
      have heq : π * a p / mix a b π p = π' * a p / mix a b π' p := e1.symm.trans e2
      rw [div_eq_div_iff hm.ne' hm'.ne'] at heq
      unfold mix at heq
      have : a p * b p * (π - π') = 0 := by linear_combination heq
      rcases mul_eq_zero.mp this with h | h
      · exact (mul_pos hA hB).ne' h
      · exact hne (by linarith)

theorem rel_zero_of_extreme (a b v : Fin s → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (hab : ∀ p, 0 < a p + b p) (hext : ∀ p, (b p = 0 ∧ v p = 1) ∨ (a p = 0 ∧ v p = 0)) {π : ℝ}
    (h0 : 0 < π) (h1 : π < 1) : rel a b v π = 0 := by
  rw [rel_eq_zero_iff a b v π (mix_pos a b ha hb hab h0 h1)]
  intro p
  rcases hext p with ⟨hB, hv⟩ | ⟨hA, hv⟩
  · have hA : 0 < a p := by have := hab p; rw [hB] at this; linarith
    rw [hv]
    unfold mix
    rw [hB, mul_zero, add_zero, div_self (mul_pos h0 hA).ne']
  · rw [hv]
    unfold mix
    rw [hA]
    simp

/-- Theorem ("Skew-sensitivity of Murphy terms"), part (c): perfect calibration (`REL = 0`) survives a
change of prevalence iff every predicted value is attained by one class alone and equals `1` (positives
only) or `0` (negatives only). -/
theorem calibration_survives_iff (a b v : Fin s → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (hab : ∀ p, 0 < a p + b p) :
    (∃ π π' : ℝ, 0 < π ∧ π < 1 ∧ 0 < π' ∧ π' < 1 ∧ π ≠ π' ∧ rel a b v π = 0 ∧ rel a b v π' = 0)
      ↔ ∀ p, (b p = 0 ∧ v p = 1) ∨ (a p = 0 ∧ v p = 0) := by
  constructor
  · rintro ⟨π, π', h0, h1, h0', h1', hne, hr, hr'⟩
    exact rel_zero_two_prevalences a b v ha hb hab h0 h1 h0' h1' hne hr hr'
  · intro hext
    exact ⟨1 / 3, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      rel_zero_of_extreme a b v ha hb hab hext (by norm_num) (by norm_num),
      rel_zero_of_extreme a b v ha hb hab hext (by norm_num) (by norm_num)⟩

/-- Class-conditional squared errors in the bin model: `α = E[(1 − v)² | Y = 1]`,
`β = E[v² | Y = 0]`. -/
def alphaBin (a v : Fin s → ℝ) : ℝ := ∑ p, a p * (1 - v p) ^ 2

def betaBin (b v : Fin s → ℝ) : ℝ := ∑ p, b p * v p ^ 2

/-- Closing sentence of the corollary ("Skew-sensitivity of Murphy terms"): when every predicted
value is attained by one class alone, the calibration map is `1` on the positive bins and `0` on the
negative ones, so `REL = π α + (1 − π) β`. -/
theorem rel_separated (a b v : Fin s → ℝ) (hab : ∀ p, 0 < a p + b p)
    (hsep : ∀ p, a p = 0 ∨ b p = 0) {π : ℝ} (h0 : 0 < π) (h1 : π < 1) :
    rel a b v π = π * alphaBin a v + (1 - π) * betaBin b v := by
  unfold rel alphaBin betaBin
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rcases hsep p with hA | hB
  · have hb : 0 < b p := by have := hab p; rw [hA] at this; linarith
    have hm : mix a b π p = (1 - π) * b p := by unfold mix; rw [hA]; ring
    rw [hm, hA]
    simp
    ring
  · have ha : 0 < a p := by have := hab p; rw [hB] at this; linarith
    have hm : mix a b π p = π * a p := by unfold mix; rw [hB]; ring
    rw [hm, hB, div_self (mul_pos h0 ha).ne']
    ring

/-- In the separated case, `REL` takes the same value at two different prevalences iff `α = β`;
it is then constant in `π`. -/
theorem rel_separated_invariant_iff (a b v : Fin s → ℝ) (hab : ∀ p, 0 < a p + b p)
    (hsep : ∀ p, a p = 0 ∨ b p = 0) {π π' : ℝ} (h0 : 0 < π) (h1 : π < 1) (h0' : 0 < π')
    (h1' : π' < 1) (hne : π ≠ π') :
    rel a b v π = rel a b v π' ↔ alphaBin a v = betaBin b v := by
  rw [rel_separated a b v hab hsep h0 h1, rel_separated a b v hab hsep h0' h1']
  constructor
  · intro h
    have : (π - π') * (alphaBin a v - betaBin b v) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hne
    · exact sub_eq_zero.mp h'
  · intro h
    rw [h]; ring

end Aggmetrics.MurphySkew

import Mathlib

/-!
# Formalization of two core theorems from

Prati, R. C. (2027). *A unified algebraic framework for classification
performance evaluation*. Information Fusion, 138, 104767.

Two of the paper's most load-bearing results (cited by every sibling paper in the
project family) are formalized here:

* `micro_eq_macro_iff` — Theorem 1 ("Micro = denominator-weighted macro").
* `skew_invariant_iff_factors_through_recall_specificity` — the skew-invariance
  characterisation theorem.
-/

open Finset

namespace Aggmetrics

/-- **Micro = denominator-weighted macro.**

For per-class denominators `den : Fin m → ℝ` (all positive), pooling numerators and
denominators globally before dividing (`micro`) equals averaging the per-class ratios
(`macro`), *for every choice of per-class numerators*, if and only if all per-class
denominators are equal. -/
theorem micro_eq_macro_iff {m : ℕ} (hm : 0 < m) (den : Fin m → ℝ) (hden : ∀ j, 0 < den j) :
    (∀ num : Fin m → ℝ,
      (∑ j, num j) / (∑ j, den j) = (1 / (m : ℝ)) * ∑ j, num j / den j)
    ↔ (∀ i j, den i = den j) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hne : (univ : Finset (Fin m)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  have key : ∀ p : Fin m, (∑ k, (if k = p then (1:ℝ) else 0) / den k) = 1 / den p := by
    intro p
    have hcongr : ∀ k, (if k = p then (1:ℝ) else 0) / den k = if k = p then 1 / den p else 0 := by
      intro k; split <;> simp_all
    rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
    simp
  constructor
  · intro h i j
    have hi := h (fun k => if k = i then 1 else 0)
    have hj := h (fun k => if k = j then 1 else 0)
    simp only [Finset.sum_ite_eq' univ, mem_univ, ite_true] at hi hj
    rw [key i] at hi
    rw [key j] at hj
    have heq1 : (1:ℝ)/(m:ℝ) * (1/den i) = 1/(m:ℝ) * (1/den j) := hi.symm.trans hj
    have hm0 : (1:ℝ)/(m:ℝ) ≠ 0 := by positivity
    have heq2 : (1:ℝ)/den i = 1/den j := mul_left_cancel₀ hm0 heq1
    field_simp [(hden i).ne', (hden j).ne'] at heq2
    linarith [heq2]
  · intro h num
    obtain ⟨i0, -⟩ := hne
    have hconst : ∀ j, den j = den i0 := fun j => h j i0
    have hdi0 : den i0 ≠ 0 := (hden i0).ne'
    simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
               ← Finset.sum_div]
    field_simp

/-- **Skew-invariance characterisation.**

A binary measure `M`, defined for all positive-margin cells `(tp, fp, fn, tn)`
(`tp + fn > 0`, `fp + tn > 0`), is *skew-invariant* — invariant to independently
rescaling the positive-class counts `(tp, fn)` by any `λ > 0` and the negative-class
counts `(fp, tn)` by any `μ > 0` — if and only if `M` factors through recall and
specificity alone: there exists `g : ℝ → ℝ → ℝ` with
`M tp fp fn tn = g (tp / (tp + fn)) (tn / (fp + tn))` everywhere on the domain. -/
theorem skew_invariant_iff_factors_through_recall_specificity
    (M : ℝ → ℝ → ℝ → ℝ → ℝ) :
    (∀ tp fp fn tn : ℝ, 0 < tp + fn → 0 < fp + tn →
      ∀ lam mu : ℝ, 0 < lam → 0 < mu →
        M (lam * tp) (mu * fp) (lam * fn) (mu * tn) = M tp fp fn tn)
    ↔
    (∃ g : ℝ → ℝ → ℝ, ∀ tp fp fn tn : ℝ, 0 < tp + fn → 0 < fp + tn →
      M tp fp fn tn = g (tp / (tp + fn)) (tn / (fp + tn))) := by
  constructor
  · intro hskew
    refine ⟨fun r s => M r (1 - s) (1 - r) s, ?_⟩
    intro tp fp fn tn htpfn hfptn
    have hlam : (0:ℝ) < 1 / (tp + fn) := by positivity
    have hmu : (0:ℝ) < 1 / (fp + tn) := by positivity
    have h := hskew tp fp fn tn htpfn hfptn (1 / (tp + fn)) (1 / (fp + tn)) hlam hmu
    have e1 : 1 / (tp + fn) * tp = tp / (tp + fn) := by ring
    have e2 : 1 / (tp + fn) * fn = 1 - tp / (tp + fn) := by
      field_simp [htpfn.ne']; ring
    have e3 : 1 / (fp + tn) * fp = 1 - tn / (fp + tn) := by
      field_simp [hfptn.ne']; ring
    have e4 : 1 / (fp + tn) * tn = tn / (fp + tn) := by ring
    rw [e1, e2, e3, e4] at h
    exact h.symm
  · rintro ⟨g, hg⟩ tp fp fn tn htpfn hfptn lam mu hlam hmu
    have htpfn' : 0 < lam * tp + lam * fn := by nlinarith [mul_pos hlam htpfn]
    have hfptn' : 0 < mu * fp + mu * tn := by nlinarith [mul_pos hmu hfptn]
    rw [hg (lam*tp) (mu*fp) (lam*fn) (mu*tn) htpfn' hfptn', hg tp fp fn tn htpfn hfptn]
    have hr : (lam * tp) / (lam * tp + lam * fn) = tp / (tp + fn) := by
      rw [show lam*tp+lam*fn = lam*(tp+fn) from by ring, mul_div_mul_left _ _ hlam.ne']
    have hs : (mu * tn) / (mu * fp + mu * tn) = tn / (fp + tn) := by
      rw [show mu*fp+mu*tn = mu*(fp+tn) from by ring, mul_div_mul_left _ _ hmu.ne']
    rw [hr, hs]

/-- **Weighted-ratio mixture identity** (always true, no skew-invariance needed): pooling
numerators and denominators and taking one ratio equals the prevalence-weighted average of
the per-class ratios, where class `j`'s weight is its own share `den j / ∑ k, den k` of the
total denominator. This is the "always-true" half underlying `micro_eq_macro_iff` above,
stated as its own reusable fact — the mechanism behind Corollary 5's micro-mixture formula
below. -/
theorem weighted_ratio_mixture {m : ℕ} (hm : 0 < m) (num den : Fin m → ℝ)
    (hden : ∀ j, 0 < den j) :
    (∑ j, num j) / (∑ j, den j) = ∑ j, (den j / ∑ k, den k) * (num j / den j) := by
  have hne : (univ : Finset (Fin m)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  have hS : (0:ℝ) < ∑ k, den k := Finset.sum_pos (fun k _ => hden k) hne
  have step : ∀ j, (den j / ∑ k, den k) * (num j / den j) = num j / ∑ k, den k := by
    intro j
    field_simp [(hden j).ne', hS.ne']
  rw [Finset.sum_congr rfl (fun j _ => step j), ← Finset.sum_div]

/-- **Corollary 5, part 2 (micro-averaging under skew): the mixture formula.**

For a skew-invariant measure `M = g ∘ (rec, spec)`, applied per class to give
`tp j, fp j, fn j, tn j`, the *pooled* (micro) recall and specificity fed to `g` are
exactly the prevalence-weighted averages of the per-class recall/specificity — `M^micro`
is `g` applied to a *mixture*, not to the per-class values directly. -/
theorem micro_skew_mixture {m : ℕ} (hm : 0 < m) (g : ℝ → ℝ → ℝ)
    (tp fp fn tn : Fin m → ℝ)
    (htpfn : ∀ j, 0 < tp j + fn j) (hfptn : ∀ j, 0 < fp j + tn j) :
    g ((∑ j, tp j) / (∑ j, (tp j + fn j))) ((∑ j, tn j) / (∑ j, (fp j + tn j)))
    = g (∑ j, ((tp j + fn j) / ∑ k, (tp k + fn k)) * (tp j / (tp j + fn j)))
        (∑ j, ((fp j + tn j) / ∑ k, (fp k + tn k)) * (tn j / (fp j + tn j))) := by
  rw [weighted_ratio_mixture hm tp (fun j => tp j + fn j) htpfn,
      weighted_ratio_mixture hm tn (fun j => fp j + tn j) hfptn]

/-- **Corollary 5's sensitivity boundary, made precise: equal per-class rates survive any
reweighting.** If every class has the *same* recall `r` and specificity `s`, the pooled
(micro) recall and specificity equal `r` and `s` too, for *any* positive per-class
denominators — `M^micro` is unaffected by class prevalence whenever the per-class rates
are equal. This is exactly the fact behind the collaborator's counterexample to the
unqualified, over-broad Corollary 8/10 in `papers/06-generalised-confusion/paper`: class
imbalance *alone* does not make a skew-invariant measure's micro-average
skew-*sensitive*. -/
theorem micro_invariant_under_equal_rates {m : ℕ} (hm : 0 < m)
    (tp fp fn tn : Fin m → ℝ) (r s : ℝ)
    (htpfn : ∀ j, 0 < tp j + fn j) (hfptn : ∀ j, 0 < fp j + tn j)
    (hrec : ∀ j, tp j / (tp j + fn j) = r) (hspec : ∀ j, tn j / (fp j + tn j) = s) :
    (∑ j, tp j) / (∑ j, (tp j + fn j)) = r ∧
    (∑ j, tn j) / (∑ j, (fp j + tn j)) = s := by
  have hne : (univ : Finset (Fin m)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  constructor
  · rw [weighted_ratio_mixture hm tp (fun j => tp j + fn j) htpfn]
    have hS : (∑ k : Fin m, (tp k + fn k)) ≠ 0 :=
      (Finset.sum_pos (fun k _ => htpfn k) hne).ne'
    simp only [hrec]
    rw [← Finset.sum_mul, ← Finset.sum_div, div_self hS, one_mul]
  · rw [weighted_ratio_mixture hm tn (fun j => fp j + tn j) hfptn]
    have hS : (∑ k : Fin m, (fp k + tn k)) ≠ 0 :=
      (Finset.sum_pos (fun k _ => hfptn k) hne).ne'
    simp only [hspec]
    rw [← Finset.sum_mul, ← Finset.sum_div, div_self hS, one_mul]

/-- **Proposition 7: exemplar-averaging's invariance boundary.**

Given population shares over label-configuration types and each type's conditional mean
`mbar`, the exemplar mixture `∑ τ, share τ * mbar τ` is invariant to the population shares
— for *every* pair of valid share distributions — if and only if `mbar` is constant across
types. -/
theorem exemplar_invariant_iff_constant_mbar {k : ℕ} (hk : 0 < k) (mbar : Fin k → ℝ) :
    (∀ share1 share2 : Fin k → ℝ,
      (∀ τ, 0 ≤ share1 τ) → (∑ τ, share1 τ = 1) →
      (∀ τ, 0 ≤ share2 τ) → (∑ τ, share2 τ = 1) →
      ∑ τ, share1 τ * mbar τ = ∑ τ, share2 τ * mbar τ)
    ↔ (∀ τ1 τ2, mbar τ1 = mbar τ2) := by
  constructor
  · intro h τ1 τ2
    have h1 := h (fun τ => if τ = τ1 then 1 else 0) (fun τ => if τ = τ2 then 1 else 0)
      (fun τ => by split <;> norm_num) (by simp)
      (fun τ => by split <;> norm_num) (by simp)
    simp only [mem_univ, ite_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq' univ] at h1
    convert h1 using 2
  · intro hconst share1 share2 hs1p hs1 hs2p hs2
    have e1 : ∀ τ, share1 τ * mbar τ = share1 τ * mbar ⟨0, hk⟩ := fun τ => by
      rw [hconst τ ⟨0, hk⟩]
    have e2 : ∀ τ, share2 τ * mbar τ = share2 τ * mbar ⟨0, hk⟩ := fun τ => by
      rw [hconst τ ⟨0, hk⟩]
    rw [Finset.sum_congr rfl (fun τ _ => e1 τ), Finset.sum_congr rfl (fun τ _ => e2 τ),
        ← Finset.sum_mul, ← Finset.sum_mul, hs1, hs2]

/-- The collaborator's own numeric counterexample to the unqualified "exemplar-averaging is
always skew-invariant" claim, verified directly: with per-type conditional recalls
`(0.5, 1)` (type 0: true `{A,B}`, predicted `{A}`; type 1: true `{A}`, predicted `{A}`),
equal population shares give exemplar-recall `0.75`, while shares `(0.8, 0.2)` give
`0.60` — the *same* per-type predictions, a *different* aggregate, from the population
mixture alone (`exemplar_invariant_iff_constant_mbar` above explains exactly why: `0.5 ≠ 1`,
so no share distribution is safe from this). -/
example :
    (∑ τ : Fin 2, (![0.5, 0.5] : Fin 2 → ℝ) τ * (![0.5, 1] : Fin 2 → ℝ) τ = 0.75) ∧
    (∑ τ : Fin 2, (![0.8, 0.2] : Fin 2 → ℝ) τ * (![0.5, 1] : Fin 2 → ℝ) τ = 0.60) := by
  constructor <;> (rw [Fin.sum_univ_two]; norm_num)

end Aggmetrics

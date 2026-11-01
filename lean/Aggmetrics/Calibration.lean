import Aggmetrics.Basic
import Aggmetrics.Mixture

/-!
# Formalization of results from `papers/06-generalised-confusion/paper` itself

Unlike `Aggmetrics.TNorm`, which formalizes a theorem `papers/06-generalised-confusion/paper`
*cites* from the base paper, the results here (`sec4_calibration.tex`) are original to that
paper's own calibration section.

* `brier_strictly_proper` — Theorem ("Brier score is strictly proper"): the expected Brier loss
  under `Y ~ Ber(p)` is uniquely minimized at the truthful prediction. The paper's own proof is a
  one-line calculus argument (derivative zero, second derivative positive); the algebraic content
  is the same either way, so this is proved directly by completing the square
  (`brier_loss_eq`), with no calculus needed at all.
* `micro_macro_exemplar_collapse` — Theorem ("Micro-macro-exemplar collapse for Brier"): unlike
  the Discrimination Framework's ratio-valued measures (`Aggmetrics.micro_eq_macro_iff`), a
  *sum* of per-cell terms — which the Brier score is — is aggregation-order-invariant
  unconditionally, with no equal-denominator condition required. Proved as a general fact about
  any `f : Fin n → Fin m → ℝ`, not just the squared-deviation term.
* `murphy_decomposition` / `levelMean_orthogonal` / `binary_variance` /
  `murphy_decomposition_levelsets` — Theorems ("Column-level Murphy decomposition" and, by the same
  algebra with the roles of `n` and `m` exchanged, "Row-level Murphy decomposition"):
  `BS = UNC − RES + REL` with `UNC = ȳ(1 − ȳ)`, `RES = mean (f(Ŷᵢ) − ȳ)²` and
  `REL = mean (Ŷᵢ − f(Ŷᵢ))²`, where `f` is the empirical calibration map `levelMean`, the mean of
  `Y` over the level set `{i : Ŷᵢ = v}`. The proof leans twice on one fact, the paper's Lemma
  "Group-mean residuals are orthogonal to group-level functions": `Yᵢ − f(Ŷᵢ)` is orthogonal to any
  function of `Ŷᵢ` alone. `murphy_decomposition` takes it as the hypothesis `horth` and proves
  everything downstream (both three-term square expansions, both cross-terms vanishing, the
  recombination); `levelMean_orthogonal` proves it for `levelMean` by grouping the summands by
  distinct predicted value, as in the paper; `murphy_decomposition_levelsets` combines the two, so
  nothing is assumed beyond the definitions.
* `brier_prevalence_decomposition` — Proposition ("Prevalence decomposition of per-class Brier"):
  `BS = π·α + (1-π)·β`, with `α`, `β` the mean squared error over positives and negatives (the
  stratified Brier components). Elementary: the law of total expectation over the label.
* `brier_skew_iff` (via `Aggmetrics.Mixture`) — Corollary ("Skew-sensitivity of `BS_j`"), exact
  form: replicating the positives `lam`-fold versus `mu`-fold leaves the per-class Brier score
  unchanged iff `α = β`.
* `alpha_eq_one_sub_recall` / `beta_eq_one_sub_specificity` — Corollary ("Connection to the
  Discrimination Framework for hard predictions"): for `p i ∈ {0,1}`, `α = 1 − recall` and
  `β = 1 − specificity`.
* `rel`, `rel_calibrated`, `rel_after_skew` — Corollary ("Skew-sensitivity of Murphy terms"), part
  (c): perfect calibration is not skew-invariant. A perfectly calibrated data set (`REL = 0`) with
  its positive examples replicated twice has `REL = 1/45`.
* `weighted_brier_skew_invariant_iff` — Remark ("Class-weighted Brier scores"): `w₁ π α + w₀ (1 − π) β`
  is skew-invariant for every `(α, β)` iff `w₁ π` and `w₀ (1 − π)` are constant in `π`. The paper previously stated that
  `REL = 0` is a skew-invariant property; it now states the correct (negative) result.
-/

namespace Aggmetrics.Calibration

/-- Algebraic identity underlying strict propriety: the expected Brier loss decomposes into a
squared bias term plus the irreducible variance `p(1-p)`. -/
theorem brier_loss_eq (p x : ℝ) :
    p * (1 - x) ^ 2 + (1 - p) * x ^ 2 = (x - p) ^ 2 + p * (1 - p) := by ring

/-- Theorem (Brier score is strictly proper): the expected Brier loss under `Y ~ Ber(p)` is
minimized, uniquely, at the truthful prediction `x = p`. -/
theorem brier_strictly_proper (p x : ℝ) (hx : x ≠ p) :
    p * (1 - p) ^ 2 + (1 - p) * p ^ 2 < p * (1 - x) ^ 2 + (1 - p) * x ^ 2 := by
  rw [brier_loss_eq p p, brier_loss_eq p x]
  have h1 : (p - p) ^ 2 = 0 := by ring
  have hxp : x - p ≠ 0 := sub_ne_zero.mpr hx
  have hpos : 0 < (x - p) ^ 2 := by positivity
  linarith

/-- Theorem (Micro-macro-exemplar collapse for Brier): for any per-cell term `f i j`, averaging
over classes then examples equals averaging over examples then classes — aggregation order is
irrelevant for a sum, in contrast to the Discrimination Framework's ratio-valued measures. -/
theorem micro_macro_exemplar_collapse {n m : ℕ} (f : Fin n → Fin m → ℝ) :
    (1 / (m : ℝ)) * ∑ j, (1 / (n : ℝ)) * ∑ i, f i j
      = (1 / (n : ℝ)) * ∑ i, (1 / (m : ℝ)) * ∑ j, f i j := by
  have hL : (1 / (m : ℝ)) * ∑ j, (1 / (n : ℝ)) * ∑ i, f i j
      = ∑ j, ∑ i, (1 / (n : ℝ) / m) * f i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hR : (1 / (n : ℝ)) * ∑ i, (1 / (m : ℝ)) * ∑ j, f i j
      = ∑ i, ∑ j, (1 / (n : ℝ) / m) * f i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hL, hR, Finset.sum_comm]

/-- Theorem (Column-level Murphy decomposition): `BS = UNC - RES + REL`, given that `f` is the
calibration map in the sense that its residuals are orthogonal to any function of the predicted
value alone (`horth`) — the property raw level-set averaging is used, in the paper, to establish. -/
theorem murphy_decomposition {n : ℕ} (Y Yhat : Fin n → ℝ) (f : ℝ → ℝ)
    (horth : ∀ h : ℝ → ℝ, ∑ i, h (Yhat i) * (Y i - f (Yhat i)) = 0) (ybar : ℝ)
    (_hybar : ybar = (1 / (n : ℝ)) * ∑ i, Y i) :
    (1 / (n : ℝ)) * ∑ i, (Y i - Yhat i) ^ 2
      = (1 / (n : ℝ)) * ∑ i, (Y i - ybar) ^ 2
        - (1 / (n : ℝ)) * ∑ i, (f (Yhat i) - ybar) ^ 2
        + (1 / (n : ℝ)) * ∑ i, (f (Yhat i) - Yhat i) ^ 2 := by
  have hsum1 : ∑ i, (Y i - Yhat i) ^ 2
      = ∑ i, (Y i - f (Yhat i)) ^ 2 + ∑ i, (f (Yhat i) - Yhat i) ^ 2 := by
    have expand : ∀ i, (Y i - Yhat i) ^ 2
        = (Y i - f (Yhat i)) ^ 2 + (f (Yhat i) - Yhat i) ^ 2
          + 2 * ((f (Yhat i) - Yhat i) * (Y i - f (Yhat i))) := fun i => by ring
    have hcross : ∑ i, (f (Yhat i) - Yhat i) * (Y i - f (Yhat i)) = 0 := horth (fun v => f v - v)
    calc ∑ i, (Y i - Yhat i) ^ 2
        = ∑ i, ((Y i - f (Yhat i)) ^ 2 + (f (Yhat i) - Yhat i) ^ 2
            + 2 * ((f (Yhat i) - Yhat i) * (Y i - f (Yhat i)))) :=
          Finset.sum_congr rfl (fun i _ => expand i)
      _ = ∑ i, (Y i - f (Yhat i)) ^ 2 + ∑ i, (f (Yhat i) - Yhat i) ^ 2
            + 2 * ∑ i, (f (Yhat i) - Yhat i) * (Y i - f (Yhat i)) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i, (Y i - f (Yhat i)) ^ 2 + ∑ i, (f (Yhat i) - Yhat i) ^ 2 := by
          rw [hcross]; ring
  have hsum2 : ∑ i, (Y i - ybar) ^ 2
      = ∑ i, (f (Yhat i) - ybar) ^ 2 + ∑ i, (Y i - f (Yhat i)) ^ 2 := by
    have expand : ∀ i, (Y i - ybar) ^ 2
        = (f (Yhat i) - ybar) ^ 2 + (Y i - f (Yhat i)) ^ 2
          + 2 * ((f (Yhat i) - ybar) * (Y i - f (Yhat i))) := fun i => by ring
    have hcross : ∑ i, (f (Yhat i) - ybar) * (Y i - f (Yhat i)) = 0 := horth (fun v => f v - ybar)
    calc ∑ i, (Y i - ybar) ^ 2
        = ∑ i, ((f (Yhat i) - ybar) ^ 2 + (Y i - f (Yhat i)) ^ 2
            + 2 * ((f (Yhat i) - ybar) * (Y i - f (Yhat i)))) :=
          Finset.sum_congr rfl (fun i _ => expand i)
      _ = ∑ i, (f (Yhat i) - ybar) ^ 2 + ∑ i, (Y i - f (Yhat i)) ^ 2
            + 2 * ∑ i, (f (Yhat i) - ybar) * (Y i - f (Yhat i)) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i, (f (Yhat i) - ybar) ^ 2 + ∑ i, (Y i - f (Yhat i)) ^ 2 := by
          rw [hcross]; ring
  have key : ∑ i, (Y i - f (Yhat i)) ^ 2
      = ∑ i, (Y i - ybar) ^ 2 - ∑ i, (f (Yhat i) - ybar) ^ 2 := by linarith [hsum2]
  rw [hsum1, key]
  ring

/-- Proposition ("Prevalence decomposition of per-class Brier"): splitting the Brier sum by the
value of the label gives `BS = π·α + (1-π)·β`, with `α` the mean squared error over the positives
and `β` over the negatives (the stratified Brier components). The identity is elementary (the
law of total expectation over the label). `pos`/`neg` are the positive and negative examples. -/
theorem brier_prevalence_decomposition {n : ℕ} (hn : n ≠ 0) (Y p : Fin n → ℝ)
    (pos neg : Finset (Fin n)) (hpos : ∀ i, i ∈ pos ↔ Y i = 1) (hneg : ∀ i, i ∈ neg ↔ Y i = 0)
    (hY : ∀ i, Y i = 0 ∨ Y i = 1) (hnp : pos.card ≠ 0) (hnn : neg.card ≠ 0) :
    (1 / (n : ℝ)) * ∑ i, (Y i - p i) ^ 2
      = ((pos.card : ℝ) / n) * ((1 / (pos.card : ℝ)) * ∑ i ∈ pos, (1 - p i) ^ 2)
        + ((neg.card : ℝ) / n) * ((1 / (neg.card : ℝ)) * ∑ i ∈ neg, (p i) ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnp' : (pos.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnp
  have hnn' : (neg.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnn
  have hunion : pos ∪ neg = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, hpos, hneg]
    exact (hY i).symm
  have hdisj : Disjoint pos neg := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have e1 := (hpos i).mp h1
    have e2 := (hneg i).mp h2
    linarith
  have hsplit : ∑ i, (Y i - p i) ^ 2 = ∑ i ∈ pos, (1 - p i) ^ 2 + ∑ i ∈ neg, (p i) ^ 2 := by
    rw [← hunion, Finset.sum_union hdisj]
    congr 1
    · exact Finset.sum_congr rfl (fun i hi => by rw [(hpos i).mp hi])
    · exact Finset.sum_congr rfl (fun i hi => by rw [(hneg i).mp hi]; ring)
  rw [hsplit]
  field_simp

/-- Corollary ("Skew-sensitivity of `BS_j`", exact form): replicating the positive examples
`lam`-fold versus `mu`-fold leaves the per-class Brier score unchanged iff `α = β`. By
`Mixture.mixture_eq_prevalence_form`, the replicated score is `π'·α + (1-π')·β` with
`π' = lam·np / (lam·np + nn)`. -/
theorem brier_skew_iff {np nn alpha beta lam mu : ℝ} (hnp : 0 < np) (hnn : 0 < nn)
    (hlam : 0 < lam) (hmu : 0 < mu) (hne : lam ≠ mu) :
    (lam * np * alpha + nn * beta) / (lam * np + nn)
        = (mu * np * alpha + nn * beta) / (mu * np + nn)
      ↔ alpha = beta :=
  Mixture.mixture_eq_iff hnp hnn hlam hmu hne

/-- Corollary ("Connection to the Discrimination Framework for hard predictions"), the positive
component: for hard predictions `p i ∈ {0,1}`, `α = 1 - recall`, with recall the mean prediction
over the positives. -/
theorem alpha_eq_one_sub_recall {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, p i = 0 ∨ p i = 1)
    (pos : Finset (Fin n)) (hnp : pos.card ≠ 0) :
    (1 / (pos.card : ℝ)) * ∑ i ∈ pos, (1 - p i) ^ 2
      = 1 - (1 / (pos.card : ℝ)) * ∑ i ∈ pos, p i := by
  have hnp' : (pos.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnp
  have h : ∀ i, (1 - p i) ^ 2 = 1 - p i := by
    intro i
    rcases hp i with h | h <;> rw [h] <;> norm_num
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  simp
  field_simp

/-- The negative component: for hard predictions, `β = 1 - specificity`, with specificity the mean
of `1 - p i` over the negatives. -/
theorem beta_eq_one_sub_specificity {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, p i = 0 ∨ p i = 1)
    (neg : Finset (Fin n)) (hnn : neg.card ≠ 0) :
    (1 / (neg.card : ℝ)) * ∑ i ∈ neg, (p i) ^ 2
      = 1 - (1 / (neg.card : ℝ)) * ∑ i ∈ neg, (1 - p i) := by
  have hnn' : (neg.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnn
  have h : ∀ i, (p i) ^ 2 = p i := by
    intro i
    rcases hp i with h | h <;> rw [h] <;> norm_num
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  simp
  field_simp
  ring

/-! ### The calibration map and the group-mean orthogonality lemma -/

/-- The empirical calibration map of the paper: `levelMean Y Yhat v` is the mean of `Y` over the
level set `{i : Yhat i = v}` (the paper's `f(p) = n_p⁻¹ ∑_{i : Ŷ_i = p} Y_i`). -/
noncomputable def levelMean {n : ℕ} (Y Yhat : Fin n → ℝ) (v : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => Yhat i = v), Y i)
    / ((Finset.univ.filter (fun i => Yhat i = v)).card : ℝ)

/-- Lemma ("Group-mean residuals are orthogonal to group-level functions"): for *any* function `g`
of the predicted value alone, `∑ᵢ g(Ŷᵢ)(Yᵢ − f(Ŷᵢ)) = 0` for the level-set calibration map `f`.
Proof, as in the paper: group the summands by the distinct predicted values `v`; within the level
set of `v`, `∑ (Yᵢ − f(v)) = 0` by the definition of `f`, whatever `g(v)` is. This discharges the
hypothesis `horth` of `murphy_decomposition`. -/
theorem levelMean_orthogonal {n : ℕ} (Y Yhat : Fin n → ℝ) (g : ℝ → ℝ) :
    ∑ i, g (Yhat i) * (Y i - levelMean Y Yhat (Yhat i)) = 0 := by
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), Yhat i ∈ Finset.univ.image Yhat :=
    fun i _ => Finset.mem_image_of_mem Yhat (Finset.mem_univ i)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_eq_zero (fun v hv => ?_)
  obtain ⟨i0, _, rfl⟩ := Finset.mem_image.mp hv
  have hcongr : ∀ i ∈ Finset.univ.filter (fun i => Yhat i = Yhat i0),
      g (Yhat i) * (Y i - levelMean Y Yhat (Yhat i))
        = g (Yhat i0) * (Y i - levelMean Y Yhat (Yhat i0)) := by
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hpos : 0 < (Finset.univ.filter (fun i => Yhat i = Yhat i0)).card :=
    Finset.card_pos.mpr ⟨i0, by simp⟩
  have hcard : ((Finset.univ.filter (fun i => Yhat i = Yhat i0)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hpos.ne'
  have key : ∀ S c : ℝ, c ≠ 0 → S - c * (S / c) = 0 := fun S c hc => by
    field_simp <;> ring
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  unfold levelMean
  rw [key _ _ hcard, mul_zero]

/-- For binary labels the empirical variance is the Bernoulli variance `ȳ(1 − ȳ)`. -/
theorem binary_variance {n : ℕ} (hn : n ≠ 0) (Y : Fin n → ℝ) (hY : ∀ i, Y i = 0 ∨ Y i = 1)
    (ybar : ℝ) (hybar : ybar = (1 / (n : ℝ)) * ∑ i, Y i) :
    (1 / (n : ℝ)) * ∑ i, (Y i - ybar) ^ 2 = ybar * (1 - ybar) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsumY : ∑ i, Y i = (n : ℝ) * ybar := by
    rw [hybar]
    field_simp
  have hterm : ∀ i, (Y i - ybar) ^ 2 = Y i * (1 - 2 * ybar) + ybar ^ 2 := by
    intro i
    rcases hY i with h | h <;> rw [h] <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.sum_mul, hsumY]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp <;> ring

/-- Theorem ("Column-level Murphy decomposition", and, by the same algebra with the roles of `n`
and `m` exchanged, "Row-level Murphy decomposition"), in the paper's own terms: for binary labels
`Y` and any predictions `Ŷ`, with `f` the empirical calibration map (`levelMean`),
`BS = UNC − RES + REL`, where `UNC = ȳ(1 − ȳ)`, `RES = mean (f(Ŷᵢ) − ȳ)²` and
`REL = mean (Ŷᵢ − f(Ŷᵢ))²`. The orthogonality hypothesis of `murphy_decomposition` is discharged
by `levelMean_orthogonal`, so nothing is assumed beyond the definitions. For the row-level
statement, take the `n` entries to be the `m` labels of one example. -/
theorem murphy_decomposition_levelsets {n : ℕ} (hn : n ≠ 0) (Y Yhat : Fin n → ℝ)
    (hY : ∀ i, Y i = 0 ∨ Y i = 1) (ybar : ℝ) (hybar : ybar = (1 / (n : ℝ)) * ∑ i, Y i) :
    (1 / (n : ℝ)) * ∑ i, (Y i - Yhat i) ^ 2
      = ybar * (1 - ybar)
        - (1 / (n : ℝ)) * ∑ i, (levelMean Y Yhat (Yhat i) - ybar) ^ 2
        + (1 / (n : ℝ)) * ∑ i, (Yhat i - levelMean Y Yhat (Yhat i)) ^ 2 := by
  have h := murphy_decomposition Y Yhat (levelMean Y Yhat) (levelMean_orthogonal Y Yhat) ybar hybar
  have e : ∑ i, (levelMean Y Yhat (Yhat i) - Yhat i) ^ 2
      = ∑ i, (Yhat i - levelMean Y Yhat (Yhat i)) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [binary_variance hn Y hY ybar hybar, e] at h
  exact h

/-- Reliability term `REL = (1/n) ∑ᵢ (Ŷᵢ − f(Ŷᵢ))²` with the empirical calibration map. -/
noncomputable def rel {n : ℕ} (Y Yh : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (Yh i - levelMean Y Yh (Yh i)) ^ 2

/-- Three examples with score `2/3` (two positive) and three with score `1/3` (one positive). -/
noncomputable def relY1 : Fin 6 → ℝ := ![1, 1, 0, 1, 0, 0]
noncomputable def relH1 : Fin 6 → ℝ := ![2/3, 2/3, 2/3, 1/3, 1/3, 1/3]
/-- The same data with the positive examples replicated twice. -/
noncomputable def relY2 : Fin 9 → ℝ := ![1, 1, 1, 1, 0, 1, 1, 0, 0]
noncomputable def relH2 : Fin 9 → ℝ := ![2/3, 2/3, 2/3, 2/3, 2/3, 1/3, 1/3, 1/3, 1/3]

/-- Corollary ("Skew-sensitivity of Murphy terms"), part (c): perfect calibration is *not* skew-invariant.
The data `(relY1, relH1)` are perfectly calibrated (`REL = 0`); replicating the positive examples
twice (`relY2, relH2`, same predicted values) gives `REL = 1/45 > 0` (`rel_after_skew`). An earlier
version of the paper claimed `REL = 0` is a skew-invariant property. -/
theorem rel_calibrated : rel relY1 relH1 = 0 := by
  unfold rel levelMean
  simp_rw [Finset.sum_filter, Finset.card_filter]
  simp [-Finset.sum_boole, Fin.sum_univ_succ, relY1, relH1]
  norm_num

theorem rel_after_skew : rel relY2 relH2 = 1 / 45 := by
  unfold rel levelMean
  simp_rw [Finset.sum_filter, Finset.card_filter]
  simp [-Finset.sum_boole, Fin.sum_univ_succ, relY2, relH2]
  norm_num

/-- Remark ("Class-weighted Brier scores"): a class-weighted Brier score `a(π) α + b(π) β` (with
`a = w₁ π`, `b = w₀ (1 − π)`) is unchanged by every change of prevalence `π ∈ S` for *every*
`(α, β)` iff `a` and `b` are both constant on `S`. -/
theorem weighted_brier_skew_invariant_iff (a b : ℝ → ℝ) (S : Set ℝ) :
    (∀ α β : ℝ, ∀ π ∈ S, ∀ π' ∈ S, a π * α + b π * β = a π' * α + b π' * β)
      ↔ ∀ π ∈ S, ∀ π' ∈ S, a π = a π' ∧ b π = b π' := by
  constructor
  · intro h π hπ π' hπ'
    refine ⟨?_, ?_⟩
    · have := h 1 0 π hπ π' hπ'
      simpa using this
    · have := h 0 1 π hπ π' hπ'
      simpa using this
  · intro h α β π hπ π' hπ'
    obtain ⟨h1, h2⟩ := h π hπ π' hπ'
    rw [h1, h2]

end Aggmetrics.Calibration

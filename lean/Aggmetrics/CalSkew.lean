import Mathlib

/-!
# Skew-invariance of calibration measures: the characterisation theorem

Formalization of Theorem ("Characterisation of skew-invariant calibration measures") of Section 4 of
the paper on generalised confusion matrices (`future_generalised_confusion`).

Model. For one class, the predicted scores of the positive examples and of the negative examples are
two multisets of reals `P`, `N`. The skew transformation replicates the positives `k`-fold and the
negatives `l`-fold (`k, l ≥ 1` integers): `(P, N) ↦ (k • P, l • N)`. This is the per-class
abstraction of the paper; replicating whole examples also changes the columns of the other classes,
which this model does not see.

* `cal_skew_a` — part (a): a measure is skew-invariant iff it depends on the data only through the
  within-class score distributions `dist P`, `dist N`. The key step: equal distributions give
  `|P'| • P = |P| • P'`, so two data sets with the same distributions are joined by a replication of
  each through a common multiple (the "chain of replications" of the paper).
* `cal_skew_b`, `cal_skew_b_conv` — part (b), for class-indexed measures `g(π, α, β)` built from the
  prevalence and the two class-conditional calibration errors `α = mean (1 − s)²` over positives and
  `β = mean s²` over negatives: skew-invariance holds iff the measure depends on the data only
  through `(α, β)`. The proof brings `(P, N)` to the prevalence of `(P', N')` with the explicit
  multipliers `k = |N| |P'|`, `l = |P| |N'|`, and uses that `α` and `β` are unchanged by replication.
  Two data sets with the same `(α, β)` and any prevalences are thus related, which is the
  "restriction to attained values" of the paper's statement.
-/

namespace Aggmetrics.CalSkew

/-- Prevalence of the positives in a class with positive scores `P` and negative scores `N`. -/
noncomputable def prev (P N : Multiset ℝ) : ℝ := (Multiset.card P : ℝ) / (Multiset.card P + Multiset.card N)

/-- Mean squared calibration error on the positives, `α = mean (1 − s)²`. -/
noncomputable def alphaM (P : Multiset ℝ) : ℝ := (P.map fun s => (1 - s) ^ 2).sum / Multiset.card P

/-- Mean squared calibration error on the negatives, `β = mean s²`. -/
noncomputable def betaM (N : Multiset ℝ) : ℝ := (N.map fun s => s ^ 2).sum / Multiset.card N

/-- Empirical within-class score distribution. -/
noncomputable def dist (P : Multiset ℝ) (x : ℝ) : ℝ := (Multiset.count x P : ℝ) / Multiset.card P

/-- Skew-invariance under integer replication: replicating the positives `k`-fold and the negatives
`l`-fold (`k, l ≥ 1`) leaves the measure unchanged. -/
def SkewInv (M : Multiset ℝ → Multiset ℝ → ℝ) : Prop :=
  ∀ P N, P ≠ 0 → N ≠ 0 → ∀ k l : ℕ, 0 < k → 0 < l → M (k • P) (l • N) = M P N

theorem card_pos_of_ne {P : Multiset ℝ} (h : P ≠ 0) : 0 < Multiset.card P :=
  Multiset.card_pos.mpr h

theorem nsmul_ne_zero' {P : Multiset ℝ} (h : P ≠ 0) {k : ℕ} (hk : 0 < k) : k • P ≠ 0 := by
  intro h0
  have := card_pos_of_ne h
  have h1 : Multiset.card (k • P) = 0 := by rw [h0]; simp
  rw [Multiset.card_nsmul] at h1
  have : 0 < k * Multiset.card P := Nat.mul_pos hk this
  omega

theorem alphaM_nsmul {P : Multiset ℝ} (h : P ≠ 0) {k : ℕ} (hk : 0 < k) :
    alphaM (k • P) = alphaM P := by
  have hc : (Multiset.card P : ℝ) ≠ 0 := by exact_mod_cast (card_pos_of_ne h).ne'
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold alphaM
  rw [Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.card_nsmul]
  push_cast
  rw [nsmul_eq_mul]
  field_simp

theorem betaM_nsmul {N : Multiset ℝ} (h : N ≠ 0) {k : ℕ} (hk : 0 < k) :
    betaM (k • N) = betaM N := by
  have hc : (Multiset.card N : ℝ) ≠ 0 := by exact_mod_cast (card_pos_of_ne h).ne'
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold betaM
  rw [Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.card_nsmul]
  push_cast
  rw [nsmul_eq_mul]
  field_simp

theorem dist_nsmul {P : Multiset ℝ} (h : P ≠ 0) {k : ℕ} (hk : 0 < k) : dist (k • P) = dist P := by
  have hc : (Multiset.card P : ℝ) ≠ 0 := by exact_mod_cast (card_pos_of_ne h).ne'
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  funext x
  unfold dist
  rw [Multiset.count_nsmul, Multiset.card_nsmul]
  push_cast
  field_simp

/-- Theorem ("Characterisation of skew-invariant calibration measures"), part (a), in the model of
integer replication of the two score multisets: a measure is skew-invariant iff it depends on the
data only through the within-class score distributions. -/
theorem cal_skew_a (M : Multiset ℝ → Multiset ℝ → ℝ) :
    SkewInv M ↔ ∀ P N P' N', P ≠ 0 → N ≠ 0 → P' ≠ 0 → N' ≠ 0 →
      dist P = dist P' → dist N = dist N' → M P N = M P' N' := by
  constructor
  · intro hinv P N P' N' hP hN hP' hN' hd hd'
    have key : ∀ {A B : Multiset ℝ}, A ≠ 0 → B ≠ 0 → dist A = dist B →
        Multiset.card B • A = Multiset.card A • B := by
      intro A B hA hB h
      have hcA : (Multiset.card A : ℝ) ≠ 0 := by exact_mod_cast (card_pos_of_ne hA).ne'
      have hcB : (Multiset.card B : ℝ) ≠ 0 := by exact_mod_cast (card_pos_of_ne hB).ne'
      refine Multiset.ext.mpr (fun x => ?_)
      have hx := congrFun h x
      unfold dist at hx
      rw [Multiset.count_nsmul, Multiset.count_nsmul]
      rw [div_eq_div_iff hcA hcB] at hx
      have : (Multiset.card B : ℝ) * (Multiset.count x A : ℝ)
          = (Multiset.card A : ℝ) * (Multiset.count x B : ℝ) := by linarith
      exact_mod_cast this
    have e1 := hinv P N hP hN (Multiset.card P') (Multiset.card N')
      (card_pos_of_ne hP') (card_pos_of_ne hN')
    have e2 := hinv P' N' hP' hN' (Multiset.card P) (Multiset.card N)
      (card_pos_of_ne hP) (card_pos_of_ne hN)
    rw [key hP hP' hd, key hN hN' hd'] at e1
    rw [← e1, e2]
  · intro hfib P N hP hN k l hk hl
    exact hfib _ _ _ _ (nsmul_ne_zero' hP hk) (nsmul_ne_zero' hN hl) hP hN
      (dist_nsmul hP hk) (dist_nsmul hN hl)

theorem prev_nsmul_eq {P N P' N' : Multiset ℝ} (hP : P ≠ 0) (hN : N ≠ 0) (hP' : P' ≠ 0)
    (hN' : N' ≠ 0) :
    prev ((Multiset.card N * Multiset.card P') • P) ((Multiset.card P * Multiset.card N') • N)
      = prev P' N' := by
  have hp : (Multiset.card P : ℝ) ≠ 0 := by exact_mod_cast (card_pos_of_ne hP).ne'
  have hn : (Multiset.card N : ℝ) ≠ 0 := by exact_mod_cast (card_pos_of_ne hN).ne'
  have hp' : (0 : ℝ) < Multiset.card P' := by exact_mod_cast card_pos_of_ne hP'
  have hn' : (0 : ℝ) < Multiset.card N' := by exact_mod_cast card_pos_of_ne hN'
  unfold prev
  rw [Multiset.card_nsmul, Multiset.card_nsmul]
  push_cast
  field_simp

/-- Part (b): a class-indexed measure, a function `g(π, α, β)` of the prevalence and the two
calibration errors, is skew-invariant iff it depends on the data only through `(α, β)`. Here: skew
invariance forces equal values for two data sets with the same `α` and `β`, whatever their
prevalences. -/
theorem cal_skew_b (M : Multiset ℝ → Multiset ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (hM : ∀ P N, P ≠ 0 → N ≠ 0 → M P N = g (prev P N) (alphaM P) (betaM N))
    (hinv : SkewInv M) (P N P' N' : Multiset ℝ) (hP : P ≠ 0) (hN : N ≠ 0) (hP' : P' ≠ 0)
    (hN' : N' ≠ 0) (ha : alphaM P = alphaM P') (hb : betaM N = betaM N') :
    M P N = M P' N' := by
  have hk : 0 < Multiset.card N * Multiset.card P' :=
    Nat.mul_pos (card_pos_of_ne hN) (card_pos_of_ne hP')
  have hl : 0 < Multiset.card P * Multiset.card N' :=
    Nat.mul_pos (card_pos_of_ne hP) (card_pos_of_ne hN')
  have e1 := hinv P N hP hN _ _ hk hl
  rw [← e1, hM _ _ (nsmul_ne_zero' hP hk) (nsmul_ne_zero' hN hl), alphaM_nsmul hP hk,
    betaM_nsmul hN hl, prev_nsmul_eq hP hN hP' hN', ha, hb, ← hM P' N' hP' hN']

/-- The converse of (b): a function of `(α, β)` alone is skew-invariant, since `α` and `β` are
unchanged by replication. -/
theorem cal_skew_b_conv (M : Multiset ℝ → Multiset ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (hM : ∀ P N, P ≠ 0 → N ≠ 0 → M P N = h (alphaM P) (betaM N)) : SkewInv M := by
  intro P N hP hN k l hk hl
  rw [hM _ _ (nsmul_ne_zero' hP hk) (nsmul_ne_zero' hN hl), hM P N hP hN, alphaM_nsmul hP hk,
    betaM_nsmul hN hl]

end Aggmetrics.CalSkew

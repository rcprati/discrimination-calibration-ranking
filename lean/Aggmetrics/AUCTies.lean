import Aggmetrics.Ranking

/-!
# AUC with half credit for ties

The paper scores a tied positive–negative pair with half credit (Definition `auc_family`,
Proposition `auc_improper`). `Aggmetrics.Ranking` uses the strict indicator `sInd` (a tie scores
`0`), which agrees with half credit whenever the report has no ties among the pairs that count. This
file adds the half-credit indicator `sIndH` and the corresponding AUC, and:

* `concordantCountH_eq_of_injective`, `expAUCH_eq_expAUC` — for reports with distinct entries the two
  conventions give the same AUC, so every strict-indicator result transfers;
* `expAUCH_no_unique_maximiser` — part (a): no report is the unique maximiser;
* `pairSumH_le_truthful`, `aucWeight_eq_of_eq`, `expAUCH_indep_le_truthful` — part (b) **without**
  assuming distinct marginals: under independent labels the truthful report maximises the expected
  AUC, ties between equal marginals included (they earn half credit on pairs of equal weight);
* `expAUCH_two_le_truthful`, `expAUCH_three_le_truthful` — part (c), any dependence, ties allowed;
* `expAUCH_dependent_counterexample_all` — part (d) for every `n = 4 + k` under half credit.
-/

namespace Aggmetrics.Ranking

/-- Half-credit indicator: `1` if the report ranks `i'` strictly below `i`, `1/2` on a tie,
`0` otherwise. -/
noncomputable def sIndH {n : ℕ} (q : Fin n → ℝ) (i i' : Fin n) : ℝ :=
  if q i' < q i then 1 else if q i' = q i then 1 / 2 else 0

noncomputable def concordantCountH {n : ℕ} (q Y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ i', Y i * (1 - Y i') * sIndH q i i'

noncomputable def aucScoreH {n : ℕ} (q Y : Fin n → ℝ) : ℝ :=
  concordantCountH q Y / ((∑ i, Y i) * (∑ i, (1 - Y i)))

noncomputable def expAUCH {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (q : Fin n → ℝ) : ℝ :=
  ∑ ω, P ω * aucScoreH q (Y ω)

theorem sIndH_add {n : ℕ} (q : Fin n → ℝ) (i i' : Fin n) : sIndH q i i' + sIndH q i' i = 1 := by
  unfold sIndH
  rcases lt_trichotomy (q i) (q i') with h | h | h
  · simp [h, not_lt.mpr h.le, ne_of_gt h]
  · simp [h]; norm_num
  · simp [h, not_lt.mpr h.le, ne_of_gt h]

theorem sIndH_nonneg {n : ℕ} (q : Fin n → ℝ) (i i' : Fin n) : 0 ≤ sIndH q i i' := by
  unfold sIndH; split_ifs <;> norm_num

theorem sIndH_le_one {n : ℕ} (q : Fin n → ℝ) (i i' : Fin n) : sIndH q i i' ≤ 1 := by
  unfold sIndH; split_ifs <;> norm_num

theorem sIndH_comp {n : ℕ} (q : Fin n → ℝ) (φ : ℝ → ℝ) (hφ : StrictMono φ) (i i' : Fin n) :
    sIndH (φ ∘ q) i i' = sIndH q i i' := by
  unfold sIndH
  simp only [Function.comp_apply, hφ.lt_iff_lt, hφ.injective.eq_iff]

theorem sIndH_eq_sInd_of_ne {n : ℕ} (q : Fin n → ℝ) {i i' : Fin n} (h : q i' ≠ q i) :
    sIndH q i i' = sInd q i i' := by
  unfold sIndH sInd
  simp [h]

/-! ### Bridge to the strict indicator -/

/-- For `0/1` labels and a report with distinct entries, half credit and the strict indicator give
the same number of concordant pairs (the diagonal pairs carry the weight `Y i (1 − Y i) = 0`). -/
theorem concordantCountH_eq_of_injective {n : ℕ} (q Y : Fin n → ℝ) (hq : Function.Injective q)
    (hY : ∀ i, Y i = 0 ∨ Y i = 1) : concordantCountH q Y = concordantCount q Y := by
  unfold concordantCountH concordantCount
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => ?_))
  by_cases hii : i = i'
  · subst hii
    rcases hY i with h | h <;> simp [h]
  · have hne : q i' ≠ q i := fun h => hii (hq h).symm
    rw [sIndH_eq_sInd_of_ne q hne]

theorem expAUCH_eq_expAUC {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (hY : ∀ ω i, Y ω i = 0 ∨ Y ω i = 1) (q : Fin n → ℝ) (hq : Function.Injective q) :
    expAUCH P Y q = expAUC P Y q := by
  unfold expAUCH expAUC aucScoreH aucScore
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [concordantCountH_eq_of_injective q (Y ω) hq (hY ω)]

/-! ### Part (a): non-uniqueness -/

theorem expAUCH_comp {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (q : Fin n → ℝ) (φ : ℝ → ℝ) (hφ : StrictMono φ) :
    expAUCH P Y (φ ∘ q) = expAUCH P Y q := by
  unfold expAUCH aucScoreH concordantCountH
  simp only [sIndH_comp q φ hφ]

theorem expAUCH_no_unique_maximiser {n : ℕ} (hn : 0 < n) {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (Y : Ω → Fin n → ℝ) (q : Fin n → ℝ)
    (hq : ∀ q', expAUCH P Y q' ≤ expAUCH P Y q) :
    ∃ q', q' ≠ q ∧ expAUCH P Y q' = expAUCH P Y q ∧ ∀ q'', expAUCH P Y q'' ≤ expAUCH P Y q' := by
  have hshift : StrictMono (fun x : ℝ => x + 1) := fun _ _ h => by linarith
  have heq : expAUCH P Y (fun i => q i + 1) = expAUCH P Y q :=
    expAUCH_comp P Y q (fun x => x + 1) hshift
  refine ⟨fun i => q i + 1, ?_, heq, fun q'' => by rw [heq]; exact hq q''⟩
  intro h
  have h0 := congrFun h ⟨0, hn⟩
  simp at h0

/-! ### Pairwise maximality with ties -/

theorem expAUCH_eq {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (q : Fin n → ℝ) :
    expAUCH P Y q = ∑ i, ∑ i', aucWeight P Y i i' * sIndH q i i' := by
  have h1 : ∀ ω, P ω * aucScoreH q (Y ω)
      = ∑ i, ∑ i', P ω * (Y ω i * (1 - Y ω i') / ((∑ k, Y ω k) * (∑ k, (1 - Y ω k))))
          * sIndH q i i' := by
    intro ω
    unfold aucScoreH concordantCountH
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    ring
  unfold expAUCH aucWeight
  simp only [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

/-- A convex combination of `a` and `b` is at most any common upper bound. -/
theorem pair_half_le {a b s t c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hst : s + t = 1)
    (ha : a ≤ c) (hb : b ≤ c) : a * s + b * t ≤ c := by
  have ht : t = 1 - s := by linarith
  subst ht
  nlinarith [mul_le_mul_of_nonneg_right ha hs0, mul_le_mul_of_nonneg_right hb (by linarith : 0 ≤ 1 - s)]

/-- Pairwise maximality under half credit, with ties in the truth: if the pair weights rank the
higher-`p` unit first and are symmetric between units with equal `p`, the truthful report `p`
maximises `∑ W i i' · sIndH q i i'` over all reports `q`. No injectivity is needed. -/
theorem pairSumH_le_truthful {n : ℕ} (W : Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (hord : ∀ i i', p i < p i' → W i i' ≤ W i' i)
    (heq : ∀ i i', p i = p i' → W i i' = W i' i) (q : Fin n → ℝ) :
    ∑ i, ∑ i', W i i' * sIndH q i i' ≤ ∑ i, ∑ i', W i i' * sIndH p i i' := by
  have hsym : ∀ r : Fin n → ℝ,
      ∑ i, ∑ i', W i i' * sIndH r i i'
        = (1 / 2) * ∑ i, ∑ i', (W i i' * sIndH r i i' + W i' i * sIndH r i' i) := by
    intro r
    have hU : ∑ i, ∑ i', W i' i * sIndH r i' i = ∑ i, ∑ i', W i i' * sIndH r i i' :=
      Finset.sum_comm
    simp only [Finset.sum_add_distrib]
    rw [hU]
    ring
  rw [hsym q, hsym p]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun i' _ => ?_))
  have hq : ∀ c, W i i' ≤ c → W i' i ≤ c →
      W i i' * sIndH q i i' + W i' i * sIndH q i' i ≤ c := fun c ha hb =>
    pair_half_le (sIndH_nonneg q i i') (sIndH_le_one q i i') (sIndH_add q i i') ha hb
  rcases lt_trichotomy (p i) (p i') with hlt | heqp | hgt
  · have e1 : sIndH p i i' = 0 := by unfold sIndH; simp [not_lt.mpr hlt.le, ne_of_gt hlt]
    have e2 : sIndH p i' i = 1 := by unfold sIndH; simp [hlt]
    rw [e1, e2]
    have := hq (W i' i) (hord i i' hlt) (le_refl _)
    linarith
  · have e1 : sIndH p i i' = 1 / 2 := by unfold sIndH; simp [heqp]
    have e2 : sIndH p i' i = 1 / 2 := by unfold sIndH; simp [heqp]
    rw [e1, e2]
    have hw := heq i i' heqp
    have := hq (W i i') (le_refl _) (le_of_eq hw.symm)
    linarith
  · have e1 : sIndH p i i' = 1 := by unfold sIndH; simp [hgt]
    have e2 : sIndH p i' i = 0 := by unfold sIndH; simp [not_lt.mpr hgt.le, ne_of_gt hgt]
    rw [e1, e2]
    have := hq (W i i') (le_refl _) (hord i' i hgt)
    linarith

theorem aucWeight_eq_of_eq {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (i i' : Fin n) (h : p i = p i') :
    aucWeight (bernP p) boolLab i i' = aucWeight (bernP p) boolLab i' i := by
  by_cases hii : i = i'
  · subst hii; rfl
  · obtain ⟨K, _, hd⟩ := aucWeight_diff p hp0 hp1 hii
    rw [h, sub_self, zero_mul] at hd
    linarith

/-- Proposition ("AUC is non-strict; truthful ranking may fail under dependence"), part (b), with
half credit for ties and **without** assuming distinct marginals: under independent labels, the
truthful report maximises the expected AUC. -/
theorem expAUCH_indep_le_truthful {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (q : Fin n → ℝ) :
    expAUCH (bernP p) boolLab q ≤ expAUCH (bernP p) boolLab p := by
  rw [expAUCH_eq, expAUCH_eq]
  exact pairSumH_le_truthful _ p (aucWeight_ord p hp0 hp1) (aucWeight_eq_of_eq p hp0 hp1) q

/-- Part (c) for three units, any dependence, ties allowed (half credit). -/
theorem expAUCH_three_le_truthful {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    (Y : Ω → Fin 3 → ℝ) (hY : ∀ ω i, Y ω i = 0 ∨ Y ω i = 1) (p : Fin 3 → ℝ)
    (hp : ∀ i, p i = ∑ ω, P ω * Y ω i) (q : Fin 3 → ℝ) :
    expAUCH P Y q ≤ expAUCH P Y p := by
  rw [expAUCH_eq, expAUCH_eq]
  refine pairSumH_le_truthful _ p ?_ ?_ q
  · intro i i' h
    rw [aucWeight_three P Y hY, aucWeight_three P Y hY]
    have := pairWeight_sub P Y p hp i i'
    linarith
  · intro i i' h
    rw [aucWeight_three P Y hY, aucWeight_three P Y hY]
    have := pairWeight_sub P Y p hp i i'
    rw [h, sub_self] at this
    linarith

/-- Part (c) for two units, any dependence, ties allowed (half credit). -/
theorem expAUCH_two_le_truthful {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    (Y : Ω → Fin 2 → ℝ) (hY : ∀ ω i, Y ω i = 0 ∨ Y ω i = 1) (p : Fin 2 → ℝ)
    (hp : ∀ i, p i = ∑ ω, P ω * Y ω i) (q : Fin 2 → ℝ) :
    expAUCH P Y q ≤ expAUCH P Y p := by
  rw [expAUCH_eq, expAUCH_eq]
  refine pairSumH_le_truthful _ p ?_ ?_ q
  · intro i i' h
    rw [aucWeight_two P Y hY, aucWeight_two P Y hY]
    have := pairWeight_sub P Y p hp i i'
    linarith
  · intro i i' h
    rw [aucWeight_two P Y hY, aucWeight_two P Y hY]
    have := pairWeight_sub P Y p hp i i'
    rw [h, sub_self] at this
    linarith

/-! ### Part (d) under half credit -/

theorem cexq_injective : Function.Injective cexq := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp [cexq] at h <;> norm_num at h)

theorem cexY_binary : ∀ ω i, cexY ω i = 0 ∨ cexY ω i = 1 := by
  intro ω i
  fin_cases ω <;> fin_cases i <;> simp [cexY]

theorem concordantCountH_append {n k : ℕ} (q Y : Fin n → ℝ) (r : Fin k → ℝ)
    (hqr : ∀ a b, q a < r b) :
    concordantCountH (Fin.append q r) (Fin.append Y (fun _ => (1 : ℝ)))
      = concordantCountH q Y + k * ∑ i, (1 - Y i) := by
  unfold concordantCountH sIndH
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, hqr, if_true, sub_self,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, one_mul, mul_one]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem aucScoreH_append_eq {n k : ℕ} (q Y : Fin n → ℝ) (r : Fin k → ℝ)
    (hqr : ∀ a b, q a < r b) (hq : Function.Injective q) (hY : ∀ i, Y i = 0 ∨ Y i = 1) :
    aucScoreH (Fin.append q r) (Fin.append Y (fun _ => (1 : ℝ)))
      = aucScore (Fin.append q r) (Fin.append Y (fun _ => (1 : ℝ))) := by
  unfold aucScoreH aucScore
  rw [concordantCountH_append q Y r hqr, concordantCount_append q Y r hqr,
    concordantCountH_eq_of_injective q Y hq hY]

/-- Proposition ("AUC is non-strict; truthful ranking may fail under dependence"), part (d), for
every number of units `n = 4 + k ≥ 4`, under the paper's half-credit convention. The added units tie
among themselves, but all of them are positive in every scenario, so their ties never count. -/
theorem expAUCH_dependent_counterexample_all (k : ℕ) :
    (∀ ω i, cexkY k ω i = 0 ∨ cexkY k ω i = 1) ∧
    (∀ i, cexkp k i = ∑ ω, cexP ω * cexkY k ω i) ∧
    expAUCH cexP (cexkY k) (cexkp k) < expAUCH cexP (cexkY k) (cexkq k) := by
  obtain ⟨hbin, hmarg, hlt⟩ := expAUC_dependent_counterexample_all k
  refine ⟨hbin, hmarg, ?_⟩
  have hp : ∀ a : Fin 4, ∀ b : Fin k, cexp a < (fun _ => (1 : ℝ)) b := fun a _ => by
    fin_cases a <;> simp [cexp] <;> norm_num
  have hq : ∀ a : Fin 4, ∀ b : Fin k, cexq a < (fun _ => (4 : ℝ)) b := fun a _ => by
    fin_cases a <;> simp [cexq] <;> norm_num
  have e1 : expAUCH cexP (cexkY k) (cexkp k) = expAUC cexP (cexkY k) (cexkp k) := by
    unfold expAUCH expAUC
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [cexkp, cexkY, aucScoreH_append_eq cexp (cexY ω) _ hp cex_injective (cexY_binary ω)]
  have e2 : expAUCH cexP (cexkY k) (cexkq k) = expAUC cexP (cexkY k) (cexkq k) := by
    unfold expAUCH expAUC
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [cexkq, cexkY, aucScoreH_append_eq cexq (cexY ω) _ hq cexq_injective (cexY_binary ω)]
  rw [e1, e2]
  exact hlt

end Aggmetrics.Ranking

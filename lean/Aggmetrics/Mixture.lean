import Aggmetrics.Basic

/-!
# Two-group mixtures under replication

A single algebraic fact serves several skew-sensitivity statements of
`papers/06-generalised-confusion/paper`: if the members of one group are replicated by a factor
`lam > 0` (weight `lam`) and the other group is left alone, the weighted average of any quantity
depends on `lam` **if and only if** the two group means differ.

* `mixture_eq_iff` — the fact in terms of the two group means `a`, `b` and group sizes.
* `replAvg` / `replAvg_eq_iff` — the same fact for a quantity `r` over two finite groups `pos` and
  `neg`, the first replicated `lam`-fold. This is the exact condition behind "Exemplar nDCG is
  skew-sensitive" (the average of per-example nDCG moves iff the mean nDCG of the positive
  examples differs from that of the negative examples), and behind the skew-sensitivity of the
  per-class Brier score (`a = α`, `b = β`).
* `replRatio` / `replRatio_eq_iff` — the analogue for a *ratio* of replicated sums: it is
  independent of the replication factor iff the ratio `∑a/∑b` coincides over the two groups. This is
  the exact condition for the skew-sensitivity of micro-nDCG (`a` = per-example DCG, `b` = ideal DCG).
-/

namespace Aggmetrics.Mixture

/-- Core identity: cross-multiplying two replicated mixtures leaves exactly the factor
`np * nn * (lam - mu) * (a - b)`. -/
theorem mixture_cross {np nn lam mu a b : ℝ} :
    (lam * np * a + nn * b) * (mu * np + nn) - (mu * np * a + nn * b) * (lam * np + nn)
      = np * nn * (lam - mu) * (a - b) := by ring

/-- Two-group mixture: with group sizes `np, nn > 0` and group means `a, b`, replicating the first
group by `lam` versus `mu` (both positive, distinct) gives the same average iff `a = b`. -/
theorem mixture_eq_iff {np nn lam mu a b : ℝ} (hnp : 0 < np) (hnn : 0 < nn)
    (hlam : 0 < lam) (hmu : 0 < mu) (hne : lam ≠ mu) :
    (lam * np * a + nn * b) / (lam * np + nn) = (mu * np * a + nn * b) / (mu * np + nn)
      ↔ a = b := by
  have h1 : 0 < lam * np + nn := add_pos (mul_pos hlam hnp) hnn
  have h2 : 0 < mu * np + nn := add_pos (mul_pos hmu hnp) hnn
  rw [div_eq_div_iff h1.ne' h2.ne']
  have key := mixture_cross (np := np) (nn := nn) (lam := lam) (mu := mu) (a := a) (b := b)
  have hfac : np * nn * (lam - mu) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hnp.ne' hnn.ne') (sub_ne_zero.mpr hne)
  constructor
  · intro h
    have hd : np * nn * (lam - mu) * (a - b) = 0 := by linarith
    rcases mul_eq_zero.mp hd with h0 | h0
    · exact absurd h0 hfac
    · linarith
  · intro hab
    rw [hab]
    ring

/-- The mixture in prevalence form: replicating the first group `lam`-fold turns its prevalence
into `π' = lam·np / (lam·np + nn)`, and the average becomes `π' a + (1 - π') b`. -/
theorem mixture_eq_prevalence_form {np nn lam a b : ℝ} (hnp : 0 < np) (hnn : 0 < nn)
    (hlam : 0 < lam) :
    (lam * np * a + nn * b) / (lam * np + nn)
      = (lam * np / (lam * np + nn)) * a + (1 - lam * np / (lam * np + nn)) * b := by
  have h1 : lam * np + nn ≠ 0 := (add_pos (mul_pos hlam hnp) hnn).ne'
  field_simp
  ring

/-- Average of `r` over a population in which the members of `pos` are replicated `lam`-fold
(weight `lam`) and the members of `neg` are kept once. -/
noncomputable def replAvg {n : ℕ} (pos neg : Finset (Fin n)) (r : Fin n → ℝ) (lam : ℝ) : ℝ :=
  (∑ i ∈ pos, lam * r i + ∑ i ∈ neg, r i) / (lam * pos.card + neg.card)

theorem replAvg_eq_sums {n : ℕ} (pos neg : Finset (Fin n)) (r : Fin n → ℝ) (lam : ℝ) :
    replAvg pos neg r lam
      = (lam * ∑ i ∈ pos, r i + ∑ i ∈ neg, r i) / (lam * pos.card + neg.card) := by
  unfold replAvg
  rw [← Finset.mul_sum]

/-- The replicated average is independent of the replication factor (for two distinct positive
factors) iff the mean of `r` over `pos` equals its mean over `neg`. -/
theorem replAvg_eq_iff {n : ℕ} (pos neg : Finset (Fin n)) (hpos : 0 < pos.card)
    (hneg : 0 < neg.card) (r : Fin n → ℝ) {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hne : lam ≠ mu) :
    replAvg pos neg r lam = replAvg pos neg r mu
      ↔ (∑ i ∈ pos, r i) / pos.card = (∑ i ∈ neg, r i) / neg.card := by
  have hnp : (0 : ℝ) < pos.card := Nat.cast_pos.mpr hpos
  have hnn : (0 : ℝ) < neg.card := Nat.cast_pos.mpr hneg
  rw [replAvg_eq_sums, replAvg_eq_sums]
  set Sp := ∑ i ∈ pos, r i with hSp
  set Sn := ∑ i ∈ neg, r i with hSn
  have h1 : 0 < lam * (pos.card : ℝ) + neg.card := add_pos (mul_pos hlam hnp) hnn
  have h2 : 0 < mu * (pos.card : ℝ) + neg.card := add_pos (mul_pos hmu hnp) hnn
  rw [div_eq_div_iff h1.ne' h2.ne', div_eq_div_iff hnp.ne' hnn.ne']
  have key : (lam * Sp + Sn) * (mu * (pos.card : ℝ) + neg.card)
      - (mu * Sp + Sn) * (lam * (pos.card : ℝ) + neg.card)
      = (lam - mu) * (Sp * neg.card - Sn * pos.card) := by ring
  constructor
  · intro h
    have hd : (lam - mu) * (Sp * neg.card - Sn * pos.card) = 0 := by linarith
    rcases mul_eq_zero.mp hd with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hne
    · linarith
  · intro h
    have h0 : Sp * neg.card - Sn * pos.card = 0 := by linarith
    have : (lam * Sp + Sn) * (mu * (pos.card : ℝ) + neg.card)
        - (mu * Sp + Sn) * (lam * (pos.card : ℝ) + neg.card) = 0 := by
      rw [key, h0, mul_zero]
    linarith

/-- Ratio of replicated sums: the numerator `a` and denominator `b` summed over `pos` (each member
replicated `lam`-fold) and over `neg` (once). With `a` the per-example DCG and `b` the per-example
ideal DCG this is micro-nDCG of the replicated population. -/
noncomputable def replRatio {n : ℕ} (pos neg : Finset (Fin n)) (a b : Fin n → ℝ) (lam : ℝ) : ℝ :=
  (∑ i ∈ pos, lam * a i + ∑ i ∈ neg, a i) / (∑ i ∈ pos, lam * b i + ∑ i ∈ neg, b i)

theorem replRatio_eq_sums {n : ℕ} (pos neg : Finset (Fin n)) (a b : Fin n → ℝ) (lam : ℝ) :
    replRatio pos neg a b lam
      = (lam * ∑ i ∈ pos, a i + ∑ i ∈ neg, a i) / (lam * ∑ i ∈ pos, b i + ∑ i ∈ neg, b i) := by
  unfold replRatio
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- The replicated ratio is independent of the replication factor (for two distinct positive
factors) iff `(∑_pos a)(∑_neg b) = (∑_neg a)(∑_pos b)`, i.e. iff the ratio `∑a/∑b` is the same over
the two groups. -/
theorem replRatio_eq_iff {n : ℕ} (pos neg : Finset (Fin n)) (a b : Fin n → ℝ)
    (hbp : 0 < ∑ i ∈ pos, b i) (hbn : 0 < ∑ i ∈ neg, b i) {lam mu : ℝ} (hlam : 0 < lam)
    (hmu : 0 < mu) (hne : lam ≠ mu) :
    replRatio pos neg a b lam = replRatio pos neg a b mu
      ↔ (∑ i ∈ pos, a i) * (∑ i ∈ neg, b i) = (∑ i ∈ neg, a i) * (∑ i ∈ pos, b i) := by
  rw [replRatio_eq_sums, replRatio_eq_sums]
  set Ap := ∑ i ∈ pos, a i with hAp
  set An := ∑ i ∈ neg, a i with hAn
  set Bp := ∑ i ∈ pos, b i with hBp
  set Bn := ∑ i ∈ neg, b i with hBn
  have h1 : 0 < lam * Bp + Bn := add_pos (mul_pos hlam hbp) hbn
  have h2 : 0 < mu * Bp + Bn := add_pos (mul_pos hmu hbp) hbn
  rw [div_eq_div_iff h1.ne' h2.ne']
  have key : (lam * Ap + An) * (mu * Bp + Bn) - (mu * Ap + An) * (lam * Bp + Bn)
      = (lam - mu) * (Ap * Bn - An * Bp) := by ring
  constructor
  · intro h
    have hd : (lam - mu) * (Ap * Bn - An * Bp) = 0 := by linarith
    rcases mul_eq_zero.mp hd with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hne
    · linarith
  · intro h
    have h0 : Ap * Bn - An * Bp = 0 := by linarith
    have : (lam * Ap + An) * (mu * Bp + Bn) - (mu * Ap + An) * (lam * Bp + Bn) = 0 := by
      rw [key, h0, mul_zero]
    linarith

end Aggmetrics.Mixture

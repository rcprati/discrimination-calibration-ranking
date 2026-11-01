import Mathlib

/-!
# Savage representation and symmetric deviation operators

Formalization of results of Section 4 ("Calibration Framework") of the paper on generalised
confusion matrices (`future_generalised_confusion`).

* `symmetric_weight_necessary` / `symmetric_weight_proper` / `symmetric_weight_strictly_proper` —
  Corollary ("Special cases of the Savage representation"), part (c), in the corrected form. For a
  symmetric deviation operator `D_φ(y, ŷ) = φ(y − ŷ)` with `φ` even and differentiable, the expected
  loss at the true probability `p` of the report `q` is `p φ(1 − q) + (1 − p) φ(q)` (`expLoss`).
  With the weight `w(t) = φ'(t) / t`: properness forces `w(p) = w(1 − p)` (first-order condition at
  the interior minimum), and conversely a symmetric `w ≥ 0` gives `L_p'(q) = w(q)(q − p)`, hence
  properness (strict if `w > 0`). An earlier version of the paper concluded from the first-order
  condition that `φ'` must be linear, so that squared error is the unique proper symmetric
  deviation operator; that is false.
* `polyPhi`, `poly_strictly_proper`, `polyPhi_not_prop_sq` — a strictly proper symmetric deviation
  operator not proportional to squared error (`φ(t) = (5/8)t² − t³/3 + t⁴/4`, weight
  `1 + (t − 1/2)²`); `quartic_not_proper` — `φ(t) = t⁴` (smooth, convex) is not proper;
  `sq_strictly_proper` — squared error as an instance.
* `concave_tangent_le`, `savage_sufficiency`, `savage_strict_sufficiency` — Theorem ("Savage
  representation"), sufficiency: for concave (strictly concave) differentiable `G` on `[0,1]` the
  sections `D(1,·) = G + (1 − ·) G'` and `D(0,·) = G − · G'` give a proper (strictly proper) scoring
  rule.
* `SavageProper`, `SavageStrictlyProper`, `bayesRisk`, `bayesRisk_tangent`, `bayesRisk_concave`,
  `bayesRisk_strictConcave`, `bayesRisk_hasDerivWithinAt`, `savage_necessity`,
  `savage_strict_necessity`, `savage_sufficiency_within`, `savage_strict_sufficiency_within`,
  `savage_iff`, `savage_strict_iff` — Theorem ("Savage representation"), both directions. For a cell
  operator whose sections `ℓ1 = D(1,·)`, `ℓ0 = D(0,·)` are merely *continuous* on `[0,1]`: proper iff
  `ℓ1 = G + (1 − ·) G'`, `ℓ0 = G − · G'` for a concave `G` that is differentiable on `[0,1]`
  (one-sided at the endpoints); strictly proper iff `G` is strictly concave. The proof: `G` is the Bayes
  risk `G(p) = p ℓ1(p) + (1 − p) ℓ0(p)`, a pointwise minimum of functions affine in `p`, hence concave;
  `d = ℓ1 − ℓ0` is a supergradient, and the slope of `G` at `x` is squeezed between `d(y)` and `d(x)`,
  so continuity of `d` gives `G' = d`. Only continuity of the sections is used, not `C¹`.
-/

namespace Aggmetrics.Savage

/-- Expected loss, at the true probability `p`, of the report `q` under the symmetric deviation
operator `D_φ(y, ŷ) = φ(y − ŷ)` with `φ` even: `y = 1` contributes `φ(1 − q)` and `y = 0`
contributes `φ(0 − q) = φ(q)`. -/
noncomputable def expLoss (φ : ℝ → ℝ) (p q : ℝ) : ℝ := p * φ (1 - q) + (1 - p) * φ q

theorem expLoss_hasDerivAt (φ φ' : ℝ → ℝ) (hd : ∀ t, HasDerivAt φ (φ' t) t) (p q : ℝ) :
    HasDerivAt (expLoss φ p) (-p * φ' (1 - q) + (1 - p) * φ' q) q := by
  have h1 : HasDerivAt (fun x => φ (1 - x)) (-φ' (1 - q)) q := by
    exact (hd (1 - q)).comp_const_sub 1 q
  have h2 := (h1.const_mul p).add ((hd q).const_mul (1 - p))
  unfold expLoss
  convert h2 using 1
  ring

/-- Necessity: if the symmetric deviation operator `φ(y − ŷ)` (with `φ` differentiable) is proper
on `[0,1]`, then its weight `φ'(t)/t` is symmetric about `1/2`:
`(1 − p) φ'(p) = p φ'(1 − p)` for every `p ∈ (0,1)` (the first-order condition). -/
theorem symmetric_weight_necessary (φ φ' : ℝ → ℝ) (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hprop : ∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 → expLoss φ p p ≤ expLoss φ p q)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : (1 - p) * φ' p = p * φ' (1 - p) := by
  have hmin : IsLocalMin (expLoss φ p) p := by
    have hI : Set.Icc (0 : ℝ) 1 ∈ nhds p := Icc_mem_nhds hp0 hp1
    filter_upwards [hI] with q hq
    exact hprop p q hp0.le hp1.le hq.1 hq.2
  have h0 := hmin.hasDerivAt_eq_zero (expLoss_hasDerivAt φ φ' hd p p)
  linarith

theorem expLoss_deriv_eq (φ φ' w : ℝ → ℝ) (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hw : ∀ t, 0 ≤ t → t ≤ 1 → φ' t = t * w t)
    (hsym : ∀ t, 0 ≤ t → t ≤ 1 → w (1 - t) = w t) (p x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    deriv (expLoss φ p) x = w x * (x - p) := by
  rw [(expLoss_hasDerivAt φ φ' hd p x).deriv, hw x h0 h1, hw (1 - x) (by linarith) (by linarith),
    hsym x h0 h1]
  ring

/-- Sufficiency: if `φ'(t) = t · w(t)` on `[0,1]` with `w ≥ 0` symmetric about `1/2`, the symmetric
deviation operator is proper: `L_p'(q) = w(q)(q − p)`, so `L_p` decreases up to `p` and increases
after it. -/
theorem symmetric_weight_proper (φ φ' w : ℝ → ℝ) (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hw : ∀ t, 0 ≤ t → t ≤ 1 → φ' t = t * w t)
    (hsym : ∀ t, 0 ≤ t → t ≤ 1 → w (1 - t) = w t) (hw0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ w t)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    expLoss φ p p ≤ expLoss φ p q := by
  have hdiff : Differentiable ℝ (expLoss φ p) := fun x =>
    (expLoss_hasDerivAt φ φ' hd p x).differentiableAt
  rcases le_total p q with hpq | hqp
  · have hmono : MonotoneOn (expLoss φ p) (Set.Icc p q) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc p q) hdiff.continuous.continuousOn
        hdiff.differentiableOn (fun x hx => ?_)
      rw [interior_Icc] at hx
      rw [expLoss_deriv_eq φ φ' w hd hw hsym p x (by linarith [hx.1]) (by linarith [hx.2])]
      exact mul_nonneg (hw0 x (by linarith [hx.1]) (by linarith [hx.2])) (by linarith [hx.1])
    exact hmono (Set.left_mem_Icc.2 hpq) (Set.right_mem_Icc.2 hpq) hpq
  · have hanti : AntitoneOn (expLoss φ p) (Set.Icc q p) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc q p) hdiff.continuous.continuousOn
        hdiff.differentiableOn (fun x hx => ?_)
      rw [interior_Icc] at hx
      rw [expLoss_deriv_eq φ φ' w hd hw hsym p x (by linarith [hx.1]) (by linarith [hx.2])]
      exact mul_nonpos_of_nonneg_of_nonpos (hw0 x (by linarith [hx.1]) (by linarith [hx.2]))
        (by linarith [hx.2])
    exact hanti (Set.left_mem_Icc.2 hqp) (Set.right_mem_Icc.2 hqp) hqp

/-- Strict version: if moreover `w > 0` on `(0,1)`, the operator is strictly proper. -/
theorem symmetric_weight_strictly_proper (φ φ' w : ℝ → ℝ) (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hw : ∀ t, 0 ≤ t → t ≤ 1 → φ' t = t * w t)
    (hsym : ∀ t, 0 ≤ t → t ≤ 1 → w (1 - t) = w t) (hwpos : ∀ t, 0 < t → t < 1 → 0 < w t)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hne : p ≠ q) :
    expLoss φ p p < expLoss φ p q := by
  have hdiff : Differentiable ℝ (expLoss φ p) := fun x =>
    (expLoss_hasDerivAt φ φ' hd p x).differentiableAt
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hmono : StrictMonoOn (expLoss φ p) (Set.Icc p q) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc p q) hdiff.continuous.continuousOn
        (fun x hx => ?_)
      rw [interior_Icc] at hx
      rw [expLoss_deriv_eq φ φ' w hd hw hsym p x (by linarith [hx.1]) (by linarith [hx.2])]
      exact mul_pos (hwpos x (by linarith [hx.1]) (by linarith [hx.2])) (by linarith [hx.1])
    exact hmono (Set.left_mem_Icc.2 hpq.le) (Set.right_mem_Icc.2 hpq.le) hpq
  · have hanti : StrictAntiOn (expLoss φ p) (Set.Icc q p) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc q p) hdiff.continuous.continuousOn
        (fun x hx => ?_)
      rw [interior_Icc] at hx
      rw [expLoss_deriv_eq φ φ' w hd hw hsym p x (by linarith [hx.1]) (by linarith [hx.2])]
      exact mul_neg_of_pos_of_neg (hwpos x (by linarith [hx.1]) (by linarith [hx.2]))
        (by linarith [hx.2])
    exact hanti (Set.left_mem_Icc.2 hqp.le) (Set.right_mem_Icc.2 hqp.le) hqp

/-! ### Instances -/

/-- A proper symmetric deviation operator that is not squared error:
`φ(t) = (5/8) t² − t³/3 + t⁴/4` (on `[0,1]`, extended evenly by `|t|`), weight
`w(t) = 1 + (t − 1/2)²`. -/
noncomputable def polyPhi (t : ℝ) : ℝ := 5 / 8 * t ^ 2 - t ^ 3 / 3 + t ^ 4 / 4
noncomputable def polyPhi' (t : ℝ) : ℝ := 5 / 4 * t - t ^ 2 + t ^ 3
noncomputable def polyW (t : ℝ) : ℝ := 1 + (t - 1 / 2) ^ 2

theorem polyPhi_hasDerivAt (t : ℝ) : HasDerivAt polyPhi (polyPhi' t) t := by
  have h2 := (hasDerivAt_pow 2 t).const_mul (5 / 8 : ℝ)
  have h3 := (hasDerivAt_pow 3 t).div_const 3
  have h4 := (hasDerivAt_pow 4 t).div_const 4
  have h := (h2.sub h3).add h4
  unfold polyPhi polyPhi'
  convert h using 1
  norm_num
  ring

theorem poly_strictly_proper (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hne : p ≠ q) : expLoss polyPhi p p < expLoss polyPhi p q :=
  symmetric_weight_strictly_proper polyPhi polyPhi' polyW polyPhi_hasDerivAt
    (fun t _ _ => by unfold polyPhi' polyW; ring)
    (fun t _ _ => by unfold polyW; ring)
    (fun t _ _ => by unfold polyW; positivity) p q hp0 hp1 hq0 hq1 hne

/-- `polyPhi` is not proportional to `t²` on `[0,1]`: `φ(1) = 13/24` but `φ(1/2) / (1/2)² = 25/48`. -/
theorem polyPhi_not_prop_sq : ¬ ∃ c : ℝ, ∀ t, 0 ≤ t → t ≤ 1 → polyPhi t = c * t ^ 2 := by
  rintro ⟨c, hc⟩
  have h1 := hc 1 (by norm_num) (by norm_num)
  have h2 := hc (1 / 2) (by norm_num) (by norm_num)
  unfold polyPhi at h1 h2
  norm_num at h1 h2
  linarith

/-- The quartic `φ(t) = t⁴` (smooth and convex) is not proper: its weight `4t²` is not symmetric. -/
theorem quartic_not_proper :
    ¬ ∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
      expLoss (fun t => t ^ 4) p p ≤ expLoss (fun t => t ^ 4) p q := by
  intro h
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 4) (4 * t ^ 3) t := fun t => by
    simpa using hasDerivAt_pow 4 t
  have := symmetric_weight_necessary (fun t => t ^ 4) (fun t => 4 * t ^ 3) hd h (1 / 4)
    (by norm_num) (by norm_num)
  norm_num at this

/-- Squared error is an instance: `φ(t) = t²`, `w ≡ 2`. -/
theorem sq_strictly_proper (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hne : p ≠ q) : expLoss (fun t => t ^ 2) p p < expLoss (fun t => t ^ 2) p q := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := fun t => by
    simpa using hasDerivAt_pow 2 t
  exact symmetric_weight_strictly_proper (fun t => t ^ 2) (fun t => 2 * t) (fun _ => 2) hd
    (fun t _ _ => by ring) (fun _ _ _ => rfl) (fun _ _ _ => by norm_num) p q hp0 hp1 hq0 hq1 hne

/-! ### Savage representation: sufficiency -/

/-- Loss section for `y = 1`: `D(1, ŷ) = G(ŷ) + (1 − ŷ) G'(ŷ)`. -/
noncomputable def savageLoss1 (G G' : ℝ → ℝ) (q : ℝ) : ℝ := G q + (1 - q) * G' q

/-- Loss section for `y = 0`: `D(0, ŷ) = G(ŷ) + (0 − ŷ) G'(ŷ)`. -/
noncomputable def savageLoss0 (G G' : ℝ → ℝ) (q : ℝ) : ℝ := G q + (0 - q) * G' q

/-- Gradient (tangent) inequality for a concave differentiable `G` on `[0,1]`. -/
theorem concave_tangent_le (G G' : ℝ → ℝ) (hG : ∀ t, HasDerivAt G (G' t) t)
    (hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G) (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) : G p ≤ G q + (p - q) * G' q := by
  rcases lt_trichotomy p q with h | h | h
  · have h1 := hconc.le_slope_of_hasDerivAt hp hq h (hG q)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at h1
    nlinarith [h1]
  · subst h
    simp
  · have h1 := hconc.slope_le_of_hasDerivAt hq hp h (hG q)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at h1
    nlinarith [h1]

/-- Theorem ("Savage representation"), sufficiency: if `G` is concave and differentiable on
`[0,1]`, the cell operator with sections `D(1,·) = G + (1 − ·) G'` and `D(0,·) = G − · G'` is proper:
the expected loss `p D(1,q) + (1 − p) D(0,q) = G(q) + (p − q) G'(q)` is at least `G(p)`, its value at
the truthful report. -/
theorem savage_sufficiency (G G' : ℝ → ℝ) (hG : ∀ t, HasDerivAt G (G' t) t)
    (hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G) (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    p * savageLoss1 G G' p + (1 - p) * savageLoss0 G G' p
      ≤ p * savageLoss1 G G' q + (1 - p) * savageLoss0 G G' q := by
  have h := concave_tangent_le G G' hG hconc p q hp hq
  unfold savageLoss1 savageLoss0
  nlinarith [h]

/-- Strict version: for strictly concave `G`, truthful reporting is the unique minimiser. -/
theorem savage_strict_sufficiency (G G' : ℝ → ℝ) (hG : ∀ t, HasDerivAt G (G' t) t)
    (hconc : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G) (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hne : p ≠ q) :
    p * savageLoss1 G G' p + (1 - p) * savageLoss0 G G' p
      < p * savageLoss1 G G' q + (1 - p) * savageLoss0 G G' q := by
  have h : G p < G q + (p - q) * G' q := by
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := hconc.lt_slope_of_hasDerivAt hp hq h (hG q)
      rw [slope_def_field, lt_div_iff₀ (sub_pos.2 h)] at h1
      nlinarith [h1]
    · have h1 := hconc.slope_lt_of_hasDerivAt hq hp h (hG q)
      rw [slope_def_field, div_lt_iff₀ (sub_pos.2 h)] at h1
      nlinarith [h1]
  unfold savageLoss1 savageLoss0
  nlinarith [h]

/-! ### Savage representation: necessity and the equivalence -/

open Filter Topology

/-- Properness on `[0,1]` of the cell operator with sections `ℓ1 = D(1,·)`, `ℓ0 = D(0,·)`: for every
true probability `p` the expected loss `p ℓ1(x) + (1 − p) ℓ0(x)` is minimised at `x = p`. -/
def SavageProper (ℓ1 ℓ0 : ℝ → ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    p * ℓ1 p + (1 - p) * ℓ0 p ≤ p * ℓ1 x + (1 - p) * ℓ0 x

/-- Strict properness: the minimiser is unique. -/
def SavageStrictlyProper (ℓ1 ℓ0 : ℝ → ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ p →
    p * ℓ1 p + (1 - p) * ℓ0 p < p * ℓ1 x + (1 - p) * ℓ0 x

/-- The Bayes risk `G(p) = p ℓ1(p) + (1 − p) ℓ0(p)`, the expected loss at the truthful report. -/
noncomputable def bayesRisk (ℓ1 ℓ0 : ℝ → ℝ) (p : ℝ) : ℝ := p * ℓ1 p + (1 - p) * ℓ0 p

/-- Supergradient inequality: `d = ℓ1 − ℓ0` is a supergradient of the Bayes risk. -/
theorem bayesRisk_tangent (ℓ1 ℓ0 : ℝ → ℝ) (h : SavageProper ℓ1 ℓ0) (p x : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    bayesRisk ℓ1 ℓ0 p ≤ bayesRisk ℓ1 ℓ0 x + (p - x) * (ℓ1 x - ℓ0 x) := by
  have h1 := h p hp x hx
  have e : p * ℓ1 x + (1 - p) * ℓ0 x
      = x * ℓ1 x + (1 - x) * ℓ0 x + (p - x) * (ℓ1 x - ℓ0 x) := by ring
  unfold bayesRisk
  linarith

theorem bayesRisk_tangent_strict (ℓ1 ℓ0 : ℝ → ℝ) (h : SavageStrictlyProper ℓ1 ℓ0) (p x : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hne : x ≠ p) :
    bayesRisk ℓ1 ℓ0 p < bayesRisk ℓ1 ℓ0 x + (p - x) * (ℓ1 x - ℓ0 x) := by
  have h1 := h p hp x hx hne
  have e : p * ℓ1 x + (1 - p) * ℓ0 x
      = x * ℓ1 x + (1 - x) * ℓ0 x + (p - x) * (ℓ1 x - ℓ0 x) := by ring
  unfold bayesRisk
  linarith

/-- The Bayes risk of a proper rule is concave: it is a pointwise minimum of functions affine in `p`. -/
theorem bayesRisk_concave (ℓ1 ℓ0 : ℝ → ℝ) (h : SavageProper ℓ1 ℓ0) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (bayesRisk ℓ1 ℓ0) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro p hp p' hp' a b ha hb hab
  have hr : a • p + b • p' ∈ Set.Icc (0 : ℝ) 1 := (convex_Icc (0 : ℝ) 1) hp hp' ha hb hab
  simp only [smul_eq_mul] at hr ⊢
  obtain ⟨r, hr_def⟩ : ∃ r, r = a * p + b * p' := ⟨_, rfl⟩
  rw [← hr_def] at hr ⊢
  have h1 := bayesRisk_tangent ℓ1 ℓ0 h p r hp hr
  have h2 := bayesRisk_tangent ℓ1 ℓ0 h p' r hp' hr
  have hz : a * (p - r) + b * (p' - r) = 0 := by
    rw [hr_def]; linear_combination (-(a * p + b * p')) * hab
  calc a * bayesRisk ℓ1 ℓ0 p + b * bayesRisk ℓ1 ℓ0 p'
      ≤ a * (bayesRisk ℓ1 ℓ0 r + (p - r) * (ℓ1 r - ℓ0 r))
        + b * (bayesRisk ℓ1 ℓ0 r + (p' - r) * (ℓ1 r - ℓ0 r)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = (a + b) * bayesRisk ℓ1 ℓ0 r + (ℓ1 r - ℓ0 r) * (a * (p - r) + b * (p' - r)) := by ring
    _ = bayesRisk ℓ1 ℓ0 r := by rw [hz, hab]; ring

/-- A strictly proper rule has a strictly concave Bayes risk. -/
theorem bayesRisk_strictConcave (ℓ1 ℓ0 : ℝ → ℝ) (h : SavageStrictlyProper ℓ1 ℓ0) :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (bayesRisk ℓ1 ℓ0) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro p hp p' hp' hpp a b ha hb hab
  have hr : a • p + b • p' ∈ Set.Icc (0 : ℝ) 1 := (convex_Icc (0 : ℝ) 1) hp hp' ha.le hb.le hab
  simp only [smul_eq_mul] at hr ⊢
  obtain ⟨r, hr_def⟩ : ∃ r, r = a * p + b * p' := ⟨_, rfl⟩
  rw [← hr_def] at hr ⊢
  have hrp : r ≠ p := by
    intro e
    have : b * (p' - p) = 0 := by rw [hr_def] at e; linear_combination e - p * hab
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hb.ne' h0
    · exact hpp (by linarith)
  have hrp' : r ≠ p' := by
    intro e
    have : a * (p - p') = 0 := by rw [hr_def] at e; linear_combination e - p' * hab
    rcases mul_eq_zero.mp this with h0 | h0
    · exact ha.ne' h0
    · exact hpp (by linarith)
  have h1 := bayesRisk_tangent_strict ℓ1 ℓ0 h p r hp hr hrp
  have h2 := bayesRisk_tangent_strict ℓ1 ℓ0 h p' r hp' hr hrp'
  have hz : a * (p - r) + b * (p' - r) = 0 := by
    rw [hr_def]; linear_combination (-(a * p + b * p')) * hab
  calc a * bayesRisk ℓ1 ℓ0 p + b * bayesRisk ℓ1 ℓ0 p'
      < a * (bayesRisk ℓ1 ℓ0 r + (p - r) * (ℓ1 r - ℓ0 r))
        + b * (bayesRisk ℓ1 ℓ0 r + (p' - r) * (ℓ1 r - ℓ0 r)) :=
        add_lt_add (mul_lt_mul_of_pos_left h1 ha) (mul_lt_mul_of_pos_left h2 hb)
    _ = (a + b) * bayesRisk ℓ1 ℓ0 r + (ℓ1 r - ℓ0 r) * (a * (p - r) + b * (p' - r)) := by ring
    _ = bayesRisk ℓ1 ℓ0 r := by rw [hz, hab]; ring

/-- Differentiability of the Bayes risk of a proper rule with continuous sections, with derivative
`ℓ1 − ℓ0`: the slope of `G` at `x` lies between the supergradients `d(y)` and `d(x)`, so it differs
from `d(x)` by at most `|d(y) − d(x)|`, which tends to `0` by continuity. -/
theorem bayesRisk_hasDerivWithinAt (ℓ1 ℓ0 : ℝ → ℝ) (hc1 : ContinuousOn ℓ1 (Set.Icc (0 : ℝ) 1))
    (hc0 : ContinuousOn ℓ0 (Set.Icc (0 : ℝ) 1)) (h : SavageProper ℓ1 ℓ0) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (bayesRisk ℓ1 ℓ0) (ℓ1 x - ℓ0 x) (Set.Icc (0 : ℝ) 1) x := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hd : ContinuousOn (fun y => ℓ1 y - ℓ0 y) (Set.Icc (0 : ℝ) 1) := hc1.sub hc0
  have hdx : Tendsto (fun y => ℓ1 y - ℓ0 y) (𝓝[Set.Icc (0 : ℝ) 1 \ {x}] x) (𝓝 (ℓ1 x - ℓ0 x)) :=
    (hd x hx).tendsto.mono_left (nhdsWithin_mono x Set.sdiff_subset)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hdx' := tendsto_iff_norm_sub_tendsto_zero.mp hdx
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hdx'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hne : y ≠ x := hy.2
  have t1 := bayesRisk_tangent ℓ1 ℓ0 h y x hy.1 hx
  have t2 := bayesRisk_tangent ℓ1 ℓ0 h x y hx hy.1
  rw [slope_def_field, Real.norm_eq_abs, Real.norm_eq_abs]
  have hA := neg_abs_le ((ℓ1 y - ℓ0 y) - (ℓ1 x - ℓ0 x))
  have hB := le_abs_self ((ℓ1 y - ℓ0 y) - (ℓ1 x - ℓ0 x))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hc : y - x < 0 := by linarith
    have hlo : ℓ1 x - ℓ0 x ≤ (bayesRisk ℓ1 ℓ0 y - bayesRisk ℓ1 ℓ0 x) / (y - x) := by
      rw [le_div_iff_of_neg hc]; nlinarith [t1]
    have hup : (bayesRisk ℓ1 ℓ0 y - bayesRisk ℓ1 ℓ0 x) / (y - x) ≤ ℓ1 y - ℓ0 y := by
      rw [div_le_iff_of_neg hc]; nlinarith [t2]
    rw [abs_le]; constructor <;> linarith
  · have hc : 0 < y - x := by linarith
    have hlo : ℓ1 y - ℓ0 y ≤ (bayesRisk ℓ1 ℓ0 y - bayesRisk ℓ1 ℓ0 x) / (y - x) := by
      rw [le_div_iff₀ hc]; nlinarith [t2]
    have hup : (bayesRisk ℓ1 ℓ0 y - bayesRisk ℓ1 ℓ0 x) / (y - x) ≤ ℓ1 x - ℓ0 x := by
      rw [div_le_iff₀ hc]; nlinarith [t1]
    rw [abs_le]; constructor <;> linarith

/-- Theorem ("Savage representation"), necessity: a proper cell operator with continuous sections
`D(1,·) = ℓ1`, `D(0,·) = ℓ0` on `[0,1]` is of the form `D(1,·) = G + (1 − ·) G'`,
`D(0,·) = G − · G'` for a concave `G` differentiable on `[0,1]` (one-sided at the endpoints). -/
theorem savage_necessity (ℓ1 ℓ0 : ℝ → ℝ) (hc1 : ContinuousOn ℓ1 (Set.Icc (0 : ℝ) 1))
    (hc0 : ContinuousOn ℓ0 (Set.Icc (0 : ℝ) 1)) (h : SavageProper ℓ1 ℓ0) :
    ∃ G G' : ℝ → ℝ, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' x) (Set.Icc (0 : ℝ) 1) x) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ℓ1 x = savageLoss1 G G' x ∧ ℓ0 x = savageLoss0 G G' x :=
  ⟨bayesRisk ℓ1 ℓ0, fun x => ℓ1 x - ℓ0 x, bayesRisk_concave ℓ1 ℓ0 h,
    fun x hx => bayesRisk_hasDerivWithinAt ℓ1 ℓ0 hc1 hc0 h x hx,
    fun x _ => ⟨by unfold savageLoss1 bayesRisk; ring, by unfold savageLoss0 bayesRisk; ring⟩⟩

/-- Strict version: a strictly proper rule has a strictly concave `G`. -/
theorem savage_strict_necessity (ℓ1 ℓ0 : ℝ → ℝ) (hc1 : ContinuousOn ℓ1 (Set.Icc (0 : ℝ) 1))
    (hc0 : ContinuousOn ℓ0 (Set.Icc (0 : ℝ) 1)) (h : SavageStrictlyProper ℓ1 ℓ0) :
    ∃ G G' : ℝ → ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' x) (Set.Icc (0 : ℝ) 1) x) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ℓ1 x = savageLoss1 G G' x ∧ ℓ0 x = savageLoss0 G G' x := by
  have hp : SavageProper ℓ1 ℓ0 := fun p hp x hx => by
    by_cases hxp : x = p
    · subst hxp; exact le_refl _
    · exact (h p hp x hx hxp).le
  exact ⟨bayesRisk ℓ1 ℓ0, fun x => ℓ1 x - ℓ0 x, bayesRisk_strictConcave ℓ1 ℓ0 h,
    fun x hx => bayesRisk_hasDerivWithinAt ℓ1 ℓ0 hc1 hc0 hp x hx,
    fun x _ => ⟨by unfold savageLoss1 bayesRisk; ring, by unfold savageLoss0 bayesRisk; ring⟩⟩

/-! ### Sufficiency over `[0,1]` (derivative within the interval) -/

theorem concave_tangent_le_within (G G' : ℝ → ℝ)
    (hG : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' x) (Set.Icc (0 : ℝ) 1) x)
    (hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G) (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) : G p ≤ G q + (p - q) * G' q := by
  rcases lt_trichotomy p q with h | h | h
  · have h1 := hconc.le_slope_of_hasDerivWithinAt hp hq h (hG q hq)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at h1
    nlinarith [h1]
  · subst h
    simp
  · have h1 := hconc.slope_le_of_hasDerivWithinAt hq hp h (hG q hq)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at h1
    nlinarith [h1]

theorem savage_sufficiency_within (G G' : ℝ → ℝ)
    (hG : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' x) (Set.Icc (0 : ℝ) 1) x)
    (hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G) (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    p * savageLoss1 G G' p + (1 - p) * savageLoss0 G G' p
      ≤ p * savageLoss1 G G' q + (1 - p) * savageLoss0 G G' q := by
  have h := concave_tangent_le_within G G' hG hconc p q hp hq
  unfold savageLoss1 savageLoss0
  nlinarith [h]

theorem savage_strict_sufficiency_within (G G' : ℝ → ℝ)
    (hG : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' x) (Set.Icc (0 : ℝ) 1) x)
    (hconc : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G) (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hne : q ≠ p) :
    p * savageLoss1 G G' p + (1 - p) * savageLoss0 G G' p
      < p * savageLoss1 G G' q + (1 - p) * savageLoss0 G G' q := by
  have h : G p < G q + (p - q) * G' q := by
    rcases lt_or_gt_of_ne (Ne.symm hne) with h | h
    · have h1 := hconc.lt_slope_of_hasDerivWithinAt hp hq h (hG q hq)
      rw [slope_def_field, lt_div_iff₀ (sub_pos.2 h)] at h1
      nlinarith [h1]
    · have h1 := hconc.slope_lt_of_hasDerivWithinAt hq hp h (hG q hq)
      rw [slope_def_field, div_lt_iff₀ (sub_pos.2 h)] at h1
      nlinarith [h1]
  unfold savageLoss1 savageLoss0
  nlinarith [h]

/-- Theorem ("Savage representation"), the equivalence: a cell operator with continuous sections
on `[0,1]` is proper iff `D(1,·) = G + (1 − ·) G'`, `D(0,·) = G − · G'` for a concave `G`,
differentiable on `[0,1]`. -/
theorem savage_iff (ℓ1 ℓ0 : ℝ → ℝ) (hc1 : ContinuousOn ℓ1 (Set.Icc (0 : ℝ) 1))
    (hc0 : ContinuousOn ℓ0 (Set.Icc (0 : ℝ) 1)) :
    SavageProper ℓ1 ℓ0 ↔ ∃ G G' : ℝ → ℝ, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' x) (Set.Icc (0 : ℝ) 1) x) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ℓ1 x = savageLoss1 G G' x ∧ ℓ0 x = savageLoss0 G G' x := by
  constructor
  · exact savage_necessity ℓ1 ℓ0 hc1 hc0
  · rintro ⟨G, G', hconc, hG, hrep⟩ p hp x hx
    have := savage_sufficiency_within G G' hG hconc p x hp hx
    rw [(hrep p hp).1, (hrep p hp).2, (hrep x hx).1, (hrep x hx).2]
    exact this

/-- The equivalence for strict properness and strict concavity. -/
theorem savage_strict_iff (ℓ1 ℓ0 : ℝ → ℝ) (hc1 : ContinuousOn ℓ1 (Set.Icc (0 : ℝ) 1))
    (hc0 : ContinuousOn ℓ0 (Set.Icc (0 : ℝ) 1)) :
    SavageStrictlyProper ℓ1 ℓ0 ↔ ∃ G G' : ℝ → ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' x) (Set.Icc (0 : ℝ) 1) x) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ℓ1 x = savageLoss1 G G' x ∧ ℓ0 x = savageLoss0 G G' x := by
  constructor
  · exact savage_strict_necessity ℓ1 ℓ0 hc1 hc0
  · rintro ⟨G, G', hconc, hG, hrep⟩ p hp x hx hne
    have := savage_strict_sufficiency_within G G' hG hconc p x hp hx hne
    rw [(hrep p hp).1, (hrep p hp).2, (hrep x hx).1, (hrep x hx).2]
    exact this

end Aggmetrics.Savage

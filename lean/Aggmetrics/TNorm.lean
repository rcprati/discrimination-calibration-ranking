import Aggmetrics.Basic

/-!
# Formalization of Theorem 3 from the base paper: marginal consistency characterises the
product t-norm

`papers/01-unified-framework/paper/main.tex`, Theorem `thm:partition` ("The product t-norm is the unique
marginally consistent t-norm"): a t-norm `T` (bare axioms only — commutative, associative,
monotone, with neutral element `1`, no continuity or Archimedean assumption) satisfies the
marginal-consistency identity `T(a,b) + T(1-a,b) = b` for all `a,b ∈ [0,1]` if and only if
`T(a,b) = a*b`. This is the theorem behind the fix applied to
`papers/06-generalised-confusion/paper/sec2_background.tex` after the collaborator's critique of
the (unrelated, weaker) partition-only property.

The published proof is a genuinely explicit three-step argument, faithfully reproduced here:

1. `halving` — setting `a = 1/2` in the marginal identity pins down `T(1/2,b) = b/2` directly.
2. `dyadic` — induction on `k` extends this to `T(m/2^k, b) = (m/2^k)·b` for every dyadic
   rational `m/2^k ∈ [0,1]`, by composing the halving identity with associativity (for
   `m ≤ 2^k`) and the marginal identity itself (for `m > 2^k`, via the "mirror" numerator
   `2^k - m`).
3. The final step extends from the dense set of dyadic rationals to every real `a ∈ [0,1]`, not
   via continuity of `T` (which is *not* assumed) but via `T`'s own monotonicity: `T(·,b)` is
   sandwiched between `d·b` and `e·b` for dyadic `d ≤ a ≤ e` arbitrarily close together, forcing
   `T(a,b) = a·b` exactly.
-/

namespace Aggmetrics.TNorm

/-- Theorem (The product t-norm is the unique marginally consistent t-norm): under the bare
t-norm axioms (closure, commutativity, associativity, monotonicity in the first argument,
neutral element `1`), the marginal-consistency identity holds at every `(a,b) ∈ [0,1]²` iff `T`
is the product. -/
theorem marginal_consistency_iff_product
    (T : ℝ → ℝ → ℝ)
    (hclosed : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ T a b ∧ T a b ≤ 1)
    (hcomm : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → T a b = T b a)
    (hassoc : ∀ a b c, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ c → c ≤ 1 →
      T (T a b) c = T a (T b c))
    (hmono : ∀ a a' b, 0 ≤ a → a ≤ 1 → 0 ≤ a' → a' ≤ 1 → 0 ≤ b → b ≤ 1 → a ≤ a' →
      T a b ≤ T a' b)
    (hid : ∀ a, 0 ≤ a → a ≤ 1 → T a 1 = a) :
    (∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → T a b + T (1 - a) b = b) ↔
      (∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → T a b = a * b) := by
  constructor
  swap
  · intro hprod a b ha1 ha2 hb1 hb2
    rw [hprod a b ha1 ha2 hb1 hb2, hprod (1 - a) b (by linarith) (by linarith) hb1 hb2]
    ring
  intro hmarg
  -- Step 1: the halving identity.
  have halving : ∀ c, 0 ≤ c → c ≤ 1 → T (1 / 2) c = c / 2 := by
    intro c hc1 hc2
    have h := hmarg (1 / 2) c (by norm_num) (by norm_num) hc1 hc2
    have hsymm : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hsymm] at h
    linarith
  -- T(0,b) = 0 and T(1,b) = b, needed for the k = 0 base case.
  have hzero_left : ∀ b, 0 ≤ b → b ≤ 1 → T 0 b = 0 := by
    intro b hb1 hb2
    have h1 : T b 0 ≤ T 1 0 :=
      hmono b 1 0 hb1 hb2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb2
    have h2 : T 1 0 = 0 := by
      rw [hcomm 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
      exact hid 0 (by norm_num) (by norm_num)
    have h3 : 0 ≤ T b 0 := (hclosed b 0 hb1 hb2 (by norm_num) (by norm_num)).1
    have h4 : T b 0 = 0 := le_antisymm (by linarith) h3
    rw [hcomm 0 b (by norm_num) (by norm_num) hb1 hb2]
    exact h4
  have hone_left : ∀ b, 0 ≤ b → b ≤ 1 → T 1 b = b := by
    intro b hb1 hb2
    rw [hcomm 1 b (by norm_num) (by norm_num) hb1 hb2]
    exact hid b hb1 hb2
  -- Step 2: extend to every dyadic rational, by induction on k.
  have dyadic : ∀ k : ℕ, ∀ m : ℕ, m ≤ 2 ^ k → ∀ b, 0 ≤ b → b ≤ 1 →
      T ((m : ℝ) / 2 ^ k) b = ((m : ℝ) / 2 ^ k) * b := by
    intro k
    induction k with
    | zero =>
      intro m hm b hb1 hb2
      interval_cases m
      · simpa using hzero_left b hb1 hb2
      · simpa using hone_left b hb1 hb2
    | succ k ih =>
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have case1 : ∀ m : ℕ, m ≤ 2 ^ k → ∀ b, 0 ≤ b → b ≤ 1 →
          T ((m : ℝ) / 2 ^ (k + 1)) b = ((m : ℝ) / 2 ^ (k + 1)) * b := by
        intro m hm b hb1 hb2
        have hmR : (0 : ℝ) ≤ (m : ℝ) / 2 ^ k := by positivity
        have hmR1 : (m : ℝ) / 2 ^ k ≤ 1 := by
          rw [div_le_one hpow_pos]; exact_mod_cast hm
        have heq : ((m : ℝ) / 2 ^ k) / 2 = (m : ℝ) / 2 ^ (k + 1) := by
          rw [pow_succ]; ring
        have hhalf : T (1 / 2) ((m : ℝ) / 2 ^ k) = (m : ℝ) / 2 ^ (k + 1) := by
          rw [halving _ hmR hmR1, heq]
        have hIH : T ((m : ℝ) / 2 ^ k) b = ((m : ℝ) / 2 ^ k) * b := ih m hm b hb1 hb2
        have hprodmem0 : 0 ≤ ((m : ℝ) / 2 ^ k) * b := by positivity
        have hprodmem1 : ((m : ℝ) / 2 ^ k) * b ≤ 1 := by
          calc ((m : ℝ) / 2 ^ k) * b ≤ 1 * 1 := mul_le_mul hmR1 hb2 hb1 (by norm_num)
            _ = 1 := by ring
        have hassoc1 : T (T (1 / 2) ((m : ℝ) / 2 ^ k)) b = T (1 / 2) (T ((m : ℝ) / 2 ^ k) b) :=
          hassoc (1 / 2) ((m : ℝ) / 2 ^ k) b (by norm_num) (by norm_num) hmR hmR1 hb1 hb2
        rw [hhalf] at hassoc1
        rw [hassoc1, hIH, halving _ hprodmem0 hprodmem1, ← heq]
        ring
      intro m hm b hb1 hb2
      by_cases hle : m ≤ 2 ^ k
      · exact case1 m hle b hb1 hb2
      · have hgt : 2 ^ k < m := by omega
        set m' := 2 ^ (k + 1) - m with hm'def
        have hpowsplit : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
        have hm'lt : m' < 2 ^ k := by omega
        have hm'le : m' ≤ 2 ^ k := hm'lt.le
        have hsum : (m' : ℝ) + (m : ℝ) = 2 ^ (k + 1) := by
          have hsumN : m' + m = 2 ^ (k + 1) := by omega
          exact_mod_cast hsumN
        have hpow_pos' : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
        have hmR1' : (0 : ℝ) ≤ (m : ℝ) / 2 ^ (k + 1) ∧ (m : ℝ) / 2 ^ (k + 1) ≤ 1 := by
          refine ⟨by positivity, ?_⟩
          rw [div_le_one hpow_pos']; exact_mod_cast hm
        have hm'R : (m' : ℝ) / 2 ^ (k + 1) = 1 - (m : ℝ) / 2 ^ (k + 1) := by
          field_simp
          linarith [hsum]
        have hcase1' : T ((m' : ℝ) / 2 ^ (k + 1)) b = ((m' : ℝ) / 2 ^ (k + 1)) * b :=
          case1 m' hm'le b hb1 hb2
        have hmarg' := hmarg ((m : ℝ) / 2 ^ (k + 1)) b hmR1'.1 hmR1'.2 hb1 hb2
        rw [← hm'R, hcase1', hm'R] at hmarg'
        have hfinal : T ((m : ℝ) / 2 ^ (k + 1)) b
            = b - (1 - (m : ℝ) / 2 ^ (k + 1)) * b := by linarith [hmarg']
        rw [hfinal]; ring
  -- Step 3: extend from dyadic rationals to every real in [0,1], via monotonicity (not
  -- continuity of T, which is not assumed).
  intro a b ha1 ha2 hb1 hb2
  rcases ha2.lt_or_eq with ha2' | rfl
  swap
  · simpa using hone_left b hb1 hb2
  have hzero : ∀ ε : ℝ, 0 < ε → |T a b - a * b| ≤ ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 : ℝ) / 2 < 1)
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have ha2npos : (0 : ℝ) ≤ a * 2 ^ n := by positivity
    have ha2nlt : a * 2 ^ n < 2 ^ n := by nlinarith [ha2', hpow_pos]
    set m := Nat.floor (a * 2 ^ n) with hmdef
    have hmle : (m : ℝ) ≤ a * 2 ^ n := Nat.floor_le ha2npos
    have hmlt1 : a * 2 ^ n < (m : ℝ) + 1 := Nat.lt_floor_add_one (a * 2 ^ n)
    have hmltpow : (m : ℝ) < 2 ^ n := lt_of_le_of_lt hmle ha2nlt
    have hmnat : m < 2 ^ n := by exact_mod_cast hmltpow
    have hmnat1 : m + 1 ≤ 2 ^ n := hmnat
    set d := (m : ℝ) / 2 ^ n with hddef
    set e := ((m : ℝ) + 1) / 2 ^ n with hedef
    have hd_le_a : d ≤ a := by rw [hddef, div_le_iff₀ hpow_pos]; linarith [hmle]
    have ha_le_e : a ≤ e := by rw [hedef, le_div_iff₀ hpow_pos]; linarith [hmlt1]
    have hd0 : 0 ≤ d := by rw [hddef]; positivity
    have hd1 : d ≤ 1 := le_trans hd_le_a ha2
    have he1 : e ≤ 1 := by
      rw [hedef, div_le_one hpow_pos]
      have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]; exact_mod_cast hmnat1
    have he0 : 0 ≤ e := le_trans hd0 (le_trans hd_le_a ha_le_e)
    have hTd : T d b = d * b := dyadic n m hmnat.le b hb1 hb2
    have hTe : T e b = e * b := by
      have heval := dyadic n (m + 1) hmnat1 b hb1 hb2
      have hcast : ((m + 1 : ℕ) : ℝ) / 2 ^ n = e := by rw [hedef]; push_cast; ring
      rwa [hcast] at heval
    have hmono1 : T d b ≤ T a b := hmono d a b hd0 hd1 ha1 ha2 hb1 hb2 hd_le_a
    have hmono2 : T a b ≤ T e b := hmono a e b ha1 ha2 he0 he1 hb1 hb2 ha_le_e
    rw [hTd] at hmono1
    rw [hTe] at hmono2
    have hde : e - d = 1 / 2 ^ n := by rw [hddef, hedef]; field_simp; ring
    have hbound : e * b - d * b ≤ 1 / 2 ^ n := by
      have hrw : e * b - d * b = (e - d) * b := by ring
      rw [hrw, hde]
      calc (1 / 2 ^ n) * b ≤ (1 / 2 ^ n) * 1 :=
            mul_le_mul_of_nonneg_left hb2 (by positivity)
        _ = 1 / 2 ^ n := by ring
    have hab_le_e : a * b ≤ e * b := mul_le_mul_of_nonneg_right ha_le_e hb1
    have hd_le_ab : d * b ≤ a * b := mul_le_mul_of_nonneg_right hd_le_a hb1
    have hn' : (1 : ℝ) / 2 ^ n < ε := by
      have hpoweq : (1 : ℝ) / 2 ^ n = (1 / 2 : ℝ) ^ n := by rw [div_pow]; norm_num
      rw [hpoweq]; exact hn
    rw [abs_le]
    constructor
    · linarith [hmono2, hab_le_e]
    · linarith [hmono1, hd_le_ab]
  by_contra hne
  have habs : 0 < |T a b - a * b| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have h2 := hzero (|T a b - a * b| / 2) (half_pos habs)
  linarith

end Aggmetrics.TNorm

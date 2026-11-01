import Aggmetrics.Basic
import Aggmetrics.Mixture

/-!
# Formalization of results from `papers/06-generalised-confusion/paper`'s ranking section

`sec5_ranking.tex`. The following results are formalized here:

* `auc_mean_rank` — Proposition ("AUC as a normalised mean rank"): the Mann–Whitney U identity
  connecting the mean descending rank of positive examples to AUC.

  The paper's proof leans on one combinatorial fact — that exactly `n⁺(n⁺-1)/2` ordered pairs of
  distinct positives satisfy a strict score comparison — which is a general fact about any finite
  injectively-scored set, independent of AUC or ranking specifically. It is proved separately below
  as `sum_card_filter_lt_eq_triangular`, by induction on the finset via repeatedly extracting its
  `f`-maximal element (a genuinely different toolkit from the rest of this project — finite order
  combinatorics, not algebra or measure theory) — rather than assumed.
* `raw_aggregation_collapse` — Theorem ("Raw DCG collapses", part (a); identically the raw half of
  "Collapse and non-collapse for AUC"): the micro, per-class, and per-example raw aggregations of
  any real cell matrix coincide, by resumming a finite double sum in either order. Proved once for
  an arbitrary matrix, since neither DCG nor AUC specifics are used.
* `weighted_vs_unweighted_mean` — the general covariance identity behind the *non*-collapse halves
  of both collapse theorems: the gap between a `b`-weighted mean and the unweighted mean of a ratio
  equals their empirical covariance divided by the mean of `b`.
* `conditional_mean_of_indicator_sum` — the algebraic core shared by "Per-class nDCG as conditional
  mean" and the substantive half of "Row-Column Duality": a population average of an
  indicator-weighted quantity equals the prevalence times the conditional average over the
  indicated subset.
* `uniform_weight_average_invariant` / `ndcg_class_skew_invariant` / `auc_class_skew_invariant` —
  Propositions ("Per-class nDCG is skew-invariant" and "AUC_j ... skew-invariant", part (a)): replicating
  every member of a subset by the same nonzero factor — the formal content of "replicating
  examples `λ`-fold" — leaves the average of any quantity over that subset unchanged. One general
  lemma, applied once for nDCG (over the positive set) and twice, nested, for AUC (over negatives
  inside the concordance fraction, then over positives outside it), exactly mirroring the paper's
  own two-step replication argument.
* `rank_reparam_invariant` / `not_strictly_proper_of_rank_dependent` — the non-strict-properness
  halves of Proposition "Positional operators are not strictly proper" and the non-uniqueness
  mechanism of "AUC_j is not strictly proper" (the paper proves the second by citing the first's
  argument): any score depending on its report only through the induced rank assigns identical
  values to a report and to that report shifted by a constant — a different report inducing the
  same ranking — so no maximiser of such a score is ever unique. The positional score is an
  instance (take `F r = ∑ j, p j * w (r j)`); for AUC see the `aucScore` bullet below.
* `ndcg_ex_skew_counterexample` — Proposition ("Exemplar nDCG is skew-sensitive"): unlike the
  skew-*invariance* results above, this proposition's content is existential (the average changes
  for *some* configuration where the replicated group differs from the rest), not universal, so it
  is rendered as an explicit instance rather than a general theorem: two examples with per-example
  nDCG values `1, 0` average to `1/2`; replicating the positive example once more (`1, 1, 0`, the
  paper's `λ=2`) shifts the average to `2/3`.
* `positional_score_maximized_at_sorted_rank` / `positional_properness` — the "is proper" (weak)
  half of "Positional operators are not strictly proper", completing that proposition alongside
  the non-strict half above (stated for the expected-score expression `∑ j, p j * w (rank j)` of
  the paper; `positional_expected_properness` below derives it from random labels): for injectively-scored reports `p` (the truth) and `q` (any
  alternative) and antitone weight `w`,
  the positional score under `p` is never smaller than under `q`. Built from Mathlib's
  rearrangement inequality (`Monovary.sum_smul_comp_perm_le_sum_smul`) applied to `p` and
  `w ∘ rank p`, which monovary because `rank` strictly reverses order (`rank_strictAnti`, needing
  no injectivity) — then transported from an arbitrary permutation to an arbitrary report `q` via
  `rank`'s own bijectivity on injectively-scored reports (`rank_bijective`, `rank0`). Together with
  the non-strict half, this closes "Positional operators are not strictly proper" in full.
* `exemplar_average_skew_iff` (via `Aggmetrics.Mixture`) — Proposition ("Exemplar nDCG is
  skew-sensitive"), exact form: replicating the positive examples of a class `lam`-fold versus
  `mu`-fold leaves the exemplar average of nDCG unchanged iff the mean nDCG over positives equals
  the mean over negatives. An earlier version of the paper stated the condition as "the distribution of `IDCG_i`
  differs between the groups", which is not the exact condition; the paper now states the exact one.
* `macro_auc_skew_invariant` / `micro_auc_skew_iff` — Proposition ("`AUC_j` and macro-AUC are
  skew-invariant; micro-AUC is not"), parts (b) and (c): macro-AUC is invariant (average of
  invariant terms); micro-AUC, under scaling one class's positives, is invariant iff that class's
  `AUC_k` equals the micro-AUC itself. (An earlier version gave as reason only that the weights `n⁺_j` vary, which is not sufficient
  on its own; the paper now states the exact condition.)
* `weighted_eq_unweighted_iff_cov_zero` / `weighted_eq_unweighted_of_const` /
  `ndcg_micro_vs_exemplar_counterexample` — Theorems ("Collapse and non-collapse for nDCG / AUC"),
  part (b), exemplar case: the weighted and unweighted means of the per-example ratios coincide iff
  `Cov(b, r) = 0`, in particular when the ideal masses are constant; and a concrete witness where
  micro-nDCG (`1/4`) and exemplar nDCG (`1/2`) differ.
* `ndcg_class_vs_micro_iff` / `ndcg_class_vs_micro_identical_iff` / `idealMass_lt` /
  `ndcg_class_micro_not_identical` — Theorem ("Raw DCG collapses; nDCG does not"), part (b), class
  case, in exact form: micro-nDCG equals the mean of the per-class nDCGs iff one linear equation in
  the class cell sums `T_j` holds, `∑_j T_j (1/B − 1/(m N_j)) = 0` (`N_j = k_j w(1)`,
  `B = ∑_i IDCG_i`); it holds for every `T` iff `m N_j = B` for all `j`; and that is impossible as
  soon as some example has two relevant labels and `w(2) < w(1)`. (This replaces the earlier
  statement that the two "coincide only in degenerate configurations, with no characterisation".)
  `micro_macro_auc_iff_cov_zero` is the AUC analogue (micro versus macro iff `Cov(n⁺_j, AUC_j) = 0`).
  The remaining comparisons of part (b), class mean versus exemplar mean, are
  `class_vs_exemplar_iff` / `class_vs_exemplar_identical_iff` (equal iff one linear equation in the
  cells; for every cell matrix iff `m N_j = n b_i` for all `i, j`) with
  `ndcg_class_exemplar_not_identical` (impossible for nDCG once some example has two relevant labels
  and `w(2) < w(1)`; for AUC, with `N_j = n⁺_j`, `b_i = k_i`, it *can* hold, namely for balanced
  classes and constant `k_i`), and `micro_exemplar_auc_iff_cov_zero` (micro-AUC versus the exemplar
  mean iff `Cov(k_i, AUC_i^ex) = 0`).
* `hardTop`, `rank_hardTop_self`, `rank_hardTop_ne`, `dcg_ex_hardTop_oneHot`,
  `dcg_ex_hardTop_lower_bound`, `hard_ranking_oneHot_average`, `hard_ranking_paper_claim_iff` —
  Proposition ("Hard-prediction limit"). Part (b) (lower bound by `Y_{j*} w(1)`) holds as stated.
  Part (a), as originally stated (exact reduction to `P@1 · w(1) / m`), is false: for one-hot `Y`
  the exemplar average is `(P@1 · w(1) + (1 − P@1) · w(2)) / m` (a wrong top-1 prediction still
  earns `w(2)` through the true class), which reduces to `P@1 · w(1) / m` iff `w(2) = 0`. The
  original argument conflated the predicted label `j*` with the true label; the paper now states
  the corrected formula.
* `sInd`, `concordantCount`, `aucScore`, `expAUC`, `expAUC_comp`, `expAUC_no_unique_maximiser`,
  `pairWeight`, `expConcordant`, `expConcordant_eq`, `expConcordant_le_truthful` — Proposition
  ("`AUC_j` is not strictly proper"). The AUC is defined as a function of the report `q` and the
  `0/1` labels `Y` (concordant pairs over `n⁺ n⁻`). *Non-uniqueness*: AUC is invariant under any
  strictly monotone reparametrization, hence so is its expectation under any finite label
  distribution (no independence assumed), so whenever `q` maximises the expected AUC the different
  report `q + 1` does too. *Maximality*: if `p i` is the probability that unit `i` is positive
  (distinct values), reporting `p` maximises the expected number of concordant pairs over all
  reports `q`, whatever the dependence between the labels, by a pairwise argument
  (`E[Y i (1 − Y i')] − E[Y i' (1 − Y i)] = p i − p i'`). *Maximality for the normalised AUC*,
  whose denominator `n⁺ n⁻` is random, is proved for independent labels
  (`expAUC_indep_le_truthful`, with `bernP`, `boolLab`, `aucWeight`, `aucWeight_diff`,
  `pairSum_le_truthful`): swapping the labels of two units `i ≠ i'` preserves `n⁺` and `n⁻`, which
  gives `b_{ii'} − b_{i'i} = (p_i − p_{i'}) K` with `K ≥ 0`. For dependent labels the statement is
  false in general, and `expAUC_dependent_counterexample` is an exact witness (four units, five label
  scenarios, expected AUC `41/66` for the truthful ranking against `83/132` for another). For
  *three* units it holds under *any* dependence (`expAUC_three_le_truthful`, via
  `auc_cell_three`, `aucWeight_three`, `pairWeight_sub`): `n⁺ n⁻ = 2` on every discordant pair, so the
  normalised weights are half the numerator weights. Four units is therefore the minimal size of a
  counterexample.
* `dcg_ex_hardTop_closed_form`, `hard_ranking_average`, `hard_ranking_average_lower_bound`,
  `hard_ranking_equality_iff` — Proposition ("Hard-prediction limit"), part (b) in full: for relevances
  `Y` (not necessarily one-hot) and one predicted label per example, the raw DCG sum is
  `Y_{j*} w(1) + w(2) (k − Y_{j*})`; the exemplar average is `(P@1 w(1) + w(2) (k̄ − P@1)) / m`; it is
  at least `P@1 w(1) / m`; and, for `w(2) > 0`, equality holds iff every example's relevances sum to its
  relevance at the predicted label (iff the predicted label is its only relevant one, for `0/1` labels
  and `k_i ≥ 1`).
* `dcg_ex_hardTopK_closed_form`, `dcg_ex_hardTopK_lower_bound`, `dcg_ex_hardTopK_strict`,
  `dcg_ex_hardTopK_indicator` — Remark ("General `k_i⁺`"): for `k` distinct predicted positives ranked
  `1, …, k` (ties among them broken arbitrarily) and predicted negatives at the min-rank `k + 1`, the
  raw DCG sum is `∑_l Y(j_l) w(l+1) + w(k+1) (∑ Y − ∑_l Y(j_l))`; it is at least the top-`k` part and
  strictly larger when `w(k+1) > 0` and a relevant label lies outside the top `k`; for the indicator
  weight `1[r ≤ k]` it equals `∑_l Y(j_l)` (`k · Precision@k_i`). The rank function is abstract
  (hypotheses on the ranks of the predicted positives and negatives), not built from a score vector.
* `auc_cell_two`, `aucWeight_two`, `expAUC_two_le_truthful`, `expAUC_dependent_counterexample_five` —
  Proposition ("`AUC_j` is not strictly proper"): for two units the truthful report maximises the
  expected AUC under any dependence (the denominator is `1`), and a five-unit exact counterexample
  (the four-unit one plus a unit that is positive with certainty; expected AUC `49/66` against `3/4`).
* `positional_expected_eq` / `positional_expected_properness` — Proposition ("Positional operators
  are not strictly proper"), the properness half *from the random labels*: the expected positional
  score over finitely many label scenarios is `∑ⱼ E[Yⱼ] w(rank_q(j))` (the paper's Eq. `disc_expect`,
  now derived), and reporting the marginals `p` maximises it for non-increasing `w`.
  `positional_expected_eq_integral` / `positional_expected_properness_measure` state the same over an
  *arbitrary* measure space (linearity of the integral), and `integral_comp_eq_sum` is the bridge to the
  finite-scenario model: for labels with values in a finite type, `E[g(Y)] = ∑_y P(Y = y) g(y)`, so the
  scenario weights of the finite-scenario theorems are these probabilities.
* `raw_dcg_class_skew_iff` / `micro_ndcg_skew_iff` (with `ndcg_class_skew_invariant`,
  `exemplar_average_skew_iff`, `raw_aggregation_collapse`) — Corollary ("Skew behaviour of the DCG
  family"): of the six aggregations (raw or normalised; micro, class, exemplar), `nDCG_j^class` is
  invariant for every data set; the raw per-class DCG is invariant iff `nDCG_j^class = 0`; the
  exemplar averages and the raw micro iff the mean per-example quantity is equal over the positive
  and the negative examples; micro-nDCG iff `∑ DCG / ∑ IDCG` is equal over the two groups. The
  paper's earlier "unique skew-invariant scalar summary" is replaced by these exact conditions.
-/

namespace Aggmetrics.Ranking

/-- General combinatorial fact, independent of AUC or ranking: for any finite set injectively
mapped into a linear order, the number of ordered pairs of distinct elements satisfying a strict
comparison, summed one element at a time, is the triangular number `k(k-1)/2`. Proved by
induction on the finset, repeatedly removing its `f`-maximal element: removing it contributes
exactly `(t.erase M).card` new comparisons (every remaining element is below it), and the
remaining count is handled by the induction hypothesis. -/
theorem sum_card_filter_lt_eq_triangular {α : Type*} [DecidableEq α] {β : Type*} [LinearOrder β]
    (f : α → β) (hf : Function.Injective f) :
    ∀ t : Finset α, (∑ x ∈ t, (t.filter (fun y => f y < f x)).card : ℝ)
      = (t.card : ℝ) * ((t.card : ℝ) - 1) / 2 := by
  intro t
  induction t using Finset.strongInductionOn with
  | _ t ih =>
    rcases t.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨M, hMmem, hMmax⟩ := t.exists_max_image f hne
      have ht'ssub : t.erase M ⊂ t := Finset.erase_ssubset hMmem
      have ihM := ih (t.erase M) ht'ssub
      have hcard_ins : t.card = (t.erase M).card + 1 :=
        (Finset.card_erase_add_one hMmem).symm
      have hins : t = insert M (t.erase M) := (Finset.insert_erase hMmem).symm
      have hMnotin' : M ∉ t.erase M := fun h => (Finset.mem_erase.mp h).1 rfl
      have hfilterM : t.filter (fun y => f y < f M) = t.erase M := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · intro h
          have hyt := h.1
          have hlt := h.2
          have hyM : y ≠ M := by
            intro h'
            rw [h'] at hlt
            exact absurd hlt (lt_irrefl _)
          exact And.intro hyM hyt
        · intro h
          have hyne := h.1
          have hyt := h.2
          have hle : f y ≤ f M := hMmax y hyt
          have hney : f y ≠ f M := fun heq => hyne (hf heq)
          exact And.intro hyt (lt_of_le_of_ne hle hney)
      have hfilter_erase : ∀ x ∈ t.erase M,
          t.filter (fun y => f y < f x) = (t.erase M).filter (fun y => f y < f x) := by
        intro x hx
        have hxt : x ∈ t := (Finset.mem_erase.mp hx).2
        have hfxM : f x ≤ f M := hMmax x hxt
        ext y
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · intro h
          have hyt := h.1
          have hlt := h.2
          have hyM : y ≠ M := by
            intro heq
            rw [heq] at hlt
            exact absurd (lt_of_lt_of_le hlt hfxM) (lt_irrefl _)
          exact And.intro (And.intro hyM hyt) hlt
        · intro h
          exact And.intro h.1.2 h.2
      have hsum_index : ∑ x ∈ t, (t.filter (fun y => f y < f x)).card
          = ∑ x ∈ insert M (t.erase M), (t.filter (fun y => f y < f x)).card :=
        congrArg (fun s : Finset α => ∑ x ∈ s, (t.filter (fun y => f y < f x)).card) hins
      have hsplit : ∑ x ∈ insert M (t.erase M), (t.filter (fun y => f y < f x)).card
          = (t.filter (fun y => f y < f M)).card
            + ∑ x ∈ t.erase M, (t.filter (fun y => f y < f x)).card :=
        Finset.sum_insert hMnotin'
      have hsum_eq : ∑ x ∈ t, (t.filter (fun y => f y < f x)).card
          = (t.erase M).card
            + ∑ x ∈ t.erase M, ((t.erase M).filter (fun y => f y < f x)).card := by
        rw [hsum_index, hsplit, hfilterM]
        congr 1
        exact Finset.sum_congr rfl (fun x hx => by rw [hfilter_erase x hx])
      have hcast := congrArg (fun k : ℕ => (k : ℝ)) hsum_eq
      push_cast at hcast
      rw [hcast, ihM, hcard_ins]
      push_cast
      ring

/-- Proposition (AUC as a normalised mean rank): with `rank` the 1-indexed descending rank by
score `s` (assumed injective, i.e. no ties), `M` the mean rank of the positive examples, and
`AUC` the fraction of concordant positive–negative pairs, `AUC` is this affine, strictly
decreasing function of `M`. No unproved combinatorial fact remains as a hypothesis:
`sum_card_filter_lt_eq_triangular` supplies the positive–positive pair count internally. -/
theorem auc_mean_rank {n : ℕ} (s : Fin n → ℝ) (hs : Function.Injective s)
    (pos neg : Finset (Fin n)) (hunion : pos ∪ neg = Finset.univ) (hdisjoint : Disjoint pos neg)
    (npos nneg : ℕ) (hnpos : npos = pos.card) (_hnneg : nneg = neg.card)
    (hnpos_pos : 0 < npos) (_hnneg_pos : 0 < nneg)
    (rank : Fin n → ℕ)
    (hrank : ∀ i, rank i = (Finset.univ.filter (fun i' => s i < s i')).card + 1)
    (M : ℝ) (hM : M = (1 / (npos : ℝ)) * ∑ i ∈ pos, (rank i : ℝ))
    (concordant : ℕ)
    (hconcordant : concordant = ∑ i ∈ pos, (neg.filter (fun i' => s i' < s i)).card)
    (AUC : ℝ) (hAUC : AUC = (concordant : ℝ) / ((npos : ℝ) * nneg)) :
    AUC = ((n : ℝ) - (1 / 2) * ((npos : ℝ) - 1) - M) / nneg := by
  have hnposR : (npos : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos_pos.ne'
  have hpp : (∑ i ∈ pos, (pos.filter (fun i' => s i' < s i)).card : ℝ)
      = (npos : ℝ) * ((npos : ℝ) - 1) / 2 := by
    rw [hnpos]; exact sum_card_filter_lt_eq_triangular s hs pos
  -- Per-example identity: rank + (things scored below) = n.
  have hrank_worse : ∀ i : Fin n,
      rank i + (Finset.univ.filter (fun i' => s i' < s i)).card = n := by
    intro i
    have hpart : (Finset.univ.filter (fun i' => s i < s i')).card
        + (Finset.univ.filter (fun i' => ¬ (s i < s i'))).card = n := by
      have huniv : (Finset.univ.filter (fun i' => s i < s i'))
          ∪ (Finset.univ.filter (fun i' => ¬ (s i < s i'))) = Finset.univ := by
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      have hdisj : Disjoint (Finset.univ.filter (fun i' => s i < s i'))
          (Finset.univ.filter (fun i' => ¬ (s i < s i'))) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_filter] at hx hx'
        exact hx'.2 hx.2
      rw [← Finset.card_union_of_disjoint hdisj, huniv]
      simp
    have hnotlt_eq : Finset.univ.filter (fun i' => ¬ (s i < s i'))
        = insert i (Finset.univ.filter (fun i' => s i' < s i)) := by
      ext i'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Finset.mem_insert]
      constructor
      · intro hle
        rcases hle.lt_or_eq with h | h
        · right; exact h
        · left; exact hs h
      · rintro (rfl | h)
        · exact le_refl _
        · exact h.le
    have hinotin : i ∉ Finset.univ.filter (fun i' => s i' < s i) := by simp
    have hcard_insert : (insert i (Finset.univ.filter (fun i' => s i' < s i))).card
        = (Finset.univ.filter (fun i' => s i' < s i)).card + 1 := by
      have heq : insert i (Finset.univ.filter (fun i' => s i' < s i))
          = {i} ∪ Finset.univ.filter (fun i' => s i' < s i) := by
        rw [Finset.singleton_union]
      have hdisj : Disjoint ({i} : Finset (Fin n))
          (Finset.univ.filter (fun i' => s i' < s i)) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_singleton] at hx
        rw [hx] at hx'
        exact hinotin hx'
      rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
      omega
    rw [hnotlt_eq, hcard_insert] at hpart
    rw [hrank]
    omega
  -- Sum this identity over the positives.
  have hsum1 : (∑ i ∈ pos, (rank i : ℝ))
      + (∑ i ∈ pos, ((Finset.univ.filter (fun i' => s i' < s i)).card : ℝ))
      = (npos : ℝ) * n := by
    have hnat : ∑ i ∈ pos, (rank i + (Finset.univ.filter (fun i' => s i' < s i)).card)
        = ∑ i ∈ pos, n := Finset.sum_congr rfl (fun i _ => hrank_worse i)
    have hcast := congrArg (fun x : ℕ => (x : ℝ)) hnat
    push_cast at hcast
    rw [Finset.sum_add_distrib, Finset.sum_const, ← hnpos] at hcast
    simpa [nsmul_eq_mul] using hcast
  have hsumrank : (∑ i ∈ pos, (rank i : ℝ)) = (npos : ℝ) * M := by
    rw [hM]; field_simp
  -- Split "scored below" by class.
  have hworse_split : ∀ i, (Finset.univ.filter (fun i' => s i' < s i)).card
      = (pos.filter (fun i' => s i' < s i)).card + (neg.filter (fun i' => s i' < s i)).card := by
    intro i
    rw [← hunion, Finset.filter_union, Finset.card_union_of_disjoint]
    exact hdisjoint.mono (Finset.filter_subset _ pos) (Finset.filter_subset _ neg)
  have hsum2 : (∑ i ∈ pos, ((Finset.univ.filter (fun i' => s i' < s i)).card : ℝ))
      = (∑ i ∈ pos, ((pos.filter (fun i' => s i' < s i)).card : ℝ))
        + (∑ i ∈ pos, ((neg.filter (fun i' => s i' < s i)).card : ℝ)) := by
    have hnat : ∑ i ∈ pos, (Finset.univ.filter (fun i' => s i' < s i)).card
        = ∑ i ∈ pos, ((pos.filter (fun i' => s i' < s i)).card
            + (neg.filter (fun i' => s i' < s i)).card) :=
      Finset.sum_congr rfl (fun i _ => hworse_split i)
    have hcast := congrArg (fun x : ℕ => (x : ℝ)) hnat
    push_cast at hcast
    rw [Finset.sum_add_distrib] at hcast
    exact hcast
  have hconcordantR : (concordant : ℝ)
      = ∑ i ∈ pos, ((neg.filter (fun i' => s i' < s i)).card : ℝ) := by
    rw [hconcordant, Nat.cast_sum]
  -- Combine everything into the concordant-pair count, then finish algebraically.
  have hcombine : (npos : ℝ) * n
      = (npos : ℝ) * M + ((npos : ℝ) * ((npos : ℝ) - 1) / 2 + (concordant : ℝ)) := by
    rw [← hsumrank, ← hpp, hconcordantR, ← hsum2]
    exact hsum1.symm
  have key : (concordant : ℝ) = (npos : ℝ) * ((n : ℝ) - (1 / 2) * ((npos : ℝ) - 1) - M) := by
    linear_combination -hcombine
  rw [hAUC, key]
  exact mul_div_mul_left _ _ hnposR

/-- Theorem ("Raw DCG collapses"; part (a), and identically the raw half of "Collapse and
non-collapse for AUC"): for any real `n × m` cell matrix `D`, the micro (double-sum), per-class
(row-averaged, then averaged over classes), and per-example (column-averaged, then averaged over
examples) raw aggregations coincide. Pure algebraic consequence of resumming a finite double sum
in either order — holds for any real matrix, not anything specific to DCG or AUC cell matrices,
which is exactly why the same proof serves both `thm:dcg_collapse`(a) and `thm:auc_collapse`(a). -/
theorem raw_aggregation_collapse {n m : ℕ} (D : Fin n → Fin m → ℝ) :
    (1 / ((n : ℝ) * m)) * ∑ i, ∑ j, D i j
        = (1 / (m : ℝ)) * ∑ j, (1 / (n : ℝ)) * ∑ i, D i j
      ∧ (1 / ((n : ℝ) * m)) * ∑ i, ∑ j, D i j
        = (1 / (n : ℝ)) * ∑ i, (1 / (m : ℝ)) * ∑ j, D i j := by
  have hswap : ∑ i, ∑ j, D i j = ∑ j, ∑ i, D i j := Finset.sum_comm
  constructor
  · calc (1 / ((n : ℝ) * m)) * ∑ i, ∑ j, D i j
        = (1 / (m : ℝ)) * ((1 / (n : ℝ)) * ∑ i, ∑ j, D i j) := by ring
      _ = (1 / (m : ℝ)) * ((1 / (n : ℝ)) * ∑ j, ∑ i, D i j) := by rw [hswap]
      _ = (1 / (m : ℝ)) * ∑ j, (1 / (n : ℝ)) * ∑ i, D i j := by rw [Finset.mul_sum]
  · calc (1 / ((n : ℝ) * m)) * ∑ i, ∑ j, D i j
        = (1 / (n : ℝ)) * ((1 / (m : ℝ)) * ∑ i, ∑ j, D i j) := by ring
      _ = (1 / (n : ℝ)) * ∑ i, (1 / (m : ℝ)) * ∑ j, D i j := by rw [Finset.mul_sum]

/-- General fact behind the ranking paper's non-collapse theorems (independent of DCG/AUC
specifics): the gap between the `b`-weighted mean of a ratio `r` and its unweighted mean equals
the empirical covariance of `b` and `r`, divided by the mean of `b`. This is the algebraic core of
`thm:dcg_collapse`(b) and `thm:auc_collapse`(b): the two aggregations of a normalised measure
coincide exactly when this covariance vanishes (e.g., when `b` is constant, making the covariance
trivially zero). -/
theorem weighted_vs_unweighted_mean {n : ℕ} (hn : n ≠ 0) (b r : Fin n → ℝ)
    (bbar rbar cov : ℝ)
    (hbbar : bbar = (1 / (n : ℝ)) * ∑ i, b i)
    (hrbar : rbar = (1 / (n : ℝ)) * ∑ i, r i)
    (hcov : cov = (1 / (n : ℝ)) * ∑ i, (b i - bbar) * (r i - rbar))
    (hbbar0 : bbar ≠ 0) :
    (∑ i, b i * r i) / (∑ i, b i) - rbar = cov / bbar := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hSb : ∑ i, b i = (n : ℝ) * bbar := by rw [hbbar]; field_simp
  have hSr : ∑ i, r i = (n : ℝ) * rbar := by rw [hrbar]; field_simp
  have hpointwise : ∀ i, (b i - bbar) * (r i - rbar)
      = b i * r i - rbar * b i - bbar * r i + bbar * rbar := by intro i; ring
  have hexpand : ∑ i, (b i - bbar) * (r i - rbar)
      = (∑ i, b i * r i) - (n : ℝ) * bbar * rbar := by
    simp_rw [hpointwise]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      hSb, hSr, nsmul_eq_mul]
    ring
  have hcov' : cov = (∑ i, b i * r i) / (n : ℝ) - bbar * rbar := by
    rw [hcov, hexpand]; field_simp
  have hSb0 : ∑ i, b i ≠ 0 := by rw [hSb]; exact mul_ne_zero hn' hbbar0
  rw [hcov', hSb]
  field_simp

/-- Theorem (the algebraic core shared by "Per-class nDCG as conditional mean" and the substantive
half of "Row-Column Duality"): a population average of an indicator-weighted quantity equals the
prevalence times the conditional average over the indicated subset. `S` plays the role of the
positive-class examples `{i : Y_{ij}=1}`; instantiating `g` with the row-rank weight
`w(rank_i(j))` gives `prop:ndcg_class_mean` exactly, and `AUC_j` is already defined directly as
this conditional-mean form in the paper (`eq:auc_class`), which is precisely why
`thm:duality` needs no further algebra beyond this one lemma. -/
theorem conditional_mean_of_indicator_sum {n : ℕ} (S : Finset (Fin n)) (hn : n ≠ 0)
    (hk : S.card ≠ 0) (g Y : Fin n → ℝ) (hY : ∀ i, Y i = if i ∈ S then 1 else 0) :
    (1 / (n : ℝ)) * ∑ i, Y i * g i
      = ((S.card : ℝ) / (n : ℝ)) * ((1 / (S.card : ℝ)) * ∑ i ∈ S, g i) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hk' : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hsum : ∑ i, Y i * g i = ∑ i ∈ S, g i := by
    simp_rw [hY, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum]
  field_simp

/-- Theorem (the algebraic core of skew-invariance under replication, `prop:ndcg_class_skew`
and `prop:auc_skew`(a)): replicating every member of a subset `S` by the same multiplicative
weight `lam ≠ 0` — the formal content of "replicating each of `S`'s examples `lam` times" — leaves
the average of any quantity `f` over `S` unchanged. Skewing a class by replicating its positive
examples `λ`-fold, or its negative examples `μ`-fold, is exactly this operation with `S` the
positive (or negative) subset, which is why invariance holds for *any* nonzero replication factor,
not just integer ones. -/
theorem uniform_weight_average_invariant {n : ℕ} (S : Finset (Fin n)) (hS : S.card ≠ 0)
    (w f : Fin n → ℝ) (lam : ℝ) (hlam : lam ≠ 0) (hw : ∀ i ∈ S, w i = lam) :
    (∑ i ∈ S, w i * f i) / (∑ i ∈ S, w i) = (∑ i ∈ S, f i) / (S.card : ℝ) := by
  have hnum : ∑ i ∈ S, w i * f i = lam * ∑ i ∈ S, f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hw i hi])
  have hden : ∑ i ∈ S, w i = lam * (S.card : ℝ) := by
    rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]; ring
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hlam

/-- Proposition, "Per-class nDCG is skew-invariant": replicating every positive
example for class `j` by the same factor `lam ≠ 0` leaves `nDCG_j^class` unchanged, since it is
exactly the `lam`-weighted average of the rank-weight `g` (the paper's `w ∘ rank`) over the
positive set, divided by `w(1)` — a direct application of `uniform_weight_average_invariant`. -/
theorem ndcg_class_skew_invariant {n : ℕ} (pos : Finset (Fin n)) (hpos : pos.card ≠ 0)
    (g : Fin n → ℝ) (w1 : ℝ) (lam : ℝ) (hlam : lam ≠ 0) :
    (1 / w1) * ((∑ i ∈ pos, lam * g i) / (∑ i ∈ pos, lam))
      = (1 / w1) * ((∑ i ∈ pos, g i) / (pos.card : ℝ)) := by
  congr 1
  exact uniform_weight_average_invariant pos hpos (fun _ => lam) g lam hlam (fun _ _ => rfl)

/-- Proposition, "AUC_j ... skew-invariant", part (a) (part (b), macro-AUC, is an average of
such terms and part (c), the skew-sensitivity of micro-AUC, are not stated in Lean):
replicating negative examples `mu`-fold inside the
concordance fraction, and positive examples `lam`-fold in the outer average over positives, both
leave `AUC_j` unchanged — two nested applications of `uniform_weight_average_invariant`,
mirroring the paper's own two-step replication argument exactly. -/
theorem auc_class_skew_invariant {n : ℕ} (pos neg : Finset (Fin n))
    (hpos : pos.card ≠ 0) (hneg : neg.card ≠ 0)
    (concord : Fin n → Fin n → ℝ) (lam mu : ℝ) (hlam : lam ≠ 0) (hmu : mu ≠ 0) :
    (∑ i ∈ pos, lam * ((∑ i' ∈ neg, mu * concord i i') / (∑ i' ∈ neg, mu)))
        / (∑ i ∈ pos, lam)
      = (∑ i ∈ pos, (∑ i' ∈ neg, concord i i') / (neg.card : ℝ)) / (pos.card : ℝ) := by
  have hinner : ∀ i, (∑ i' ∈ neg, mu * concord i i') / (∑ i' ∈ neg, mu)
      = (∑ i' ∈ neg, concord i i') / (neg.card : ℝ) := fun i =>
    uniform_weight_average_invariant neg hneg (fun _ => mu) (concord i) mu hmu (fun _ _ => rfl)
  simp_rw [hinner]
  exact uniform_weight_average_invariant pos hpos (fun _ => lam)
    (fun i => (∑ i' ∈ neg, concord i i') / (neg.card : ℝ)) lam hlam (fun _ _ => rfl)

/-- Definition, `def:rank`: the descending rank of index `j` in a real score
vector `q` — one more than the number of indices strictly outscoring `j`. -/
noncomputable def rank {m : ℕ} (q : Fin m → ℝ) (j : Fin m) : ℕ :=
  (Finset.univ.filter (fun j' => q j' > q j)).card + 1

/-- Theorem (the algebraic core of both non-strict-properness propositions,
`prop:disc_improper` and `prop:auc_improper`): the rank vector of a report is invariant under
composing it with any strictly monotone reparametrisation `φ : ℝ → ℝ`, since `φ` preserves every
pairwise `<` comparison that `rank` is built from. -/
theorem rank_reparam_invariant {m : ℕ} (q : Fin m → ℝ) (φ : ℝ → ℝ) (hφ : StrictMono φ)
    (j : Fin m) : rank (φ ∘ q) j = rank q j := by
  unfold rank
  simp only [Function.comp_apply]
  rw [Finset.filter_congr (fun j' _ => hφ.lt_iff_lt)]

/-- Theorem (Propositions "Positional operators are not strictly proper" and "AUC_j is not
strictly proper", non-strict-properness halves — the paper proves `prop:auc_improper` by citing
`prop:disc_improper`'s argument; only the positional instance is stated here): any score that
factors through the rank of its report — as the positional/DCG score does, and, informally, the
AUC concordance score — assigns the *same* value to a report `p` and
to `p` shifted by a constant, which induces an identical ranking (`rank_reparam_invariant` with
the fixed-point-free strict monotone `x ↦ x+1`) yet is a genuinely different report. So no report
that is *a* maximiser of such a score can be the *unique* one: shifting it by a constant produces
a second, distinct maximiser with the same score. This isolates exactly the "not strictly" content
of both propositions; the weaker "is proper" direction (truthful reporting attains the maximum at
all) is a separate fact resting on the rearrangement inequality and is not covered here. -/
theorem not_strictly_proper_of_rank_dependent {m : ℕ} (hm : 0 < m) (score : (Fin m → ℝ) → ℝ)
    (F : (Fin m → ℕ) → ℝ) (hscore : ∀ q, score q = F (rank q)) (p : Fin m → ℝ) :
    score (fun j => p j + 1) = score p ∧ (fun j => p j + 1) ≠ p := by
  have hshift : StrictMono (fun x : ℝ => x + 1) := fun _ _ h => by linarith
  refine ⟨?_, ?_⟩
  · have heq : rank (fun j => p j + 1) = rank p :=
      funext (fun j => rank_reparam_invariant p (fun x => x + 1) hshift j)
    rw [hscore, hscore, heq]
  · intro h
    have h0 := congrFun h ⟨0, hm⟩
    simp at h0

/-- A concrete counterexample witnessing "Exemplar nDCG is skew-sensitive"
(`prop:ndcg_ex_skew`). Unlike the skew-*invariance* results above, this proposition's content is
existential ("the average changes for *some* configuration where the two groups differ"), not
universal, so it is rendered here as an explicit instance rather than a general theorem. Two
examples with per-example nDCG values `1` (the positive example for class `j`) and `0` (a
negative example) average to `1/2`; replicating the positive example once more — three examples
`1, 1, 0`, exactly the paper's `λ`-fold replication of the positive group with `λ=2` — shifts the
unweighted population average to `2/3`. This is the same mechanism as
`weighted_vs_unweighted_mean`: replication changes the mixing proportion between two subgroups
with different mean `nDCG_i`, and the population average moves whenever those subgroup means
differ, exactly as the proof of `prop:ndcg_ex_skew` argues in general. -/
theorem ndcg_ex_skew_counterexample :
    (1 / (2 : ℝ)) * (∑ i : Fin 2, (![1, 0] : Fin 2 → ℝ) i)
      ≠ (1 / (3 : ℝ)) * (∑ i : Fin 3, (![1, 1, 0] : Fin 3 → ℝ) i) := by
  simp [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num

/-- Theorem (the rearrangement-inequality core of the "is proper" (weak) halves of
`prop:disc_improper` and `prop:auc_improper`; superseded in application by `positional_properness`
below, which connects this fact to the file's own `rank` definition directly): for any report
`p` and any *ascending* weight sequence `wAsc` (an ascending relabelling of the paper's descending
`w(rank)`, since the paper indexes by worst-to-best rank while this reindexes worst-to-best
position), the permutation `(Tuple.sort p)⁻¹` — the permutation assigning each label its own
sorted position among the `p`-values — maximises `∑ j, p j * wAsc(θ j)` over every permutation
`θ` of the positions. This is Mathlib's rearrangement inequality
(`Monovary.sum_smul_comp_perm_le_sum_smul`), applied to `p` pre-composed with the sorting
permutation (`Tuple.sort`, `Tuple.monotone_sort`) and `wAsc`, both monotone and hence
(`Monotone.monovary`) monovarying. -/
theorem positional_score_maximized_at_sorted_rank {m : ℕ} (p wAsc : Fin m → ℝ)
    (hwAsc : Monotone wAsc) (θ : Equiv.Perm (Fin m)) :
    ∑ j, p j * wAsc (θ j) ≤ ∑ j, p j * wAsc ((Tuple.sort p)⁻¹ j) := by
  set σ := Tuple.sort p with hσdef
  have hmono : Monotone (p ∘ σ) := Tuple.monotone_sort p
  have hmv : Monovary (p ∘ σ) wAsc := hmono.monovary hwAsc
  have hkey := hmv.sum_smul_comp_perm_le_sum_smul (σ := θ * σ)
  simp only [smul_eq_mul] at hkey
  have hL : ∑ i, (p ∘ σ) i * wAsc ((θ * σ) i) = ∑ j, p j * wAsc (θ j) := by
    have h := Equiv.sum_comp σ (fun j => p j * wAsc (θ j))
    simpa [Equiv.Perm.mul_apply, Function.comp_apply] using h
  have hR : ∑ i, (p ∘ σ) i * wAsc i = ∑ j, p j * wAsc (σ⁻¹ j) := by
    have h := Equiv.sum_comp σ (fun j => p j * wAsc (σ⁻¹ j))
    simpa [Function.comp_apply] using h
  rw [hL, hR] at hkey
  exact hkey

/-- `rank` strictly reverses order: a strictly higher score gets a strictly lower (better) rank
number. No injectivity needed — a direct strict-subset-of-filters argument. -/
theorem rank_strictAnti {m : ℕ} (q : Fin m → ℝ) {i j : Fin m} (hij : q j < q i) :
    rank q i < rank q j := by
  unfold rank
  have hssub : (Finset.univ.filter (fun k => q k > q i))
      ⊂ (Finset.univ.filter (fun k => q k > q j)) := by
    constructor
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact lt_trans hij hk
    · intro hsub
      have hmem : i ∈ Finset.univ.filter (fun k => q k > q i) :=
        hsub (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hij)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact lt_irrefl _ hmem
  have := Finset.card_lt_card hssub
  omega

/-- `rank` is injective on injectively-scored reports: distinct labels never tie. -/
theorem rank_injective {m : ℕ} (q : Fin m → ℝ) (hq : Function.Injective q) :
    Function.Injective (rank q) := by
  intro i j hij
  by_contra hne
  have hqne : q i ≠ q j := fun h => hne (hq h)
  rcases lt_or_gt_of_ne hqne with h | h
  · have := rank_strictAnti q h; omega
  · have := rank_strictAnti q h; omega

/-- `rank` never exceeds the population size `m`. -/
theorem rank_le {m : ℕ} (q : Fin m → ℝ) (j : Fin m) : rank q j ≤ m := by
  change (Finset.univ.filter (fun j' => q j' > q j)).card + 1 ≤ m
  have hsub : (Finset.univ.filter (fun j' => q j' > q j)) ⊆ (Finset.univ : Finset (Fin m)).erase j := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rintro rfl; exact lt_irrefl _ hk
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin] at hc
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le j.1) j.2
  omega

/-- The 0-indexed rank, valued in `Fin m` itself rather than in `ℕ`, so it can be packaged as a
self-map of `Fin m` (and, once shown bijective, as an `Equiv.Perm`). -/
noncomputable def rank0 {m : ℕ} (q : Fin m → ℝ) (j : Fin m) : Fin m :=
  ⟨rank q j - 1, by
    have h1 : rank q j ≤ m := rank_le q j
    have h2 : 0 < m := lt_of_le_of_lt (Nat.zero_le j.1) j.2
    omega⟩

/-- For injectively-scored reports, `rank0` is a bijection of `Fin m` with itself: ranks realise
every value from best to worst exactly once. -/
theorem rank_bijective {m : ℕ} (q : Fin m → ℝ) (hq : Function.Injective q) :
    Function.Bijective (rank0 q) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun i j h => ?_, rfl⟩
  have h1 : (rank0 q i).val = (rank0 q j).val := congrArg Fin.val h
  simp only [rank0] at h1
  have hpi : 1 ≤ rank q i := by unfold rank; omega
  have hpj : 1 ≤ rank q j := by unfold rank; omega
  exact rank_injective q hq (by omega)

/-- Theorem (closing the connection: the full "is proper" (weak) half of `prop:disc_improper`,
tied directly to this file's own `rank`): for injectively-scored reports `p` (the true
probabilities) and `q` (an arbitrary alternative report) and any antitone weight `w` (the paper's
descending `w(rank)`), the positional score under the *true* report `p` is never smaller than
under any other report `q`. Combined with `not_strictly_proper_of_rank_dependent` (which already
shows this maximiser is never *unique*), this closes both halves of `prop:disc_improper` in full
(for the expected-score expression of the paper; derived from the random labels in `positional_expected_properness`). It does not address
`prop:auc_improper`: the AUC score is not of the form `∑ j, p j * w (rank j)`; see `aucScore`,
`expAUC_no_unique_maximiser` and `expConcordant_le_truthful` for that proposition. The proof reindexes `q`'s score
by the bijection `rank0 q` and `p`'s by `rank0 p`, transports through the permutation
`(rank0 q).trans (rank0 p).symm` (as `Equiv.Perm (Fin m)`), and applies Mathlib's rearrangement
inequality to `p` and `w ∘ rank p`, which monovary because `rank` strictly reverses order
(`rank_strictAnti`) and `w` is antitone. -/
theorem positional_properness {m : ℕ} (p q : Fin m → ℝ) (hp : Function.Injective p)
    (hq : Function.Injective q) (w : ℕ → ℝ) (hw : Antitone w) :
    ∑ j, p j * w (rank q j) ≤ ∑ j, p j * w (rank p j) := by
  have hmv : Monovary p (fun j => w (rank p j)) := by
    intro i j hlt
    by_contra hcon
    push_neg at hcon
    have hr := rank_strictAnti p hcon
    have hw' := hw hr.le
    simp only at hlt
    linarith
  set σp := Equiv.ofBijective (rank0 p) (rank_bijective p hp) with hσp
  set σq := Equiv.ofBijective (rank0 q) (rank_bijective q hq) with hσq
  set θ : Equiv.Perm (Fin m) := σq.trans σp.symm with hθ
  have hkey := hmv.sum_smul_comp_perm_le_sum_smul (σ := θ)
  simp only [smul_eq_mul] at hkey
  have hL : ∀ j, w (rank p (θ j)) = w (rank q j) := by
    intro j
    have hσeq : σp (θ j) = σq j := by
      rw [hθ]; simp [Equiv.trans_apply]
    have h0eq : rank0 p (θ j) = rank0 q j := by
      simpa [σp, σq, Equiv.ofBijective_apply] using hσeq
    have hcast : rank p (θ j) = rank q j := by
      have h1 := congrArg Fin.val h0eq
      simp only [rank0] at h1
      have h2 : 1 ≤ rank p (θ j) := by unfold rank; omega
      have h3 : 1 ≤ rank q j := by unfold rank; omega
      omega
    rw [hcast]
  simp_rw [hL] at hkey
  exact hkey

/-! ### Exact conditions for skew-sensitivity and collapse -/

/-- Proposition ("Exemplar nDCG is skew-sensitive"), exact form: replicating the positive examples
of class `j` `lam`-fold versus `mu`-fold leaves the exemplar average of per-example nDCG unchanged
iff the mean nDCG over the positive examples equals the mean over the negative examples. (An earlier version of the paper stated the condition as "the distribution of `IDCG_i`
differs between the groups"; the exact condition is on the group means of `nDCG_i`.) -/
theorem exemplar_average_skew_iff {n : ℕ} (pos neg : Finset (Fin n)) (hpos : 0 < pos.card)
    (hneg : 0 < neg.card) (ndcg : Fin n → ℝ) {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hne : lam ≠ mu) :
    Mixture.replAvg pos neg ndcg lam = Mixture.replAvg pos neg ndcg mu
      ↔ (∑ i ∈ pos, ndcg i) / pos.card = (∑ i ∈ neg, ndcg i) / neg.card :=
  Mixture.replAvg_eq_iff pos neg hpos hneg ndcg hlam hmu hne

/-- Proposition ("`AUC_j` and macro-AUC are skew-invariant; micro-AUC is not"), part (b): the
macro average of the per-class replicated `AUC_j` equals the unreplicated macro average, because
each term is invariant (`auc_class_skew_invariant`). -/
theorem macro_auc_skew_invariant {n m : ℕ} (pos neg : Fin m → Finset (Fin n))
    (hpos : ∀ j, (pos j).card ≠ 0) (hneg : ∀ j, (neg j).card ≠ 0)
    (concord : Fin m → Fin n → Fin n → ℝ) (lam mu : Fin m → ℝ)
    (hlam : ∀ j, lam j ≠ 0) (hmu : ∀ j, mu j ≠ 0) :
    (1 / (m : ℝ)) * ∑ j, ((∑ i ∈ pos j, lam j * ((∑ i' ∈ neg j, mu j * concord j i i')
        / (∑ i' ∈ neg j, mu j))) / (∑ i ∈ pos j, lam j))
      = (1 / (m : ℝ)) * ∑ j, ((∑ i ∈ pos j, (∑ i' ∈ neg j, concord j i i')
        / ((neg j).card : ℝ)) / ((pos j).card : ℝ)) := by
  congr 1
  exact Finset.sum_congr rfl (fun j _ =>
    auc_class_skew_invariant (pos j) (neg j) (hpos j) (hneg j) (concord j) (lam j) (mu j)
      (hlam j) (hmu j))

/-- Proposition ("`AUC_j` and macro-AUC are skew-invariant; micro-AUC is not"), part (c), exact
form: scaling the positives of one class `k` by `lam` versus `mu` leaves micro-AUC
`∑ n⁺_j AUC_j / ∑ n⁺_j` unchanged iff `AUC_k` equals the micro-AUC itself. (An earlier version of the paper gave only "it weights each `AUC_j` by `n⁺_j`, which varies
with `λ`", which is not sufficient on its own: the weights vary but the average need not.) If the `AUC_j` are not all equal, some class `k` violates this condition. -/
theorem micro_auc_skew_iff {m : ℕ} (npos auc : Fin m → ℝ) (hpos : ∀ j, 0 < npos j) (k : Fin m)
    {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) (hne : lam ≠ mu) :
    (∑ j, (if j = k then lam else 1) * (npos j * auc j))
        / (∑ j, (if j = k then lam else 1) * npos j)
      = (∑ j, (if j = k then mu else 1) * (npos j * auc j))
        / (∑ j, (if j = k then mu else 1) * npos j)
      ↔ auc k * (∑ j, npos j) = ∑ j, npos j * auc j := by
  have hs : ∀ (c : ℝ) (f : Fin m → ℝ),
      ∑ j, (if j = k then c else 1) * f j = ∑ j, f j + (c - 1) * f k := by
    intro c f
    have hterm : ∀ j, (if j = k then c else 1) * f j
        = f j + (c - 1) * (if j = k then f j else 0) := by
      intro j
      by_cases h : j = k
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hD : ∀ c : ℝ, 0 < c → 0 < ∑ j, (if j = k then c else 1) * npos j := by
    intro c hc
    refine Finset.sum_pos (fun j _ => mul_pos ?_ (hpos j)) ⟨k, Finset.mem_univ k⟩
    by_cases h : j = k
    · rw [if_pos h]; exact hc
    · rw [if_neg h]; exact one_pos
  have hDl := hD lam hlam
  have hDm := hD mu hmu
  rw [hs lam npos] at hDl
  rw [hs mu npos] at hDm
  rw [hs lam (fun j => npos j * auc j), hs lam npos, hs mu (fun j => npos j * auc j),
    hs mu npos]
  set S := ∑ j, npos j * auc j with hS
  set N := ∑ j, npos j with hN
  rw [div_eq_div_iff hDl.ne' hDm.ne']
  have key : (S + (lam - 1) * (npos k * auc k)) * (N + (mu - 1) * npos k)
      - (S + (mu - 1) * (npos k * auc k)) * (N + (lam - 1) * npos k)
      = (lam - mu) * npos k * (auc k * N - S) := by ring
  have hnk : npos k ≠ 0 := (hpos k).ne'
  have hfac : (lam - mu) * npos k ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hne) hnk
  constructor
  · intro h
    have hd : (lam - mu) * npos k * (auc k * N - S) = 0 := by linarith
    rcases mul_eq_zero.mp hd with h0 | h0
    · exact absurd h0 hfac
    · linarith
  · intro h
    have h0 : auc k * N - S = 0 := by linarith
    have : (S + (lam - 1) * (npos k * auc k)) * (N + (mu - 1) * npos k)
        - (S + (mu - 1) * (npos k * auc k)) * (N + (lam - 1) * npos k) = 0 := by
      rw [key, h0, mul_zero]
    linarith

/-- Theorem ("Collapse and non-collapse for `nDCG`"), part (b), exact form for the exemplar case:
the `b`-weighted mean of the ratios `r = a/b` equals their unweighted mean iff the empirical
covariance of `b` and `r` is zero. -/
theorem weighted_eq_unweighted_iff_cov_zero {n : ℕ} (hn : n ≠ 0) (b r : Fin n → ℝ)
    (bbar rbar cov : ℝ) (hbbar : bbar = (1 / (n : ℝ)) * ∑ i, b i)
    (hrbar : rbar = (1 / (n : ℝ)) * ∑ i, r i)
    (hcov : cov = (1 / (n : ℝ)) * ∑ i, (b i - bbar) * (r i - rbar)) (hbbar0 : bbar ≠ 0) :
    (∑ i, b i * r i) / (∑ i, b i) = rbar ↔ cov = 0 := by
  have h := weighted_vs_unweighted_mean hn b r bbar rbar cov hbbar hrbar hcov hbbar0
  constructor
  · intro hx
    rw [hx, sub_self] at h
    rcases div_eq_zero_iff.mp h.symm with h0 | h0
    · exact h0
    · exact absurd h0 hbbar0
  · intro hc
    rw [hc, zero_div] at h
    linarith

/-- When all examples have the same ideal mass (e.g. all `k_i = k`, so `IDCG_i` is constant), the
two aggregations of the exemplar case coincide. -/
theorem weighted_eq_unweighted_of_const {n : ℕ} (hn : n ≠ 0) (b r : Fin n → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hb : ∀ i, b i = c) :
    (∑ i, b i * r i) / (∑ i, b i) = (1 / (n : ℝ)) * ∑ i, r i := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have e1 : ∑ i, b i * r i = c * ∑ i, r i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hb i])
  have e2 : ∑ i, b i = (n : ℝ) * c := by
    rw [Finset.sum_congr rfl (fun i _ => hb i)]
    simp
  rw [e1, e2]
  field_simp

/-- A concrete witness of non-collapse: per-example DCG `a = (1, 0)` and ideal mass
`b = (1, 3)` give micro-nDCG `1/4` but exemplar-averaged nDCG `1/2`. -/
theorem ndcg_micro_vs_exemplar_counterexample :
    (∑ i : Fin 2, (![1, 0] : Fin 2 → ℝ) i) / (∑ i : Fin 2, (![1, 3] : Fin 2 → ℝ) i)
      ≠ (1 / (2 : ℝ)) * ∑ i : Fin 2, (![1, 0] : Fin 2 → ℝ) i / (![1, 3] : Fin 2 → ℝ) i := by
  norm_num [Fin.sum_univ_two]

/-! ### Hard-prediction limit -/

/-- The hard top-1 prediction vector: score `1` on the predicted label `js`, `0` elsewhere. -/
def hardTop {m : ℕ} (js : Fin m) : Fin m → ℝ := fun j => if j = js then 1 else 0

theorem rank_hardTop_self {m : ℕ} (js : Fin m) : rank (hardTop js) js = 1 := by
  unfold rank
  have h : (Finset.univ.filter (fun j' => hardTop js j' > hardTop js js)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j' _
    by_cases hj : j' = js
    · norm_num [hardTop, hj]
    · norm_num [hardTop, hj]
  rw [h]
  simp

theorem rank_hardTop_ne {m : ℕ} (js j : Fin m) (hj : j ≠ js) : rank (hardTop js) j = 2 := by
  unfold rank
  have h : (Finset.univ.filter (fun j' => hardTop js j' > hardTop js j)) = {js} := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hj' : j' = js
    · subst hj'
      norm_num [hardTop, hj]
    · norm_num [hardTop, hj', hj]
  rw [h]
  simp

/-- Proposition ("Hard-prediction limit"), per-example form for one-hot `Y` with true class `c`:
the example's raw DCG sum is `w(1)` if the top-1 prediction is correct and `w(2)` otherwise. (The
true class is ranked second under min-rank ties, and a wrong prediction still earns `w(2)`.) -/
theorem dcg_ex_hardTop_oneHot {m : ℕ} (w : ℕ → ℝ) (c js : Fin m) :
    ∑ j, (if j = c then (1 : ℝ) else 0) * w (rank (hardTop js) j)
      = if c = js then w 1 else w 2 := by
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : c = js
  · subst h
    rw [rank_hardTop_self]
    simp
  · rw [rank_hardTop_ne js c h]
    simp [h]

/-- Proposition ("Hard-prediction limit"), part (b): for any nonnegative weight and nonnegative
relevance, the raw DCG sum of a hard top-1 prediction is at least `Y_{j*} · w(1)`. -/
theorem dcg_ex_hardTop_lower_bound {m : ℕ} (w : ℕ → ℝ) (hw : ∀ r, 0 ≤ w r) (js : Fin m)
    (Y : Fin m → ℝ) (hY : ∀ j, 0 ≤ Y j) :
    Y js * w 1 ≤ ∑ j, Y j * w (rank (hardTop js) j) := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ js), rank_hardTop_self]
  have : 0 ≤ ∑ j ∈ Finset.univ.erase js, Y j * w (rank (hardTop js) j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hY j) (hw _))
  linarith

/-- Proposition ("Hard-prediction limit"), part (a): in the one-hot multiclass case, the exemplar
average of the DCG with hard top-1 predictions is `(P@1 · w(1) + (1 - P@1) · w(2)) / m`. It equals
`P@1 · w(1) / m` (the form stated in an earlier version of the paper) only if `w(2) = 0`. -/
theorem hard_ranking_oneHot_average {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (c js : Fin n → Fin m) (w : ℕ → ℝ) (P : ℝ)
    (hP : P = (1 / (n : ℝ)) * ∑ i, (if c i = js i then (1 : ℝ) else 0)) :
    (1 / (n : ℝ)) * ∑ i, ((1 / (m : ℝ)) * ∑ j, (if j = c i then (1 : ℝ) else 0)
        * w (rank (hardTop (js i)) j))
      = (P * w 1 + (1 - P) * w 2) / m := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have per : ∀ i, (1 / (m : ℝ)) * ∑ j, (if j = c i then (1 : ℝ) else 0)
        * w (rank (hardTop (js i)) j)
      = (1 / (m : ℝ)) * (w 2 + (if c i = js i then (1 : ℝ) else 0) * (w 1 - w 2)) := by
    intro i
    rw [dcg_ex_hardTop_oneHot]
    by_cases h : c i = js i
    · simp [h]
    · simp [h]
  have hSe : ∑ i, (if c i = js i then (1 : ℝ) else 0) = n * P := by
    rw [hP]
    field_simp
  have hsum : ∑ i, (w 2 + (if c i = js i then (1 : ℝ) else 0) * (w 1 - w 2))
      = n * w 2 + (n * P) * (w 1 - w 2) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hSe]
    simp
  simp_rw [per]
  rw [← Finset.mul_sum, hsum]
  field_simp
  ring

/-- Where the paper's claim `DCG^ex = Y_{j*} w(1) / m` fails: for one-hot `Y` it holds for every
true class `c` iff `w(2) = 0` (given a class `c0` different from the predicted one). -/
theorem hard_ranking_paper_claim_iff {m : ℕ} (w : ℕ → ℝ) (js c0 : Fin m) (hc0 : c0 ≠ js) :
    (∀ c : Fin m, (if c = js then w 1 else w 2) = (if c = js then w 1 else 0)) ↔ w 2 = 0 := by
  constructor
  · intro h
    have := h c0
    simpa [hc0] using this
  · intro h c
    by_cases hc : c = js <;> simp [hc, h]

/-! ### AUC as a function of the report, and its properness -/

/-- Indicator (as a real) that the report `q` ranks `i'` strictly below `i`. -/
noncomputable def sInd {n : ℕ} (q : Fin n → ℝ) (i i' : Fin n) : ℝ := if q i' < q i then 1 else 0

theorem sInd_comp {n : ℕ} (q : Fin n → ℝ) (φ : ℝ → ℝ) (hφ : StrictMono φ) (i i' : Fin n) :
    sInd (φ ∘ q) i i' = sInd q i i' := by
  unfold sInd
  simp only [Function.comp_apply, hφ.lt_iff_lt]

theorem sInd_cases {n : ℕ} (q : Fin n → ℝ) (i i' : Fin n) :
    sInd q i i' = 0 ∨ sInd q i i' = 1 := by
  unfold sInd
  split_ifs
  · right; rfl
  · left; rfl

/-- At most one of "`i` above `i'`" and "`i'` above `i`" holds. -/
theorem sInd_add_le {n : ℕ} (q : Fin n → ℝ) (i i' : Fin n) :
    sInd q i i' + sInd q i' i ≤ 1 := by
  unfold sInd
  by_cases h : q i' < q i
  · have h2 : ¬ q i < q i' := not_lt.mpr h.le
    simp [h, h2]
  · by_cases h2 : q i < q i'
    · simp [h, h2]
    · simp [h, h2]

/-- Number of concordant (positive, negative) pairs of the report `q` for the `0/1` labels `Y`:
ordered pairs `(i, i')` with `Y i = 1`, `Y i' = 0` and `q i' < q i`. -/
noncomputable def concordantCount {n : ℕ} (q Y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ i', Y i * (1 - Y i') * sInd q i i'

/-- AUC of the report `q` for the `0/1` labels `Y`: concordant pairs over `n⁺ · n⁻`. -/
noncomputable def aucScore {n : ℕ} (q Y : Fin n → ℝ) : ℝ :=
  concordantCount q Y / ((∑ i, Y i) * (∑ i, (1 - Y i)))

/-- AUC depends on the report only through the pairwise order: it is invariant under any strictly
monotone reparametrization. -/
theorem aucScore_comp {n : ℕ} (q Y : Fin n → ℝ) (φ : ℝ → ℝ) (hφ : StrictMono φ) :
    aucScore (φ ∘ q) Y = aucScore q Y := by
  unfold aucScore concordantCount
  simp only [sInd_comp q φ hφ]

/-- Expected AUC of the report `q` over a finite set of label scenarios `ω` with weights `P ω`
(no independence between units is assumed: `Y ω` is an arbitrary label vector per scenario). -/
noncomputable def expAUC {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (q : Fin n → ℝ) : ℝ :=
  ∑ ω, P ω * aucScore q (Y ω)

theorem expAUC_comp {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (q : Fin n → ℝ) (φ : ℝ → ℝ) (hφ : StrictMono φ) :
    expAUC P Y (φ ∘ q) = expAUC P Y q := by
  unfold expAUC
  exact Finset.sum_congr rfl (fun ω _ => by rw [aucScore_comp q (Y ω) φ hφ])

/-- Proposition ("`AUC_j` is not strictly proper"), the non-uniqueness half, for the expected AUC
under any finite label distribution: whenever a report `q` maximises the expected AUC, so does the
different report `q + 1` (which induces the same ranking). No report is the unique maximiser. -/
theorem expAUC_no_unique_maximiser {n : ℕ} (hn : 0 < n) {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (Y : Ω → Fin n → ℝ) (q : Fin n → ℝ)
    (hq : ∀ q', expAUC P Y q' ≤ expAUC P Y q) :
    ∃ q', q' ≠ q ∧ expAUC P Y q' = expAUC P Y q ∧ ∀ q'', expAUC P Y q'' ≤ expAUC P Y q' := by
  have hshift : StrictMono (fun x : ℝ => x + 1) := fun _ _ h => by linarith
  have heq : expAUC P Y (fun i => q i + 1) = expAUC P Y q :=
    expAUC_comp P Y q (fun x => x + 1) hshift
  refine ⟨fun i => q i + 1, ?_, heq, fun q'' => by rw [heq]; exact hq q''⟩
  intro h
  have h0 := congrFun h ⟨0, hn⟩
  simp at h0

/-- AUC depends on the report only through the pairwise indicators `sInd`: two reports inducing the
same ranking have the same AUC for every labelling. -/
theorem aucScore_congr {n : ℕ} (q q' Y : Fin n → ℝ) (h : ∀ i i', sInd q i i' = sInd q' i i') :
    aucScore q Y = aucScore q' Y := by
  unfold aucScore concordantCount
  simp only [h]

theorem expAUC_congr {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (q q' : Fin n → ℝ) (h : ∀ i i', sInd q i i' = sInd q' i i') :
    expAUC P Y q = expAUC P Y q' := by
  unfold expAUC
  exact Finset.sum_congr rfl (fun ω _ => by rw [aucScore_congr q q' (Y ω) h])

/-- Weight of the ordered pair `(i, i')` among the scenarios: `E[Y i · (1 − Y i')]`. -/
noncomputable def pairWeight {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (i i' : Fin n) : ℝ :=
  ∑ ω, P ω * (Y ω i * (1 - Y ω i'))

/-- Expected number of concordant pairs of the report `q`. -/
noncomputable def expConcordant {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (q : Fin n → ℝ) : ℝ :=
  ∑ ω, P ω * concordantCount q (Y ω)

theorem expConcordant_eq {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (q : Fin n → ℝ) :
    expConcordant P Y q = ∑ i, ∑ i', pairWeight P Y i i' * sInd q i i' := by
  unfold expConcordant concordantCount pairWeight
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  ring

/-- Elementary two-pair bound: if `b ≤ a`, `a, b ≥ 0` and the indicators `x, y ∈ {0,1}` are not
both `1`, then `a·x + b·y ≤ a`. -/
theorem pair_term_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a) (x y : ℝ)
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hxy : x + y ≤ 1) : a * x + b * y ≤ a := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy <;> linarith

/-- Proposition ("`AUC_j` is not strictly proper"), the maximality half, for the expected number of
concordant pairs: if `p i` is the probability that unit `i` is positive (`p i = ∑ ω P ω · Y ω i`),
with distinct values, then reporting `p` maximises the expected number of concordant pairs over all
reports `q` — whatever the dependence between the units' labels. The argument is pairwise:
`E[Y i (1 − Y i')] − E[Y i' (1 − Y i)] = p i − p i'`, so ranking the higher-`p` unit above is the
better choice for every pair at once. (For the *normalised* AUC, whose denominator `n⁺ n⁻` is
random, see `expAUC_indep_le_truthful`: it holds for independent labels, and fails in general.) -/
theorem expConcordant_le_truthful {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (Y : Ω → Fin n → ℝ) (hY : ∀ ω i, Y ω i = 0 ∨ Y ω i = 1)
    (p : Fin n → ℝ) (hp : ∀ i, p i = ∑ ω, P ω * Y ω i) (hpinj : Function.Injective p)
    (q : Fin n → ℝ) :
    expConcordant P Y q ≤ expConcordant P Y p := by
  have hnonneg : ∀ i i', 0 ≤ pairWeight P Y i i' := by
    intro i i'
    unfold pairWeight
    refine Finset.sum_nonneg (fun ω _ => mul_nonneg (hP ω) ?_)
    rcases hY ω i with h | h <;> rcases hY ω i' with h' | h' <;> simp [h, h']
  have hdiff : ∀ i i', pairWeight P Y i i' - pairWeight P Y i' i = p i - p i' := by
    intro i i'
    rw [hp i, hp i']
    unfold pairWeight
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have hsym : ∀ r : Fin n → ℝ,
      ∑ i, ∑ i', pairWeight P Y i i' * sInd r i i'
        = (1 / 2) * ∑ i, ∑ i', (pairWeight P Y i i' * sInd r i i'
            + pairWeight P Y i' i * sInd r i' i) := by
    intro r
    have hU : ∑ i, ∑ i', pairWeight P Y i' i * sInd r i' i
        = ∑ i, ∑ i', pairWeight P Y i i' * sInd r i i' := Finset.sum_comm
    simp only [Finset.sum_add_distrib]
    rw [hU]
    ring
  rw [expConcordant_eq, expConcordant_eq, hsym q, hsym p]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun i' _ => ?_))
  by_cases hii : i = i'
  · subst hii
    simp [sInd]
  · have hne : p i ≠ p i' := fun h => hii (hpinj h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hab : pairWeight P Y i i' ≤ pairWeight P Y i' i := by
        have := hdiff i i'
        linarith
      have e1 : sInd p i i' = 0 := by
        unfold sInd
        simp [not_lt.mpr hlt.le]
      have e2 : sInd p i' i = 1 := by
        unfold sInd
        simp [hlt]
      have hx := sInd_cases q i' i
      have hy := sInd_cases q i i'
      have hxy : sInd q i' i + sInd q i i' ≤ 1 := by
        have := sInd_add_le q i i'
        linarith
      have := pair_term_le (hnonneg i' i) (hnonneg i i') hab (sInd q i' i) (sInd q i i') hx hy hxy
      rw [e1, e2]
      linarith
    · have hab : pairWeight P Y i' i ≤ pairWeight P Y i i' := by
        have := hdiff i i'
        linarith
      have e1 : sInd p i i' = 1 := by
        unfold sInd
        simp [hgt]
      have e2 : sInd p i' i = 0 := by
        unfold sInd
        simp [not_lt.mpr hgt.le]
      have hx := sInd_cases q i i'
      have hy := sInd_cases q i' i
      have hxy := sInd_add_le q i i'
      have := pair_term_le (hnonneg i i') (hnonneg i' i) hab (sInd q i i') (sInd q i' i) hx hy hxy
      rw [e1, e2]
      linarith

/-- Corollary ("Skew behaviour of the DCG family"), part (b): the raw per-class DCG, the average of
the cell values `D i = Y i · w(rank_i(j))` over the population, with the positive examples of
class `j` replicated `lam`-fold, is independent of `lam` iff the mean of `g` (the rank weight) over
the positives is `0`, i.e. iff `nDCG_j^class = 0` (the cells of the negatives are zero). -/
theorem raw_dcg_class_skew_iff {n : ℕ} (pos neg : Finset (Fin n)) (hpos : 0 < pos.card)
    (hneg : 0 < neg.card) (D g : Fin n → ℝ) (hDpos : ∀ i ∈ pos, D i = g i)
    (hDneg : ∀ i ∈ neg, D i = 0) {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hne : lam ≠ mu) :
    Mixture.replAvg pos neg D lam = Mixture.replAvg pos neg D mu
      ↔ (∑ i ∈ pos, g i) / pos.card = 0 := by
  rw [Mixture.replAvg_eq_iff pos neg hpos hneg D hlam hmu hne]
  have e1 : ∑ i ∈ pos, D i = ∑ i ∈ pos, g i := Finset.sum_congr rfl hDpos
  have e2 : ∑ i ∈ neg, D i = 0 := Finset.sum_eq_zero hDneg
  rw [e1, e2]
  simp

/-- Corollary ("Skew behaviour of the DCG family"), part (d): micro-nDCG
`∑ DCG_i / ∑ IDCG_i` of the population with the positive examples of class `j` replicated
`lam`-fold is independent of `lam` iff `(∑_pos DCG)(∑_neg IDCG) = (∑_neg DCG)(∑_pos IDCG)`, i.e.
iff the ratio `∑ DCG / ∑ IDCG` is the same over the positive and over the negative examples.
(Parts (a) and (c): `ndcg_class_skew_invariant`, and `exemplar_average_skew_iff` together with
`raw_aggregation_collapse` for the raw micro and the raw and normalised exemplar averages.) -/
theorem micro_ndcg_skew_iff {n : ℕ} (pos neg : Finset (Fin n)) (dcg idcg : Fin n → ℝ)
    (hbp : 0 < ∑ i ∈ pos, idcg i) (hbn : 0 < ∑ i ∈ neg, idcg i) {lam mu : ℝ} (hlam : 0 < lam)
    (hmu : 0 < mu) (hne : lam ≠ mu) :
    Mixture.replRatio pos neg dcg idcg lam = Mixture.replRatio pos neg dcg idcg mu
      ↔ (∑ i ∈ pos, dcg i) * (∑ i ∈ neg, idcg i) = (∑ i ∈ neg, dcg i) * (∑ i ∈ pos, idcg i) :=
  Mixture.replRatio_eq_iff pos neg dcg idcg hbp hbn hlam hmu hne

/-- Pairwise maximality, abstractly: if the pair weights `W` are nonnegative and rank the higher-`p`
unit's direction first (`p i < p i' → W i i' ≤ W i' i`), then the sorted report `p` maximises
`∑ W i i' · 1[q i' < q i]` over all reports `q`. -/
theorem pairSum_le_truthful {n : ℕ} (W : Fin n → Fin n → ℝ) (hW : ∀ i i', 0 ≤ W i i')
    (p : Fin n → ℝ) (hpinj : Function.Injective p)
    (hord : ∀ i i', p i < p i' → W i i' ≤ W i' i) (q : Fin n → ℝ) :
    ∑ i, ∑ i', W i i' * sInd q i i' ≤ ∑ i, ∑ i', W i i' * sInd p i i' := by
  have hsym : ∀ r : Fin n → ℝ,
      ∑ i, ∑ i', W i i' * sInd r i i'
        = (1 / 2) * ∑ i, ∑ i', (W i i' * sInd r i i' + W i' i * sInd r i' i) := by
    intro r
    have hU : ∑ i, ∑ i', W i' i * sInd r i' i = ∑ i, ∑ i', W i i' * sInd r i i' :=
      Finset.sum_comm
    simp only [Finset.sum_add_distrib]
    rw [hU]
    ring
  rw [hsym q, hsym p]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun i' _ => ?_))
  by_cases hii : i = i'
  · subst hii
    simp [sInd]
  · have hne : p i ≠ p i' := fun h => hii (hpinj h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hab : W i i' ≤ W i' i := hord i i' hlt
      have e1 : sInd p i i' = 0 := by
        unfold sInd
        simp [not_lt.mpr hlt.le]
      have e2 : sInd p i' i = 1 := by
        unfold sInd
        simp [hlt]
      have hx := sInd_cases q i' i
      have hy := sInd_cases q i i'
      have hxy : sInd q i' i + sInd q i i' ≤ 1 := by
        have := sInd_add_le q i i'
        linarith
      have := pair_term_le (hW i' i) (hW i i') hab (sInd q i' i) (sInd q i i') hx hy hxy
      rw [e1, e2]
      linarith
    · have hab : W i' i ≤ W i i' := hord i' i hgt
      have e1 : sInd p i i' = 1 := by
        unfold sInd
        simp [hgt]
      have e2 : sInd p i' i = 0 := by
        unfold sInd
        simp [not_lt.mpr hgt.le]
      have hx := sInd_cases q i i'
      have hy := sInd_cases q i' i
      have hxy := sInd_add_le q i i'
      have := pair_term_le (hW i i') (hW i' i) hab (sInd q i i') (sInd q i' i) hx hy hxy
      rw [e1, e2]
      linarith

/-- Weight of the ordered pair `(i, i')` in the expected *normalised* AUC:
`E[Y i (1 − Y i') / (n⁺ n⁻)]`. -/
noncomputable def aucWeight {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (i i' : Fin n) : ℝ :=
  ∑ ω, P ω * (Y ω i * (1 - Y ω i') / ((∑ k, Y ω k) * (∑ k, (1 - Y ω k))))

/-- The expected AUC is a sum over ordered pairs, weighted by `aucWeight`. -/
theorem expAUC_eq {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (q : Fin n → ℝ) :
    expAUC P Y q = ∑ i, ∑ i', aucWeight P Y i i' * sInd q i i' := by
  have h1 : ∀ ω, P ω * aucScore q (Y ω)
      = ∑ i, ∑ i', P ω * (Y ω i * (1 - Y ω i') / ((∑ k, Y ω k) * (∑ k, (1 - Y ω k))))
          * sInd q i i' := by
    intro ω
    unfold aucScore concordantCount
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    ring
  unfold expAUC aucWeight
  simp only [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

/-- Independent Bernoulli factor of unit `k` for outcome `b`. -/
def bf {n : ℕ} (p : Fin n → ℝ) (k : Fin n) (b : Bool) : ℝ := if b then p k else 1 - p k

/-- Product (independent Bernoulli) law with success probabilities `p` on `Fin n → Bool`. -/
noncomputable def bernP {n : ℕ} (p : Fin n → ℝ) (ω : Fin n → Bool) : ℝ := ∏ k, bf p k (ω k)

/-- Labels `0/1` of an outcome `ω`. -/
def boolLab {n : ℕ} (ω : Fin n → Bool) : Fin n → ℝ := fun k => if ω k then 1 else 0

/-- Product of the factors of the units other than `i` and `i'`. -/
noncomputable def bernRest {n : ℕ} (p : Fin n → ℝ) (i i' : Fin n) (ω : Fin n → Bool) : ℝ :=
  ∏ k ∈ (Finset.univ.erase i).erase i', bf p k (ω k)

theorem bernP_eq {n : ℕ} (p : Fin n → ℝ) {i i' : Fin n} (hii : i ≠ i') (ω : Fin n → Bool) :
    bernP p ω = bf p i (ω i) * (bf p i' (ω i') * bernRest p i i' ω) := by
  unfold bernP bernRest
  rw [Finset.mul_prod_erase (Finset.univ.erase i) (fun k => bf p k (ω k))
        (Finset.mem_erase.mpr ⟨hii.symm, Finset.mem_univ i'⟩),
      Finset.mul_prod_erase Finset.univ (fun k => bf p k (ω k)) (Finset.mem_univ i)]

theorem bernRest_swap {n : ℕ} (p : Fin n → ℝ) (i i' : Fin n) (ω : Fin n → Bool) :
    bernRest p i i' (ω ∘ Equiv.swap i i') = bernRest p i i' ω := by
  unfold bernRest
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have h1 : k ≠ i' := (Finset.mem_erase.mp hk).1
  have h2 : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  simp [Equiv.swap_apply_of_ne_of_ne h2 h1]

theorem bf_nonneg {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (k : Fin n)
    (b : Bool) : 0 ≤ bf p k b := by
  unfold bf
  cases b
  · simp; linarith [hp1 k]
  · simpa using hp0 k

theorem bernP_nonneg {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (ω : Fin n → Bool) : 0 ≤ bernP p ω :=
  Finset.prod_nonneg (fun k _ => bf_nonneg p hp0 hp1 k _)

theorem bernRest_nonneg {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (i i' : Fin n) (ω : Fin n → Bool) : 0 ≤ bernRest p i i' ω :=
  Finset.prod_nonneg (fun k _ => bf_nonneg p hp0 hp1 k _)

theorem boolLab_sum_nonneg {n : ℕ} (ω : Fin n → Bool) :
    0 ≤ ∑ k, boolLab ω k ∧ 0 ≤ ∑ k, (1 - boolLab ω k) := by
  constructor
  · exact Finset.sum_nonneg (fun k _ => by unfold boolLab; split_ifs <;> norm_num)
  · exact Finset.sum_nonneg (fun k _ => by unfold boolLab; split_ifs <;> norm_num)

theorem boolLab_cell_nonneg {n : ℕ} (ω : Fin n → Bool) (i i' : Fin n) :
    0 ≤ boolLab ω i * (1 - boolLab ω i')
          / ((∑ k, boolLab ω k) * (∑ k, (1 - boolLab ω k))) := by
  refine div_nonneg ?_ (mul_nonneg (boolLab_sum_nonneg ω).1 (boolLab_sum_nonneg ω).2)
  unfold boolLab
  split_ifs <;> norm_num

theorem aucWeight_nonneg {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (i i' : Fin n) : 0 ≤ aucWeight (bernP p) boolLab i i' :=
  Finset.sum_nonneg (fun ω _ =>
    mul_nonneg (bernP_nonneg p hp0 hp1 ω) (boolLab_cell_nonneg ω i i'))

/-- The label-swap identity behind the proof for independent labels: for units `i ≠ i'`,
`b_{ii'} - b_{i'i} = (p_i - p_{i'}) · K` with `K ≥ 0`, where `b` is `aucWeight`. -/
theorem aucWeight_diff {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    {i i' : Fin n} (hii : i ≠ i') :
    ∃ K : ℝ, 0 ≤ K ∧
      aucWeight (bernP p) boolLab i i' - aucWeight (bernP p) boolLab i' i = (p i - p i') * K := by
  let sw : (Fin n → Bool) → (Fin n → Bool) := fun ω => ω ∘ Equiv.swap i i'
  have hinv : Function.Involutive sw := by
    intro ω
    funext k
    simp [sw, Function.comp]
  let e : Equiv.Perm (Fin n → Bool) := hinv.toPerm sw
  have he : ∀ ω, e ω = sw ω := fun ω => rfl
  set D : (Fin n → Bool) → ℝ := fun ω => (∑ k, boolLab ω k) * (∑ k, (1 - boolLab ω k)) with hD
  have hDsw : ∀ ω, D (sw ω) = D ω := by
    intro ω
    have h1 : ∑ k, boolLab (sw ω) k = ∑ k, boolLab ω k :=
      Equiv.sum_comp (Equiv.swap i i') (boolLab ω)
    have h2 : ∑ k, (1 - boolLab (sw ω) k) = ∑ k, (1 - boolLab ω k) :=
      Equiv.sum_comp (Equiv.swap i i') (fun k => 1 - boolLab ω k)
    simp only [hD, h1, h2]
  have hrest : ∀ ω, bernRest p i i' (sw ω) = bernRest p i i' ω := fun ω =>
    bernRest_swap p i i' ω
  refine ⟨∑ ω, bernRest p i i' ω * (boolLab ω i * (1 - boolLab ω i') / D ω), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun ω _ =>
      mul_nonneg (bernRest_nonneg p hp0 hp1 i i' ω) (boolLab_cell_nonneg ω i i'))
  · have hrw : aucWeight (bernP p) boolLab i' i
        = ∑ ω, bernP p (sw ω) * (boolLab ω i * (1 - boolLab ω i') / D ω) := by
      unfold aucWeight
      rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      rw [he]
      have hl1 : boolLab (sw ω) i' = boolLab ω i := by simp [boolLab, sw]
      have hl2 : boolLab (sw ω) i = boolLab ω i' := by simp [boolLab, sw]
      rw [hl1, hl2]
      have := hDsw ω
      simp only [hD] at this ⊢
      rw [this]
    rw [hrw]
    unfold aucWeight
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have e1 := bernP_eq p hii ω
    have e2 := bernP_eq p hii (sw ω)
    rw [hrest ω] at e2
    have hs1 : sw ω i = ω i' := by simp [sw]
    have hs2 : sw ω i' = ω i := by simp [sw]
    rw [hs1, hs2] at e2
    cases hi : ω i <;> cases hi' : ω i' <;>
      simp [e1, e2, hi, hi', bf, boolLab, hD] <;> ring

theorem aucWeight_ord {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (i i' : Fin n) (h : p i < p i') :
    aucWeight (bernP p) boolLab i i' ≤ aucWeight (bernP p) boolLab i' i := by
  have hii : i ≠ i' := fun e => by rw [e] at h; exact lt_irrefl _ h
  obtain ⟨K, hK, hd⟩ := aucWeight_diff p hp0 hp1 hii
  have : (p i - p i') * K ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hK
  linarith

/-- Proposition ("`AUC_j` is not strictly proper"), part (ii): if the labels of different units are
independent with success probabilities `p` (distinct), reporting `p` maximises the expected
*normalised* AUC (with the convention that AUC is `0` when `n⁺ n⁻ = 0`, which only rescales the
expectation) over all reports `q`. -/
theorem expAUC_indep_le_truthful {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hpinj : Function.Injective p) (q : Fin n → ℝ) :
    expAUC (bernP p) boolLab q ≤ expAUC (bernP p) boolLab p := by
  rw [expAUC_eq, expAUC_eq]
  exact pairSum_le_truthful _ (aucWeight_nonneg p hp0 hp1) p hpinj (aucWeight_ord p hp0 hp1) q

/-- Class-case of Theorem ("Raw DCG collapses; nDCG does not"), part (b): with `T j = ∑_i D_ij` the
class cell sums, `N j = k_j · w(1) > 0` the class ideals and `B = ∑_i IDCG_i > 0`, micro-nDCG
equals the mean of the per-class nDCGs iff one linear equation in the `T j` holds. -/
theorem ndcg_class_vs_micro_iff {m : ℕ} (T N : Fin m → ℝ) (B : ℝ) (hN : ∀ j, 0 < N j)
    (hB : 0 < B) (hm : 0 < m) :
    (∑ j, T j) / B = (1 / (m : ℝ)) * ∑ j, T j / N j
      ↔ ∑ j, T j * (1 / B - 1 / ((m : ℝ) * N j)) = 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have key : (∑ j, T j) / B - (1 / (m : ℝ)) * ∑ j, T j / N j
      = ∑ j, T j * (1 / B - 1 / ((m : ℝ) * N j)) := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have := (hN j).ne'
    field_simp
  rw [← sub_eq_zero, key]

/-- The two normalisations agree for *every* vector of class sums `T` iff `m · N j = B` for every
class `j`. -/
theorem ndcg_class_vs_micro_identical_iff {m : ℕ} (N : Fin m → ℝ) (B : ℝ) (hN : ∀ j, 0 < N j)
    (hB : 0 < B) (hm : 0 < m) :
    (∀ T : Fin m → ℝ, (∑ j, T j) / B = (1 / (m : ℝ)) * ∑ j, T j / N j)
      ↔ ∀ j, (m : ℝ) * N j = B := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · intro h j
    have h1 := (ndcg_class_vs_micro_iff (fun l => if l = j then (1 : ℝ) else 0) N B hN hB hm).mp
      (h _)
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    have hmN : (m : ℝ) * N j ≠ 0 := (mul_pos hm' (hN j)).ne'
    have h3 : 1 / B = 1 / ((m : ℝ) * N j) := by linarith
    rw [div_eq_div_iff hB.ne' hmN] at h3
    linarith
  · intro h T
    refine (ndcg_class_vs_micro_iff T N B hN hB hm).mpr (Finset.sum_eq_zero (fun j _ => ?_))
    rw [← h j]
    simp

/-- Number of relevant labels of example `i` (`k_i`). -/
def krow {n m : ℕ} (Y : Fin n → Fin m → Bool) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => Y i j = true)).card

/-- Number of positive examples of class `j` (`k_j`). -/
def kcol {n m : ℕ} (Y : Fin n → Fin m → Bool) (j : Fin m) : ℕ :=
  (Finset.univ.filter (fun i => Y i j = true)).card

theorem sum_kcol_eq_sum_krow {n m : ℕ} (Y : Fin n → Fin m → Bool) :
    ∑ j, kcol Y j = ∑ i, krow Y i := by
  unfold kcol krow
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- Total ideal DCG `∑_i IDCG_i`, with `IDCG_i = ∑_{r=1}^{k_i} w(r)`. -/
noncomputable def idealMass {n : ℕ} (w : ℕ → ℝ) (k : Fin n → ℕ) : ℝ :=
  ∑ i, ∑ r ∈ Finset.range (k i), w (r + 1)

/-- The total ideal DCG is strictly below `w(1) · ∑_i k_i` as soon as some example has at least two
relevant labels and `w(2) < w(1)` (for non-increasing `w`). -/
theorem idealMass_lt {n : ℕ} (w : ℕ → ℝ) (hw : Antitone w) (k : Fin n → ℕ)
    (hk : ∃ i, 2 ≤ k i) (hw2 : w 2 < w 1) :
    idealMass w k < w 1 * ∑ i, (k i : ℝ) := by
  obtain ⟨i0, hi0⟩ := hk
  have hle : ∀ i, ∑ r ∈ Finset.range (k i), w (r + 1) ≤ w 1 * (k i : ℝ) := by
    intro i
    calc ∑ r ∈ Finset.range (k i), w (r + 1) ≤ ∑ r ∈ Finset.range (k i), w 1 :=
          Finset.sum_le_sum (fun r _ => hw (by omega))
      _ = w 1 * (k i : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlt : ∑ r ∈ Finset.range (k i0), w (r + 1) < w 1 * (k i0 : ℝ) := by
    calc ∑ r ∈ Finset.range (k i0), w (r + 1) < ∑ r ∈ Finset.range (k i0), w 1 :=
          Finset.sum_lt_sum (fun r _ => hw (by omega))
            ⟨1, Finset.mem_range.mpr (by omega), by simpa using hw2⟩
      _ = w 1 * (k i0 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  unfold idealMass
  rw [Finset.mul_sum]
  exact Finset.sum_lt_sum (fun i _ => hle i) ⟨i0, Finset.mem_univ i0, hlt⟩

/-- The class and micro normalisations of nDCG are never interchangeable: if some example has at
least two relevant labels, `w(2) < w(1)` and `w` is non-increasing, there is no way to make
`m · N j = B` hold for every class (with `N j = k_j · w(1)`, `B = ∑_i IDCG_i`), so the equality of
micro-nDCG and the class mean is a genuine constraint on the data, not an identity. -/
theorem ndcg_class_micro_not_identical {n m : ℕ} (hm : 0 < m) (Y : Fin n → Fin m → Bool)
    (w : ℕ → ℝ) (hw : Antitone w) (hw2 : w 2 < w 1) (hk : ∃ i, 2 ≤ krow Y i) :
    ¬ ∀ j, (m : ℝ) * (w 1 * (kcol Y j : ℝ)) = idealMass w (krow Y) := by
  intro h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : ∑ j, (m : ℝ) * (w 1 * (kcol Y j : ℝ)) = ∑ j : Fin m, idealMass w (krow Y) :=
    Finset.sum_congr rfl (fun j _ => h j)
  have hcast : (∑ j, (kcol Y j : ℝ)) = ∑ i, (krow Y i : ℝ) := by
    exact_mod_cast sum_kcol_eq_sum_krow Y
  have hL : ∑ j, (m : ℝ) * (w 1 * (kcol Y j : ℝ)) = (m : ℝ) * (w 1 * ∑ i, (krow Y i : ℝ)) := by
    rw [← hcast, Finset.mul_sum, Finset.mul_sum]
  rw [hL, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h2 := mul_left_cancel₀ hm'.ne' hsum
  have h3 := idealMass_lt w hw (krow Y) hk hw2
  linarith

/-- Theorem ("Collapse and non-collapse for AUC"), part (b), micro versus macro: micro-AUC
`∑ n⁺_j AUC_j / ∑ n⁺_j` equals macro-AUC iff the class sizes `n⁺_j` and the `AUC_j` are
empirically uncorrelated (an instance of `weighted_eq_unweighted_iff_cov_zero`). -/
theorem micro_macro_auc_iff_cov_zero {m : ℕ} (hm : m ≠ 0) (npos auc : Fin m → ℝ)
    (nbar abar cov : ℝ) (hnbar : nbar = (1 / (m : ℝ)) * ∑ j, npos j)
    (habar : abar = (1 / (m : ℝ)) * ∑ j, auc j)
    (hcov : cov = (1 / (m : ℝ)) * ∑ j, (npos j - nbar) * (auc j - abar)) (hnbar0 : nbar ≠ 0) :
    (∑ j, npos j * auc j) / (∑ j, npos j) = abar ↔ cov = 0 :=
  weighted_eq_unweighted_iff_cov_zero hm npos auc nbar abar cov hnbar habar hcov hnbar0

/-- Any report inducing the same ranking as the truthful one `p` is also a maximiser of the expected
normalised AUC for independent labels (so, with `expAUC_no_unique_maximiser`, the truthful report is
a maximiser but never the unique one). -/
theorem expAUC_indep_same_ranking_max {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hpinj : Function.Injective p) (p' q : Fin n → ℝ)
    (h : ∀ i i', sInd p' i i' = sInd p i i') :
    expAUC (bernP p) boolLab q ≤ expAUC (bernP p) boolLab p' := by
  rw [expAUC_congr (bernP p) boolLab p' p h]
  exact expAUC_indep_le_truthful p hp0 hp1 hpinj q

/-- Class mean versus exemplar mean of two normalisations of one cell matrix `D` (`D i j` the cell of
example `i`, class `j`; `N j` the class normaliser, `b i` the example normaliser). This covers the
third comparison of Theorem ("Raw DCG collapses; nDCG does not"), part (b) (`N j = k_j w(1)`,
`b i = IDCG_i`, cells `D_ij`), and macro- versus exemplar-AUC in Theorem ("Collapse and non-collapse
for AUC"), part (b) (`N j = n⁺_j`, `b i = k_i`, cells `A_ij`): the two scalars are equal iff one
linear equation in the cells holds. -/
theorem class_vs_exemplar_iff {n m : ℕ} (D : Fin n → Fin m → ℝ) (N : Fin m → ℝ) (b : Fin n → ℝ) :
    (1 / (m : ℝ)) * ∑ j, (∑ i, D i j) / N j = (1 / (n : ℝ)) * ∑ i, (∑ j, D i j) / b i
      ↔ ∑ i, ∑ j, D i j * (1 / ((m : ℝ) * N j) - 1 / ((n : ℝ) * b i)) = 0 := by
  have e1 : (1 / (m : ℝ)) * ∑ j, (∑ i, D i j) / N j
      = ∑ i, ∑ j, D i j * (1 / ((m : ℝ) * N j)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have e2 : (1 / (n : ℝ)) * ∑ i, (∑ j, D i j) / b i
      = ∑ i, ∑ j, D i j * (1 / ((n : ℝ) * b i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have key : (1 / (m : ℝ)) * ∑ j, (∑ i, D i j) / N j - (1 / (n : ℝ)) * ∑ i, (∑ j, D i j) / b i
      = ∑ i, ∑ j, D i j * (1 / ((m : ℝ) * N j) - 1 / ((n : ℝ) * b i)) := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [← sub_eq_zero, key]

/-- The class mean and the exemplar mean agree for *every* cell matrix iff `m · N j = n · b i` for
all `i, j`. -/
theorem class_vs_exemplar_identical_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (N : Fin m → ℝ)
    (b : Fin n → ℝ) (hN : ∀ j, 0 < N j) (hb : ∀ i, 0 < b i) :
    (∀ D : Fin n → Fin m → ℝ,
        (1 / (m : ℝ)) * ∑ j, (∑ i, D i j) / N j = (1 / (n : ℝ)) * ∑ i, (∑ j, D i j) / b i)
      ↔ ∀ i j, (m : ℝ) * N j = (n : ℝ) * b i := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h i j
    have hsingle : ∀ Y : Fin n → Fin m → ℝ,
        ∑ i', ∑ j', (if i' = i ∧ j' = j then (1 : ℝ) else 0) * Y i' j' = Y i j := by
      intro Y
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj'
          simp [hj']
        · intro h
          exact absurd (Finset.mem_univ j) h
      · intro i' _ hi'
        apply Finset.sum_eq_zero
        intro j' _
        simp [hi']
      · intro h
        exact absurd (Finset.mem_univ i) h
    have h1 := (class_vs_exemplar_iff
      (fun i' j' => if i' = i ∧ j' = j then (1 : ℝ) else 0) N b).mp (h _)
    have h2 : 1 / ((m : ℝ) * N j) - 1 / ((n : ℝ) * b i) = 0 :=
      (hsingle (fun i' j' => 1 / ((m : ℝ) * N j') - 1 / ((n : ℝ) * b i'))).symm.trans h1
    have h3 : 1 / ((m : ℝ) * N j) = 1 / ((n : ℝ) * b i) := by linarith
    rw [div_eq_div_iff (mul_pos hm' (hN j)).ne' (mul_pos hn' (hb i)).ne'] at h3
    linarith
  · intro h D
    refine (class_vs_exemplar_iff D N b).mpr (Finset.sum_eq_zero (fun i _ => ?_))
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [← h i j]
    simp

/-- Third comparison of Theorem ("Raw DCG collapses; nDCG does not"), part (b): the class mean and
the exemplar mean of nDCG are never interchangeable. If some example has at least two relevant
labels, `w` is non-increasing and `w(2) < w(1)`, then `m · N j = n · IDCG_i` (with `N j = k_j w(1)`)
cannot hold for all `i, j`, so by `class_vs_exemplar_identical_iff` there are cell matrices on which
the two scalars differ. -/
theorem ndcg_class_exemplar_not_identical {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (Y : Fin n → Fin m → Bool) (w : ℕ → ℝ) (hw : Antitone w) (hw2 : w 2 < w 1)
    (hk : ∃ i, 2 ≤ krow Y i) :
    ¬ ∀ i j, (m : ℝ) * (w 1 * (kcol Y j : ℝ))
        = (n : ℝ) * ∑ r ∈ Finset.range (krow Y i), w (r + 1) := by
  intro h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ndcg_class_micro_not_identical hm Y w hw hw2 hk (fun j => ?_)
  have hsum : ∑ _i : Fin n, (m : ℝ) * (w 1 * (kcol Y j : ℝ))
      = ∑ i, (n : ℝ) * ∑ r ∈ Finset.range (krow Y i), w (r + 1) :=
    Finset.sum_congr rfl (fun i _ => h i j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    at hsum
  have h2 := mul_left_cancel₀ hn'.ne' hsum
  unfold idealMass
  exact h2

/-- Theorem ("Collapse and non-collapse for AUC"), part (b), micro versus exemplar: with
`AUC_i^ex = ∑_j A_ij / k_i`, micro-AUC `= ∑_i k_i AUC_i^ex / ∑_i k_i` equals the exemplar mean iff
`Cov(k_i, AUC_i^ex) = 0` (an instance of `weighted_eq_unweighted_iff_cov_zero`; in particular when
all `k_i` are equal). -/
theorem micro_exemplar_auc_iff_cov_zero {n : ℕ} (hn : n ≠ 0) (k aucex : Fin n → ℝ)
    (kbar abar cov : ℝ) (hkbar : kbar = (1 / (n : ℝ)) * ∑ i, k i)
    (habar : abar = (1 / (n : ℝ)) * ∑ i, aucex i)
    (hcov : cov = (1 / (n : ℝ)) * ∑ i, (k i - kbar) * (aucex i - abar)) (hkbar0 : kbar ≠ 0) :
    (∑ i, k i * aucex i) / (∑ i, k i) = abar ↔ cov = 0 :=
  weighted_eq_unweighted_iff_cov_zero hn k aucex kbar abar cov hkbar habar hcov hkbar0

/-- Expectation of the positional score over finitely many label scenarios. -/
theorem positional_expected_eq {m : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin m → ℝ)
    (r : Fin m → ℕ) (w : ℕ → ℝ) :
    ∑ ω, P ω * (∑ j, Y ω j * w (r j)) = ∑ j, (∑ ω, P ω * Y ω j) * w (r j) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun ω _ => by ring))

/-- Proposition ("Positional operators are not strictly proper"), properness half, from the random
labels: if `p j = E[Y j]` (distinct) and the report `q` has distinct entries, then reporting `p`
maximises the *expected* positional score `E[∑ⱼ Yⱼ w(rank_q(j))]` over the finitely many label
scenarios, for non-increasing `w`. With `positional_expected_eq` this derives the expected-score
formula (Eq. `disc_expect`) rather than taking it as given. -/
theorem positional_expected_properness {m : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    (Y : Ω → Fin m → ℝ) (p : Fin m → ℝ) (hp : ∀ j, p j = ∑ ω, P ω * Y ω j)
    (hpinj : Function.Injective p) (q : Fin m → ℝ) (hq : Function.Injective q) (w : ℕ → ℝ)
    (hw : Antitone w) :
    ∑ ω, P ω * (∑ j, Y ω j * w (rank q j)) ≤ ∑ ω, P ω * (∑ j, Y ω j * w (rank p j)) := by
  rw [positional_expected_eq, positional_expected_eq]
  simp only [← hp]
  exact positional_properness p q hpinj hq w hw

/-- Exact counterexample to the maximality of the truthful report for the *normalised* AUC when the
labels are dependent (`expAUC_dependent_counterexample`): four units, five label scenarios with
probabilities `1, 2, 3, 2, 3` out of `11`. The marginals `cexp = (8, 5, 7, 6)/11` are distinct; the
truthful ranking has expected AUC `41/66`, the ranking `cexq` has `83/132`. -/
noncomputable def cexP : Fin 5 → ℝ := ![1/11, 2/11, 3/11, 2/11, 3/11]
noncomputable def cexY : Fin 5 → Fin 4 → ℝ :=
  ![![0, 0, 0, 1], ![0, 1, 1, 0], ![1, 0, 1, 0], ![1, 0, 1, 1], ![1, 1, 0, 1]]
noncomputable def cexp : Fin 4 → ℝ := ![8/11, 5/11, 7/11, 6/11]
noncomputable def cexq : Fin 4 → ℝ := ![3, 0, 1, 2]

theorem cex_marginals : ∀ i, cexp i = ∑ ω, cexP ω * cexY ω i := by
  intro i
  fin_cases i <;> simp [cexp, cexP, cexY, Fin.sum_univ_succ] <;> norm_num

theorem cex_injective : Function.Injective cexp := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp [cexp] at h)

theorem cex_expAUC_truthful : expAUC cexP cexY cexp = 41 / 66 := by
  simp [expAUC, aucScore, concordantCount, sInd, Fin.sum_univ_succ, cexP, cexY, cexp]
  norm_num

theorem cex_expAUC_other : expAUC cexP cexY cexq = 83 / 132 := by
  simp [expAUC, aucScore, concordantCount, sInd, Fin.sum_univ_succ, cexP, cexY, cexq]
  norm_num

theorem expAUC_dependent_counterexample :
    (∀ ω i, cexY ω i = 0 ∨ cexY ω i = 1) ∧ (∀ ω, 0 ≤ cexP ω) ∧ ∑ ω, cexP ω = 1 ∧
    (∀ i, cexp i = ∑ ω, cexP ω * cexY ω i) ∧ Function.Injective cexp ∧
    expAUC cexP cexY cexp < expAUC cexP cexY cexq := by
  refine ⟨?_, ?_, ?_, cex_marginals, cex_injective, ?_⟩
  · intro ω i
    fin_cases ω <;> fin_cases i <;> simp [cexY]
  · intro ω
    fin_cases ω <;> simp [cexP] <;> norm_num
  · simp [cexP, Fin.sum_univ_succ]
    norm_num
  · rw [cex_expAUC_truthful, cex_expAUC_other]
    norm_num

/-- `E[Y i (1 − Y i')] − E[Y i' (1 − Y i)] = p i − p i'` under any joint law of the labels. -/
theorem pairWeight_sub {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i = ∑ ω, P ω * Y ω i) (i i' : Fin n) :
    pairWeight P Y i i' - pairWeight P Y i' i = p i - p i' := by
  rw [hp i, hp i']
  unfold pairWeight
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

theorem pairWeight_nonneg {n : ℕ} {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (Y : Ω → Fin n → ℝ) (hY : ∀ ω i, Y ω i = 0 ∨ Y ω i = 1) (i i' : Fin n) :
    0 ≤ pairWeight P Y i i' := by
  unfold pairWeight
  refine Finset.sum_nonneg (fun ω _ => mul_nonneg (hP ω) ?_)
  rcases hY ω i with h | h <;> rcases hY ω i' with h' | h' <;> simp [h, h']

/-- For three units and `0/1` labels, `n⁺ n⁻ = 2` whenever a pair `(i, i')` has `y i = 1`, `y i' = 0`
(the third label `y` gives `(1 + y)(2 − y) = 2`), so the normalised pair cell is half the numerator
cell. -/
theorem auc_cell_three (y : Fin 3 → ℝ) (hy : ∀ k, y k = 0 ∨ y k = 1) (i i' : Fin 3) :
    y i * (1 - y i') / ((∑ k, y k) * (∑ k, (1 - y k))) = (1 / 2) * (y i * (1 - y i')) := by
  rcases hy 0 with h0 | h0 <;> rcases hy 1 with h1 | h1 <;> rcases hy 2 with h2 | h2 <;>
    fin_cases i <;> fin_cases i' <;> simp [Fin.sum_univ_succ, h0, h1, h2] <;> norm_num

theorem aucWeight_three {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin 3 → ℝ)
    (hY : ∀ ω i, Y ω i = 0 ∨ Y ω i = 1) (i i' : Fin 3) :
    aucWeight P Y i i' = (1 / 2) * pairWeight P Y i i' := by
  unfold aucWeight pairWeight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [auc_cell_three (Y ω) (hY ω) i i']
  ring

/-- Proposition ("`AUC_j` is not strictly proper"), part (ii), for *three* units and *any*
dependence between the labels: the truthful report maximises the expected normalised AUC. The
denominator `n⁺ n⁻` is constant (`= 2`) on every discordant pair, so the normalised pair weights are
half the numerator weights and the pairwise argument of `expConcordant_le_truthful` applies. For
four or more units the statement fails in general (`expAUC_dependent_counterexample`). -/
theorem expAUC_three_le_truthful {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (Y : Ω → Fin 3 → ℝ) (hY : ∀ ω i, Y ω i = 0 ∨ Y ω i = 1) (p : Fin 3 → ℝ)
    (hp : ∀ i, p i = ∑ ω, P ω * Y ω i) (hpinj : Function.Injective p) (q : Fin 3 → ℝ) :
    expAUC P Y q ≤ expAUC P Y p := by
  rw [expAUC_eq, expAUC_eq]
  refine pairSum_le_truthful _ ?_ p hpinj ?_ q
  · intro i i'
    rw [aucWeight_three P Y hY]
    exact mul_nonneg (by norm_num) (pairWeight_nonneg P hP Y hY i i')
  · intro i i' h
    rw [aucWeight_three P Y hY, aucWeight_three P Y hY]
    have := pairWeight_sub P Y p hp i i'
    linarith

section MeasureBridge

open MeasureTheory

/-- Linearity of the expectation for the positional score, over an arbitrary measure space: the
report `r` (hence the ranks) is deterministic, so `E[∑ⱼ Yⱼ w(r j)] = ∑ⱼ E[Yⱼ] w(r j)`. -/
theorem positional_expected_eq_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m : ℕ}
    (Y : Ω → Fin m → ℝ) (hY : ∀ j, Integrable (fun ω => Y ω j) μ) (r : Fin m → ℕ) (w : ℕ → ℝ) :
    ∫ ω, ∑ j, Y ω j * w (r j) ∂μ = ∑ j, (∫ ω, Y ω j ∂μ) * w (r j) := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun j _ => integral_mul_const (w (r j)) (fun ω => Y ω j))
  · intro j _
    exact (hY j).mul_const _

/-- Proposition ("Positional operators are not strictly proper"), properness half, over an arbitrary
probability space of labels: if `p j = E[Y j]` (distinct) and the report `q` has distinct entries, then
reporting `p` maximises the expected positional score, for non-increasing `w`. -/
theorem positional_expected_properness_measure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {m : ℕ} (Y : Ω → Fin m → ℝ) (hY : ∀ j, Integrable (fun ω => Y ω j) μ) (p : Fin m → ℝ)
    (hp : ∀ j, p j = ∫ ω, Y ω j ∂μ) (hpinj : Function.Injective p) (q : Fin m → ℝ)
    (hq : Function.Injective q) (w : ℕ → ℝ) (hw : Antitone w) :
    ∫ ω, ∑ j, Y ω j * w (rank q j) ∂μ ≤ ∫ ω, ∑ j, Y ω j * w (rank p j) ∂μ := by
  rw [positional_expected_eq_integral μ Y hY, positional_expected_eq_integral μ Y hY]
  simp only [← hp]
  exact positional_properness p q hpinj hq w hw

/-- Bridge to the finite-scenario model: for random labels `Y` taking values in a finite type, the
expectation of any function of `Y` over an arbitrary probability space is the finite sum over the
values `y` weighted by `P(Y = y)`. The scenario weights `P ω` of `expAUC` and
`positional_expected_properness` are these probabilities. -/
theorem integral_comp_eq_sum {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype α]
    [MeasurableSingletonClass α] (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → α)
    (hY : Measurable Y) (g : α → ℝ) :
    ∫ ω, g (Y ω) ∂μ = ∑ y, μ.real (Y ⁻¹' {y}) * g y := by
  rw [← integral_map hY.aemeasurable (measurable_of_finite g).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [smul_eq_mul, map_measureReal_apply hY (measurableSet_singleton y)]

end MeasureBridge

/-- Proposition ("Hard-prediction limit"), the multilabel closed form: with one predicted label `js`
(rank `1`) and every other label at rank `2` under the min-rank convention, the raw DCG sum of an
example with relevances `Y` is `Y_{js} w(1) + w(2) (k − Y_{js})`, with `k = ∑ⱼ Yⱼ`. -/
theorem dcg_ex_hardTop_closed_form {m : ℕ} (w : ℕ → ℝ) (js : Fin m) (Y : Fin m → ℝ) :
    ∑ j, Y j * w (rank (hardTop js) j) = Y js * w 1 + w 2 * (∑ j, Y j - Y js) := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ js), rank_hardTop_self]
  have h : ∑ j ∈ Finset.univ.erase js, Y j * w (rank (hardTop js) j)
      = ∑ j ∈ Finset.univ.erase js, Y j * w 2 :=
    Finset.sum_congr rfl (fun j hj => by rw [rank_hardTop_ne js j (Finset.ne_of_mem_erase hj)])
  rw [h, ← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ js)]
  ring

/-- The exemplar average of the raw DCG with hard top-1 predictions, for arbitrary relevances `Y`:
`(P@1 · w(1) + w(2) (k̄ − P@1)) / m`, where `P@1 = (1/n) ∑ᵢ Y_{i,j*ᵢ}` and `k̄ = (1/n) ∑ᵢ kᵢ`. -/
theorem hard_ranking_average {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (Y : Fin n → Fin m → ℝ)
    (js : Fin n → Fin m) (w : ℕ → ℝ) (P kbar : ℝ) (hP : P = (1 / (n : ℝ)) * ∑ i, Y i (js i))
    (hk : kbar = (1 / (n : ℝ)) * ∑ i, ∑ j, Y i j) :
    (1 / (n : ℝ)) * ∑ i, ((1 / (m : ℝ)) * ∑ j, Y i j * w (rank (hardTop (js i)) j))
      = (P * w 1 + w 2 * (kbar - P)) / m := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have per : ∀ i, (1 / (m : ℝ)) * ∑ j, Y i j * w (rank (hardTop (js i)) j)
      = (1 / (m : ℝ)) * (Y i (js i) * w 1 + w 2 * (∑ j, Y i j - Y i (js i))) := fun i => by
    rw [dcg_ex_hardTop_closed_form w (js i) (Y i)]
  simp only [per]
  have hsum : ∑ i, (Y i (js i) * w 1 + w 2 * (∑ j, Y i j - Y i (js i)))
      = w 1 * ∑ i, Y i (js i) + w 2 * (∑ i, ∑ j, Y i j - ∑ i, Y i (js i)) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  have hS : ∑ i, Y i (js i) = (n : ℝ) * P := by rw [hP]; field_simp
  have hK : ∑ i, ∑ j, Y i j = (n : ℝ) * kbar := by rw [hk]; field_simp
  rw [← Finset.mul_sum, hsum, hS, hK]
  field_simp

theorem hard_ranking_excess_nonneg {n m : ℕ} (Y : Fin n → Fin m → ℝ) (hY : ∀ i j, 0 ≤ Y i j)
    (js : Fin n → Fin m) (i : Fin n) : 0 ≤ ∑ j, Y i j - Y i (js i) := by
  have := Finset.single_le_sum (fun j _ => hY i j) (Finset.mem_univ (js i))
  linarith

/-- Proposition ("Hard-prediction limit"), part (b), averaged: `P@1 · w(1) / m` is a lower bound on the
exemplar average of the raw DCG with hard top-1 predictions, for nonnegative weights and relevances. -/
theorem hard_ranking_average_lower_bound {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (Y : Fin n → Fin m → ℝ) (hY : ∀ i j, 0 ≤ Y i j) (js : Fin n → Fin m) (w : ℕ → ℝ)
    (hw : ∀ r, 0 ≤ w r) (P : ℝ) (hP : P = (1 / (n : ℝ)) * ∑ i, Y i (js i)) :
    P * w 1 / m ≤ (1 / (n : ℝ)) * ∑ i, ((1 / (m : ℝ)) * ∑ j, Y i j * w (rank (hardTop (js i)) j)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  obtain ⟨kbar, hk⟩ : ∃ kbar, kbar = (1 / (n : ℝ)) * ∑ i, ∑ j, Y i j := ⟨_, rfl⟩
  rw [hard_ranking_average hn hm Y js w P kbar hP hk]
  have hd : kbar - P = (1 / (n : ℝ)) * ∑ i, (∑ j, Y i j - Y i (js i)) := by
    rw [hk, hP, Finset.sum_sub_distrib]; ring
  have hnn : 0 ≤ kbar - P := by
    rw [hd]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun i _ => hard_ranking_excess_nonneg Y hY js i))
  have : 0 ≤ w 2 * (kbar - P) := mul_nonneg (hw 2) hnn
  rw [div_le_div_iff_of_pos_right hm']
  linarith

/-- Proposition ("Hard-prediction limit"), part (b), equality clause: for `w(2) > 0` and nonnegative
relevances, the lower bound `P@1 · w(1) / m` is attained iff every example's relevances sum to its
relevance at the predicted label, that is (for `0/1` relevances and `k_i ≥ 1`) iff the top-predicted
label is the example's only relevant one. -/
theorem hard_ranking_equality_iff {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (Y : Fin n → Fin m → ℝ)
    (hY : ∀ i j, 0 ≤ Y i j) (js : Fin n → Fin m) (w : ℕ → ℝ) (hw2 : 0 < w 2) (P : ℝ)
    (hP : P = (1 / (n : ℝ)) * ∑ i, Y i (js i)) :
    (1 / (n : ℝ)) * ∑ i, ((1 / (m : ℝ)) * ∑ j, Y i j * w (rank (hardTop (js i)) j))
        = P * w 1 / m
      ↔ ∀ i, ∑ j, Y i j = Y i (js i) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  obtain ⟨kbar, hk⟩ : ∃ kbar, kbar = (1 / (n : ℝ)) * ∑ i, ∑ j, Y i j := ⟨_, rfl⟩
  rw [hard_ranking_average hn hm Y js w P kbar hP hk, div_left_inj' hm'.ne']
  have hd : kbar - P = (1 / (n : ℝ)) * ∑ i, (∑ j, Y i j - Y i (js i)) := by
    rw [hk, hP, Finset.sum_sub_distrib]; ring
  constructor
  · intro h
    have h1 : w 2 * (kbar - P) = 0 := by linarith
    have h2 : kbar - P = 0 := by
      rcases mul_eq_zero.mp h1 with h0 | h0
      · exact absurd h0 hw2.ne'
      · exact h0
    rw [hd] at h2
    have h3 : ∑ i, (∑ j, Y i j - Y i (js i)) = 0 := by
      rcases mul_eq_zero.mp h2 with h0 | h0
      · exact absurd h0 (by positivity)
      · exact h0
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => hard_ranking_excess_nonneg Y hY js i)).mp h3 i (Finset.mem_univ i)
    linarith
  · intro h
    have h3 : ∑ i, (∑ j, Y i j - Y i (js i)) = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [h i]; ring)
    have : kbar - P = 0 := by rw [hd, h3]; ring
    rw [this]; ring

/-! ### Hard-prediction limit, general `k` (Remark `hard_ranking_general_k`) -/

/-- Remark ("General `k_i⁺`"), closed form: for `k` predicted positives `j 0, …, j (k-1)` (distinct)
ranked `1, …, k` (ties among them broken as in the remark) and every predicted negative ranked `k + 1`
(the min-rank convention), the raw DCG sum of an example with relevances `Y` is
`∑_l Y(j_l) w(l+1) + w(k+1) (∑ Y − ∑_l Y(j_l))`. -/
theorem dcg_ex_hardTopK_closed_form {m k : ℕ} (w : ℕ → ℝ) (j : Fin k → Fin m)
    (hj : Function.Injective j) (ρ : Fin m → ℕ) (hρ1 : ∀ l, ρ (j l) = l + 1)
    (hρ2 : ∀ x, x ∉ Set.range j → ρ x = k + 1) (Y : Fin m → ℝ) :
    ∑ x, Y x * w (ρ x)
      = ∑ l, Y (j l) * w ((l : ℕ) + 1) + w (k + 1) * (∑ x, Y x - ∑ l, Y (j l)) := by
  classical
  set S : Finset (Fin m) := Finset.univ.image j with hS
  have hmem : ∀ x, x ∈ S ↔ x ∈ Set.range j := by
    intro x; simp [hS]
  have h1 : ∑ x ∈ S, Y x * w (ρ x) = ∑ l, Y (j l) * w ((l : ℕ) + 1) := by
    rw [hS, Finset.sum_image (fun a _ b _ h => hj h)]
    exact Finset.sum_congr rfl (fun l _ => by rw [hρ1 l])
  have h1' : ∑ x ∈ S, Y x = ∑ l, Y (j l) := by
    rw [hS, Finset.sum_image (fun a _ b _ h => hj h)]
  have h2 : ∑ x ∈ Sᶜ, Y x * w (ρ x) = w (k + 1) * ∑ x ∈ Sᶜ, Y x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have : x ∉ Set.range j := fun h => (Finset.mem_compl.mp hx) ((hmem x).mpr h)
    rw [hρ2 x this]; ring
  have h3 : ∑ x ∈ Sᶜ, Y x = ∑ x, Y x - ∑ x ∈ S, Y x := by
    have := Finset.sum_compl_add_sum S Y
    linarith
  rw [← Finset.sum_compl_add_sum S (fun x => Y x * w (ρ x)), add_comm, h1, h2, h3, h1']

/-- Remark, lower bound: for nonnegative weights and relevances, the exemplar DCG is at least its
top-`k` part `∑_l Y(j_l) w(l+1)`. -/
theorem dcg_ex_hardTopK_lower_bound {m k : ℕ} (w : ℕ → ℝ) (hw : ∀ r, 0 ≤ w r) (j : Fin k → Fin m)
    (hj : Function.Injective j) (ρ : Fin m → ℕ) (hρ1 : ∀ l, ρ (j l) = l + 1)
    (hρ2 : ∀ x, x ∉ Set.range j → ρ x = k + 1) (Y : Fin m → ℝ) (hY : ∀ x, 0 ≤ Y x) :
    ∑ l, Y (j l) * w ((l : ℕ) + 1) ≤ ∑ x, Y x * w (ρ x) := by
  rw [dcg_ex_hardTopK_closed_form w j hj ρ hρ1 hρ2 Y]
  have hle : ∑ l, Y (j l) ≤ ∑ x, Y x := by
    classical
    rw [← Finset.sum_image (f := Y) (fun a _ b _ h => hj h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hY x)
  have : 0 ≤ w (k + 1) * (∑ x, Y x - ∑ l, Y (j l)) := mul_nonneg (hw _) (by linarith)
  linarith

/-- Remark, strictness: if `w(k+1) > 0` and some relevant label (`Y x > 0`) lies outside the
predicted top `k`, the exemplar DCG strictly exceeds its top-`k` part (`R_i > 0`). -/
theorem dcg_ex_hardTopK_strict {m k : ℕ} (w : ℕ → ℝ) (hwk : 0 < w (k + 1)) (j : Fin k → Fin m)
    (hj : Function.Injective j) (ρ : Fin m → ℕ) (hρ1 : ∀ l, ρ (j l) = l + 1)
    (hρ2 : ∀ x, x ∉ Set.range j → ρ x = k + 1) (Y : Fin m → ℝ) (hY : ∀ x, 0 ≤ Y x)
    (x₀ : Fin m) (hx₀ : x₀ ∉ Set.range j) (hpos : 0 < Y x₀) :
    ∑ l, Y (j l) * w ((l : ℕ) + 1) < ∑ x, Y x * w (ρ x) := by
  rw [dcg_ex_hardTopK_closed_form w j hj ρ hρ1 hρ2 Y]
  classical
  have hle : ∑ l, Y (j l) < ∑ x, Y x := by
    rw [← Finset.sum_image (f := Y) (fun a _ b _ h => hj h)]
    refine Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ x₀) ?_ hpos
      (fun x _ _ => hY x)
    intro h
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp h
    exact hx₀ ⟨l, hl⟩
  have : 0 < w (k + 1) * (∑ x, Y x - ∑ l, Y (j l)) := mul_pos hwk (by linarith)
  linarith

/-- Remark, exact reduction: for the indicator weight `w(r) = 1[r ≤ k]` (support in
`{1, …, k}`), the tail vanishes and the exemplar DCG equals the number of relevant labels among the
`k` predicted ones, that is `k · Precision@k_i` (so `DCG^ex_i = k · Precision@k_i / m` after the
`1/m` factor). -/
theorem dcg_ex_hardTopK_indicator {m k : ℕ} (j : Fin k → Fin m) (hj : Function.Injective j)
    (ρ : Fin m → ℕ) (hρ1 : ∀ l, ρ (j l) = l + 1) (hρ2 : ∀ x, x ∉ Set.range j → ρ x = k + 1)
    (Y : Fin m → ℝ) :
    ∑ x, Y x * (if ρ x ≤ k then (1 : ℝ) else 0) = ∑ l, Y (j l) := by
  have := dcg_ex_hardTopK_closed_form (fun r => if r ≤ k then (1 : ℝ) else 0) j hj ρ hρ1 hρ2 Y
  rw [this]
  have hk : ¬ (k + 1 ≤ k) := by omega
  have hl : ∀ l : Fin k, ((l : ℕ) + 1 ≤ k) := fun l => l.isLt
  simp [hk, hl]

/-! ### `auc_improper`: two units, and a five-unit counterexample -/

theorem auc_cell_two (y : Fin 2 → ℝ) (hy : ∀ k, y k = 0 ∨ y k = 1) (i i' : Fin 2) :
    y i * (1 - y i') / ((∑ k, y k) * (∑ k, (1 - y k))) = y i * (1 - y i') := by
  rcases hy 0 with h0 | h0 <;> rcases hy 1 with h1 | h1 <;>
    fin_cases i <;> fin_cases i' <;> simp [Fin.sum_univ_succ, h0, h1] <;> norm_num

theorem aucWeight_two {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → Fin 2 → ℝ)
    (hY : ∀ ω i, Y ω i = 0 ∨ Y ω i = 1) (i i' : Fin 2) :
    aucWeight P Y i i' = pairWeight P Y i i' := by
  unfold aucWeight pairWeight
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [auc_cell_two (Y ω) (hY ω) i i']

/-- Proposition ("`AUC_j` is not strictly proper"), part (ii), for *two* units and any dependence:
the denominator `n⁺ n⁻` is `1` on every discordant pair. -/
theorem expAUC_two_le_truthful {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (Y : Ω → Fin 2 → ℝ) (hY : ∀ ω i, Y ω i = 0 ∨ Y ω i = 1) (p : Fin 2 → ℝ)
    (hp : ∀ i, p i = ∑ ω, P ω * Y ω i) (hpinj : Function.Injective p) (q : Fin 2 → ℝ) :
    expAUC P Y q ≤ expAUC P Y p := by
  rw [expAUC_eq, expAUC_eq]
  refine pairSum_le_truthful _ ?_ p hpinj ?_ q
  · intro i i'
    rw [aucWeight_two P Y hY]
    exact pairWeight_nonneg P hP Y hY i i'
  · intro i i' h
    rw [aucWeight_two P Y hY, aucWeight_two P Y hY]
    have := pairWeight_sub P Y p hp i i'
    linarith

noncomputable def cex5Y : Fin 5 → Fin 5 → ℝ :=
  ![![0, 0, 0, 1, 1], ![0, 1, 1, 0, 1], ![1, 0, 1, 0, 1], ![1, 0, 1, 1, 1], ![1, 1, 0, 1, 1]]
noncomputable def cex5p : Fin 5 → ℝ := ![8/11, 5/11, 7/11, 6/11, 1]
noncomputable def cex5q : Fin 5 → ℝ := ![3, 0, 1, 2, 4]

theorem cex5_marginals : ∀ i, cex5p i = ∑ ω, cexP ω * cex5Y ω i := by
  intro i
  fin_cases i <;> simp [cex5p, cexP, cex5Y, Fin.sum_univ_succ] <;> norm_num

theorem cex5_injective : Function.Injective cex5p := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp [cex5p] at h <;> norm_num at h)

theorem cex5_expAUC_truthful : expAUC cexP cex5Y cex5p = 49 / 66 := by
  simp [expAUC, aucScore, concordantCount, sInd, Fin.sum_univ_succ, cexP, cex5Y, cex5p]
  norm_num

theorem cex5_expAUC_other : expAUC cexP cex5Y cex5q = 3 / 4 := by
  simp [expAUC, aucScore, concordantCount, sInd, Fin.sum_univ_succ, cexP, cex5Y, cex5q]
  norm_num

/-- Five units: adding to the four-unit counterexample a fifth unit that is positive with certainty
(ranked first by both reports) keeps the failure: the truthful report has expected AUC `49/66`, the
report that swaps units 3 and 4 has `3/4`. -/
theorem expAUC_dependent_counterexample_five :
    (∀ ω i, cex5Y ω i = 0 ∨ cex5Y ω i = 1) ∧ (∀ ω, 0 ≤ cexP ω) ∧ ∑ ω, cexP ω = 1 ∧
    (∀ i, cex5p i = ∑ ω, cexP ω * cex5Y ω i) ∧ Function.Injective cex5p ∧
    expAUC cexP cex5Y cex5p < expAUC cexP cex5Y cex5q := by
  refine ⟨?_, ?_, ?_, cex5_marginals, cex5_injective, ?_⟩
  · intro ω i
    fin_cases ω <;> fin_cases i <;> simp [cex5Y]
  · intro ω
    fin_cases ω <;> simp [cexP] <;> norm_num
  · simp [cexP, Fin.sum_univ_succ]
    norm_num
  · rw [cex5_expAUC_truthful, cex5_expAUC_other]
    norm_num

/-! ### The dependent counterexample for every `n ≥ 4`

Appending `k` units that are positive in every scenario, and that both reports rank above the
original four, adds `k · n⁻` concordant pairs and `k` positives in every scenario. The difference of
expected AUC between the truthful report and the report that swaps units 3 and 4 is then
`−(5k² + 4k + 3) / (66 (k+1)(k+2)(k+3)) < 0` for every `k`. The added units have equal marginals
(`1`); the paper makes all marginals distinct by perturbing them to `1 − ε_l` (continuity), which is
not formalised. -/

/-- Appending `k` certain positives scored above every original unit adds `k · n⁻` concordant
pairs. -/
theorem concordantCount_append {n k : ℕ} (q Y : Fin n → ℝ) (r : Fin k → ℝ)
    (hqr : ∀ a b, q a < r b) :
    concordantCount (Fin.append q r) (Fin.append Y (fun _ => (1 : ℝ)))
      = concordantCount q Y + k * ∑ i, (1 - Y i) := by
  unfold concordantCount sInd
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, hqr, if_true, sub_self,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, one_mul, mul_one]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sum_append_one {n k : ℕ} (Y : Fin n → ℝ) :
    ∑ i, Fin.append Y (fun _ : Fin k => (1 : ℝ)) i = ∑ i, Y i + k := by
  simp [Fin.sum_univ_add]

theorem sum_one_sub_append_one {n k : ℕ} (Y : Fin n → ℝ) :
    ∑ i, (1 - Fin.append Y (fun _ : Fin k => (1 : ℝ)) i) = ∑ i, (1 - Y i) := by
  simp [Fin.sum_univ_add]

theorem aucScore_append {n k : ℕ} (q Y : Fin n → ℝ) (r : Fin k → ℝ) (hqr : ∀ a b, q a < r b) :
    aucScore (Fin.append q r) (Fin.append Y (fun _ => (1 : ℝ)))
      = (concordantCount q Y + k * ∑ i, (1 - Y i)) / ((∑ i, Y i + k) * ∑ i, (1 - Y i)) := by
  unfold aucScore
  rw [concordantCount_append q Y r hqr, sum_append_one, sum_one_sub_append_one]

/-- Label scenarios of the four-unit counterexample with `k` added certain positives. -/
noncomputable def cexkY (k : ℕ) : Fin 5 → Fin (4 + k) → ℝ :=
  fun ω => Fin.append (cexY ω) (fun _ => 1)
/-- Truthful report (the marginals): the added units have marginal `1`. -/
noncomputable def cexkp (k : ℕ) : Fin (4 + k) → ℝ := Fin.append cexp (fun _ => 1)
/-- The report that swaps units 3 and 4 of the truthful ranking; added units on top. -/
noncomputable def cexkq (k : ℕ) : Fin (4 + k) → ℝ := Fin.append cexq (fun _ => 4)

theorem cexk_marginals (k : ℕ) : ∀ i, cexkp k i = ∑ ω, cexP ω * cexkY k ω i := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [cexkp, cexkY, Fin.append_left]
    exact cex_marginals a
  · simp only [cexkp, cexkY, Fin.append_right, mul_one]
    simp [cexP, Fin.sum_univ_succ]
    norm_num

theorem cexk_expAUC_truthful (k : ℕ) :
    expAUC cexP (cexkY k) (cexkp k)
      = ∑ ω, cexP ω * ((concordantCount cexp (cexY ω) + k * ∑ i, (1 - cexY ω i))
          / ((∑ i, cexY ω i + k) * ∑ i, (1 - cexY ω i))) := by
  unfold expAUC
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [cexkp, cexkY, aucScore_append cexp (cexY ω) _ (fun a _ => by
    fin_cases a <;> simp [cexp] <;> norm_num)]

theorem cexk_expAUC_other (k : ℕ) :
    expAUC cexP (cexkY k) (cexkq k)
      = ∑ ω, cexP ω * ((concordantCount cexq (cexY ω) + k * ∑ i, (1 - cexY ω i))
          / ((∑ i, cexY ω i + k) * ∑ i, (1 - cexY ω i))) := by
  unfold expAUC
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [cexkq, cexkY, aucScore_append cexq (cexY ω) _ (fun a _ => by
    fin_cases a <;> simp [cexq] <;> norm_num)]

/-- Exact difference of expected AUC, truthful minus alternative, with `k` added units. -/
theorem cexk_expAUC_diff (k : ℕ) :
    expAUC cexP (cexkY k) (cexkp k) - expAUC cexP (cexkY k) (cexkq k)
      = -(5 * (k : ℝ) ^ 2 + 4 * k + 3) / (66 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3)) := by
  rw [cexk_expAUC_truthful, cexk_expAUC_other]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  simp [Fin.sum_univ_succ, cexP, cexY, cexp, cexq, concordantCount, sInd]
  norm_num
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (k : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

/-- Proposition ("AUC is non-strict; truthful ranking may fail under dependence"), part (d), for
every number of units `n = 4 + k ≥ 4`: the truthful report has strictly smaller expected AUC than
the report that swaps units 3 and 4. The original four marginals are distinct; the added units
have marginal `1`. -/
theorem expAUC_dependent_counterexample_all (k : ℕ) :
    (∀ ω i, cexkY k ω i = 0 ∨ cexkY k ω i = 1) ∧
    (∀ i, cexkp k i = ∑ ω, cexP ω * cexkY k ω i) ∧
    expAUC cexP (cexkY k) (cexkp k) < expAUC cexP (cexkY k) (cexkq k) := by
  refine ⟨fun ω i => ?_, cexk_marginals k, ?_⟩
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [cexkY, Fin.append_left]
      fin_cases ω <;> fin_cases a <;> simp [cexY]
    · simp [cexkY]
  · have hd := cexk_expAUC_diff k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hneg : -(5 * (k : ℝ) ^ 2 + 4 * k + 3)
        / (66 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3)) < 0 := by
      apply div_neg_of_neg_of_pos
      · nlinarith
      · positivity
    linarith

end Aggmetrics.Ranking

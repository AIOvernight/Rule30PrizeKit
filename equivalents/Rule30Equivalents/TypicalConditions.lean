import Rule30Equivalents.Typicality
import Rule30Equivalents.Fluctuations
import Rule30Equivalents.EmpiricalMeasures
import Rule30Equivalents.PresburgerExpansion
import Rule30Equivalents.LempelZiv
import Rule30Equivalents.Christol
import Rule30Equivalents.RegularSequences
import Rule30Equivalents.PisotNumbers
import Rule30Equivalents.SkolemMahlerLech
import Mathlib.Data.Finsupp.Encodable

/-!
# The other sufficient conditions hold almost surely

Besides the stronger statements of `StrongerStatements` (`Typicality`), Problem 1 follows from
sufficient conditions proved in other files. Most of them hold for almost every configuration, with
the seed replaced by the configuration (`ae_sufficientConditions_trace`); in particular none of
those is vacuous.

* **Countably many exceptions.** `k`-automatic sequences are countably many
  (`Automatic.countable_setOf_isAutomatic`), so almost every center column is not `k`-automatic for
  any `k ≥ 2`, not `k`-regular over any field (`ae_not_isRegularSeq_trace`), and its generating
  function is transcendental over `𝔽_p(X)` for every prime `p` (Christol's theorem,
  `ae_transcendental_series_trace`). In a real base `β > 2` the value is one-to-one
  (`BinaryIrrational.value_injective`) and `ℚ(β)` is countable (`countable_adjoin`), so
  `x_β ∉ ℚ(β)` almost surely (`ae_value_not_mem_adjoin_trace`).
* **Automatic complexity.** A word with automatic complexity at most `K` is the only word of its
  length accepted by one of the finitely many automata with `K` states, so the prefix of length `n`
  has automatic complexity at most `K` with probability at most `D_K 2^-n`
  (`measure_autComplexityLE_le`), and the automatic complexity of the prefixes tends to infinity
  almost surely (`ae_autComplexity_tendsto`).
* **Densities and discrepancies.** Every arithmetic progression of the column has density `1/2`
  (`ae_density_progressions_trace`: its cells have distinct feet), the remainder `N(n) - α n` is
  unbounded for every `α` (`ae_unbounded_remainder_trace`: the density is `1/2`, and for `α = 1/2`
  the discrepancy oscillates), and so is the remainder `N_w(n) - α n` of every word `w`
  (`unbounded_word_remainder_of_isNormal`: for `α = 2^-|w|` the block `w^L` raises it by a multiple
  of `L`). The empirical measures converge to the fair-coin measure, which has no atoms.
* **Zero sets.** The black times are not the zero set of a linear recurrence sequence over `ℚ` (the
  Skolem–Mahler–Lech theorem) or over a finite field (`ae_not_zero_set_rat_trace`,
  `ae_not_zero_set_finite_trace`).
* **Words.** For every disjunctive sequence, multiplication is definable in `(ℕ, +, S)`
  (`PresburgerExpansion.mul_definable_of_disjunctive`), and the unbordered words `1 0^L` occur
  arbitrarily late (`not_bordered_one_zeros`). For every sequence that is not eventually periodic,
  the Lempel–Ziv complexity is unbounded, and infinitely many prefixes end with no repetition of
  exponent `φ²` (the Mignosi–Restivo–Salemi theorem).
-/

namespace Rule30Equivalents.TypicalConditions

open MeasureTheory Filter Topology Ruliology.CellularAutomata Rule30Realization Genericity
  RandomConfigurations Typicality
open scoped LaurentSeries RatFunc

/-- A countable set of sequences is avoided almost surely. -/
theorem ae_notMem_of_countable {s : Set (ℕ → Bool)} (hs : s.Countable) :
    ∀ᵐ v ∂(coins ℕ), v ∉ s :=
  measure_eq_zero_iff_ae_notMem.1 (hs.measure_zero _)

/-! ### Automatic sequences -/

/-- Almost every fair-coin sequence is not `k`-automatic for any `k ≥ 2`. -/
theorem ae_not_isAutomatic : ∀ᵐ v ∂(coins ℕ), ∀ k, 2 ≤ k → ¬ Automatic.IsAutomatic k v :=
  ae_all_iff.2 fun k => by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · exact Eventually.of_forall fun _ h => absurd h (by omega)
    · exact (ae_notMem_of_countable (Automatic.countable_setOf_isAutomatic hk)).mono
        fun _ h _ => h

theorem ae_not_isAutomatic_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ k, 2 ≤ k → ¬ Automatic.IsAutomatic k (trace x) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_not_isAutomatic

/-- For almost every configuration the center column is not `k`-regular over `K`, for any
`k ≥ 2`. -/
theorem ae_not_isRegularSeq_trace (K : Type*) [Field K] :
    ∀ᵐ x ∂(coins ℤ), ∀ k, 2 ≤ k → ¬ RegularSequences.IsRegularSeq K k (trace x) :=
  ae_not_isAutomatic_trace.mono fun x hx k hk h =>
    hx k hk ((RegularSequences.isRegularSeq_iff_isAutomatic k (trace x)).1 h)

/-- **For almost every configuration the generating function of the center column is
transcendental over `𝔽_p(X)` for every prime `p`** (Christol's theorem). -/
theorem ae_transcendental_series_trace : ∀ᵐ x ∂(coins ℤ), ∀ (p : ℕ) [Fact p.Prime],
    Transcendental (RatFunc (ZMod p))
      ((LinearRelations.series (ZMod p) (trace x) : PowerSeries (ZMod p)) : (ZMod p)⸨X⸩) :=
  ae_not_isAutomatic_trace.mono fun x hx p hp halg =>
    hx p hp.out.two_le ((Christol.isAutomatic_iff_isAlgebraic (trace x)).2 halg)

/-! ### Automatic complexity -/

instance (K : ℕ) : Finite (DFA Bool (Fin K)) := by
  refine Finite.of_injective (fun M : DFA Bool (Fin K) => (M.step, M.start, M.accept)) ?_
  rintro ⟨s₁, a₁, f₁⟩ ⟨s₂, a₂, f₂⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- **Low automatic complexity is rare**: the prefix of length `n` has automatic complexity at most
`K` with probability at most `D_K 2^-n`, with `D_K` the number of automata with `K` states. -/
theorem measure_autComplexityLE_le (K n : ℕ) :
    coins ℕ {v | Automatic.AutComplexityLE ((List.range n).map v) K} ≤
      Nat.card (DFA Bool (Fin K)) * 2⁻¹ ^ n := by
  classical
  haveI := Fintype.ofFinite (DFA Bool (Fin K))
  -- one automaton accepts at most one prefix
  have hone : ∀ M : DFA Bool (Fin K),
      coins ℕ {v | Automatic.UniquelyAccepts M ((List.range n).map v)} ≤ 2⁻¹ ^ n := by
    intro M
    by_cases hne : {v | Automatic.UniquelyAccepts M ((List.range n).map v)}.Nonempty
    · obtain ⟨w, hw⟩ := hne
      calc coins ℕ {v | Automatic.UniquelyAccepts M ((List.range n).map v)}
          ≤ coins ℕ {v | ∀ j < n, v (0 + j) = w j} := measure_mono fun v hv => by
            have heq := hw.2 ((List.range n).map v) (by simp) hv.1
            intro j hj
            have := congrArg (fun l => l[j]?) heq
            simpa [List.getElem?_map, List.getElem?_range hj] using this
        _ = 2⁻¹ ^ n := measure_triangular (ι := ℕ) (fun j v => v (0 + j))
            (fun _ => measurable_pi_apply _) (fun j => 0 + j) (fun j v => by simp)
            (fun j v j' hj' => by dsimp only; rw [Function.update_of_ne (by omega)]) w n
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
      exact zero_le
  calc coins ℕ {v | Automatic.AutComplexityLE ((List.range n).map v) K}
      ≤ ∑ M : DFA Bool (Fin K), coins ℕ {v | Automatic.UniquelyAccepts M ((List.range n).map v)} :=
        (measure_mono fun v hv => by
          obtain ⟨M, hM⟩ := hv
          exact Set.mem_iUnion.2 ⟨M, hM⟩).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _M : DFA Bool (Fin K), (2⁻¹ : ENNReal) ^ n := Finset.sum_le_sum fun M _ => hone M
    _ = Nat.card (DFA Bool (Fin K)) * 2⁻¹ ^ n := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- **The automatic complexity of the prefixes of almost every fair-coin sequence tends to
infinity** (Borel–Cantelli). -/
theorem ae_autComplexity_tendsto : ∀ᵐ v ∂(coins ℕ), ∀ K : ℕ,
    ∀ᶠ n in atTop, ¬ Automatic.AutComplexityLE ((List.range n).map v) K := by
  refine ae_all_iff.2 fun K => ?_
  have hsum : ∑' n, coins ℕ {v | Automatic.AutComplexityLE ((List.range n).map v) K} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => measure_autComplexityLE_le K n)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofNat_ne_top
  exact (ae_eventually_notMem hsum).mono fun v hv => hv

/-! ### Densities and discrepancies -/

/-- **For almost every configuration every arithmetic progression `k ↦ c(r + kP)` of the center
column has density `1/2`**: its cells `(r + kP, 0)` have distinct feet, so they are fair coins. -/
theorem ae_density_progressions_trace : ∀ᵐ x ∂(coins ℤ), ∀ P r : ℕ, 0 < P →
    Tendsto (fun n : ℕ =>
      (((Finset.range n).filter fun k => trace x (r + k * P) = true).card : ℝ) / n) atTop
        (𝓝 (1 / 2)) := by
  refine ae_all_iff.2 fun P => ae_all_iff.2 fun r => ?_
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · exact Eventually.of_forall fun _ h => absurd h (lt_irrefl 0)
  have hinj : Function.Injective fun k : ℕ => Mixing.foot ((r + k * P, 0) : ℕ × ℤ) := by
    intro k l h
    simp only [Mixing.foot] at h
    have h' : (k : ℤ) * P = l * P := by push_cast at h; linarith
    exact_mod_cast mul_right_cancel₀ (by exact_mod_cast hP.ne' : (P : ℤ) ≠ 0) h'
  filter_upwards [(Mixing.measurePreserving_cells hinj).quasiMeasurePreserving.ae ae_isNormal]
    with x hx _
  simpa [Fin.forall_fin_one, one_div] using hx 1 fun _ => true

/-- The density of black cells of a normal sequence is `1/2`. -/
theorem tendsto_ones_div {b : ℕ → Bool} (hb : StrongerStatements.IsNormal b) :
    Tendsto (fun n : ℕ => (BoundedRemainder.ones b n : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  have h1 := hb 1 fun _ => true
  simp only [Fin.forall_fin_one, Fin.val_zero, add_zero, pow_one] at h1
  rw [one_div]
  refine h1.congr fun n => ?_
  simp [BoundedRemainder.ones, Nat.count_eq_card_filter_range]

/-- If `f n / n → β` and `α ≠ β`, then `f n - α n` is unbounded. -/
theorem exists_lt_abs_sub_of_tendsto {f : ℕ → ℝ} {β : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / n) atTop (𝓝 β)) {α : ℝ} (hα : α ≠ β) (C : ℝ) :
    ∃ n, C < |f n - α * n| := by
  -- `|f n / n - α| > δ` once `f n / n` is within `δ = |β - α|/2` of `β`
  set δ := |β - α| / 2 with hδ
  have hδpos : 0 < δ := by
    have : 0 < |β - α| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hα))
    positivity
  obtain ⟨n, hn1, hn2⟩ := ((hf.eventually (Metric.ball_mem_nhds _ hδpos)).and
    (eventually_gt_atTop ⌈C / δ⌉₊)).exists
  refine ⟨n, ?_⟩
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn2
    exact_mod_cast this
  rw [Real.dist_eq] at hn1
  have hfar : δ < |f n / n - α| := by
    have := abs_sub_abs_le_abs_sub (β - α) (f n / n - α)
    rw [show β - α - (f n / n - α) = -(f n / n - β) by ring, abs_neg] at this
    linarith
  have heq : |f n - α * n| = n * |f n / n - α| := by
    rw [← abs_of_pos hnpos, ← abs_mul, abs_of_pos hnpos, mul_sub, mul_div_cancel₀ _ hnpos.ne',
      mul_comm (n : ℝ) α]
  have hCn : C < δ * n := by
    have h1 : C / δ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn2)
    rwa [div_lt_iff₀ hδpos, mul_comm] at h1
  rw [heq]
  nlinarith

/-- **For almost every configuration the remainder `N(n) - α n` is unbounded for every `α`**: the
density is `1/2`, and for `α = 1/2` the discrepancy oscillates beyond every bound. -/
theorem ae_unbounded_remainder_trace : ∀ᵐ x ∂(coins ℤ), ∀ α C : ℝ, ∃ n,
    C < |(BoundedRemainder.ones (trace x) n : ℝ) - α * n| := by
  filter_upwards [ae_isNormal_trace, Fluctuations.ae_oscillating_discrepancy_trace]
    with x hn hosc α C
  rcases eq_or_ne α (1 / 2) with rfl | hα
  · obtain ⟨n, hn'⟩ := hosc.1 C
    refine ⟨n, hn'.trans_le ?_⟩
    rw [mul_comm, mul_one_div]
    exact le_abs_self _
  exact exists_lt_abs_sub_of_tendsto (tendsto_ones_div hn) hα C

/-- **Word remainders of a normal sequence are unbounded**: for a word `w` of length `m ≥ 1` and
every `α`, `N_w(n) - α n` is unbounded. For `α ≠ 2^-m` the frequency of `w` is `2^-m`. For
`α = 2^-m`, the block `w^L` holds `L` occurrences of `w` within `m L` cells, so it raises the
remainder by at least `L (1 - m 2^-m)`, and `m < 2^m`. -/
theorem unbounded_word_remainder_of_isNormal {b : ℕ → Bool} (hb : StrongerStatements.IsNormal b)
    {m : ℕ} (hm : 0 < m) (w : Fin m → Bool) (α C : ℝ) : ∃ n, C <
      |(BoundedRemainder.ones (fun i => decide (∀ j : Fin m, b (i + j) = w j)) n : ℝ) - α * n| := by
  set I : ℕ → Bool := fun i => decide (∀ j : Fin m, b (i + j) = w j) with hI
  have hfreq : Tendsto (fun n : ℕ => (BoundedRemainder.ones I n : ℝ) / n) atTop
      (𝓝 ((2 : ℝ)⁻¹ ^ m)) := by
    refine (hb m w).congr fun n => ?_
    simp [BoundedRemainder.ones, Nat.count_eq_card_filter_range, hI]
  rcases ne_or_eq α ((2 : ℝ)⁻¹ ^ m) with hα | rfl
  · exact exists_lt_abs_sub_of_tendsto hfreq hα C
  by_contra hbound
  push Not at hbound
  -- the block `w^L` with `L δ > 2C`, `δ = 1 - m 2^-m`
  set δ : ℝ := 1 - m * (2 : ℝ)⁻¹ ^ m with hδ
  have hδpos : 0 < δ := by
    have h1 : (m : ℝ) < 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (m : ℝ) * (2 : ℝ)⁻¹ ^ m < 1 := by
      rw [inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)]
      exact h1
    linarith
  set L : ℕ := ⌈2 * C / δ⌉₊ + 1 with hL
  have hLδ : 2 * C < L * δ := by
    have h1 : 2 * C / δ < L := by
      rw [hL]
      push_cast
      linarith [Nat.le_ceil (2 * C / δ)]
    rwa [div_lt_iff₀ hδpos] at h1
  obtain ⟨s, hs⟩ := StrongerStatements.disjunctive_of_isNormal hb (m * L)
    fun k : Fin (m * L) => w ⟨k % m, Nat.mod_lt _ hm⟩
  -- the occurrences of `w` at `s + l m`, `l < L`
  have hocc : ∀ l < L, I (s + l * m) = true := fun l hl => by
    simp only [hI, decide_eq_true_eq]
    intro j
    have hk : l * m + (j : ℕ) < m * L := by
      have := j.isLt
      have : (l + 1) * m ≤ L * m := Nat.mul_le_mul_right m hl
      nlinarith
    have h := hs ⟨l * m + j, hk⟩
    have hj : (⟨(l * m + (j : ℕ)) % m, Nat.mod_lt _ hm⟩ : Fin m) = j := by
      ext
      simp only
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
    calc b (s + l * m + j) = b (s + (l * m + j)) := by rw [add_assoc]
      _ = w ⟨(l * m + (j : ℕ)) % m, Nat.mod_lt _ hm⟩ := h
      _ = w j := by rw [hj]
  have hcount : L ≤ BoundedRemainder.ones (fun k => I (s + k)) (m * L) := by
    rw [BoundedRemainder.ones, Nat.count_eq_card_filter_range]
    calc L = ((Finset.range L).image (· * m)).card := by
          rw [Finset.card_image_of_injective _ fun a b h => Nat.eq_of_mul_eq_mul_right hm h,
            Finset.card_range]
      _ ≤ _ := Finset.card_le_card fun k hk => by
          obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hk
          rw [Finset.mem_range] at hl
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨?_, hocc l hl⟩
          have : (l + 1) * m ≤ L * m := Nat.mul_le_mul_right m hl
          nlinarith
  have hsplit := BoundedRemainder.ones_add I s (m * L)
  have h1 := abs_le.1 (hbound s)
  have h2 := abs_le.1 (hbound (s + m * L))
  have hcount' : (L : ℝ) ≤ BoundedRemainder.ones (fun k => I (s + k)) (m * L) := by
    exact_mod_cast hcount
  have hsplit' : (BoundedRemainder.ones I (s + m * L) : ℝ) =
      BoundedRemainder.ones I s + BoundedRemainder.ones (fun k => I (s + k)) (m * L) := by
    exact_mod_cast hsplit
  push_cast at h2
  rw [hδ] at hLδ
  nlinarith

/-- For almost every configuration, every word remainder `N_w(n) - α n` of the center column is
unbounded. -/
theorem ae_unbounded_word_remainder_trace : ∀ᵐ x ∂(coins ℤ), ∀ (m : ℕ), 0 < m →
    ∀ (w : Fin m → Bool) (α C : ℝ), ∃ n, C < |(BoundedRemainder.ones
      (fun i => decide (∀ j : Fin m, trace x (i + j) = w j)) n : ℝ) - α * n| :=
  ae_isNormal_trace.mono fun _ hx _ hm w α C => unbounded_word_remainder_of_isNormal hx hm w α C

/-- For almost every configuration the empirical measures of the center column have a cluster
point without atoms, the fair-coin measure. -/
theorem ae_nonatomic_mapClusterPt_trace : ∀ᵐ x ∂(coins ℤ), ∃ ν : ProbabilityMeasure (ℕ → Bool),
    MapClusterPt ν atTop (EmpiricalMeasures.empirical (trace x)) ∧
      ∀ y, (ν : Measure (ℕ → Bool)) {y} = 0 :=
  EmpiricalMeasures.ae_tendsto_empirical_trace.mono fun _ hx =>
    ⟨coinsPM ℕ, hx.mapClusterPt, fun y => coins_singleton y⟩

/-! ### Words -/

/-- For almost every configuration, multiplication is definable in `(ℕ, 0, 1, +, S)` with `S` the
black times of the center column. -/
theorem ae_mul_definable_trace : ∀ᵐ x ∂(coins ℤ),
    PresburgerExpansion.SDef {t | trace x t = true} {v : Fin 3 → ℕ | v 0 = v 1 * v 2} :=
  ae_disjunctive_trace.mono fun x hx => PresburgerExpansion.mul_definable_of_disjunctive
    fun n w => by
      obtain ⟨i, hi⟩ := hx n w
      exact ⟨i, fun j => by rw [Set.mem_setOf_eq, hi j]⟩

/-- The word `1 0^L` is unbordered: its nonempty prefixes start with `1`, its proper suffixes with
`0`. -/
theorem not_bordered_one_zeros (L : ℕ) : ¬ Lyndon.Bordered (true :: List.replicate L false) := by
  rintro ⟨k, hk0, hkL, heq⟩
  simp only [List.length_cons, List.length_replicate] at hkL
  have h0 := congrArg (fun l => l[0]?) heq
  obtain ⟨m, hm⟩ : ∃ m, L + 1 - k = m + 1 := ⟨L - k, by omega⟩
  simp only [List.length_cons, List.length_replicate, hm, List.drop_succ_cons,
    List.getElem?_drop, add_zero, List.getElem?_take, if_pos hk0, List.getElem?_cons_zero,
    List.getElem?_replicate] at h0
  split_ifs at h0 with h
  simp at h0

/-- **Long unbordered factors occur arbitrarily late in a disjunctive sequence.** -/
theorem late_long_unbordered_of_disjunctive {b : ℕ → Bool} (hb : Disjunctive b) (n L : ℕ) :
    ∃ i ℓ : ℕ, n ≤ i ∧ L ≤ ℓ ∧
      ¬ Lyndon.Bordered ((List.range ℓ).map fun j => b (i + j)) := by
  obtain ⟨i, hi, hw⟩ := Mixing.exists_ge_of_disjunctive hb
    (fun j : Fin (L + 1) => decide ((j : ℕ) = 0)) n
  refine ⟨i, L + 1, hi, by omega, ?_⟩
  have heq : (List.range (L + 1)).map (fun j => b (i + j)) = true :: List.replicate L false := by
    refine List.ext_getElem (by simp) fun j h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    have := hw ⟨j, by simpa using h1⟩
    simp only at this
    rw [this]
    rcases j with _ | j
    · simp
    · simp
  rw [heq]
  exact not_bordered_one_zeros L

/-- For almost every configuration the Lempel–Ziv complexity of the prefixes of the center column
is unbounded. -/
theorem ae_lz_unbounded_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ K, ∃ n, K < WordForms.lzComplexity (trace x) n :=
  ae_not_eventuallyPeriodic_trace.mono fun x hx K => by
    by_contra h
    push Not at h
    exact hx ((LempelZiv.eventuallyPeriodic_iff_lz_bounded (trace x)).2 ⟨K, h⟩)

/-- For almost every configuration infinitely many prefixes of the center column end with no
repetition of exponent `φ²` (the Mignosi–Restivo–Salemi theorem). -/
theorem ae_golden_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ N, ∃ n, N ≤ n ∧ ¬ WordForms.EndsWithGoldenPower (trace x) n :=
  ae_not_eventuallyPeriodic_trace.mono fun x hx N => by
    by_contra hall
    push Not at hall
    exact hx (GoldenPowers.eventuallyPeriodic_of_gp fun n hn =>
      WordForms.gp_of_endsWithGoldenPower (hall n hn))

/-- For almost every configuration the black times of the center column are not the zero set of a
linear recurrence sequence over `ℚ` (the Skolem–Mahler–Lech theorem makes such zero sets eventually
periodic). -/
theorem ae_not_zero_set_rat_trace : ∀ᵐ x ∂(coins ℤ), ∀ (E : LinearRecurrence ℚ) (u : ℕ → ℚ),
    E.IsSolution u → {t | u t = 0} ≠ {t | trace x t = true} :=
  ae_not_eventuallyPeriodic_trace.mono fun x hx E u hu hS => hx (by
    obtain ⟨T, P, hP, hTP⟩ := SkolemMahlerLech.skolem_mahler_lech E hu
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have := hTP t ht
    rw [hS] at this
    simp only [Set.mem_setOf_eq] at this
    cases h1 : trace x (t + P) <;> cases h2 : trace x t <;> simp_all)

/-- The same over every finite field. -/
theorem ae_not_zero_set_finite_trace (K : Type*) [Field K] [Finite K] :
    ∀ᵐ x ∂(coins ℤ), ∀ (E : LinearRecurrence K) (u : ℕ → K),
      E.IsSolution u → {t | u t = 0} ≠ {t | trace x t = true} :=
  ae_not_eventuallyPeriodic_trace.mono fun _ hx _ _ hu hS =>
    hx (LinearRelations.eventuallyPeriodic_of_zero_set hu hS)

/-! ### Values in a real base -/

/-- `ℚ(β)` is countable: its elements are quotients of polynomials in `β`. -/
theorem countable_adjoin (β : ℝ) :
    ((IntermediateField.adjoin ℚ ({β} : Set ℝ) : IntermediateField ℚ ℝ) : Set ℝ).Countable := by
  haveI : Countable (AddMonoidAlgebra ℚ ℕ) := inferInstanceAs (Countable (ℕ →₀ ℚ))
  haveI : Countable (Polynomial ℚ) := Polynomial.toFinsupp_injective.countable
  refine (Set.countable_range fun q : Polynomial ℚ × Polynomial ℚ =>
    Polynomial.aeval β q.1 / Polynomial.aeval β q.2).mono fun y hy => ?_
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ y).1 hy
  exact ⟨(r, s), rfl⟩

/-- **For `β > 2`, almost every configuration has `x_β ∉ ℚ(β)`**: the value is one-to-one and
`ℚ(β)` is countable. -/
theorem ae_value_not_mem_adjoin_trace {β : ℝ} (hβ : 2 < β) :
    ∀ᵐ x ∂(coins ℤ),
      BinaryIrrational.value β (trace x) ∉ IntermediateField.adjoin ℚ ({β} : Set ℝ) := by
  have hcount : {v : ℕ → Bool |
      BinaryIrrational.value β v ∈ IntermediateField.adjoin ℚ ({β} : Set ℝ)}.Countable :=
    Set.MapsTo.countable_of_injOn (f := BinaryIrrational.value β) (fun _ hv => hv)
      (BinaryIrrational.value_injective hβ).injOn (countable_adjoin β)
  exact measurePreserving_trace.quasiMeasurePreserving.ae (ae_notMem_of_countable hcount)

/-! ### The sufficient conditions, almost surely -/

/-- **The other sufficient conditions hold for almost every configuration.** For almost every
configuration `x`, the center column `trace x` satisfies, with `c` replaced by `trace x`, the
hypotheses of `BoundedRemainder.problem1_of_unbounded_remainder`,
`problem1_of_unbounded_word_remainder` (every word of length `m ≥ 1`),
`problem1_of_problem2_of_unbounded_discrepancy` (density `1/2` and an unbounded discrepancy),
`problem1_of_oscillating_discrepancy`, `problem1_of_unpredictable_half`,
`EmpiricalMeasures.problem1_of_nonatomic_mapClusterPt`, `Automatic.problem1_of_not_automatic`,
`problem1_of_not_two_three_automatic`, `problem1_of_automaticComplexity_tendsto_top`,
`PresburgerExpansion.problem1_of_mul_definable`, `ProblemTwo.problem1_of_density_on_progressions`,
`Transcendence.problem1_of_transcendental_F2_or_F3`,
`WordForms.problem1_of_infinitely_many_prefixes_without_golden_power`,
`problem1_of_late_long_unbordered_factors`, `problem1_of_lz_unbounded` and
`LinearRelations.problem1_of_not_zero_set` over `ℚ`. -/
theorem ae_sufficientConditions_trace : ∀ᵐ x ∂(coins ℤ),
    (∀ α C : ℝ, ∃ n, C < |(BoundedRemainder.ones (trace x) n : ℝ) - α * n|) ∧
    (∀ (m : ℕ), 0 < m → ∀ (w : Fin m → Bool) (α C : ℝ), ∃ n, C < |(BoundedRemainder.ones
      (fun i => decide (∀ j : Fin m, trace x (i + j) = w j)) n : ℝ) - α * n|) ∧
    Symmetry.HalfDensity (trace x) ∧
    ((∀ C : ℝ, ∃ n, C < (BoundedRemainder.ones (trace x) n : ℝ) - n / 2) ∧
      ∀ C : ℝ, ∃ n, (BoundedRemainder.ones (trace x) n : ℝ) - n / 2 < -C) ∧
    (∀ (σ : Type) [Finite σ] (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool),
      BoundedRemainder.PredictsAtHalf (trace x) σ s₀ δ g) ∧
    (∃ ν : ProbabilityMeasure (ℕ → Bool), MapClusterPt ν atTop
      (EmpiricalMeasures.empirical (trace x)) ∧ ∀ y, (ν : Measure (ℕ → Bool)) {y} = 0) ∧
    (∀ k, 2 ≤ k → ¬ Automatic.IsAutomatic k (trace x)) ∧
    (∀ K : ℕ, ∀ᶠ n in atTop, ¬ Automatic.AutComplexityLE ((List.range n).map (trace x)) K) ∧
    PresburgerExpansion.SDef {t | trace x t = true} {v : Fin 3 → ℕ | v 0 = v 1 * v 2} ∧
    (∀ P r : ℕ, 0 < P → Tendsto (fun n : ℕ =>
      (((Finset.range n).filter fun k => trace x (r + k * P) = true).card : ℝ) / n) atTop
        (𝓝 (1 / 2))) ∧
    (∀ (p : ℕ) [Fact p.Prime], Transcendental (RatFunc (ZMod p))
      ((LinearRelations.series (ZMod p) (trace x) : PowerSeries (ZMod p)) : (ZMod p)⸨X⸩)) ∧
    (∀ N, ∃ n, N ≤ n ∧ ¬ WordForms.EndsWithGoldenPower (trace x) n) ∧
    (∀ n L : ℕ, ∃ i ℓ : ℕ, n ≤ i ∧ L ≤ ℓ ∧
      ¬ Lyndon.Bordered ((List.range ℓ).map fun j => trace x (i + j))) ∧
    (∀ K, ∃ n, K < WordForms.lzComplexity (trace x) n) ∧
    (∀ (E : LinearRecurrence ℚ) (u : ℕ → ℚ), E.IsSolution u →
      {t | u t = 0} ≠ {t | trace x t = true}) := by
  filter_upwards [ae_unbounded_remainder_trace, ae_unbounded_word_remainder_trace,
    ae_halfDensity_trace,
    Fluctuations.ae_oscillating_discrepancy_trace, BoundedRemainder.ae_predictsAtHalf_trace,
    ae_nonatomic_mapClusterPt_trace, ae_not_isAutomatic_trace,
    measurePreserving_trace.quasiMeasurePreserving.ae ae_autComplexity_tendsto,
    ae_mul_definable_trace, ae_density_progressions_trace, ae_transcendental_series_trace,
    ae_golden_trace, ae_disjunctive_trace, ae_lz_unbounded_trace, ae_not_zero_set_rat_trace]
    with x h1 hw h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hd h13 hz
  exact ⟨h1, hw, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    late_long_unbordered_of_disjunctive hd, h13, hz⟩

end Rule30Equivalents.TypicalConditions

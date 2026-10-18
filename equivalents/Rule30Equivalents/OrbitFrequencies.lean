import Rule30Equivalents.Mixing

/-!
# Pattern frequencies along rule 30 orbits

Catalog Section 7, item 11, continued: a pointwise ergodic theorem for rule 30 and local
patterns, proved from independence alone. Mathlib has no pointwise ergodic theorem, but it has
Etemadi's strong law of large numbers, which needs only pairwise independence.

* `indepFun_indicator`, `map_indicator_eq`: indicators of independent events are independent
  random variables, and indicators of events of equal probability have the same law.
* `measure_inter_window_time`: the window `I` of row `s` and of row `t` are independent when some
  `m` separates them, `m ≤ i - s` and `i - t < m` on `I` (independence beyond the light cone,
  `Mixing.measure_inter_window`).
* `ae_tendsto_residue`: along a residue class `r + kg` of times with `g` larger than the width of
  `I`, these events are pairwise independent with probability `2^-|I|`, so the strong law applies.
* `ae_orbit_frequency`: averaging the residue classes
  (`RandomConfigurations.tendsto_average_of_residues`), **for almost every configuration, every
  pattern on every window `[-n, n]` appears in the rows of the space-time diagram with frequency
  `2^-(2n+1)`.**
-/

namespace Rule30Equivalents.OrbitFrequencies

open MeasureTheory ProbabilityTheory Filter Topology Finset Ruliology.CellularAutomata
  Rule30Realization Genericity RandomConfigurations Mixing

/-- Indicators of two independent events are independent random variables. -/
theorem indepFun_indicator {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E F : Set Ω} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (h : μ (E ∩ F) = μ E * μ F) :
    IndepFun (E.indicator (1 : Ω → ℝ)) (F.indicator (1 : Ω → ℝ)) μ := by
  have hind := (IndepSet_iff_Indep E F μ).1 ((indepSet_iff_measure_inter_eq_mul hE hF μ).2 h)
  have hle : ∀ G : Set Ω, MeasurableSpace.comap (G.indicator (1 : Ω → ℝ)) inferInstance ≤
      MeasurableSpace.generateFrom {G} := fun G => by
    letI : MeasurableSpace Ω := MeasurableSpace.generateFrom {G}
    exact Measurable.comap_le (measurable_one.indicator
      (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton G)))
  rw [IndepFun_iff_Indep]
  exact (indep_of_indep_of_le_left (indep_of_indep_of_le_left hind (hle E)).symm (hle F)).symm

/-- Indicators of events of equal probability have the same law. -/
theorem map_indicator_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E F : Set Ω} (hE : MeasurableSet E) (hF : MeasurableSet F) (h : μ E = μ F) :
    μ.map (E.indicator (1 : Ω → ℝ)) = μ.map (F.indicator (1 : Ω → ℝ)) := by
  classical
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_one.indicator hE) hA,
    Measure.map_apply (measurable_one.indicator hF) hA,
    show (1 : Ω → ℝ) = fun _ => 1 from rfl, Set.indicator_const_preimage_eq_union,
    Set.indicator_const_preimage_eq_union]
  split_ifs <;> simp [prob_compl_eq_one_sub hE, prob_compl_eq_one_sub hF, h]

/-- **Two rows far apart in time are independent on a window**. -/
theorem measure_inter_window_time {I : Finset ℤ} {w : ℤ → Bool} {s t : ℕ} {m : ℤ}
    (hs : ∀ i ∈ I, m ≤ i - s) (ht : ∀ i ∈ I, i - t < m) :
    coins ℤ ({x | ∀ i ∈ I, evol x s i = w i} ∩ {x | ∀ i ∈ I, evol x t i = w i}) =
      coins ℤ {x | ∀ i ∈ I, evol x s i = w i} * coins ℤ {x | ∀ i ∈ I, evol x t i = w i} := by
  have hAm : ∀ x p, p < m → (Function.update x p (!x p) ∈ {x : ℤ → Bool | ∀ i ∈ I,
      evol x s i = w i} ↔ x ∈ {x : ℤ → Bool | ∀ i ∈ I, evol x s i = w i}) := by
    intro x p hp
    simp only [Set.mem_setOf_eq]
    refine forall₂_congr fun i hi => ?_
    rw [AlgebraicDegree.evol_update_of_far (Or.inl (by have := hs i hi; omega))]
  rw [measure_inter_window (measurableSet_window s I w) hAm t w I ht, measure_window t I w]

/-- **The strong law along one residue class of times.** -/
theorem ae_tendsto_residue (I : Finset ℤ) (w : ℤ → Bool) (g r : ℕ)
    (hsep : ∀ j k : ℕ, j < k → ∃ m : ℤ, (∀ i ∈ I, m ≤ i - (r + j * g : ℕ)) ∧
      ∀ i ∈ I, i - (r + k * g : ℕ) < m) :
    ∀ᵐ x ∂(coins ℤ), Tendsto (fun K : ℕ => (∑ k ∈ range K,
      ({y | ∀ i ∈ I, evol y (r + k * g) i = w i}.indicator (1 : (ℤ → Bool) → ℝ) x)) / K) atTop
        (𝓝 ((2 : ℝ)⁻¹ ^ I.card)) := by
  let E : ℕ → Set (ℤ → Bool) := fun k => {y | ∀ i ∈ I, evol y (r + k * g) i = w i}
  let Y : ℕ → (ℤ → Bool) → ℝ := fun k => (E k).indicator 1
  have hE : ∀ k, MeasurableSet (E k) := fun k => measurableSet_window _ I w
  have hμE : ∀ k, coins ℤ (E k) = 2⁻¹ ^ I.card := fun k => measure_window _ I w
  have hind : Pairwise fun j k => IndepFun (Y j) (Y k) (coins ℤ) := by
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · obtain ⟨m, hm1, hm2⟩ := hsep j k h
      exact indepFun_indicator (hE j) (hE k) (measure_inter_window_time hm1 hm2)
    · obtain ⟨m, hm1, hm2⟩ := hsep k j h
      exact (indepFun_indicator (hE k) (hE j) (measure_inter_window_time hm1 hm2)).symm
  have hident : ∀ k, IdentDistrib (Y k) (Y 0) (coins ℤ) (coins ℤ) := fun k =>
    ⟨(measurable_one.indicator (hE k)).aemeasurable,
      (measurable_one.indicator (hE 0)).aemeasurable,
      map_indicator_eq (hE k) (hE 0) ((hμE k).trans (hμE 0).symm)⟩
  have hint : Integrable (Y 0) (coins ℤ) := (integrable_const 1).indicator (hE 0)
  have hmean : (coins ℤ)[Y 0] = (2 : ℝ)⁻¹ ^ I.card := by
    rw [integral_indicator_one (hE 0), measureReal_def, hμE 0, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  filter_upwards [strong_law_ae Y hint hind hident] with x hx
  rw [hmean] at hx
  refine hx.congr fun K => ?_
  rw [smul_eq_mul, inv_mul_eq_div]

/-- **Pattern frequencies along almost every orbit** (a pointwise ergodic theorem for local
patterns): for almost every configuration `x`, every pattern `v` on every window `[-n, n]`
appears in the rows of the space-time diagram of `x` with frequency `2^-(2n+1)`. -/
theorem ae_orbit_frequency :
    ∀ᵐ x ∂(coins ℤ), ∀ (n : ℕ) (v : Finset.Icc (-(n : ℤ)) n → Bool),
      Tendsto (fun T : ℕ => (∑ t ∈ range T, ({y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n,
        evol y t i = extend v i}.indicator (1 : (ℤ → Bool) → ℝ) x)) / T) atTop
          (𝓝 ((2 : ℝ)⁻¹ ^ (2 * n + 1))) := by
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun v => ?_
  have hcard : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    omega
  have hres : ∀ᵐ x ∂(coins ℤ), ∀ r : Fin (2 * n + 1), Tendsto (fun K : ℕ => (∑ k ∈ range K,
      ({y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n, evol y (r + k * (2 * n + 1)) i =
        extend v i}.indicator (1 : (ℤ → Bool) → ℝ) x)) / K) atTop
          (𝓝 ((2 : ℝ)⁻¹ ^ (Finset.Icc (-(n : ℤ)) n).card)) := by
    refine ae_all_iff.2 fun r => ae_tendsto_residue _ _ (2 * n + 1) r fun j k hjk => ?_
    refine ⟨-(n : ℤ) - (r + j * (2 * n + 1) : ℕ), fun i hi => ?_, fun i hi => ?_⟩
    · have := (Finset.mem_Icc.1 hi).1
      omega
    · have hi2 := (Finset.mem_Icc.1 hi).2
      have hkj : (j + 1) * (2 * n + 1) ≤ k * (2 * n + 1) := Nat.mul_le_mul_right _ hjk
      have hkj' : ((j * (2 * n + 1) : ℕ) : ℤ) + (2 * n + 1) ≤ ((k * (2 * n + 1) : ℕ) : ℤ) := by
        rw [add_mul, one_mul] at hkj
        exact_mod_cast hkj
      push_cast at hkj' ⊢
      omega
  filter_upwards [hres] with x hx
  rw [← hcard]
  refine tendsto_average_of_residues (Nat.succ_pos _)
    (a := fun t => {y | ∀ i ∈ Finset.Icc (-(n : ℤ)) n, evol y t i = extend v i}.indicator
      (1 : (ℤ → Bool) → ℝ) x)
    (fun i => by simp only [Set.indicator]; split_ifs <;> norm_num)
    (fun i => by simp only [Set.indicator]; split_ifs <;> norm_num) fun r hr => hx ⟨r, hr⟩

end Rule30Equivalents.OrbitFrequencies

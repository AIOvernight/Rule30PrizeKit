import Rule30Equivalents.RandomConfigurations

/-!
# Rule 30 preserves the fair-coin measure and is mixing

Catalog Section 7, item 11, continued: rule 30 as a measure-preserving dynamical system on
`{0,1}^ℤ` with the fair-coin measure `coins ℤ`. Everything comes from left-permutivity: flipping
the coin at `a - t` flips the cell `(t, a)` (`Genericity.evol_flip_at`), preserves the measure, and
changes no cell `(t, i)` with `i > a`. Adding the cells of a finite window `I` from the left, each
one halves the measure (`RandomConfigurations.two_mul_measure_flip`).

* `measure_inter_window`: if an event `A` does not depend on the coins left of `m`, and
  `i - t < m` for every `i ∈ I`, then the window `I` of the `t`-th image is uniform and independent
  of `A`.
* `measurePreserving_evol`: every iterate of rule 30 preserves `coins ℤ` (Hedlund's theorem for
  rule 30).
* `measure_window_inter_window`: the window `J` of a configuration and the window `I` of its
  `t`-th image are independent once `t > max I - min J`. So rule 30 is mixing, and topologically
  mixing (`exists_mem_evol_mem`).
* `ae_isNormal_columns`: for almost every configuration, every column of the space-time diagram
  is normal (shift invariance and `RandomConfigurations.ae_isNormal_trace`).
-/

namespace Rule30Equivalents.Mixing

open MeasureTheory Filter Topology Ruliology.CellularAutomata Rule30Realization Genericity
  RandomConfigurations

theorem measurableSet_window (t : ℕ) (I : Finset ℤ) (w : ℤ → Bool) :
    MeasurableSet {x : ℤ → Bool | ∀ i ∈ I, evol x t i = w i} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurable_evol t i (measurableSet_singleton (w i))

/-- **Independence beyond the light cone.** If `A` does not depend on the coins left of `m`, and
every cell `i` of the window `I` has `i - t < m`, then the window `I` of the `t`-th image is
uniform and independent of `A`. -/
theorem measure_inter_window {A : Set (ℤ → Bool)} (hA : MeasurableSet A) {m : ℤ}
    (hAm : ∀ x p, p < m → (Function.update x p (!x p) ∈ A ↔ x ∈ A)) (t : ℕ) (w : ℤ → Bool) :
    ∀ I : Finset ℤ, (∀ i ∈ I, i - t < m) →
      coins ℤ (A ∩ {x | ∀ i ∈ I, evol x t i = w i}) = coins ℤ A * 2⁻¹ ^ I.card := by
  intro I
  induction I using Finset.induction_on_min with
  | empty =>
    intro _
    simp
  | insert a s ha ih =>
    intro hI
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    set E := A ∩ {x : ℤ → Bool | ∀ i ∈ s, evol x t i = w i} with hEdef
    -- flipping the coin at `a - t` preserves `E`
    have hinv : ∀ x, Function.update x (a - t) (!x (a - t)) ∈ E ↔ x ∈ E := by
      intro x
      simp only [hEdef, Set.mem_inter_iff, Set.mem_setOf_eq,
        hAm x (a - t) (hI a (Finset.mem_insert_self a s))]
      refine and_congr_right fun _ => forall₂_congr fun i hi => ?_
      rw [AlgebraicDegree.evol_update_of_far (Or.inl (by have := ha i hi; omega))]
    have h : 2 * coins ℤ (E ∩ {x | evol x t a = w a}) = coins ℤ E :=
      two_mul_measure_flip (hA.inter (measurableSet_window t s w)) (measurable_evol t a) _ hinv
        (fun x _ => evol_flip_at x t a) (w a)
    have hset : A ∩ {x : ℤ → Bool | ∀ i ∈ insert a s, evol x t i = w i} =
        E ∩ {x | evol x t a = w a} := by
      ext x
      simp only [hEdef, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert,
        forall_eq_or_imp]
      tauto
    rw [hset, eq_mul_inv_of_two_mul h, ih fun i hi => hI i (Finset.mem_insert_of_mem hi),
      Finset.card_insert_of_notMem has, pow_succ, mul_assoc]

/-- **Every window of every iterate is uniform**: the cells of a finite window `I` after `t` steps
take each pattern with probability `2^-|I|`. -/
theorem measure_window (t : ℕ) (I : Finset ℤ) (w : ℤ → Bool) :
    coins ℤ {x | ∀ i ∈ I, evol x t i = w i} = 2⁻¹ ^ I.card := by
  obtain ⟨M, hM⟩ := I.bddAbove
  have h := measure_inter_window MeasurableSet.univ (m := M + 1) (fun x p _ => by simp) t w I
    fun i hi => by
      have := hM (Finset.mem_coe.2 hi)
      omega
  rwa [Set.univ_inter, measure_univ, one_mul] at h

/-- **Rule 30 preserves the fair-coin measure** (Hedlund's theorem for rule 30): every iterate
maps `coins ℤ` to itself. -/
theorem measurePreserving_evol (t : ℕ) :
    MeasurePreserving (fun x : ℤ → Bool => evol x t) (coins ℤ) (coins ℤ) := by
  have hF : Measurable fun x : ℤ → Bool => evol x t :=
    measurable_pi_lambda _ fun p => measurable_evol t p
  refine ⟨hF, IsProjectiveLimit.unique (P := fun I : Finset ℤ => Measure.pi fun _ : I => coin)
    (fun I => ?_) (Measure.isProjectiveLimit_infinitePi _)⟩
  rw [Measure.map_map (Finset.measurable_restrict _) hF]
  refine Measure.ext_iff_singleton.2 fun v => ?_
  rw [Measure.map_apply ((Finset.measurable_restrict _).comp hF) (measurableSet_singleton v),
    Measure.pi_singleton]
  let w : ℤ → Bool := fun i => if h : i ∈ I then v ⟨i, h⟩ else false
  have hset : (I.restrict ∘ fun x : ℤ → Bool => evol x t) ⁻¹' {v} =
      {x | ∀ i ∈ I, evol x t i = w i} := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro h i hi
      simp only [w, dif_pos hi]
      rw [← h]
      rfl
    · intro h
      funext i
      have := h i.1 i.2
      simp only [w, dif_pos i.2] at this
      exact this
  rw [hset, measure_window, Finset.prod_congr rfl fun i _ => coin_singleton (v i),
    Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- **Rule 30 is mixing**: the window `J` of a random configuration and the window `I` of its
`t`-th image are independent as soon as some `m` separates them: `m ≤ j` for `j ∈ J` and
`i - t < m` for `i ∈ I`. -/
theorem measure_window_inter_window (t : ℕ) (J I : Finset ℤ) (u w : ℤ → Bool) (m : ℤ)
    (hJ : ∀ j ∈ J, m ≤ j) (hI : ∀ i ∈ I, i - t < m) :
    coins ℤ {x | (∀ j ∈ J, x j = u j) ∧ ∀ i ∈ I, evol x t i = w i} =
      2⁻¹ ^ J.card * 2⁻¹ ^ I.card := by
  have hA : MeasurableSet {x : ℤ → Bool | ∀ j ∈ J, x j = u j} := measurableSet_window 0 J u
  have h := measure_inter_window hA (m := m) (fun x p hp => by
    simp only [Set.mem_setOf_eq]
    refine forall₂_congr fun j hj => ?_
    rw [Function.update_of_ne (by have := hJ j hj; omega)]) t w I hI
  rw [Set.setOf_and, h, show {x : ℤ → Bool | ∀ j ∈ J, x j = u j} =
    {x | ∀ j ∈ J, evol x 0 j = u j} from rfl, measure_window]

/-- **Rule 30 is topologically mixing**: for nonempty open sets `U` and `V`, from some time on,
every `t`-th image of `U` meets `V`. -/
theorem exists_mem_evol_mem {U V : Set (ℤ → Bool)} (hU : IsOpen U) (hV : IsOpen V)
    (hU0 : U.Nonempty) (hV0 : V.Nonempty) : ∃ T : ℕ, ∀ t ≥ T, ∃ x ∈ U, evol x t ∈ V := by
  obtain ⟨u, hu⟩ := hU0
  obtain ⟨v, hv⟩ := hV0
  obtain ⟨n₁, hn₁⟩ := exists_window_subset (hU.mem_nhds hu)
  obtain ⟨n₂, hn₂⟩ := exists_window_subset (hV.mem_nhds hv)
  have h1 : n₁ ≤ max n₁ n₂ := le_max_left _ _
  have h2 : n₂ ≤ max n₁ n₂ := le_max_right _ _
  refine ⟨2 * max n₁ n₂ + 1, fun t ht => ?_⟩
  set N := max n₁ n₂
  have hpos := measure_window_inter_window t (Finset.Icc (-(N : ℤ)) N) (Finset.Icc (-(N : ℤ)) N)
    u v (-(N : ℤ)) (fun j hj => (Finset.mem_Icc.1 hj).1) fun i hi => by
      have := (Finset.mem_Icc.1 hi).2
      omega
  have hne : coins ℤ {x | (∀ j ∈ Finset.Icc (-(N : ℤ)) N, x j = u j) ∧
      ∀ i ∈ Finset.Icc (-(N : ℤ)) N, evol x t i = v i} ≠ 0 := by
    rw [hpos]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))
      (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))
  obtain ⟨x, hxJ, hxI⟩ := nonempty_of_measure_ne_zero hne
  exact ⟨x, hn₁ fun p hp1 hp2 => hxJ p (Finset.mem_Icc.2 ⟨by omega, by omega⟩),
    hn₂ fun p hp1 hp2 => hxI p (Finset.mem_Icc.2 ⟨by omega, by omega⟩)⟩

/-- **Normal columns almost surely**: for almost every configuration, every column of its
space-time diagram is normal. -/
theorem ae_isNormal_columns :
    ∀ᵐ x ∂(coins ℤ), ∀ p : ℤ, StrongerStatements.IsNormal fun t => evol x t p := by
  refine ae_all_iff.2 fun p => ?_
  have hshift : MeasurePreserving (fun (x : ℤ → Bool) (q : ℤ) => x (q + p)) (coins ℤ)
      (coins ℤ) :=
    ⟨by fun_prop, Measure.map_infinitePi_infinitePi_of_inj (add_left_injective p)⟩
  filter_upwards [hshift.quasiMeasurePreserving.ae ae_isNormal_trace] with x hx
  have hcol : (fun t => evol x t p) = trace fun q => x (q + p) := by
    funext t
    have := Rule30ZeroBoundaryBarriers.evol_shift_all (x := fun q => x (q + p)) (x' := x)
      (d := p) (fun q => rfl) t 0
    rw [zero_add] at this
    exact this
  rw [hcol]
  exact hx

end Rule30Equivalents.Mixing

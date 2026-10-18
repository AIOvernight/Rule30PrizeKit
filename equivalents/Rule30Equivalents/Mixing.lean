import Rule30Equivalents.RandomConfigurations
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.Dynamics.Ergodic.Ergodic

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
  `t`-th image are independent once `t > max I - min J`. So rule 30 is topologically mixing
  (`exists_mem_evol_mem`).
* `tendsto_measure_inter_preimage`: **rule 30 is mixing**, `μ(A ∩ F^{-t} B) → μ(A) μ(B)` for all
  measurable `A` and `B`: for cylinders the two sides agree once `t` exceeds the distance between
  their windows (`measure_inter_preimage_cylinder`), and every measurable set is close to a
  cylinder (`exists_cylinder_approx`, from Mathlib's approximation by a generating ring of sets).
  Hence `ergodic_evol_one`: rule 30 is ergodic, in Mathlib's sense of `Ergodic`.
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

theorem measurable_evol_all (t : ℕ) : Measurable fun x : ℤ → Bool => evol x t :=
  measurable_pi_lambda _ fun p => measurable_evol t p

/-- A pattern on the window `I`, extended by white cells. -/
def extend {I : Finset ℤ} (v : I → Bool) (i : ℤ) : Bool := if h : i ∈ I then v ⟨i, h⟩ else false

theorem preimage_restrict_singleton (t : ℕ) (I : Finset ℤ) (v : I → Bool) :
    (fun x : ℤ → Bool => I.restrict (evol x t)) ⁻¹' {v} =
      {x | ∀ i ∈ I, evol x t i = extend v i} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro h i hi
    simp only [extend, dif_pos hi]
    rw [← h]
    rfl
  · intro h
    funext i
    have := h i.1 i.2
    simp only [extend, dif_pos i.2] at this
    exact this

/-- **Rule 30 preserves the fair-coin measure** (Hedlund's theorem for rule 30): every iterate
maps `coins ℤ` to itself. -/
theorem measurePreserving_evol (t : ℕ) :
    MeasurePreserving (fun x : ℤ → Bool => evol x t) (coins ℤ) (coins ℤ) := by
  have hF := measurable_evol_all t
  refine ⟨hF, IsProjectiveLimit.unique (P := fun I : Finset ℤ => Measure.pi fun _ : I => coin)
    (fun I => ?_) (Measure.isProjectiveLimit_infinitePi _)⟩
  rw [Measure.map_map (Finset.measurable_restrict _) hF]
  refine Measure.ext_iff_singleton.2 fun v => ?_
  rw [Measure.map_apply ((Finset.measurable_restrict _).comp hF) (measurableSet_singleton v),
    Measure.pi_singleton, show (I.restrict ∘ fun x : ℤ → Bool => evol x t) =
      fun x => I.restrict (evol x t) from rfl, preimage_restrict_singleton, measure_window,
    Finset.prod_congr rfl fun i _ => coin_singleton (v i), Finset.prod_const, Finset.card_univ,
    Fintype.card_coe]

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

/-! ### Mixing for all measurable sets, and ergodicity -/

/-- **The window law given a far event**: restricted to an event `A` that does not depend on the
coins left of `m`, the window `I` of the `t`-th image has `μ(A)` times the uniform law. -/
theorem map_restrict_window {A : Set (ℤ → Bool)} (hA : MeasurableSet A) {m : ℤ}
    (hAm : ∀ x p, p < m → (Function.update x p (!x p) ∈ A ↔ x ∈ A)) (t : ℕ) (I : Finset ℤ)
    (hI : ∀ i ∈ I, i - t < m) :
    ((coins ℤ).restrict A).map (fun x => I.restrict (evol x t)) =
      coins ℤ A • Measure.pi fun _ : I => coin := by
  have hg : Measurable fun x : ℤ → Bool => I.restrict (evol x t) :=
    (Finset.measurable_restrict I).comp (measurable_evol_all t)
  refine Measure.ext_iff_singleton.2 fun v => ?_
  rw [Measure.map_apply hg (measurableSet_singleton v),
    Measure.restrict_apply (hg (measurableSet_singleton v)), preimage_restrict_singleton,
    Set.inter_comm, measure_inter_window hA hAm t _ I hI, Measure.smul_apply, smul_eq_mul,
    Measure.pi_singleton, Finset.prod_congr rfl fun i _ => coin_singleton (v i),
    Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- A far event and a cylinder over the window `I` of the `t`-th image are independent. -/
theorem measure_inter_preimage_cylinder {A : Set (ℤ → Bool)} (hA : MeasurableSet A) {m : ℤ}
    (hAm : ∀ x p, p < m → (Function.update x p (!x p) ∈ A ↔ x ∈ A)) (t : ℕ) {I : Finset ℤ}
    (hI : ∀ i ∈ I, i - t < m) {S : Set (I → Bool)} (hS : MeasurableSet S) :
    coins ℤ (A ∩ (fun x => evol x t) ⁻¹' cylinder I S) = coins ℤ A * coins ℤ (cylinder I S) := by
  have hg : Measurable fun x : ℤ → Bool => I.restrict (evol x t) :=
    (Finset.measurable_restrict I).comp (measurable_evol_all t)
  have h := congrArg (fun ν : Measure (I → Bool) => ν S) (map_restrict_window hA hAm t I hI)
  simp only at h
  rw [Measure.map_apply hg hS, Measure.restrict_apply (hg hS), Measure.smul_apply,
    smul_eq_mul] at h
  rw [Set.inter_comm, Measure.infinitePi_cylinder _ hS]
  exact h

theorem abs_measureReal_sub_le (μ : Measure (ℤ → Bool)) [IsFiniteMeasure μ]
    (s t : Set (ℤ → Bool)) : |μ.real s - μ.real t| ≤ μ.real (symmDiff s t) := by
  have h1 : μ.real s ≤ μ.real t + μ.real (symmDiff s t) := by
    refine (measureReal_mono fun x hx => ?_).trans (measureReal_union_le _ _)
    by_cases ht : x ∈ t
    · exact Or.inl ht
    · exact Or.inr (Set.mem_symmDiff.2 (Or.inl ⟨hx, ht⟩))
  have h2 : μ.real t ≤ μ.real s + μ.real (symmDiff s t) := by
    refine (measureReal_mono fun x hx => ?_).trans (measureReal_union_le _ _)
    by_cases hs : x ∈ s
    · exact Or.inl hs
    · exact Or.inr (Set.mem_symmDiff.2 (Or.inr ⟨hx, hs⟩))
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Every measurable set is close to a cylinder. -/
theorem exists_cylinder_approx {s : Set (ℤ → Bool)} (hs : MeasurableSet s) {ε : ℝ} (hε : 0 < ε) :
    ∃ (I : Finset ℤ) (S : Set (I → Bool)), MeasurableSet S ∧
      (coins ℤ).real (symmDiff (cylinder I S) s) < ε := by
  obtain ⟨t, ht, hts⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := coins ℤ)
    isSetRing_measurableCylinders ⟨{Set.univ}, Set.countable_singleton _,
      Set.singleton_subset_iff.2 (univ_mem_measurableCylinders _), by simp⟩
    generateFrom_measurableCylinders.symm hs (ENNReal.ofReal_pos.2 hε)
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  exact ⟨I, S, hS, ENNReal.toReal_lt_of_lt_ofReal hts⟩

/-- **Rule 30 is mixing** for the fair-coin measure: `μ(A ∩ F^{-t} B) → μ(A) μ(B)` for all
measurable `A` and `B`. For cylinders the two sides agree once `t` exceeds the distance between
their windows (`measure_inter_preimage_cylinder`); every measurable set is close to a cylinder. -/
theorem tendsto_measure_inter_preimage {A B : Set (ℤ → Bool)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    Tendsto (fun t : ℕ => (coins ℤ).real (A ∩ (fun x => evol x t) ⁻¹' B)) atTop
      (𝓝 ((coins ℤ).real A * (coins ℤ).real B)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, SA, hSA, hA'⟩ := exists_cylinder_approx hA (ε := ε / 4) (by positivity)
  obtain ⟨I, SB, hSB, hB'⟩ := exists_cylinder_approx hB (ε := ε / 4) (by positivity)
  obtain ⟨m, hm⟩ := J.bddBelow
  obtain ⟨M, hM⟩ := I.bddAbove
  refine ⟨(M - m + 1).toNat, fun t ht => ?_⟩
  have hsep : ∀ i ∈ I, i - t < m := fun i hi => by
    have := hM (Finset.mem_coe.2 hi)
    omega
  -- the cylinder over `J` does not see the coins left of `m`
  have hAm : ∀ x p, p < m →
      (Function.update x p (!x p) ∈ cylinder J SA ↔ x ∈ cylinder J SA) := by
    intro x p hp
    simp only [mem_cylinder]
    have : J.restrict (Function.update x p (!x p)) = J.restrict x := funext fun j =>
      Function.update_of_ne (by have := hm (Finset.mem_coe.2 j.2); omega) _ _
    rw [this]
  have hcyl := measure_inter_preimage_cylinder (MeasurableSet.cylinder J hSA) hAm t hsep hSB
  have hcyl' : (coins ℤ).real (cylinder J SA ∩ (fun x => evol x t) ⁻¹' cylinder I SB) =
      (coins ℤ).real (cylinder J SA) * (coins ℤ).real (cylinder I SB) := by
    rw [measureReal_def, hcyl, ENNReal.toReal_mul]
    rfl
  have hF := measurePreserving_evol t
  -- the first error term
  have hsub : symmDiff (A ∩ (fun x => evol x t) ⁻¹' B)
      (cylinder J SA ∩ (fun x => evol x t) ⁻¹' cylinder I SB) ⊆
        symmDiff A (cylinder J SA) ∪ (fun x => evol x t) ⁻¹' symmDiff B (cylinder I SB) := by
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union, Set.mem_preimage] at hx ⊢
    tauto
  have hpre : (coins ℤ).real ((fun x => evol x t) ⁻¹' symmDiff B (cylinder I SB)) =
      (coins ℤ).real (symmDiff B (cylinder I SB)) := by
    rw [measureReal_def, measureReal_def, hF.measure_preimage
      (hB.symmDiff (MeasurableSet.cylinder I hSB)).nullMeasurableSet]
  have e1 : |(coins ℤ).real (A ∩ (fun x => evol x t) ⁻¹' B) -
      (coins ℤ).real (cylinder J SA ∩ (fun x => evol x t) ⁻¹' cylinder I SB)| < ε / 2 := by
    refine (abs_measureReal_sub_le _ _ _).trans_lt ?_
    refine ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans_lt ?_
    rw [hpre, symmDiff_comm A, symmDiff_comm B]
    linarith
  -- the second error term
  have ha := abs_measureReal_sub_le (coins ℤ) (cylinder J SA) A
  have hb := abs_measureReal_sub_le (coins ℤ) (cylinder I SB) B
  have e2 : |(coins ℤ).real (cylinder J SA) * (coins ℤ).real (cylinder I SB) -
      (coins ℤ).real A * (coins ℤ).real B| < ε / 2 := by
    have h0a : 0 ≤ (coins ℤ).real A := measureReal_nonneg
    have h1a : (coins ℤ).real A ≤ 1 := measureReal_le_one
    have h0b : 0 ≤ (coins ℤ).real (cylinder I SB) := measureReal_nonneg
    have h1b : (coins ℤ).real (cylinder I SB) ≤ 1 := measureReal_le_one
    rw [show (coins ℤ).real (cylinder J SA) * (coins ℤ).real (cylinder I SB) -
        (coins ℤ).real A * (coins ℤ).real B =
      ((coins ℤ).real (cylinder J SA) - (coins ℤ).real A) * (coins ℤ).real (cylinder I SB) +
        (coins ℤ).real A * ((coins ℤ).real (cylinder I SB) - (coins ℤ).real B) by ring]
    calc _ ≤ |((coins ℤ).real (cylinder J SA) - (coins ℤ).real A) *
          (coins ℤ).real (cylinder I SB)| +
          |(coins ℤ).real A * ((coins ℤ).real (cylinder I SB) - (coins ℤ).real B)| :=
          abs_add_le _ _
      _ = |(coins ℤ).real (cylinder J SA) - (coins ℤ).real A| * (coins ℤ).real (cylinder I SB) +
          (coins ℤ).real A * |(coins ℤ).real (cylinder I SB) - (coins ℤ).real B| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0b, abs_of_nonneg h0a]
      _ ≤ |(coins ℤ).real (cylinder J SA) - (coins ℤ).real A| * 1 +
          1 * |(coins ℤ).real (cylinder I SB) - (coins ℤ).real B| := by
          gcongr
      _ < ε / 2 := by linarith
  rw [Real.dist_eq]
  calc |(coins ℤ).real (A ∩ (fun x => evol x t) ⁻¹' B) - (coins ℤ).real A * (coins ℤ).real B|
      ≤ |(coins ℤ).real (A ∩ (fun x => evol x t) ⁻¹' B) -
          (coins ℤ).real (cylinder J SA ∩ (fun x => evol x t) ⁻¹' cylinder I SB)| +
        |(coins ℤ).real (cylinder J SA) * (coins ℤ).real (cylinder I SB) -
          (coins ℤ).real A * (coins ℤ).real B| := by
        rw [← hcyl']
        exact abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add e1 e2
    _ = ε := by ring

/-- **Rule 30 is ergodic** for the fair-coin measure: an invariant measurable set has measure
`μ(s) = μ(s)²`, so `0` or `1`. -/
theorem ergodic_evol_one : Ergodic (fun x : ℤ → Bool => evol x 1) (coins ℤ) := by
  refine ⟨measurePreserving_evol 1, ⟨fun s hs hinv => ?_⟩⟩
  have hinvt : ∀ t, (fun x : ℤ → Bool => evol x t) ⁻¹' s = s := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      have hcomp : (fun x : ℤ → Bool => evol x (t + 1)) =
          (fun x => evol x t) ∘ fun x => evol x 1 := by
        funext x p
        show evol x (t + 1) p = evol (fun q => evol x 1 q) t p
        rw [Rule30ZeroBoundaryBarriers.evol_restart, Nat.add_comm]
      rw [hcomp, Set.preimage_comp, ih, hinv]
  have h := tendsto_measure_inter_preimage hs hs
  simp only [hinvt, Set.inter_self] at h
  have hsq : (coins ℤ).real s = (coins ℤ).real s * (coins ℤ).real s :=
    tendsto_nhds_unique tendsto_const_nhds h
  have h01 : (coins ℤ).real s = 0 ∨ (coins ℤ).real s = 1 := by
    have : (coins ℤ).real s * ((coins ℤ).real s - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  rw [Filter.eventuallyConst_set]
  rcases h01 with h0 | h1
  · right
    exact measure_eq_zero_iff_ae_notMem.1 ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0)
  · left
    have hc : (coins ℤ).real sᶜ = 0 := by
      rw [measureReal_compl hs, probReal_univ, h1, sub_self]
    exact ae_iff.2 ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 hc)

end Rule30Equivalents.Mixing

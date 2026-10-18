import Rule30Equivalents.Genericity
import Rule30Equivalents.ProblemTwo
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Distributions.Uniform

/-!
# Random configurations

Catalog Section 7, item 11, in measure: the measure-theoretic counterpart of
[Genericity](Genericity.lean). Start rule 30 from independent fair coins on `ℤ` (`coins ℤ`, the
uniform Bernoulli product measure).

* `measurePreserving_trace`: the center trace `x ↦ (evol x t 0)ₜ` pushes `coins ℤ` to `coins ℕ`,
  so the trace of a random configuration is a sequence of independent fair coins. Flipping the coin
  at `-(n+1)` preserves the measure (`map_flip`), fixes the trace up to time `n` and flips it at
  time `n + 1` (left-permutivity), so every prefix of length `n + 1` has probability `2^-(n+1)`
  (`measure_prefix`); cylinders over initial segments then determine the measure.
* `ae_halfDensity_trace`: by the strong law of large numbers, for almost every configuration the
  trace has density `1/2`. The same set of configurations is meager
  (`Genericity.isMeagre_halfDensity_trace`), so it is a full-measure meager set
  (`isMeagre_and_ae_halfDensity_trace`).
* `ae_not_eventuallyPeriodic_trace`: the eventually periodic sequences are countably many
  (`countable_eventuallyPeriodic`) and `coins ℕ` has no atoms (`coins_singleton`), so for almost
  every configuration the trace is not eventually periodic.

So the analogues of Problems 1 and 2 hold for almost every initial configuration. The single black
cell is one configuration, a null set, so neither statement says anything about `c` itself.
-/

namespace Rule30Equivalents.RandomConfigurations

open MeasureTheory ProbabilityTheory Filter Topology Ruliology.CellularAutomata Rule30Realization
  Genericity

/-- The fair coin on `Bool`. -/
noncomputable def coin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coin := by
  unfold coin
  infer_instance

theorem coin_singleton (b : Bool) : coin {b} = 2⁻¹ := by
  rw [coin, PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b),
    PMF.uniformOfFintype_apply]
  simp

/-- Independent fair coins indexed by `ι`. -/
noncomputable abbrev coins (ι : Type*) : Measure (ι → Bool) :=
  Measure.infinitePi fun _ : ι => coin

theorem coins_map_eval {ι : Type*} (i : ι) : (coins ι).map (fun x => x i) = coin :=
  Measure.infinitePi_map_eval _ i

theorem coins_map_restrict {ι : Type*} (I : Finset ι) :
    (coins ι).map I.restrict = Measure.pi fun _ : I => coin :=
  Measure.infinitePi_map_restrict _

theorem coins_pi {ι : Type*} (s : Finset ι) (t : ι → Set Bool) :
    coins ι (Set.pi s t) = ∏ i ∈ s, coin (t i) :=
  Measure.infinitePi_pi _ fun _ _ => MeasurableSet.of_discrete

theorem measurable_evol (t : ℕ) (p : ℤ) : Measurable fun x : ℤ → Bool => evol x t p :=
  (continuous_evol t p).measurable

theorem measurable_trace : Measurable trace := continuous_trace.measurable

/-- Flipping the coin at `j`, coordinatewise. -/
theorem flip_eq (j : ℤ) : (fun x : ℤ → Bool => Function.update x j (!x j)) =
    fun x i => (if i = j then (fun b : Bool => !b) else id) (x i) := by
  funext x i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

theorem measurable_flip (j : ℤ) : Measurable fun x : ℤ → Bool => Function.update x j (!x j) := by
  rw [flip_eq]
  exact measurable_pi_lambda _ fun i => Measurable.of_discrete.comp (measurable_pi_apply i)

/-- Flipping one coin preserves the fair-coin measure. -/
theorem map_flip (j : ℤ) :
    (coins ℤ).map (fun x => Function.update x j (!x j)) = coins ℤ := by
  rw [flip_eq, coins, Measure.infinitePi_map_pi _ fun i => Measurable.of_discrete]
  refine congrArg Measure.infinitePi (funext fun i => ?_)
  split_ifs
  · refine Measure.ext_iff_singleton.2 fun b => ?_
    rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton b),
      show (fun b : Bool => !b) ⁻¹' {b} = {!b} by ext a; cases a <;> cases b <;> simp,
      coin_singleton, coin_singleton]
  · exact Measure.map_id

theorem measurableSet_prefix (w : ℕ → Bool) (n : ℕ) :
    MeasurableSet {x : ℤ → Bool | ∀ t ≤ n, trace x t = w t} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
    measurable_evol t 0 (measurableSet_singleton (w t))

theorem two_mul_inv_two_pow (n : ℕ) : 2 * (2⁻¹ : ENNReal) ^ (n + 1) = 2⁻¹ ^ n := by
  rw [pow_succ, mul_comm, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
    mul_one]

/-- **Every prefix of the trace has probability `2^-(n+1)`.** Flipping the coin at `-(n+1)`
preserves the measure, fixes the trace up to time `n` and flips it at time `n + 1`. -/
theorem measure_prefix (w : ℕ → Bool) :
    ∀ n : ℕ, coins ℤ {x | ∀ t ≤ n, trace x t = w t} = 2⁻¹ ^ (n + 1)
  | 0 => by
    have : {x : ℤ → Bool | ∀ t ≤ 0, trace x t = w t} = (fun x => x 0) ⁻¹' {w 0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        exact h 0 le_rfl
      · intro h t ht
        obtain rfl : t = 0 := by omega
        exact h
    rw [this, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _),
      coins_map_eval, coin_singleton, zero_add, pow_one]
  | n + 1 => by
    have ih := measure_prefix w n
    set A : Set (ℤ → Bool) := {x | ∀ t ≤ n, trace x t = w t} with hA
    let B : Bool → Set (ℤ → Bool) := fun b => A ∩ {x | trace x (n + 1) = b}
    have hB : ∀ b, MeasurableSet (B b) := fun b =>
      (hA ▸ measurableSet_prefix w n).inter
        (measurable_evol (n + 1) 0 (measurableSet_singleton b))
    -- flipping the coin at `-(n+1)` exchanges `B b` and `B !b`
    have hφ : ∀ b, (fun x => Function.update x (-((n + 1 : ℕ) : ℤ)) (!x (-((n + 1 : ℕ) : ℤ)))) ⁻¹'
        B b = B (!b) := by
      intro b
      ext x
      have hlow : ∀ t ≤ n, trace (Function.update x (-((n + 1 : ℕ) : ℤ))
          (!x (-((n + 1 : ℕ) : ℤ)))) t = trace x t := fun t ht =>
        AlgebraicDegree.evol_congr t 0 fun k hk1 _ => by
          rw [Function.update_of_ne (by omega)]
      have htop : trace (Function.update x (-((n + 1 : ℕ) : ℤ)) (!x (-((n + 1 : ℕ) : ℤ))))
          (n + 1) = !trace x (n + 1) := evol_flip x (n + 1)
      simp only [B, A, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, htop]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun t ht => (hlow t ht).symm.trans (h1 t ht), ?_⟩
        rw [← h2, Bool.not_not]
      · rintro ⟨h1, h2⟩
        refine ⟨fun t ht => (hlow t ht).trans (h1 t ht), ?_⟩
        rw [h2, Bool.not_not]
    have heq : ∀ b, coins ℤ (B b) = coins ℤ (B (!b)) := fun b => by
      rw [← hφ b, ← Measure.map_apply (measurable_flip _) (hB b), map_flip]
    have hsum : coins ℤ (B true) + coins ℤ (B false) = coins ℤ A := by
      rw [← measure_union _ (hB false)]
      · congr 1
        ext x
        simp only [B, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
        cases trace x (n + 1) <;> simp
      · rw [Set.disjoint_left]
        intro x h1 h2
        simp only [B, Set.mem_inter_iff, Set.mem_setOf_eq] at h1 h2
        rw [h1.2] at h2
        exact Bool.noConfusion h2.2
    have htarget : {x : ℤ → Bool | ∀ t ≤ n + 1, trace x t = w t} = B (w (n + 1)) := by
      ext x
      simp only [B, A, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro h
        exact ⟨fun t ht => h t (by omega), h (n + 1) le_rfl⟩
      · rintro ⟨h1, h2⟩ t ht
        rcases Nat.lt_or_ge t (n + 1) with h' | h'
        · exact h1 t (by omega)
        · obtain rfl : t = n + 1 := by omega
          exact h2
    have hhalf : coins ℤ (B true) = 2⁻¹ ^ (n + 1 + 1) := by
      have h2 : 2 * coins ℤ (B true) = 2 * 2⁻¹ ^ (n + 1 + 1) := by
        calc 2 * coins ℤ (B true) = coins ℤ (B true) + coins ℤ (B false) := by
              rw [two_mul]
              nth_rewrite 2 [heq true]
              rfl
          _ = 2⁻¹ ^ (n + 1) := by rw [hsum, ih]
          _ = 2 * 2⁻¹ ^ (n + 1 + 1) := (two_mul_inv_two_pow (n + 1)).symm
      exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 h2
    rw [htarget]
    cases hw : w (n + 1)
    · rw [heq false, Bool.not_false, hhalf]
    · exact hhalf

/-- **The trace of a random configuration is a random sequence**: the trace map pushes the
fair-coin measure on `{0,1}^ℤ` to the fair-coin measure on `{0,1}^ℕ`. -/
theorem measurePreserving_trace : MeasurePreserving trace (coins ℤ) (coins ℕ) := by
  refine ⟨measurable_trace, ?_⟩
  have : IsProbabilityMeasure ((coins ℤ).map trace) :=
    Measure.isProbabilityMeasure_map measurable_trace.aemeasurable
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun s hs => ?_) (by rw [measure_univ, measure_univ])
  rw [measurableCylinders_nat] at hs
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hs
  obtain ⟨a, S, hS, rfl⟩ := hs
  rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict _) hS,
    ← Measure.map_apply (Finset.measurable_restrict _) hS, coins_map_restrict,
    Measure.map_map (Finset.measurable_restrict _) measurable_trace]
  congr 1
  refine Measure.ext_iff_singleton.2 fun v => ?_
  rw [Measure.map_apply ((Finset.measurable_restrict _).comp measurable_trace)
    (measurableSet_singleton v), Measure.pi_singleton]
  -- the event is a prefix of the trace
  let w : ℕ → Bool := fun t => if h : t ≤ a then v ⟨t, Finset.mem_Iic.2 h⟩ else false
  have hset : ((Finset.Iic a).restrict ∘ trace) ⁻¹' {v} = {x | ∀ t ≤ a, trace x t = w t} := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro h t ht
      simp only [w, dif_pos ht]
      rw [← h]
      rfl
    · intro h
      funext i
      have := h i.1 (Finset.mem_Iic.1 i.2)
      simp only [w, dif_pos (Finset.mem_Iic.1 i.2)] at this
      exact this
  rw [hset, measure_prefix, Finset.prod_congr rfl fun i _ => coin_singleton (v i),
    Finset.prod_const, Finset.card_univ, Fintype.card_coe, Nat.card_Iic]

/-! ### Density `1/2` almost surely -/

/-- **Density `1/2` for a random sequence**: almost every fair-coin sequence has density `1/2`
(the strong law of large numbers). -/
theorem ae_halfDensity : ∀ᵐ v ∂(coins ℕ), Symmetry.HalfDensity v := by
  let g : Bool → ℝ := fun b => if b then 1 else 0
  let X : ℕ → (ℕ → Bool) → ℝ := fun i v => g (v i)
  have hg : Measurable g := Measurable.of_discrete
  have hX : ∀ i, Measurable (X i) := fun i => hg.comp (measurable_pi_apply i)
  have hmap : ∀ i, (coins ℕ).map (X i) = coin.map g := fun i => by
    rw [show X i = g ∘ fun v => v i from rfl, ← Measure.map_map hg (measurable_pi_apply i),
      coins_map_eval]
  have hind : iIndepFun X (coins ℕ) := iIndepFun_infinitePi (X := fun _ => g) fun _ => hg
  have hident : ∀ i, IdentDistrib (X i) (X 0) (coins ℕ) (coins ℕ) := fun i =>
    ⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [hmap, hmap]⟩
  have hint : Integrable (X 0) (coins ℕ) := by
    have : Integrable g ((coins ℕ).map fun v => v 0) := by
      rw [coins_map_eval]
      exact Integrable.of_finite
    exact this.comp_measurable (measurable_pi_apply 0)
  have hmean : (coins ℕ)[X 0] = 1 / 2 := by
    show ∫ v, g (v 0) ∂(coins ℕ) = 1 / 2
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hg.aestronglyMeasurable,
      coins_map_eval, integral_fintype Integrable.of_finite]
    simp [g, measureReal_def, coin_singleton]
  filter_upwards [strong_law_ae X hint (fun i j hij => hind.indepFun hij) hident] with v hv
  rw [ProblemTwo.halfDensity_iff_tendsto]
  rw [hmean] at hv
  refine hv.congr fun n => ?_
  rw [smul_eq_mul, ProblemTwo.count_eq_sum, inv_mul_eq_div]

/-- **Density `1/2` for almost every configuration**: for almost every configuration, the rule 30
trace has density `1/2`. -/
theorem ae_halfDensity_trace : ∀ᵐ x ∂(coins ℤ), Symmetry.HalfDensity (trace x) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_halfDensity

/-- **Meager but of full measure**: the configurations whose trace has density `1/2` form a meager
set of full measure. -/
theorem isMeagre_and_ae_halfDensity_trace :
    IsMeagre {x : ℤ → Bool | Symmetry.HalfDensity (trace x)} ∧
      ∀ᵐ x ∂(coins ℤ), Symmetry.HalfDensity (trace x) :=
  ⟨isMeagre_halfDensity_trace, ae_halfDensity_trace⟩

/-! ### No eventual period almost surely -/

/-- Two sequences with the same eventual period `P` from `T` on are equal once they agree below
`T + P`. -/
theorem eq_of_periodic {u v : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (hu : ∀ t, T ≤ t → u (t + P) = u t) (hv : ∀ t, T ≤ t → v (t + P) = v t)
    (h : ∀ t < T + P, u t = v t) : u = v := by
  funext t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases Nat.lt_or_ge t (T + P) with ht | ht
    · exact h t ht
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + P := ⟨t - P, by omega⟩
      rw [hu s (by omega), hv s (by omega)]
      exact ih s (by omega)

/-- The eventually periodic sequences are countably many. -/
theorem countable_eventuallyPeriodic : {v : ℕ → Bool | EventuallyPeriodic v}.Countable := by
  have hsub : {v : ℕ → Bool | EventuallyPeriodic v} ⊆ ⋃ (T : ℕ) (P : ℕ) (u : Fin (T + P) → Bool),
      {v | 0 < P ∧ (∀ t, T ≤ t → v (t + P) = v t) ∧ ∀ i : Fin (T + P), v i = u i} := by
    rintro v ⟨T, P, hP, hv⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨T, P, fun i => v i, hP, hv, fun i => rfl⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun T => Set.countable_iUnion fun P =>
    Set.countable_iUnion fun u => Set.Subsingleton.countable ?_)
  rintro v ⟨hP, hv, hvu⟩ v' ⟨-, hv', hvu'⟩
  exact eq_of_periodic hP hv hv' fun t ht => (hvu ⟨t, ht⟩).trans (hvu' ⟨t, ht⟩).symm

/-- A fair-coin sequence has no atoms. -/
theorem coins_singleton (v : ℕ → Bool) : coins ℕ {v} = 0 := by
  have hle : ∀ n : ℕ, coins ℕ {v} ≤ 2⁻¹ ^ (n + 1) := fun n => by
    calc coins ℕ {v} ≤ coins ℕ (Set.pi (Finset.range (n + 1) : Set ℕ) fun t => {v t}) :=
          measure_mono fun u hu => by
            rw [Set.mem_singleton_iff] at hu
            subst hu
            exact fun t _ => rfl
      _ = 2⁻¹ ^ (n + 1) := by
          rw [coins_pi]
          simp [coin_singleton]
  have hlim : Tendsto (fun n : ℕ => (2⁻¹ : ENNReal) ^ (n + 1)) atTop (𝓝 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)).comp
      (tendsto_add_atTop_nat 1)
  exact le_antisymm (ge_of_tendsto' hlim hle) zero_le

/-- **No eventual period for a random sequence**: almost every fair-coin sequence is not
eventually periodic. -/
theorem ae_not_eventuallyPeriodic : ∀ᵐ v ∂(coins ℕ), ¬ EventuallyPeriodic v := by
  have : NoAtoms (coins ℕ) := ⟨coins_singleton⟩
  rw [ae_iff]
  simp only [not_not]
  exact countable_eventuallyPeriodic.measure_zero _

/-- **No eventual period for almost every configuration**: for almost every configuration, the
rule 30 trace is not eventually periodic. -/
theorem ae_not_eventuallyPeriodic_trace :
    ∀ᵐ x ∂(coins ℤ), ¬ EventuallyPeriodic (trace x) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_not_eventuallyPeriodic

end Rule30Equivalents.RandomConfigurations

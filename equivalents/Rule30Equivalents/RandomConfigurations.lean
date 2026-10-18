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
* `ae_isNormal`: **Borel's normal number theorem** for fair coins. For a word `u` of length `m`
  and a residue `r`, the blocks `v(r + k m), …, v(r + k m + m - 1)` are independent fair words
  (`map_blocks`, by reindexing and currying the product measure), so by the strong law of large
  numbers `u` occurs with frequency `2⁻ᵐ` along the residue class `r`
  (`ae_tendsto_residue_frequency`); averaging over the `m` classes gives frequency `2⁻ᵐ`
  (`tendsto_average_of_residues`).
* `ae_isNormal_trace`: for almost every configuration the trace is normal; hence it has density
  `1/2` (`ae_halfDensity_trace`), is disjunctive (`ae_disjunctive_trace`) and is not eventually
  periodic (`ae_not_eventuallyPeriodic_trace`). The configurations whose trace has density `1/2`
  form a meager set (`Genericity.isMeagre_halfDensity_trace`) of full measure
  (`isMeagre_and_ae_halfDensity_trace`).

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

/-! ### Normality almost surely (Borel) -/

/-- Summing over `[0, m q)` by residues modulo `m`. -/
theorem sum_range_mul (a : ℕ → ℝ) (m q : ℕ) :
    ∑ i ∈ Finset.range (m * q), a i =
      ∑ r ∈ Finset.range m, ∑ k ∈ Finset.range q, a (r + k * m) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [mul_add_one, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_range_succ, Nat.add_comm (m * q) r, Nat.mul_comm m q]

/-- **Averages from residue classes**: a `[0, 1]`-valued sequence whose averages along every
residue class modulo `m` tend to `L` has averages tending to `L`. -/
theorem tendsto_average_of_residues {a : ℕ → ℝ} {m : ℕ} (hm : 0 < m) {L : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (h : ∀ r < m, Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, a (r + k * m)) / K) atTop
      (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, a i) / N) atTop (𝓝 L) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : Tendsto (fun N : ℕ => N / m) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * m, fun N hN => (Nat.le_div_iff_mul_le hm).2 hN⟩
  -- the averages over `[0, m q)`
  have hA : Tendsto (fun q : ℕ => (∑ i ∈ Finset.range (m * q), a i) / (m * q : ℕ)) atTop
      (𝓝 L) := by
    have hsum := (tendsto_finsetSum (Finset.range m) fun r hr =>
      h r (Finset.mem_range.1 hr)).const_mul (m : ℝ)⁻¹
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hm'.ne', one_mul] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with q hq1
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq1
    rw [sum_range_mul, Finset.sum_div, Finset.mul_sum, Nat.cast_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  -- `m ⌊N / m⌋ / N → 1`
  have hB : Tendsto (fun N : ℕ => ((m * (N / m) : ℕ) : ℝ) / N) atTop (𝓝 1) := by
    have hlow : Tendsto (fun N : ℕ => 1 - (m : ℝ) / N) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 : N ≤ m * (N / m) + m := by
        have := Nat.div_add_mod N m
        have := Nat.mod_lt N hm
        omega
      have h2 : (N : ℝ) ≤ ((m * (N / m) : ℕ) : ℝ) + m := by exact_mod_cast h1
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN', one_mul]
      linarith
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_one hN']
      exact_mod_cast Nat.mul_div_le N m
  -- the remainder over `[m ⌊N / m⌋, N)`
  have hsplit : ∀ N, ∑ i ∈ Finset.range N, a i = ∑ i ∈ Finset.range (m * (N / m)), a i +
      ∑ x ∈ Finset.range (N % m), a (m * (N / m) + x) := fun N => by
    rw [← Finset.sum_range_add, Nat.div_add_mod]
  have hC : Tendsto (fun N : ℕ => ((∑ i ∈ Finset.range N, a i) -
      ∑ i ∈ Finset.range (m * (N / m)), a i) / N) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)) (Eventually.of_forall fun N => ?_)
      (Eventually.of_forall fun N => ?_)
    · rw [hsplit, add_sub_cancel_left]
      exact div_nonneg (Finset.sum_nonneg fun x _ => ha0 _) (Nat.cast_nonneg _)
    · rw [hsplit, add_sub_cancel_left]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      calc ∑ x ∈ Finset.range (N % m), a (m * (N / m) + x)
          ≤ ∑ x ∈ Finset.range (N % m), (1 : ℝ) := Finset.sum_le_sum fun x _ => ha1 _
        _ ≤ m := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          exact_mod_cast (Nat.mod_lt N hm).le
  have hlim := ((hA.comp hq).mul hB).add hC
  rw [mul_one, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop m] with N hN
  have hq1 : 0 < N / m := Nat.div_pos hN hm
  have hmq : (0 : ℝ) < ((m * (N / m) : ℕ) : ℝ) := by positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hm hN
  simp only [Function.comp]
  field_simp
  ring

/-- The blocks `v(r + k m), …, v(r + k m + m - 1)`, `k = 0, 1, …`, of a fair-coin sequence are
independent fair words. -/
theorem map_blocks {m : ℕ} (hm : 0 < m) (r : ℕ) :
    (coins ℕ).map (fun v k (j : Fin m) => v (r + k * m + j)) =
      Measure.infinitePi fun _ : ℕ => coins (Fin m) := by
  have hinj : Function.Injective fun p : ℕ × Fin m => r + p.1 * m + p.2 := by
    rintro ⟨k, j⟩ ⟨k', j'⟩ h
    have h' : (j : ℕ) + k * m = j' + k' * m := by simp only at h; omega
    have hj : (j : ℕ) = j' := by
      have := congrArg (· % m) h'
      simpa only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt j'.2]
        using this
    have hk : k = k' := by
      have := congrArg (· / m) h'
      simpa only [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt j.2, Nat.div_eq_of_lt j'.2,
        zero_add] using this
    rw [hk, Fin.ext hj]
  have h1 : (coins ℕ).map (fun v (p : ℕ × Fin m) => v (r + p.1 * m + p.2)) =
      Measure.infinitePi fun _ : ℕ × Fin m => coin :=
    Measure.map_infinitePi_infinitePi_of_inj hinj
  have h2 : (Measure.infinitePi fun _ : ℕ × Fin m => coin).map
      (MeasurableEquiv.curry ℕ (Fin m) Bool) =
        Measure.infinitePi fun _ : ℕ => coins (Fin m) :=
    Measure.infinitePi_map_curry fun _ _ => coin
  rw [← h2, ← h1, Measure.map_map (MeasurableEquiv.curry ℕ (Fin m) Bool).measurable
    (by fun_prop)]
  rfl

/-- **Borel's theorem for one word along one residue class**: the strong law of large numbers
for the independent blocks. -/
theorem ae_tendsto_block_frequency {m : ℕ} (u : Fin m → Bool) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => coins (Fin m)),
      Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, if ω k = u then (1 : ℝ) else 0) / K) atTop
        (𝓝 ((2 : ℝ)⁻¹ ^ m)) := by
  let ρ : Measure (ℕ → Fin m → Bool) := Measure.infinitePi fun _ : ℕ => coins (Fin m)
  let g : (Fin m → Bool) → ℝ := fun b => if b = u then 1 else 0
  let X : ℕ → (ℕ → Fin m → Bool) → ℝ := fun k ω => g (ω k)
  have hg : Measurable g := Measurable.of_discrete
  have hX : ∀ k, Measurable (X k) := fun k => hg.comp (measurable_pi_apply k)
  have hmap : ∀ k, ρ.map (X k) = (coins (Fin m)).map g := fun k => by
    rw [show X k = g ∘ fun ω => ω k from rfl, ← Measure.map_map hg (measurable_pi_apply k),
      Measure.infinitePi_map_eval]
  have hind : iIndepFun X ρ := iIndepFun_infinitePi (X := fun _ => g) fun _ => hg
  have hident : ∀ k, IdentDistrib (X k) (X 0) ρ ρ := fun k =>
    ⟨(hX k).aemeasurable, (hX 0).aemeasurable, by rw [hmap, hmap]⟩
  have hint : Integrable (X 0) ρ := by
    have : Integrable g (ρ.map fun ω => ω 0) := by
      rw [Measure.infinitePi_map_eval]
      exact Integrable.of_finite
    exact this.comp_measurable (measurable_pi_apply 0)
  have hmean : ρ[X 0] = (2 : ℝ)⁻¹ ^ m := by
    show ∫ ω, g (ω 0) ∂ρ = _
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hg.aestronglyMeasurable,
      Measure.infinitePi_map_eval, integral_fintype Integrable.of_finite]
    simp [g, measureReal_def, coin_singleton]
  filter_upwards [strong_law_ae X hint (fun i j hij => hind.indepFun hij) hident] with ω hω
  rw [hmean] at hω
  refine hω.congr fun K => ?_
  rw [smul_eq_mul, inv_mul_eq_div]

/-- The same, read in the fair-coin sequence: along the residue class `r` modulo `m`, the word
`u` occurs with frequency `2⁻ᵐ`. -/
theorem ae_tendsto_residue_frequency {m : ℕ} (hm : 0 < m) (u : Fin m → Bool) (r : ℕ) :
    ∀ᵐ v ∂(coins ℕ), Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K,
      if ∀ j : Fin m, v (r + k * m + j) = u j then (1 : ℝ) else 0) / K) atTop
        (𝓝 ((2 : ℝ)⁻¹ ^ m)) := by
  have hmp : MeasurePreserving (fun v k (j : Fin m) => v (r + k * m + j)) (coins ℕ)
      (Measure.infinitePi fun _ : ℕ => coins (Fin m)) := ⟨by fun_prop, map_blocks hm r⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae (ae_tendsto_block_frequency u)] with v hv
  refine hv.congr fun K => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [funext_iff]

/-- **Borel's normal number theorem** for fair coins: almost every fair-coin sequence is
normal. -/
theorem ae_isNormal : ∀ᵐ v ∂(coins ℕ), StrongerStatements.IsNormal v := by
  unfold StrongerStatements.IsNormal
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun w => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- the empty word occurs everywhere
    refine Eventually.of_forall fun v => ?_
    rw [pow_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Finset.filter_true_of_mem fun i _ j => j.elim0, Finset.card_range,
      div_self (Nat.cast_ne_zero.2 (by omega))]
  · filter_upwards [ae_all_iff.2 fun r : Fin n => ae_tendsto_residue_frequency hn w r]
      with v hv
    have := tendsto_average_of_residues hn
      (a := fun i => if ∀ j : Fin n, v (i + j) = w j then (1 : ℝ) else 0)
      (fun i => by dsimp only; split_ifs <;> norm_num)
      (fun i => by dsimp only; split_ifs <;> norm_num)
      fun r hr => hv ⟨r, hr⟩
    refine this.congr fun N => ?_
    rw [Finset.sum_boole]

/-- **Normal traces almost surely**: for almost every configuration, the rule 30 trace is
normal. -/
theorem ae_isNormal_trace : ∀ᵐ x ∂(coins ℤ), StrongerStatements.IsNormal (trace x) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_isNormal

/-! ### Consequences: category versus measure -/

/-- For almost every configuration, the trace has density `1/2`. -/
theorem ae_halfDensity_trace : ∀ᵐ x ∂(coins ℤ), Symmetry.HalfDensity (trace x) :=
  ae_isNormal_trace.mono fun _ h => ProblemTwo.halfDensity_of_isNormal h

/-- For almost every configuration, the trace is disjunctive. -/
theorem ae_disjunctive_trace : ∀ᵐ x ∂(coins ℤ), Disjunctive (trace x) :=
  ae_isNormal_trace.mono fun _ h => StrongerStatements.disjunctive_of_isNormal h

/-- For almost every configuration, the trace is not eventually periodic. -/
theorem ae_not_eventuallyPeriodic_trace :
    ∀ᵐ x ∂(coins ℤ), ¬ EventuallyPeriodic (trace x) :=
  ae_isNormal_trace.mono fun _ h =>
    StrongerStatements.not_eventuallyPeriodic_of_disjunctive
      (StrongerStatements.disjunctive_of_isNormal h)

/-- **Meager but of full measure**: the configurations whose trace has density `1/2` (a fortiori
those with a normal trace) form a meager set of full measure. -/
theorem isMeagre_and_ae_halfDensity_trace :
    IsMeagre {x : ℤ → Bool | Symmetry.HalfDensity (trace x)} ∧
      ∀ᵐ x ∂(coins ℤ), Symmetry.HalfDensity (trace x) :=
  ⟨isMeagre_halfDensity_trace, ae_halfDensity_trace⟩

end Rule30Equivalents.RandomConfigurations

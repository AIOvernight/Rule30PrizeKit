import Rule30Equivalents.Mixing
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Problem 2 through empirical measures

Catalog Section 6.1, the ergodic form. The empirical measure of a bit sequence `b` over the times
`0, …, N` is `μ_N = (δ_b + δ_{σb} + ⋯ + δ_{σᴺb}) / (N + 1)` on `{0,1}^ℕ` (`empirical`), a point of
the compact space of probability measures (Mathlib's Prokhorov theorem). Its mass on the cylinder
`[1] = {v | v 0 = 1}` is the proportion of `1`s among `b 0, …, b N` (`empirical_one`).

* `continuous_mass_one`: `ν ↦ ν [1]` is continuous, since `[1]` is clopen (portmanteau).
* `tendsto_comp_iff_forall_mapClusterPt`: in a compact space, `g(u N) → L` for a continuous `g`
  iff `g x = L` at every cluster point `x` of `(u N)`.
* `halfDensity_iff_mapClusterPt`, `problem2_iff_mapClusterPt`: **Problem 2 holds iff every limit
  point of the empirical measures of the center column gives the cylinder `[1]` mass `1/2`.**
* `isNormal_iff_tendsto_empirical`: **a bit sequence is normal iff its empirical measures converge
  weakly to the fair-coin measure** (normal sequences are the generic points of the fair coin).
  Cylinders are clopen (portmanteau) and form a π-system of arbitrarily small neighbourhoods
  (Mathlib's `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`). With Borel's theorem,
  the trace of almost every configuration is generic (`ae_tendsto_empirical_trace`).
-/

namespace Rule30Equivalents.EmpiricalMeasures

open MeasureTheory Filter Topology Finset Ruliology.CellularAutomata

/-- The cylinder of sequences starting with `1`. -/
def one : Set (ℕ → Bool) := {v | v 0 = true}

theorem isClopen_one : IsClopen one :=
  (isClopen_discrete {true}).preimage (continuous_apply (A := fun _ : ℕ => Bool) 0)

theorem measurableSet_one : MeasurableSet one :=
  (measurableSet_singleton true).preimage (measurable_pi_apply 0)

/-- The empirical measure of the points `u 0, …, u N` of a measurable space. -/
noncomputable def empiricalOf {X : Type*} [MeasurableSpace X] (u : ℕ → X) (N : ℕ) :
    ProbabilityMeasure X :=
  ⟨((N : ENNReal) + 1)⁻¹ • ∑ n ∈ range (N + 1), Measure.dirac (u n), by
    constructor
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [measure_univ, sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    push_cast
    exact ENNReal.inv_mul_cancel (by simp) (by simp)⟩

/-- The mass of a measurable set `s` is the proportion of the times `i ≤ N` with `u i ∈ s`. -/
theorem empiricalOf_apply {X : Type*} [MeasurableSpace X] (u : ℕ → X) (N : ℕ) {s : Set X}
    [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    ((empiricalOf u N) s : ℝ) = (#{i ∈ range (N + 1) | u i ∈ s} : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  have hμ : (empiricalOf u N : Measure X) s =
      ((N : ENNReal) + 1)⁻¹ * (#{i ∈ range (N + 1) | u i ∈ s} : ENNReal) := by
    show (((N : ENNReal) + 1)⁻¹ • ∑ n ∈ range (N + 1), Measure.dirac (u n)) s = _
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul, ← sum_boole]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [Measure.dirac_apply' _ hs, Set.indicator_apply]
    simp only [Pi.one_apply]
  rw [ProbabilityMeasure.coeFn_def, ENNReal.coe_toNNReal_eq_toReal, hμ, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, div_eq_inv_mul]
  push_cast
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp

/-- The empirical measure of `b` over the times `0, …, N`: of the shifts `b, σb, …, σᴺb`. -/
noncomputable def empirical (b : ℕ → Bool) (N : ℕ) : ProbabilityMeasure (ℕ → Bool) :=
  empiricalOf (fun n => Mixing.shift^[n] b) N

theorem empirical_apply (b : ℕ → Bool) (N : ℕ) {s : Set (ℕ → Bool)} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) :
    ((empirical b N) s : ℝ) =
      (#{i ∈ range (N + 1) | Mixing.shift^[i] b ∈ s} : ℝ) / ((N + 1 : ℕ) : ℝ) :=
  empiricalOf_apply _ N hs

/-- **The mass of `[1]` is the proportion of `1`s** among `b 0, …, b N`. -/
theorem empirical_one (b : ℕ → Bool) (N : ℕ) :
    ((empirical b N) one : ℝ) =
      (((List.range (N + 1)).filter b).length : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  classical
  rw [empirical_apply b N measurableSet_one, ProblemTwo.count_eq_sum, sum_boole]
  congr 3
  refine filter_congr fun i _ => ?_
  simp [one, Mixing.shift_iterate]

/-- `ν ↦ ν [1]` is continuous: `[1]` is clopen, so its frontier is null (portmanteau). -/
theorem continuous_mass_one :
    Continuous fun ν : ProbabilityMeasure (ℕ → Bool) => (ν one : ℝ) := by
  refine continuous_iff_continuousAt.2 fun ν => ?_
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto (μs := id)
    (L := 𝓝 ν) tendsto_id (E := one) (by rw [isClopen_one.frontier_eq]; simp)
  exact (NNReal.continuous_coe.tendsto _).comp h

/-- **Limits through cluster points**: in a compact space, `g(u N) → L` for a continuous `g` iff
`g x = L` at every cluster point `x` of `(u N)`. -/
theorem tendsto_comp_iff_forall_mapClusterPt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {u : ℕ → X} {g : X → ℝ} (hg : Continuous g) {L : ℝ} :
    Tendsto (g ∘ u) atTop (𝓝 L) ↔ ∀ x, MapClusterPt x atTop u → g x = L := by
  constructor
  · intro h x hx
    have hgx : ClusterPt (g x) (map (g ∘ u) atTop) :=
      ClusterPt.map hx hg.continuousAt (tendsto_map'_iff.2 tendsto_map)
    have hL : ClusterPt (g x) (𝓝 L) := hgx.mono h
    by_contra hne
    exact hL.ne (disjoint_iff.1 (disjoint_nhds_nhds.2 hne))
  · intro h
    by_contra hne
    rw [Metric.tendsto_atTop] at hne
    push Not at hne
    obtain ⟨ε, hε, hfreq⟩ := hne
    let S : Set ℕ := {n | ε ≤ dist ((g ∘ u) n) L}
    have hfr : ∃ᶠ n in atTop, n ∈ S := Filter.frequently_atTop.2 hfreq
    haveI : NeBot (atTop ⊓ 𝓟 S) := Filter.frequently_iff_neBot.1 hfr
    obtain ⟨x, -, hx⟩ := isCompact_univ.exists_clusterPt (f := map u (atTop ⊓ 𝓟 S))
      (le_principal_iff.2 univ_mem)
    have hgx := h x (hx.mono (map_mono inf_le_left))
    have hcl : ClusterPt (g x) (map (g ∘ u) (atTop ⊓ 𝓟 S)) :=
      ClusterPt.map hx hg.continuousAt (tendsto_map'_iff.2 tendsto_map)
    have hsub : map (g ∘ u) (atTop ⊓ 𝓟 S) ≤ 𝓟 {y | ε ≤ dist y L} := by
      rw [le_principal_iff, Filter.mem_map]
      exact mem_inf_of_right (mem_principal_self S)
    have hmem : g x ∈ closure {y | ε ≤ dist y L} := mem_closure_iff_clusterPt.2 (hcl.mono hsub)
    have hS : IsClosed {y : ℝ | ε ≤ dist y L} :=
      isClosed_le continuous_const (continuous_id.dist continuous_const)
    rw [hS.closure_eq, Set.mem_setOf_eq, hgx, dist_self] at hmem
    linarith

/-- **Density `1/2` through empirical measures**, for every bit sequence: every limit point of
the empirical measures gives the cylinder `[1]` mass `1/2`. -/
theorem halfDensity_iff_mapClusterPt (b : ℕ → Bool) : Symmetry.HalfDensity b ↔
    ∀ ν : ProbabilityMeasure (ℕ → Bool), MapClusterPt ν atTop (empirical b) →
      (ν one : ℝ) = 1 / 2 := by
  rw [← tendsto_comp_iff_forall_mapClusterPt continuous_mass_one,
    ProblemTwo.halfDensity_iff_tendsto, ← tendsto_add_atTop_iff_nat 1]
  refine tendsto_congr fun N => ?_
  simp only [Function.comp, empirical_one]

/-- **Problem 2 through empirical measures**: Problem 2 holds iff every limit point of the
empirical measures of the center column gives the cylinder `[1]` mass `1/2`. -/
theorem problem2_iff_mapClusterPt : Rule30Prize.Problem2 ↔
    ∀ ν : ProbabilityMeasure (ℕ → Bool), MapClusterPt ν atTop (empirical c) →
      (ν one : ℝ) = 1 / 2 :=
  halfDensity_iff_mapClusterPt c

/-! ### Normal sequences are the generic points of the fair coin -/

/-- The cylinder of sequences starting with the word `w`. -/
def cyl {n : ℕ} (w : Fin n → Bool) : Set (ℕ → Bool) := {v | ∀ j : Fin n, v j = w j}

theorem isClopen_cyl {n : ℕ} (w : Fin n → Bool) : IsClopen (cyl w) := by
  have : cyl w = ⋂ j : Fin n, (fun v : ℕ → Bool => v j) ⁻¹' {w j} := by
    ext v
    simp [cyl]
  rw [this]
  exact isClopen_iInter_of_finite fun j =>
    (isClopen_discrete {w j}).preimage (continuous_apply (A := fun _ : ℕ => Bool) j)

theorem measurableSet_cyl {n : ℕ} (w : Fin n → Bool) : MeasurableSet (cyl w) :=
  (isClopen_cyl w).isClosed.measurableSet

/-- The fair-coin measure as a point of the space of probability measures. -/
noncomputable def coinsPM : ProbabilityMeasure (ℕ → Bool) :=
  ⟨RandomConfigurations.coins ℕ, inferInstance⟩

theorem coinsPM_cyl {n : ℕ} (w : Fin n → Bool) : (coinsPM (cyl w) : ℝ) = (2 : ℝ)⁻¹ ^ n := by
  have hset : cyl w = Set.pi (Finset.range n : Set ℕ)
      (fun j => {if h : j < n then w ⟨j, h⟩ else false}) := by
    ext v
    simp only [cyl, Set.mem_setOf_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
      Set.mem_singleton_iff]
    constructor
    · intro h j hj
      rw [dif_pos hj]
      exact h ⟨j, hj⟩
    · intro h j
      have := h j j.2
      rwa [dif_pos j.2] at this
  rw [ProbabilityMeasure.coeFn_def, ENNReal.coe_toNNReal_eq_toReal]
  show (RandomConfigurations.coins ℕ (cyl w)).toReal = _
  rw [hset, RandomConfigurations.coins_pi, Finset.prod_congr rfl fun j _ =>
    RandomConfigurations.coin_singleton _, Finset.prod_const, Finset.card_range,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]

/-- **Normal sequences are the generic points of the fair-coin measure**: a bit sequence is normal
iff its empirical measures converge weakly to the fair-coin measure on `{0,1}^ℕ`. Cylinders are
clopen (portmanteau), and they form a π-system of arbitrarily small neighbourhoods (Mathlib's
`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`). -/
theorem isNormal_iff_tendsto_empirical (b : ℕ → Bool) :
    StrongerStatements.IsNormal b ↔ Tendsto (empirical b) atTop (𝓝 coinsPM) := by
  have hfreq : ∀ {n : ℕ} (w : Fin n → Bool) (N : ℕ), ((empirical b N) (cyl w) : ℝ) =
      (#{i ∈ range (N + 1) | ∀ j : Fin n, b (i + j) = w j} : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    intro n w N
    classical
    rw [empirical_apply b N (measurableSet_cyl w)]
    congr 3
    refine filter_congr fun i _ => ?_
    simp only [cyl, Set.mem_setOf_eq, Mixing.shift_iterate, Nat.add_comm]
  have hnorm : StrongerStatements.IsNormal b ↔ ∀ n (w : Fin n → Bool),
      Tendsto (fun N => ((empirical b N) (cyl w) : ℝ)) atTop (𝓝 ((2 : ℝ)⁻¹ ^ n)) := by
    refine forall_congr' fun n => forall_congr' fun w => ?_
    rw [← tendsto_add_atTop_iff_nat 1]
    exact tendsto_congr fun N => (hfreq w N).symm
  rw [hnorm]
  constructor
  · intro h
    refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
      (S := {s | ∃ n, ∃ w : Fin n → Bool, s = cyl w}) ?_ ?_ ?_ ?_
    · rintro s ⟨n, w, rfl⟩ t ⟨m, w', rfl⟩ ⟨v, hv1, hv2⟩
      rcases le_total n m with hnm | hmn
      · refine ⟨m, w', Set.ext fun u => ⟨fun hu => hu.2, fun hu => ⟨fun j => ?_, hu⟩⟩⟩
        have h1 := hu ⟨j, by omega⟩
        have h2 := hv2 ⟨j, by omega⟩
        have h3 := hv1 j
        dsimp only at h1 h2 h3
        rw [h1, ← h2, h3]
      · refine ⟨n, w, Set.ext fun u => ⟨fun hu => hu.1, fun hu => ⟨hu, fun j => ?_⟩⟩⟩
        have h1 := hu ⟨j, by omega⟩
        have h2 := hv1 ⟨j, by omega⟩
        have h3 := hv2 j
        dsimp only at h1 h2 h3
        rw [h1, ← h2, h3]
    · rintro s ⟨n, w, rfl⟩
      exact measurableSet_cyl w
    · intro u hu x hx
      obtain ⟨L, hL⟩ := Genericity.exists_prefix_subset (hu.mem_nhds hx)
      refine ⟨cyl fun j : Fin L => x j, ⟨L, _, rfl⟩,
        (isClopen_cyl _).isOpen.mem_nhds fun j => rfl, fun v hv => hL fun t ht => ?_⟩
      exact hv ⟨t, ht⟩
    · rintro s ⟨n, w, rfl⟩
      have h' := h n w
      rw [← coinsPM_cyl w] at h'
      exact NNReal.tendsto_coe.1 h'
  · intro h n w
    have h' := (NNReal.continuous_coe.tendsto _).comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h (isClopen_cyl w))
    rw [coinsPM_cyl] at h'
    exact h'

/-- **Almost every trace is generic for the fair coin**: for almost every configuration, the
empirical measures of its center trace converge weakly to the fair-coin measure. -/
theorem ae_tendsto_empirical_trace :
    ∀ᵐ x ∂(RandomConfigurations.coins ℤ),
      Tendsto (empirical (Genericity.trace x)) atTop (𝓝 coinsPM) :=
  RandomConfigurations.ae_isNormal_trace.mono fun _ h =>
    (isNormal_iff_tendsto_empirical _).1 h

end Rule30Equivalents.EmpiricalMeasures

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
-/

namespace Rule30Equivalents.EmpiricalMeasures

open MeasureTheory Filter Topology Finset Ruliology.CellularAutomata

/-- The cylinder of sequences starting with `1`. -/
def one : Set (ℕ → Bool) := {v | v 0 = true}

theorem isClopen_one : IsClopen one :=
  (isClopen_discrete {true}).preimage (continuous_apply (A := fun _ : ℕ => Bool) 0)

theorem measurableSet_one : MeasurableSet one :=
  (measurableSet_singleton true).preimage (measurable_pi_apply 0)

/-- The empirical measure of `b` over the times `0, …, N`. -/
noncomputable def empirical (b : ℕ → Bool) (N : ℕ) : ProbabilityMeasure (ℕ → Bool) :=
  ⟨((N : ENNReal) + 1)⁻¹ • ∑ n ∈ range (N + 1), Measure.dirac (Mixing.shift^[n] b), by
    constructor
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [measure_univ, sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    push_cast
    exact ENNReal.inv_mul_cancel (by simp) (by simp)⟩

theorem empirical_apply_one (b : ℕ → Bool) (N : ℕ) :
    (empirical b N : Measure (ℕ → Bool)) one =
      ((N : ENNReal) + 1)⁻¹ * (#{n ∈ range (N + 1) | b n = true} : ENNReal) := by
  classical
  show (((N : ENNReal) + 1)⁻¹ • ∑ n ∈ range (N + 1),
    Measure.dirac (Mixing.shift^[n] b)) one = _
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul, ← sum_boole]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [Measure.dirac_apply' _ measurableSet_one, Set.indicator_apply]
  simp only [one, Set.mem_setOf_eq, Mixing.shift_iterate, zero_add, Pi.one_apply]

/-- **The mass of `[1]` is the proportion of `1`s** among `b 0, …, b N`. -/
theorem empirical_one (b : ℕ → Bool) (N : ℕ) :
    ((empirical b N) one : ℝ) =
      (((List.range (N + 1)).filter b).length : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  rw [ProbabilityMeasure.coeFn_def, ENNReal.coe_toNNReal_eq_toReal, empirical_apply_one,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ProblemTwo.count_eq_sum,
    sum_boole, div_eq_inv_mul]
  push_cast
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp

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

end Rule30Equivalents.EmpiricalMeasures

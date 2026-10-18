import Rule30Equivalents.RandomConfigurations
import Rule30Equivalents.Preimages
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.TopologicalEntropy.Semiconj
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Dynamics.Ergodic.Function

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
* `tendsto_birkhoffAverage_integral`: **the L² ergodic theorem for rule 30** (von Neumann, through
  Mathlib's `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` for the Koopman
  operator `koopman`): for every `g ∈ L²` the averages `(g + g ∘ F + ⋯ + g ∘ F^(N-1)) / N`
  converge in `L²` to the constant `∫ g`; the limit is invariant, hence constant by ergodicity.
* `ae_existsUnique_preimage`, `residual_existsUnique_preimage`: **rule 30 is invertible almost
  everywhere and generically**: almost every configuration, and a comeager set of them, show `010`
  arbitrarily far to the right and so have exactly one preimage
  (`Preimages.eq_of_evol_one_eq_of_frequently`). Hence rule 30 is injective on a set of full
  measure (`exists_injOn_ae`), though not injective (`Preimages.exists_ne_left_eq`), and every
  row of the space-time diagram of almost every configuration determines it
  (`ae_injective_iterate`).
* `mixing_all_orders`: **rule 30 is mixing of all orders**: cylinders at times whose gaps exceed
  the width of their windows are independent (`measure_biInter_preimage_cylinder`), so
  `μ(F^{-t₀} A₀ ∩ ⋯ ∩ F^{-tₙ₋₁} Aₙ₋₁) → μ(A₀) ⋯ μ(Aₙ₋₁)` as the gaps between the times grow.
* `ae_frequently_mem`, `residual_frequently_mem`: for almost every configuration, and for a
  comeager set of configurations, the orbit enters every nonempty open set at arbitrarily large
  times, so its omega-limit set is all of `{0,1}^ℤ` (by ergodicity, and by topological mixing and
  Baire).
* `ae_rightHalves_frequently`: for almost every configuration, every pattern appears at the cells
  `0, …, N - 1` at arbitrarily late times, so every sequence is a limit point of the right halves of
  the rows (for the seed, Kopra's theorem gives infinitely many limit points).
* `evol_flip_front`, `sensitive`: the right front of a perturbation moves at speed one, and rule 30
  is sensitive to initial conditions.
* `log_two_le_coverEntropy`: **rule 30 has topological entropy at least `log 2`** (Mathlib's
  `coverEntropy`): the center trace is a uniformly continuous factor map onto the full shift on
  `{0,1}^ℕ`, whose entropy is at least `log 2` (`log_two_le_coverEntropy_shift`). And
  `coverEntropy_le_two_mul_log_two`: **at most `2 log 2`**, since every entourage contains
  agreement on a window `[-N, N]` (`exists_windowRel_subset`) and one configuration per pattern on
  `[-(N + n), N + n]` covers `n` steps (`coverMincard_le`).
* `measurePreserving_path`: along any path that never moves right, `p (t + 1) ≤ p t`, the cells
  `F^t(x)_{p t}` are independent fair coins (`measure_prefix_path`); so for almost every
  configuration they form a normal sequence (`ae_isNormal_path`). Columns are the constant paths
  (`ae_isNormal_columns`), and the left edge of the light cone is `p t = -t`. Along a right
  diagonal the cells are not fair coins: `(t, a)` and `(t + 1, a + 1)` agree with probability
  `1/4` (`measure_diag_eq`).
* `ae_isNormal_rows`: for almost every configuration the right half of every row is normal (every
  iterate preserves the measure).
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

/-! ### Cells along paths -/

/-- **Along a path that never moves right, every prefix has probability `2^-(n+1)`**: for
`p (t + 1) ≤ p t`, the cells `F^t(x)_{p t}` up to time `n` do not see the coins left of
`p n - n`, and the cell at time `n + 1` sits beyond their light cone (`measure_inter_window`). -/
theorem measure_prefix_path {p : ℕ → ℤ} (hp : ∀ t, p (t + 1) ≤ p t) (w : ℕ → Bool) :
    ∀ n : ℕ, coins ℤ {x | ∀ t ≤ n, evol x t (p t) = w t} = 2⁻¹ ^ (n + 1)
  | 0 => by
    have h := measure_window 0 {p 0} fun _ => w 0
    rw [Finset.card_singleton] at h
    rw [← h]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_singleton, forall_eq]
    constructor
    · intro hx
      exact hx 0 le_rfl
    · intro hx t ht
      obtain rfl : t = 0 := by omega
      exact hx
  | n + 1 => by
    have hanti : Antitone p := antitone_nat_of_succ_le hp
    set A := {x : ℤ → Bool | ∀ t ≤ n, evol x t (p t) = w t} with hAdef
    have hA : MeasurableSet A := by
      simp only [hAdef, Set.setOf_forall]
      exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
        measurable_evol t (p t) (measurableSet_singleton _)
    have hAm : ∀ x q, q < p n - n → (Function.update x q (!x q) ∈ A ↔ x ∈ A) := by
      intro x q hq
      simp only [hAdef, Set.mem_setOf_eq]
      refine forall₂_congr fun t ht => ?_
      have := hanti ht
      rw [AlgebraicDegree.evol_update_of_far (Or.inl (by omega))]
    have h := measure_inter_window hA hAm (n + 1) (fun _ => w (n + 1)) {p (n + 1)}
      fun i hi => by
        rw [Finset.mem_singleton] at hi
        have := hp n
        push_cast
        omega
    have hset : {x : ℤ → Bool | ∀ t ≤ n + 1, evol x t (p t) = w t} =
        A ∩ {x | ∀ i ∈ ({p (n + 1)} : Finset ℤ), evol x (n + 1) i = w (n + 1)} := by
      ext x
      simp only [hAdef, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_singleton, forall_eq]
      constructor
      · intro hx
        exact ⟨fun t ht => hx t (by omega), hx (n + 1) le_rfl⟩
      · rintro ⟨h1, h2⟩ t ht
        rcases Nat.lt_or_ge t (n + 1) with h' | h'
        · exact h1 t (by omega)
        · obtain rfl : t = n + 1 := by omega
          exact h2
    rw [hset, h, measure_prefix_path hp w n, Finset.card_singleton, pow_one, ← pow_succ]

/-- **The cells along a path that never moves right are independent fair coins**: for
`p (t + 1) ≤ p t`, the map `x ↦ (F^t(x)_{p t})ₜ` carries `coins ℤ` to `coins ℕ`. Columns are the
constant paths; the left edge of the light cone is `p t = -t`. -/
theorem measurePreserving_path {p : ℕ → ℤ} (hp : ∀ t, p (t + 1) ≤ p t) :
    MeasurePreserving (fun (x : ℤ → Bool) (t : ℕ) => evol x t (p t)) (coins ℤ) (coins ℕ) :=
  measurePreserving_of_measure_prefix (measurable_pi_lambda _ fun t => measurable_evol t (p t))
    (measure_prefix_path hp)

/-- For almost every configuration, the cells along a given path that never moves right form a
normal sequence. -/
theorem ae_isNormal_path {p : ℕ → ℤ} (hp : ∀ t, p (t + 1) ≤ p t) :
    ∀ᵐ x ∂(coins ℤ), StrongerStatements.IsNormal fun t => evol x t (p t) :=
  (measurePreserving_path hp).quasiMeasurePreserving.ae ae_isNormal

/-- **Right diagonals are not fair coins**: the cells `(t, a)` and `(t + 1, a + 1)` agree with
probability `1/4`, not `1/2`, because `F^(t+1)(x)_{a+1} = F^t(x)_a ⊕ (F^t(x)_{a+1} ∨ F^t(x)_{a+2})`
and the cells `a + 1`, `a + 2` of `F^t(x)` are white together with probability `1/4`. -/
theorem measure_diag_eq (t : ℕ) (a : ℤ) :
    coins ℤ {x | evol x (t + 1) (a + 1) = evol x t a} = 4⁻¹ := by
  have hset : {x : ℤ → Bool | evol x (t + 1) (a + 1) = evol x t a} =
      {x | ∀ i ∈ ({a + 1, a + 2} : Finset ℤ), evol x t i = (fun _ => false) i} := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
      forall_eq]
    rw [AlgebraicDegree.evol_succ, show a + 1 - 1 = a by ring, show a + 1 + 1 = a + 2 by ring]
    cases evol x t a <;> cases evol x t (a + 1) <;> cases evol x t (a + 2) <;> decide
  rw [hset, measure_window t {a + 1, a + 2} (fun _ => false),
    Finset.card_pair (by omega : a + 1 ≠ a + 2), ← ENNReal.inv_pow]
  norm_num

/-- **Normal columns almost surely**: for almost every configuration, every column of its
space-time diagram is normal (columns are constant paths). -/
theorem ae_isNormal_columns :
    ∀ᵐ x ∂(coins ℤ), ∀ p : ℤ, StrongerStatements.IsNormal fun t => evol x t p :=
  ae_all_iff.2 fun p => ae_isNormal_path (p := fun _ => p) fun _ => le_rfl

/-- **Normal rows almost surely**: for almost every configuration, the right half of every row
of its space-time diagram is normal. Restricting to the cells `n ≥ 0` maps the fair-coin measure to
the fair-coin measure on `{0,1}^ℕ`, and every iterate preserves it. -/
theorem ae_isNormal_rows :
    ∀ᵐ x ∂(coins ℤ), ∀ t : ℕ, StrongerStatements.IsNormal fun n : ℕ => evol x t n := by
  have hright : MeasurePreserving (fun (x : ℤ → Bool) (n : ℕ) => x n) (coins ℤ) (coins ℕ) :=
    ⟨by fun_prop, Measure.map_infinitePi_infinitePi_of_inj (Nat.cast_injective (R := ℤ))⟩
  refine ae_all_iff.2 fun t => ?_
  exact ((hright.comp (measurePreserving_evol t)).quasiMeasurePreserving.ae ae_isNormal)

/-! ### Rule 30 is invertible almost everywhere -/

/-- A disjunctive sequence shows every word beyond every position. -/
theorem exists_ge_of_disjunctive {v : ℕ → Bool} (hv : Disjunctive v) {n : ℕ} (w : Fin n → Bool)
    (N : ℕ) : ∃ i ≥ N, ∀ j : Fin n, v (i + j) = w j := by
  obtain ⟨i, hi⟩ := hv (N + n) fun j => if h : N ≤ j.1 then w ⟨j.1 - N, by omega⟩ else false
  refine ⟨i + N, Nat.le_add_left N i, fun j => ?_⟩
  have := hi ⟨N + j.1, by omega⟩
  simp only [Nat.le_add_right, dif_pos, Nat.add_sub_cancel_left] at this
  rw [show i + N + j.1 = i + (N + j.1) by ring]
  exact this

/-- **Rule 30 is invertible almost everywhere**: almost every configuration has exactly one
preimage. Its right half is normal (`ae_isNormal_rows`), so it shows `010` arbitrarily far to the
right, and such a configuration has only one preimage
(`Preimages.eq_of_evol_one_eq_of_frequently`); it has one by `surjective_evol_one`. -/
theorem ae_existsUnique_preimage : ∀ᵐ y ∂(coins ℤ), ∃! x : ℤ → Bool, evol x 1 = y := by
  filter_upwards [ae_isNormal_rows] with y hy
  have hd : Disjunctive fun n : ℕ => evol y 0 n := fun n w =>
    StrongerStatements.disjunctive_of_isNormal (hy 0) n w
  obtain ⟨x, hx⟩ := surjective_evol_one y
  refine ⟨x, hx, fun x' hx' =>
    Preimages.eq_of_evol_one_eq_of_frequently (hx'.trans hx.symm) fun n => ?_⟩
  obtain ⟨i, hi, hw⟩ := exists_ge_of_disjunctive hd ![false, true, false] n.toNat
  refine ⟨i, by omega, ?_⟩
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    add_zero] at h0 h1 h2
  push_cast at h0 h1 h2
  rw [hx']
  exact ⟨h0, h1, h2⟩

/-- **Rule 30 is injective on a set of full measure**, though not injective. -/
theorem exists_injOn_ae :
    ∃ E : Set (ℤ → Bool), coins ℤ Eᶜ = 0 ∧ Set.InjOn (fun x : ℤ → Bool => evol x 1) E := by
  have h := (measurePreserving_evol 1).quasiMeasurePreserving.ae ae_existsUnique_preimage
  refine ⟨{x | ∃! x' : ℤ → Bool, evol x' 1 = evol x 1}, ae_iff.1 h, fun x hx x'' _ hxx => ?_⟩
  obtain ⟨z, -, hz⟩ := hx
  exact (hz x rfl).trans (hz x'' hxx.symm).symm

/-- The configurations that show `010` arbitrarily far to the right form a comeager set. -/
theorem residual_frequently_window :
    {y : ℤ → Bool | ∀ n : ℤ, ∃ q ≥ n, y q = false ∧ y (q + 1) = true ∧ y (q + 2) = false} ∈
      residual (ℤ → Bool) := by
  have hU : ∀ N : ℕ, {y : ℤ → Bool | ∃ q ≥ (N : ℤ),
      y q = false ∧ y (q + 1) = true ∧ y (q + 2) = false} ∈ residual (ℤ → Bool) := by
    intro N
    refine residual_of_dense_open ?_ ?_
    · have hev : ∀ (q : ℤ) (b : Bool), IsOpen {y : ℤ → Bool | y q = b} := fun q b =>
        (isOpen_discrete ({b} : Set Bool)).preimage (continuous_apply (A := fun _ : ℤ => Bool) q)
      simp only [Set.setOf_exists, Set.setOf_and]
      exact isOpen_iUnion fun q => isOpen_const.inter
        ((hev q false).inter ((hev (q + 1) true).inter (hev (q + 2) false)))
    · rw [dense_iff_inter_open]
      rintro V hV ⟨v, hv⟩
      obtain ⟨n, hn⟩ := exists_window_subset (hV.mem_nhds hv)
      -- put `010` at `q = n + N + 1`, beyond the window
      set q : ℤ := n + N + 1
      refine ⟨fun p => if p = q then false else if p = q + 1 then true else if p = q + 2 then false
        else v p, hn fun p _ hp => ?_, q, by omega, by simp, by simp, by simp⟩
      simp only [show p ≠ q by omega, show p ≠ q + 1 by omega, show p ≠ q + 2 by omega, if_false]
  refine Filter.mem_of_superset (countable_iInter_mem.2 hU) fun y hy n => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
  obtain ⟨q, hq, h⟩ := hy n.toNat
  exact ⟨q, by omega, h⟩

/-- **Rule 30 is invertible on a comeager set**: a comeager set of configurations has exactly
one preimage. -/
theorem residual_existsUnique_preimage :
    {y : ℤ → Bool | ∃! x : ℤ → Bool, evol x 1 = y} ∈ residual (ℤ → Bool) := by
  refine Filter.mem_of_superset residual_frequently_window fun y hy => ?_
  obtain ⟨x, hx⟩ := surjective_evol_one y
  refine ⟨x, hx, fun x' hx' =>
    Preimages.eq_of_evol_one_eq_of_frequently (hx'.trans hx.symm) fun n => ?_⟩
  rw [hx']
  exact hy n

/-- **Every row determines almost every configuration**: for almost every configuration `x`, no
other configuration has the same image as `x` under any iterate of rule 30. Each `F^(n+1) x` has
a unique preimage almost surely (`ae_existsUnique_preimage`, carried back along `F^(n+1)`, which
preserves the measure), so `F^(n+1) x' = F^(n+1) x` gives `F^n x' = F^n x`. -/
theorem ae_injective_iterate :
    ∀ᵐ x ∂(coins ℤ), ∀ (n : ℕ) (x' : ℤ → Bool), evol x' n = evol x n → x' = x := by
  have h : ∀ᵐ x ∂(coins ℤ), ∀ n : ℕ, ∃! z : ℤ → Bool, evol z 1 = evol x (n + 1) :=
    ae_all_iff.2 fun n =>
      (measurePreserving_evol (n + 1)).quasiMeasurePreserving.ae ae_existsUnique_preimage
  filter_upwards [h] with x hx n
  induction n with
  | zero => exact fun x' hx' => hx'
  | succ n ih =>
    intro x' hx'
    apply ih
    obtain ⟨z, -, hz⟩ := hx n
    have e1 : evol (evol x' n) 1 = evol x (n + 1) := by
      rw [← hx']
      exact funext fun p => Rule30ZeroBoundaryBarriers.evol_restart x' n 1 p
    have e2 : evol (evol x n) 1 = evol x (n + 1) :=
      funext fun p => Rule30ZeroBoundaryBarriers.evol_restart x n 1 p
    exact (hz _ e1).trans (hz _ e2).symm

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

/-! ### Mixing of all orders -/

/-- With gaps of at least `G` between consecutive times, each time trails every later one by at
least `G`. -/
theorem add_le_of_gaps {t : ℕ → ℕ} {G : ℕ} :
    ∀ {n : ℕ}, (∀ j, j + 1 < n + 1 → t j + G ≤ t (j + 1)) → ∀ j < n, t j + G ≤ t n
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, ht, j, hj => by
    have hn : t n + G ≤ t (n + 1) := ht n (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have := add_le_of_gaps (n := n) (fun i hi => ht i (by omega)) j hj
      omega
    · exact hn

/-- **Cylinders at well-separated times are independent**: if the windows `I j` lie in `[a, b]`
and consecutive times differ by more than `b - a`, the cylinders over the windows `I j` of the
images at the times `t j` are independent. Each new cylinder sits beyond the light cone of the
earlier ones (`measure_inter_preimage_cylinder`). -/
theorem measure_biInter_preimage_cylinder {I : ℕ → Finset ℤ} {S : ∀ j, Set (I j → Bool)}
    (hS : ∀ j, MeasurableSet (S j)) {a b : ℤ} {G : ℕ} (hG : b - a < G) (t : ℕ → ℕ) :
    ∀ n : ℕ, (∀ j < n, ∀ i ∈ I j, a ≤ i ∧ i ≤ b) → (∀ j, j + 1 < n → t j + G ≤ t (j + 1)) →
      coins ℤ (⋂ j ∈ Finset.range n, (fun x => evol x (t j)) ⁻¹' cylinder (I j) (S j)) =
        ∏ j ∈ Finset.range n, coins ℤ (cylinder (I j) (S j))
  | 0, _, _ => by simp
  | n + 1, hI, ht => by
    have ih := measure_biInter_preimage_cylinder hS hG t n (fun j hj => hI j (by omega))
      fun j hj => ht j (by omega)
    have hlag := add_le_of_gaps ht
    set E := ⋂ j ∈ Finset.range n, (fun x : ℤ → Bool => evol x (t j)) ⁻¹' cylinder (I j) (S j)
      with hE
    have hEm : MeasurableSet E := Finset.measurableSet_biInter _ fun j _ =>
      measurable_evol_all (t j) (MeasurableSet.cylinder (I j) (hS j))
    -- `E` does not see the coins left of `b - t n + 1`
    have hEinv : ∀ x p, p < b - t n + 1 → (Function.update x p (!x p) ∈ E ↔ x ∈ E) := by
      intro x p hp
      simp only [hE, Set.mem_iInter, Set.mem_preimage, mem_cylinder]
      refine forall₂_congr fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      have hres : (I j).restrict (evol (Function.update x p (!x p)) (t j)) =
          (I j).restrict (evol x (t j)) := funext fun i => by
        have hi := hI j (by omega) i i.2
        have := hlag j hj'
        exact AlgebraicDegree.evol_update_of_far (Or.inl (by omega)) x _
      rw [hres]
    have hsep : ∀ i ∈ I n, i - (t n : ℤ) < b - t n + 1 := fun i hi => by
      have := (hI n (by omega) i hi).2
      omega
    rw [Finset.range_add_one, Finset.set_biInter_insert, Set.inter_comm,
      Finset.prod_insert Finset.notMem_range_self,
      measure_inter_preimage_cylinder hEm hEinv (t n) hsep (hS n), ih, mul_comm]

theorem symmDiff_biInter_subset {X Y : ℕ → Set (ℤ → Bool)} (s : Finset ℕ) :
    symmDiff (⋂ j ∈ s, X j) (⋂ j ∈ s, Y j) ⊆ ⋃ j ∈ s, symmDiff (X j) (Y j) := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_iInter, Set.mem_iUnion, not_forall] at hx ⊢
  rcases hx with ⟨hX, j, hj, hjY⟩ | ⟨hY, j, hj, hjX⟩
  · exact ⟨j, hj, Or.inl ⟨hX j hj, hjY⟩⟩
  · exact ⟨j, hj, Or.inr ⟨hY j hj, hjX⟩⟩

theorem abs_prod_sub_prod_le {x y : ℕ → ℝ} (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) (n : ℕ) :
    |∏ j ∈ Finset.range n, x j - ∏ j ∈ Finset.range n, y j| ≤
      ∑ j ∈ Finset.range n, |x j - y j| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
    set P := ∏ j ∈ Finset.range n, x j
    set Q := ∏ j ∈ Finset.range n, y j
    have h0 : 0 ≤ P := Finset.prod_nonneg fun j _ => (hx j).1
    have h1 : P ≤ 1 := Finset.prod_le_one (fun j _ => (hx j).1) fun j _ => (hx j).2
    rw [show P * x n - Q * y n = P * (x n - y n) + (P - Q) * y n by ring]
    calc |P * (x n - y n) + (P - Q) * y n| ≤ |P * (x n - y n)| + |(P - Q) * y n| :=
          abs_add_le _ _
      _ = P * |x n - y n| + |P - Q| * y n := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (hy n).1]
      _ ≤ 1 * |x n - y n| + |P - Q| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hy n).2 (abs_nonneg _))
      _ ≤ _ := by linarith

/-- **Rule 30 is mixing of all orders** for the fair-coin measure: for measurable sets
`A 0, …, A (n - 1)` and times `t 0, …, t (n - 1)` with large enough gaps, the events
`F^(t j) x ∈ A j` are almost independent. For cylinders they are independent once the gaps
exceed the width of the windows (`measure_biInter_preimage_cylinder`); every measurable set is close
to a cylinder, and `F^t` preserves the measure. -/
theorem mixing_all_orders {A : ℕ → Set (ℤ → Bool)} (hA : ∀ j, MeasurableSet (A j)) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℕ, ∀ t : ℕ → ℕ, (∀ j, j + 1 < n → t j + G ≤ t (j + 1)) →
      |(coins ℤ).real (⋂ j ∈ Finset.range n, (fun x => evol x (t j)) ⁻¹' A j) -
        ∏ j ∈ Finset.range n, (coins ℤ).real (A j)| < ε := by
  set δ := ε / (2 * (n + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  choose I S hS happrox using fun j => exists_cylinder_approx (hA j) hδ0
  obtain ⟨a, ha⟩ := ((Finset.range n).biUnion I).bddBelow
  obtain ⟨b, hb⟩ := ((Finset.range n).biUnion I).bddAbove
  refine ⟨(b - a + 1).toNat, fun t ht => ?_⟩
  have hG : b - a < ((b - a + 1).toNat : ℤ) := by
    have := Int.self_le_toNat (b - a + 1)
    omega
  have hab : ∀ j < n, ∀ i ∈ I j, a ≤ i ∧ i ≤ b := fun j hj i hi => by
    have hmem : i ∈ (Finset.range n).biUnion I :=
      Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, hi⟩
    exact ⟨ha (Finset.mem_coe.2 hmem), hb (Finset.mem_coe.2 hmem)⟩
  have hcyl : (coins ℤ).real
      (⋂ j ∈ Finset.range n, (fun x => evol x (t j)) ⁻¹' cylinder (I j) (S j)) =
        ∏ j ∈ Finset.range n, (coins ℤ).real (cylinder (I j) (S j)) := by
    rw [measureReal_def, measure_biInter_preimage_cylinder hS hG t n hab ht, ENNReal.toReal_prod]
    rfl
  -- replacing each `A j` by its cylinder
  have e1 : |(coins ℤ).real (⋂ j ∈ Finset.range n, (fun x => evol x (t j)) ⁻¹' A j) -
      (coins ℤ).real (⋂ j ∈ Finset.range n, (fun x => evol x (t j)) ⁻¹' cylinder (I j) (S j))| ≤
        n * δ := by
    refine (abs_measureReal_sub_le _ _ _).trans ?_
    refine (measureReal_mono (symmDiff_biInter_subset _) (measure_ne_top _ _)).trans
      ((measureReal_biUnion_finset_le _ _).trans ?_)
    calc ∑ j ∈ Finset.range n, (coins ℤ).real (symmDiff ((fun x => evol x (t j)) ⁻¹' A j)
          ((fun x => evol x (t j)) ⁻¹' cylinder (I j) (S j)))
        ≤ ∑ _j ∈ Finset.range n, δ := Finset.sum_le_sum fun j _ => by
          rw [← Set.preimage_symmDiff, (measurePreserving_evol (t j)).measureReal_preimage
            ((hA j).symmDiff (MeasurableSet.cylinder _ (hS j))).nullMeasurableSet, symmDiff_comm]
          exact (happrox j).le
      _ = n * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e2 : |∏ j ∈ Finset.range n, (coins ℤ).real (cylinder (I j) (S j)) -
      ∏ j ∈ Finset.range n, (coins ℤ).real (A j)| ≤ n * δ := by
    refine (abs_prod_sub_prod_le (fun j => ⟨measureReal_nonneg, measureReal_le_one⟩)
      (fun j => ⟨measureReal_nonneg, measureReal_le_one⟩) n).trans ?_
    calc ∑ j ∈ Finset.range n, |(coins ℤ).real (cylinder (I j) (S j)) - (coins ℤ).real (A j)|
        ≤ ∑ _j ∈ Finset.range n, δ := Finset.sum_le_sum fun j _ =>
          (abs_measureReal_sub_le _ _ _).trans (happrox j).le
      _ = n * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hfin : 2 * (n * δ) < ε := by
    rw [hδ, show 2 * ((n : ℝ) * (ε / (2 * (n + 1)))) = ε * n / (n + 1) by field_simp,
      div_lt_iff₀ hn1]
    linarith
  calc |(coins ℤ).real (⋂ j ∈ Finset.range n, (fun x => evol x (t j)) ⁻¹' A j) -
        ∏ j ∈ Finset.range n, (coins ℤ).real (A j)|
      ≤ |(coins ℤ).real (⋂ j ∈ Finset.range n, (fun x => evol x (t j)) ⁻¹' A j) -
          (coins ℤ).real
            (⋂ j ∈ Finset.range n, (fun x => evol x (t j)) ⁻¹' cylinder (I j) (S j))| +
        |∏ j ∈ Finset.range n, (coins ℤ).real (cylinder (I j) (S j)) -
          ∏ j ∈ Finset.range n, (coins ℤ).real (A j)| := by
        rw [← hcyl]
        exact abs_sub_le _ _ _
    _ ≤ n * δ + n * δ := add_le_add e1 e2
    _ < ε := by linarith

/-! ### The L² ergodic theorem -/

section MeanErgodic

/-- The Koopman operator of rule 30 on `L²` of the fair-coin measure: `g ↦ g ∘ F`. -/
noncomputable def koopman : Lp ℝ 2 (coins ℤ) →L[ℝ] Lp ℝ 2 (coins ℤ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℤ → Bool => evol x 1)
    (measurePreserving_evol 1)).toContinuousLinearMap

theorem norm_koopman_le : ‖koopman‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

/-- **The L² ergodic theorem for rule 30** (von Neumann's mean ergodic theorem): for every
`g ∈ L²`, the averages `(g + g ∘ F + ⋯ + g ∘ F^(N-1)) / N` converge in `L²` to a constant, since
the only functions invariant under rule 30 are the constants (`ergodic_evol_one`). -/
theorem exists_tendsto_birkhoffAverage_const (g : Lp ℝ 2 (coins ℤ)) :
    ∃ c : ℝ, Tendsto (fun N => birkhoffAverage ℝ koopman _root_.id N g) atTop
      (𝓝 (Lp.const 2 (coins ℤ) c)) := by
  have h := koopman.tendsto_birkhoffAverage_orthogonalProjection norm_koopman_le g
  set P : Lp ℝ 2 (coins ℤ) := ((LinearMap.eqLocus koopman 1).orthogonalProjection g :
    Lp ℝ 2 (coins ℤ)) with hPdef
  have hP : koopman P = P := by
    have := ((LinearMap.eqLocus koopman 1).orthogonalProjection g).2
    rw [LinearMap.mem_eqLocus] at this
    simpa using this
  -- as an a.e.-class, `P ∘ F = P`, so `P` is constant
  have hP' : P.1.compMeasurePreserving (fun x : ℤ → Bool => evol x 1) ergodic_evol_one.1 =
      P.1 := congrArg Subtype.val hP
  obtain ⟨c, hc⟩ := ergodic_evol_one.eq_const_of_compMeasurePreserving_eq hP'
  refine ⟨c, ?_⟩
  have hPc : P = Lp.const 2 (coins ℤ) c := Subtype.ext hc
  rw [← hPc]
  exact h

/-- The integral of an `L²` function is its inner product with the constant `1`. -/
theorem inner_const_one (g : Lp ℝ 2 (coins ℤ)) :
    inner ℝ (Lp.const 2 (coins ℤ) (1 : ℝ)) g = ∫ x, g x ∂(coins ℤ) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const 2 (coins ℤ) (1 : ℝ)] with x hx
  rw [hx]
  simp

/-- Rule 30 preserves integrals: `∫ g ∘ F = ∫ g`. -/
theorem integral_koopman (h : Lp ℝ 2 (coins ℤ)) :
    ∫ x, koopman h x ∂(coins ℤ) = ∫ x, h x ∂(coins ℤ) := by
  have hF := measurePreserving_evol 1
  have hc : (koopman h : (ℤ → Bool) → ℝ) =ᵐ[coins ℤ] h ∘ fun x : ℤ → Bool => evol x 1 :=
    Lp.coeFn_compMeasurePreserving h hF
  rw [integral_congr_ae hc]
  have hm : AEStronglyMeasurable (h : (ℤ → Bool) → ℝ) (Measure.map (fun x : ℤ → Bool => evol x 1)
      (coins ℤ)) := by
    rw [hF.map_eq]
    exact Lp.aestronglyMeasurable h
  have := integral_map hF.measurable.aemeasurable hm
  rw [hF.map_eq] at this
  exact this.symm

/-- **The L² ergodic theorem for rule 30**, with its limit: for every `g ∈ L²`, the averages
`(g + g ∘ F + ⋯ + g ∘ F^(N-1)) / N` converge in `L²` to the constant `∫ g`. The limit is a constant
(`exists_tendsto_birkhoffAverage_const`); pairing with `1` is continuous, and each average has
integral `∫ g`. -/
theorem tendsto_birkhoffAverage_integral (g : Lp ℝ 2 (coins ℤ)) :
    Tendsto (fun N => birkhoffAverage ℝ koopman _root_.id N g) atTop
      (𝓝 (Lp.const 2 (coins ℤ) (∫ x, g x ∂(coins ℤ)))) := by
  obtain ⟨c, hc⟩ := exists_tendsto_birkhoffAverage_const g
  have hiter : ∀ k : ℕ, inner ℝ (Lp.const 2 (coins ℤ) (1 : ℝ)) (koopman^[k] g) =
      ∫ x, g x ∂(coins ℤ) := by
    intro k
    rw [inner_const_one]
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', integral_koopman, ih]
  have hinner : ∀ N : ℕ, 1 ≤ N → inner ℝ (Lp.const 2 (coins ℤ) (1 : ℝ))
      (birkhoffAverage ℝ koopman _root_.id N g) = ∫ x, g x ∂(coins ℤ) := by
    intro N hN
    rw [birkhoffAverage, real_inner_smul_right, birkhoffSum, inner_sum]
    simp only [id, hiter, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  have hlim := Filter.Tendsto.inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := Lp.const 2 (coins ℤ) (1 : ℝ))) hc
  have hconst : inner ℝ (Lp.const 2 (coins ℤ) (1 : ℝ)) (Lp.const 2 (coins ℤ) c) = c := by
    rw [inner_const_one, integral_congr_ae (Lp.coeFn_const 2 (coins ℤ) c)]
    simp
  have hc' : c = ∫ x, g x ∂(coins ℤ) := by
    rw [← hconst]
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hinner N hN).symm
  rw [← hc']
  exact hc

end MeanErgodic

/-! ### Orbits that return to every open set -/

/-- The configurations whose `t`-th image, for some `t ≥ T`, shows the pattern `v` on `I`. -/
def visits (I : Finset ℤ) (v : I → Bool) (T : ℕ) : Set (ℤ → Bool) :=
  ⋃ t ∈ Set.Ici T, {x | ∀ i ∈ I, evol x t i = extend v i}

theorem measurableSet_visits (I : Finset ℤ) (v : I → Bool) (T : ℕ) :
    MeasurableSet (visits I v T) :=
  MeasurableSet.biUnion (Set.to_countable _) fun t _ => measurableSet_window t I _

theorem isOpen_window (t : ℕ) (I : Finset ℤ) (v : I → Bool) :
    IsOpen {x : ℤ → Bool | ∀ i ∈ I, evol x t i = extend v i} := by
  have hc : Continuous fun x : ℤ → Bool => I.restrict (evol x t) :=
    continuous_pi fun i : I => continuous_evol t i
  rw [← preimage_restrict_singleton]
  exact (isOpen_discrete {v}).preimage hc

/-- After any time, almost every orbit shows the pattern `v` on `I`: the set `visits I v T` is
almost invariant, so by ergodicity null or full, and it contains a window event of positive
measure. -/
theorem ae_mem_visits (I : Finset ℤ) (v : I → Bool) (T : ℕ) :
    ∀ᵐ x ∂(coins ℤ), x ∈ visits I v T := by
  have hsub : (fun x : ℤ → Bool => evol x 1) ⁻¹' visits I v T ⊆ visits I v T := by
    intro x hx
    simp only [visits, Set.mem_preimage, Set.mem_iUnion, Set.mem_Ici, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨t, ht, h⟩ := hx
    refine ⟨1 + t, by omega, fun i hi => ?_⟩
    rw [← Rule30ZeroBoundaryBarriers.evol_restart x 1 t i]
    exact h i hi
  rcases ergodic_evol_one.ae_empty_or_univ_of_preimage_ae_le
      (measurableSet_visits I v T).nullMeasurableSet hsub.eventuallyLE with h | h
  · exfalso
    have hle : coins ℤ {x | ∀ i ∈ I, evol x T i = extend v i} ≤ coins ℤ (visits I v T) :=
      measure_mono fun x hx => Set.mem_biUnion (Set.mem_Ici.2 le_rfl) hx
    rw [measure_congr h, measure_empty, measure_window] at hle
    exact absurd hle (not_le.2 (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _))
  · exact h.mem_iff.mono fun x hx => hx.2 trivial

/-- **Almost every orbit returns to every open set**: for almost every configuration `x`, every
nonempty open set contains `evol x t` for arbitrarily large `t`, so the omega-limit set of `x`
is all of `{0,1}^ℤ`. -/
theorem ae_frequently_mem :
    ∀ᵐ x ∂(coins ℤ), ∀ U : Set (ℤ → Bool), IsOpen U → U.Nonempty →
      ∀ T : ℕ, ∃ t ≥ T, evol x t ∈ U := by
  have h : ∀ᵐ x ∂(coins ℤ), ∀ (n : ℕ) (v : Finset.Icc (-(n : ℤ)) n → Bool) (T : ℕ),
      x ∈ visits (Finset.Icc (-(n : ℤ)) n) v T :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun v => ae_all_iff.2 fun T => ae_mem_visits _ v T
  filter_upwards [h] with x hx
  rintro U hU ⟨y, hy⟩ T
  obtain ⟨n, hn⟩ := exists_window_subset (hU.mem_nhds hy)
  have hxv := hx n ((Finset.Icc (-(n : ℤ)) n).restrict y) T
  simp only [visits, Set.mem_iUnion, Set.mem_Ici, Set.mem_setOf_eq] at hxv
  obtain ⟨t, ht, hw⟩ := hxv
  refine ⟨t, ht, hn fun p hp1 hp2 => ?_⟩
  have := hw p (Finset.mem_Icc.2 ⟨hp1, hp2⟩)
  simp only [extend, dif_pos (Finset.mem_Icc.2 ⟨hp1, hp2⟩)] at this
  exact this

/-- **Generic orbits return to every open set**: for a comeager set of configurations `x`, every
nonempty open set contains `evol x t` for arbitrarily large `t`. Each `visits I v T` is open and,
by topological mixing, dense. -/
theorem residual_frequently_mem :
    {x : ℤ → Bool | ∀ U : Set (ℤ → Bool), IsOpen U → U.Nonempty →
      ∀ T : ℕ, ∃ t ≥ T, evol x t ∈ U} ∈ residual (ℤ → Bool) := by
  have h : (⋂ (n : ℕ) (v : Finset.Icc (-(n : ℤ)) n → Bool) (T : ℕ),
      visits (Finset.Icc (-(n : ℤ)) n) v T) ∈ residual (ℤ → Bool) := by
    refine countable_iInter_mem.2 fun n => countable_iInter_mem.2 fun v =>
      countable_iInter_mem.2 fun T => residual_of_dense_open ?_ ?_
    · exact isOpen_biUnion fun t _ => isOpen_window t _ v
    · rw [dense_iff_inter_open]
      intro U hU hU0
      have hV : IsOpen {y : ℤ → Bool | ∀ i ∈ Finset.Icc (-(n : ℤ)) n, y i = extend v i} :=
        isOpen_window 0 _ v
      obtain ⟨T₀, hT₀⟩ := exists_mem_evol_mem hU hV hU0 ⟨extend v, fun i _ => rfl⟩
      obtain ⟨x, hxU, hxV⟩ := hT₀ (max T T₀) (le_max_right _ _)
      exact ⟨x, hxU, Set.mem_biUnion (Set.mem_Ici.2 (le_max_left T T₀)) hxV⟩
  refine mem_of_superset h fun x hx => ?_
  rintro U hU ⟨y, hy⟩ T
  obtain ⟨n, hn⟩ := exists_window_subset (hU.mem_nhds hy)
  have hxv := Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hx n)
    ((Finset.Icc (-(n : ℤ)) n).restrict y)) T
  simp only [visits, Set.mem_iUnion, Set.mem_Ici, Set.mem_setOf_eq] at hxv
  obtain ⟨t, ht, hw⟩ := hxv
  refine ⟨t, ht, hn fun p hp1 hp2 => ?_⟩
  have := hw p (Finset.mem_Icc.2 ⟨hp1, hp2⟩)
  simp only [extend, dif_pos (Finset.mem_Icc.2 ⟨hp1, hp2⟩)] at this
  exact this

/-! ### Perturbations -/

/-- **The right front of a perturbation moves at speed one**: flipping the cell `q` flips the cell
`(t, q + t)` and changes no cell right of it. -/
theorem evol_flip_front (x : ℤ → Bool) (q : ℤ) (t : ℕ) :
    evol (Function.update x q (!x q)) t (q + t) = !evol x t (q + t) ∧
      ∀ p, q + t < p → evol (Function.update x q (!x q)) t p = evol x t p := by
  refine ⟨?_, fun p hp => AlgebraicDegree.evol_update_of_far (Or.inl (by omega)) x _⟩
  have h := evol_flip_at x t (q + t)
  rwa [show q + t - t = q by ring] at h

/-- **Rule 30 is sensitive to initial conditions**: every configuration has, in each of its
neighbourhoods, a configuration whose center cell differs from its own at some time. -/
theorem sensitive (x : ℤ → Bool) (n : ℕ) :
    ∃ y : ℤ → Bool, (∀ p, -(n : ℤ) ≤ p → p ≤ n → y p = x p) ∧ ∃ t, evol y t 0 ≠ evol x t 0 := by
  refine ⟨Function.update x (-((n + 1 : ℕ) : ℤ)) (!x (-((n + 1 : ℕ) : ℤ))), fun p hp _ =>
    Function.update_of_ne (by omega) _ _, n + 1, ?_⟩
  rw [evol_flip x (n + 1)]
  cases evol x (n + 1) 0 <;> simp

/-- **Right halves of almost every orbit come back to every pattern**: for almost every
configuration, every pattern `v 0, …, v (N - 1)` appears at the cells `0, …, N - 1` at arbitrarily
late times, so every sequence is a limit point of the right halves of the rows. For the single
seed, Kopra's theorem gives infinitely many limit points (`LimitPoints`). -/
theorem ae_rightHalves_frequently (v : ℕ → Bool) :
    ∀ᵐ x ∂(coins ℤ), ∀ N T : ℕ, ∃ t ≥ T, ∀ n < N, evol x t n = v n := by
  filter_upwards [ae_frequently_mem] with x hx
  intro N T
  have hU : IsOpen {y : ℤ → Bool | ∀ n < N, y n = v n} := by
    have : {y : ℤ → Bool | ∀ n < N, y n = v n} =
        ⋂ n ∈ Finset.range N, {y : ℤ → Bool | y n = v n} := by
      ext y
      simp
    rw [this]
    exact isOpen_biInter_finset fun n _ =>
      (isOpen_discrete {v n}).preimage (continuous_apply (A := fun _ : ℤ => Bool) (n : ℤ))
  obtain ⟨t, ht, hmem⟩ := hx _ hU ⟨fun p => v p.toNat, fun n _ => by simp⟩ T
  exact ⟨t, ht, hmem⟩

/-! ### Topological entropy -/

section Entropy

open Dynamics Uniformity

/-- The full shift on `{0,1}^ℕ` has topological entropy at least `log 2`: a dynamical cover for
the first coordinate over `n` steps must show every word of length `n`. -/
theorem log_two_le_coverEntropy_shift :
    ENNReal.log 2 ≤ coverEntropy ShiftOrbit.shift (Set.univ : Set (ℕ → Bool)) := by
  let V : SetRel (ℕ → Bool) (ℕ → Bool) := {p | p.1 0 = p.2 0}
  have hV : V ∈ 𝓤 (ℕ → Bool) :=
    (Pi.uniformContinuous_proj (fun _ : ℕ => Bool) 0)
      (UniformSpace.uniformSpace_eq_bot.mp rfl : SetRel.id ∈ 𝓤 Bool)
  refine le_trans ?_ (coverEntropyEntourage_le_coverEntropy ShiftOrbit.shift Set.univ hV)
  rw [← ExpGrowth.expGrowthSup_pow]
  refine ExpGrowth.expGrowthSup_monotone fun n => ?_
  -- a dynamical cover shows every word of length `n`
  have key : ∀ s : Finset (ℕ → Bool), IsDynCoverOf ShiftOrbit.shift Set.univ V n s →
      2 ^ n ≤ s.card := by
    intro s hs
    have hsurj : (s.image fun y => fun k : Fin n => y k) = Finset.univ := by
      refine Finset.eq_univ_of_forall fun w => ?_
      obtain ⟨y, hy, hxy⟩ := hs (x := fun t => if h : t < n then w ⟨t, h⟩ else false)
        (Set.mem_univ _)
      refine Finset.mem_image.2 ⟨y, hy, funext fun k => ?_⟩
      simp only [dynEntourage, Set.mem_iInter, Set.mem_preimage, Prod.map_iterate,
        Prod.map_apply, ShiftOrbit.shift_iterate, V, Set.mem_setOf_eq, add_zero] at hxy
      have hk := hxy k k.2
      simp only [dif_pos k.2] at hk
      exact hk.symm
    calc 2 ^ n = (Finset.univ : Finset (Fin n → Bool)).card := by simp
      _ = (s.image fun y => fun k : Fin n => y k).card := by rw [hsurj]
      _ ≤ s.card := Finset.card_image_le
  have hmin : ((2 ^ n : ℕ) : ℕ∞) ≤ coverMincard ShiftOrbit.shift Set.univ V n :=
    le_iInf₂ fun s hs => by exact_mod_cast key s hs
  have := ENat.toENNReal_le.2 hmin
  simpa using this

/-- **Rule 30 has topological entropy at least `log 2`**: the center trace is a uniformly
continuous factor map onto the full shift on `{0,1}^ℕ` (`RandomConfigurations.trace_evol_one`,
`Genericity.surjective_trace`). -/
theorem log_two_le_coverEntropy :
    ENNReal.log 2 ≤ coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ := by
  have hsemi : Function.Semiconj trace (fun x : ℤ → Bool => evol x 1) ShiftOrbit.shift := fun x =>
    trace_evol_one x
  have h := coverEntropy_image_le_of_uniformContinuous hsemi
    (CompactSpace.uniformContinuous_of_continuous continuous_trace) Set.univ
  rw [Set.image_univ_of_surjective surjective_trace] at h
  exact log_two_le_coverEntropy_shift.trans h

/-- Agreement on the window `[-N, N]`. -/
def windowRel (N : ℕ) : SetRel (ℤ → Bool) (ℤ → Bool) :=
  {p | ∀ i, -(N : ℤ) ≤ i → i ≤ N → p.1 i = p.2 i}

/-- Every entourage of `{0,1}^ℤ` contains agreement on some window `[-N, N]`. -/
theorem exists_windowRel_subset {U : SetRel (ℤ → Bool) (ℤ → Bool)} (hU : U ∈ 𝓤 (ℤ → Bool)) :
    ∃ N : ℕ, windowRel N ⊆ U := by
  rw [Pi.uniformity, Filter.mem_iInf] at hU
  obtain ⟨I, hI, V, hV, rfl⟩ := hU
  obtain ⟨a, ha⟩ := hI.bddBelow
  obtain ⟨b, hb⟩ := hI.bddAbove
  refine ⟨(max (-a) b).toNat, fun p hp => Set.mem_iInter.2 fun i => ?_⟩
  obtain ⟨t, ht, hsub⟩ := Filter.mem_comap.1 (hV i)
  have hai := ha i.2
  have hbi := hb i.2
  have heq : p.1 i = p.2 i := hp i (by omega) (by omega)
  refine hsub ?_
  show (p.1 i, p.2 i) ∈ t
  rw [heq]
  exact refl_mem_uniformity ht

/-- The iterates of rule 30 as a map. -/
theorem iterate_evol_one (k : ℕ) (x : ℤ → Bool) :
    (fun x : ℤ → Bool => evol x 1)^[k] x = evol x k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    funext p
    rw [Rule30ZeroBoundaryBarriers.evol_restart x 1 k p, Nat.add_comm]

/-- **A dynamical cover**: agreement on `[-N, N]` for `n` steps of rule 30 needs at most one
configuration per pattern on `[-(N + n), N + n]`, by the light cone. -/
theorem coverMincard_le (N n : ℕ) :
    coverMincard (fun x : ℤ → Bool => evol x 1) Set.univ (windowRel N) n ≤
      2 ^ (2 * (N + n) + 1) := by
  classical
  let W : Finset ℤ := Finset.Icc (-((N + n : ℕ) : ℤ)) (N + n : ℕ)
  let s : Finset (ℤ → Bool) := Finset.univ.image fun v : W → Bool => extend v
  have hcov : IsDynCoverOf (fun x : ℤ → Bool => evol x 1) Set.univ (windowRel N) n s := by
    intro x _
    refine ⟨extend (W.restrict x), Finset.mem_coe.2 (Finset.mem_image_of_mem _
      (Finset.mem_univ _)), ?_⟩
    simp only [dynEntourage, Set.mem_iInter, Set.mem_preimage, Prod.map_iterate,
      Prod.map_apply, windowRel, Set.mem_setOf_eq]
    intro k hk i hi1 hi2
    rw [iterate_evol_one, iterate_evol_one]
    refine AlgebraicDegree.evol_congr k i fun j hj1 hj2 => ?_
    have hj : j ∈ W := Finset.mem_Icc.2 ⟨by push_cast; omega, by push_cast; omega⟩
    simp only [extend, dif_pos hj, Finset.restrict]
  refine hcov.coverMincard_le_card.trans ?_
  have hcard : s.card ≤ 2 ^ (2 * (N + n) + 1) := by
    refine Finset.card_image_le.trans ?_
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, W,
      Int.card_Icc]
    rw [show ((N + n : ℕ) : ℤ) + 1 - -((N + n : ℕ) : ℤ) = ((2 * (N + n) + 1 : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]
  exact_mod_cast hcard

/-- **Rule 30 has topological entropy at most `2 log 2`** (Mathlib's `coverEntropy`), so
`log 2 ≤ h(rule 30) ≤ 2 log 2` with `log_two_le_coverEntropy`: every entourage contains agreement
on a window `[-N, N]`, and the dynamical covers `coverMincard_le` grow like `4^n`. -/
theorem coverEntropy_le_two_mul_log_two :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤ 2 * ENNReal.log 2 := by
  refine iSup₂_le fun U hU => ?_
  obtain ⟨N, hN⟩ := exists_windowRel_subset hU
  refine (coverEntropyEntourage_antitone _ _ hN).trans ?_
  have hle : ∀ n : ℕ, ((coverMincard (fun x : ℤ → Bool => evol x 1) Set.univ (windowRel N) n :
      ℕ∞) : ENNReal) ≤ 2 ^ (2 * N + 1) * 4 ^ n := fun n => by
    have h := ENat.toENNReal_le.2 (coverMincard_le N n)
    refine h.trans_eq ?_
    rw [show 2 * (N + n) + 1 = (2 * N + 1) + 2 * n by ring, pow_add, pow_mul]
    push_cast
    norm_num
  calc coverEntropyEntourage (fun x : ℤ → Bool => evol x 1) Set.univ (windowRel N)
      ≤ ExpGrowth.expGrowthSup fun n : ℕ => (4 : ENNReal) ^ n :=
        ExpGrowth.expGrowthSup_le_of_eventually_le (b := 2 ^ (2 * N + 1)) (by simp)
          (Eventually.of_forall hle)
    _ = ENNReal.log 4 := ExpGrowth.expGrowthSup_pow
    _ = 2 * ENNReal.log 2 := by
      rw [show (4 : ENNReal) = 2 ^ 2 by norm_num, ENNReal.log_pow]
      norm_cast

end Entropy

end Rule30Equivalents.Mixing

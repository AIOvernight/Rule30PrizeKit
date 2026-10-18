import Rule30Equivalents.ShiftOrbit
import Rule30Equivalents.WordsAutomata
import Rule30Equivalents.BinaryIrrational
import Rule30Equivalents.LinearRelations
import Rule30Equivalents.PowerSeriesF2
import Rule30Equivalents.Automatic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stronger statements that imply Problem 1

Catalog Section 4 lists statements, mostly open, each of which implies Problem 1. This file proves
those implications (`problem1_of_*`). Where a statement is about a density or a distance, the
theorem uses the weaker consequence that some set is infinite, so it covers the stated form.

* `problem1_of_effective_boundary`: `t ↦ c(t) ∧ c(t + 1)` is not eventually periodic.
* `problem1_of_every_line`: no line of slope `p/q`, `|p| < q`, carries an eventually periodic
  sequence.
* `problem1_of_unbounded_runs`: `0ⁿ` (or `1ⁿ`) occurs in `c` for every `n`.
* `problem1_of_anti_toeplitz`: no residue class `k ↦ c(r + kP)` is eventually constant.
* `problem1_of_infinite_disagreements`: for every `τ ≥ 1`, `c(t) ≠ c(t + τ)` infinitely often (in
  particular if the disagreements have positive upper density).
* `problem1_of_far_from_periodic`: `c` differs infinitely often from every periodic sequence (in
  particular if it has positive Besicovitch distance from all of them).
* `problem1_of_uncountable_orbit_closure`, `problem1_of_exponential_complexity` (positive
  entropy): the orbit closure is uncountable, or the factor complexity grows exponentially.
* `problem1_of_disjunctive`, `problem1_of_isNormal`: every word occurs in `c`; `c` is normal.
* `problem1_of_transcendental_binary`: `x₂ = 0.c(0)c(1)…₂` is transcendental.
* `problem1_of_linComplexity_tendsto`: the linear complexity `Lₙ` of the prefixes over `𝔽₂`
  satisfies `Lₙ/n → 1/2`.
* `problem1_of_hankel_eventually_nonzero`: the integer Hankel determinants are nonzero from some
  size on.
* `problem1_of_defect_bound`: the Π⁰₁ defect bound.
* `problem1_of_hypertranscendental`: `∑ c(t) zᵗ` satisfies no algebraic differential equation
  over `ℚ`.
* `problem1_of_unbounded_abelianComplexity`: the abelian complexity of `c` is unbounded.
* `problem1_of_irrExponentGE`: the irrationality exponent of `x₂` is at least some `μ > 1`, for
  example `μ(x₂) = 2`.
* `problem1_of_not_isMahler`: `∑ c(t) zᵗ` is not a `k`-Mahler function.
* `problem1_of_expansionComplexity_unbounded`: the expansion complexity of `∑ c(t) Xᵗ` over `𝔽₂`
  is unbounded.
* `problem1_of_not_isMorphic`: `c` is not morphic.
* `problem1_of_recurrent_not_purelyPeriodic`: `c` is recurrent and not purely periodic; a
  recurrent eventually periodic sequence is purely periodic (`IsRecurrent.purelyPeriodic`), so for
  a recurrent `c` Problem 1 is the case `T = 0` (`problem1_iff_not_purelyPeriodic_of_recurrent`).
-/

namespace Rule30Equivalents.StrongerStatements

open Filter Topology Ruliology.CellularAutomata

/-- **Effective boundary.** -/
theorem problem1_of_effective_boundary (h : ¬ EventuallyPeriodic fun t => c t && c (t + 1)) :
    Rule30Prize.Problem1 := by
  rintro ⟨T, P, hP, hper⟩
  have hper' : ∀ t, T ≤ t → c (t + P) = c t := hper
  refine h ⟨T, P, hP, fun t ht => ?_⟩
  show (c (t + P) && c (t + P + 1)) = (c t && c (t + 1))
  rw [show t + P + 1 = (t + 1) + P by omega, hper' t ht, hper' (t + 1) (by omega)]

/-- **Every line.** The line of slope `p/q` through `(t₀, x₀)` is `t ↦ cell(qt + t₀, pt + x₀)`. -/
theorem problem1_of_every_line
    (h : ∀ (p : ℤ) (q t₀ : ℕ) (x₀ : ℤ), 0 < q → |p| < q →
      ¬ EventuallyPeriodic fun t => Rule30Jen.cell (q * t + t₀) (p * t + x₀)) :
    Rule30Prize.Problem1 := by
  have := h 0 1 0 0 one_pos (by simp)
  simpa using this

/-- **Unbounded runs.** -/
theorem problem1_of_unbounded_runs (b : Bool) (h : ∀ n, ∃ t, ∀ i < n, c (t + i) = b) :
    Rule30Prize.Problem1 := by
  rintro ⟨T, P, hP, hper⟩
  obtain ⟨t, ht⟩ := h (T + P)
  apply Rule30Prize.center_not_eventually_constant
  refine ⟨max t T, b, fun s hs => ?_⟩
  set w := max t T + (s - max t T) % P with hw
  have hwP : (s - max t T) % P < P := Nat.mod_lt _ hP
  have hmod : w % P = s % P := by
    rw [hw, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_sub_cancel' hs]
  have hcw : c w = b := by
    have := ht (w - t) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  rw [← hcw]
  exact Automatic.eq_of_mod_eq hper (by omega) (by omega) hmod.symm

/-- **Anti-Toeplitz.** -/
theorem problem1_of_anti_toeplitz (h : ∀ P, 0 < P → ∀ r, ¬ ∃ K b, ∀ k, K ≤ k → c (r + k * P) = b) :
    Rule30Prize.Problem1 := fun ⟨T, P, hP, hper⟩ =>
  h P hP T ⟨0, c T, fun k _ => OmegaRegular.periodic_add_mul c T P hper le_rfl k⟩

/-- **Disagreements.** If for every `τ ≥ 1` the times with `c(t) ≠ c(t + τ)` are infinitely many,
for instance of positive upper density, Problem 1 holds. -/
theorem problem1_of_infinite_disagreements (h : ∀ τ, 0 < τ → {t | c t ≠ c (t + τ)}.Infinite) :
    Rule30Prize.Problem1 := fun ⟨T, P, hP, hper⟩ =>
  h P hP ((Set.finite_lt_nat T).subset fun t ht => by
    by_contra hT
    exact ht (hper t (not_lt.1 hT)).symm)

/-- **Far from periodic sequences.** If `c` differs infinitely often from every periodic sequence,
for instance if its Besicovitch distance from each of them is positive, Problem 1 holds. -/
theorem problem1_of_far_from_periodic
    (h : ∀ (y : ℕ → Bool) (P : ℕ), 0 < P → (∀ t, y (t + P) = y t) → {t | c t ≠ y t}.Infinite) :
    Rule30Prize.Problem1 := by
  rintro ⟨T, P, hP, hper⟩
  refine h (fun t => c (T * P + t % P)) P hP (fun t => by simp) ((Set.finite_lt_nat T).subset ?_)
  intro t ht
  by_contra hT
  apply ht
  exact Automatic.eq_of_mod_eq hper (not_lt.1 hT)
    (le_trans (Nat.le_mul_of_pos_right T hP) (Nat.le_add_right _ _)) (by simp)

/-- **Uncountable orbit closure.** -/
theorem problem1_of_uncountable_orbit_closure
    (h : ¬ (closure (Set.range fun n : ℕ => fun t => c (n + t))).Countable) :
    Rule30Prize.Problem1 :=
  WordsAutomata.problem1_iff_orbit_closure_infinite.2 fun hfin => h hfin.countable

/-- **Positive entropy**: the factor complexity grows exponentially. -/
theorem problem1_of_exponential_complexity
    (h : ∃ a : ℝ, 1 < a ∧ ∀ n, a ^ n ≤ ((ShiftOrbit.factors c n).ncard : ℝ)) :
    Rule30Prize.Problem1 := by
  obtain ⟨a, ha, hn⟩ := h
  rw [ShiftOrbit.problem1_iff_ncard_factors_unbounded]
  intro C
  obtain ⟨n, hC⟩ := pow_unbounded_of_one_lt (C : ℝ) ha
  exact ⟨n, by exact_mod_cast hC.trans_le (hn n)⟩

/-- **Disjunctive**: every word occurs in `c`. -/
theorem problem1_of_disjunctive (h : ∀ n (w : Fin n → Bool), ∃ i, ∀ j : Fin n, c (i + j) = w j) :
    Rule30Prize.Problem1 := by
  rw [ShiftOrbit.problem1_iff_ncard_factors]
  intro n
  have : ShiftOrbit.factors c n = Set.univ :=
    Set.eq_univ_of_forall fun w => let ⟨i, hi⟩ := h n w; ⟨i, funext hi⟩
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  exact Nat.lt_two_pow_self

/-- `b` is normal in base `2`: every word of length `n` occurs with frequency `2⁻ⁿ`. -/
def IsNormal (b : ℕ → Bool) : Prop :=
  ∀ n (w : Fin n → Bool), Tendsto (fun N : ℕ =>
    (((Finset.range N).filter fun i => ∀ j : Fin n, b (i + j) = w j).card : ℝ) / N) atTop
      (𝓝 ((2 : ℝ)⁻¹ ^ n))

/-- **Normality** (of `x₂` in base `2`): a normal sequence is disjunctive. -/
theorem problem1_of_isNormal (h : IsNormal c) : Rule30Prize.Problem1 := by
  refine problem1_of_disjunctive fun n w => ?_
  obtain ⟨N, hN⟩ := ((h n w).eventually (lt_mem_nhds (by positivity : (0 : ℝ) < 2⁻¹ ^ n))).exists
  by_contra hne
  push Not at hne
  have : ((Finset.range N).filter fun i => ∀ j : Fin n, c (i + j) = w j) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro _ hi
    obtain ⟨j, hj⟩ := hne i
    exact hj (hi j)
  rw [this] at hN
  simp at hN

/-- **`x₂` transcendental.** -/
theorem problem1_of_transcendental_binary
    (h : Transcendental ℚ BinaryIrrational.centerBinary) : Rule30Prize.Problem1 := by
  rw [BinaryIrrational.problem1_iff_irrational_binary]
  rintro ⟨q, hq⟩
  exact h (hq ▸ isAlgebraic_algebraMap q)

/-- The linear complexity of the prefix of length `n` over `𝔽₂`: the shortest linear feedback
shift register that generates it. -/
noncomputable def linComplexity (n : ℕ) : ℕ :=
  sInf {d | ∃ a : Fin d → ZMod 2, ∀ t, t + d < n →
    (if c (t + d) then 1 else 0 : ZMod 2) = ∑ i, a i * (if c (t + i) then 1 else 0)}

/-- **`Lₙ/n → 1/2`**: then `Lₙ → ∞`. -/
theorem problem1_of_linComplexity_tendsto
    (h : Tendsto (fun n : ℕ => (linComplexity n : ℝ) / n) atTop (𝓝 (1 / 2))) :
    Rule30Prize.Problem1 := by
  rw [PowerSeriesF2.problem1_iff_linear_complexity_unbounded]
  intro d
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (h.eventually (lt_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2)))
  obtain ⟨M, hM⟩ : ∃ M, M = max N (4 * d + 4) := ⟨_, rfl⟩
  refine ⟨M, fun ⟨a, ha⟩ => ?_⟩
  have hle : linComplexity M ≤ d := Nat.sInf_le ⟨a, ha⟩
  have h1 := hN M (hM ▸ le_max_left _ _)
  have hM4 : 4 * d + 4 ≤ M := hM ▸ le_max_right _ _
  have h2 : ((4 * d + 4 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
  have hpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  rw [lt_div_iff₀ hpos] at h1
  have h3 : (linComplexity M : ℝ) ≤ d := by exact_mod_cast hle
  push_cast at h2
  linarith

/-- **Hankel determinants nonzero from some size on.** -/
theorem problem1_of_hankel_eventually_nonzero
    (h : ∃ m₀, ∀ m, m₀ ≤ m →
      (Matrix.of fun i j : Fin m => LinearRelations.cK ℤ ((i : ℕ) + (j : ℕ))).det ≠ 0) :
    Rule30Prize.Problem1 :=
  LinearRelations.problem1_iff_hankel_det_int.2 fun N =>
    let ⟨m₀, hm⟩ := h; ⟨max N m₀, le_max_left _ _, hm _ (le_max_right _ _)⟩

/-- **The Π⁰₁ defect bound.** -/
theorem problem1_of_defect_bound
    (h : ∀ T P, 0 < P → ∃ t, T ≤ t ∧ t ≤ T + 3 * Nat.log 2 (T + P + 1) ∧ c (t + P) ≠ c t) :
    Rule30Prize.Problem1 := fun ⟨T, P, hP, hper⟩ =>
  let ⟨t, ht, _, hne⟩ := h T P hP; hne (hper t ht)

/-- `F` satisfies an algebraic differential equation over `ℚ`: `P(z, F, F′, …, F⁽ⁿ⁾) = 0` for a
nonzero polynomial `P` in `n + 2` variables. -/
def IsDifferentiallyAlgebraic (F : PowerSeries ℚ) : Prop :=
  ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℚ), P ≠ 0 ∧
    MvPolynomial.aeval (Fin.cons PowerSeries.X fun i : Fin (n + 1) =>
      (⇑(PowerSeries.derivative ℚ))^[i] F) P = 0

/-- **Hypertranscendence**: if `∑ c(t) zᵗ` satisfies no algebraic differential equation over `ℚ`,
Problem 1 holds. An eventually periodic `c` gives `Q(z) C(z) − P(z) = 0`, an equation of order
`0`. -/
theorem problem1_of_hypertranscendental
    (h : ¬ IsDifferentiallyAlgebraic (LinearRelations.series ℚ c)) : Rule30Prize.Problem1 := by
  intro hep
  obtain ⟨P, Q, hQ, hPQ⟩ :=
    (LinearRelations.eventuallyPeriodic_iff_rational_coeff_zero (K := ℚ) c).1 hep
  apply h
  set E : MvPolynomial (Fin 2) ℚ :=
    Polynomial.aeval (MvPolynomial.X 0) Q * MvPolynomial.X 1 - Polynomial.aeval (MvPolynomial.X 0) P
  -- `E` under an evaluation: `Q(z) y − P(z)`
  have key : ∀ {A : Type} [CommRing A] [Algebra ℚ A] (v : Fin 2 → A) (R : Polynomial ℚ),
      MvPolynomial.aeval v (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) R) =
        Polynomial.aeval (v 0) R := by
    intro A _ _ v R
    rw [← Polynomial.aeval_algHom_apply (MvPolynomial.aeval v)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) R, MvPolynomial.aeval_X]
  have hE : ∀ {A : Type} [CommRing A] [Algebra ℚ A] (v : Fin 2 → A),
      MvPolynomial.aeval v E = Polynomial.aeval (v 0) Q * v 1 - Polynomial.aeval (v 0) P := by
    intro A _ _ v
    simp only [E, map_sub, map_mul, key, MvPolynomial.aeval_X]
  refine ⟨0, E, fun h0 => hQ ?_, ?_⟩
  · have h1 := hE (A := ℚ) ![0, 1]
    have h2 := hE (A := ℚ) ![0, 0]
    rw [h0, map_zero] at h1 h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.coe_aeval_eq_eval] at h1 h2
    rw [Polynomial.coeff_zero_eq_eval_zero]
    linarith
  · rw [hE]
    show Polynomial.aeval PowerSeries.X Q * LinearRelations.series ℚ c -
      Polynomial.aeval PowerSeries.X P = 0
    rw [Polynomial.aeval_def, Polynomial.aeval_def,
      show algebraMap ℚ (PowerSeries ℚ) = PowerSeries.C from rfl,
      Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_C_X_eq_coe, hPQ, sub_self]

/-! ### Abelian complexity, irrationality exponent, Mahler functions -/

/-- The abelian complexity of `b`: the number of distinct counts of `true` among its factors of
length `n`. -/
noncomputable def abelianComplexity (b : ℕ → Bool) (n : ℕ) : ℕ :=
  ((fun w : Fin n → Bool => (Finset.univ.filter fun i => w i = true).card) ''
    ShiftOrbit.factors b n).ncard

/-- **Unbounded abelian complexity.** -/
theorem problem1_of_unbounded_abelianComplexity (h : ∀ C, ∃ n, C < abelianComplexity c n) :
    Rule30Prize.Problem1 := fun hep => by
  obtain ⟨C, hC⟩ := (ShiftOrbit.eventuallyPeriodic_iff_bounded_ncard_factors c).1 hep
  obtain ⟨n, hn⟩ := h C
  exact absurd (lt_of_lt_of_le hn ((Set.ncard_image_le (Set.toFinite _)).trans (hC n)))
    (lt_irrefl _)

/-- `x` has irrationality exponent at least `μ`: for every `ν < μ` there are infinitely many
rationals `q ≠ x` with `|x - q| < den(q)^(-ν)`. -/
def IrrExponentGE (x μ : ℝ) : Prop :=
  ∀ ν < μ, {q : ℚ | 0 < |x - q| ∧ |x - q| < (q.den : ℝ) ^ (-ν)}.Infinite

/-- A rational number has only finitely many approximations of order `3/2`. -/
theorem finite_approx (r : ℚ) :
    {q : ℚ | 0 < |(r : ℝ) - q| ∧ |(r : ℝ) - q| < (q.den : ℝ) ^ (-(3 / 2 : ℝ))}.Finite := by
  set D := r.den
  set B : ℕ := ⌈|(r : ℝ)|⌉₊ + 1
  refine (((Set.finite_Icc (-((B * D ^ 2 : ℕ) : ℤ)) ((B * D ^ 2 : ℕ) : ℤ)).prod
    (Set.finite_Iio (D ^ 2))).image fun z => (z.1 : ℚ) / z.2).subset ?_
  rintro q ⟨hq0, hq⟩
  have hden0 : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hD0 : (0 : ℝ) < D := by exact_mod_cast r.den_pos
  -- `|r - q| · den r · den q ≥ 1`
  have hr : (r : ℝ) * D = r.num := by exact_mod_cast Rat.mul_den_eq_num r
  have hqq : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have hint : (1 : ℝ) ≤ |(r : ℝ) - q| * (D * q.den) := by
    have e : ((r : ℝ) - q) * (D * q.den) = ((r.num * q.den - q.num * r.den : ℤ) : ℝ) := by
      push_cast
      linear_combination (q.den : ℝ) * hr - (D : ℝ) * hqq
    have hne : r.num * q.den - q.num * r.den ≠ 0 := by
      intro h0
      apply hq0.ne'
      rw [abs_eq_zero, sub_eq_zero]
      have h1 : ((r : ℝ) - q) * (D * q.den) = 0 := by rw [e, h0]; simp
      rcases mul_eq_zero.1 h1 with h2 | h2
      · linarith
      · exact absurd h2 (by positivity)
    rw [← abs_of_pos (show (0 : ℝ) < D * q.den by positivity), ← abs_mul, e]
    exact_mod_cast Int.one_le_abs hne
  -- squaring: `1 ≤ |r - q|² D² den² < D² / den`, so `den < D²`
  have hsq : |(r : ℝ) - q| ^ 2 < (q.den : ℝ) ^ (-(3 : ℝ)) := by
    have h0 : 0 ≤ |(r : ℝ) - q| := abs_nonneg _
    have := pow_lt_pow_left₀ hq h0 (two_ne_zero)
    rwa [← Real.rpow_natCast ((q.den : ℝ) ^ (-(3 / 2 : ℝ))) 2, ← Real.rpow_mul hden0.le,
      show (-(3 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -(3 : ℝ) by push_cast; ring] at this
  have hden_lt : (q.den : ℝ) < (D : ℝ) ^ 2 := by
    have h3 : (q.den : ℝ) ^ (-(3 : ℝ)) = ((q.den : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hden0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h3] at hsq
    have h4 : (1 : ℝ) ≤ |(r : ℝ) - q| ^ 2 * ((D : ℝ) * q.den) ^ 2 := by
      have := pow_le_pow_left₀ zero_le_one hint 2
      rwa [one_pow, mul_pow] at this
    have h5 : |(r : ℝ) - q| ^ 2 * ((D : ℝ) * q.den) ^ 2 <
        ((q.den : ℝ) ^ 3)⁻¹ * ((D : ℝ) * q.den) ^ 2 :=
      mul_lt_mul_of_pos_right hsq (by positivity)
    have h6 : ((q.den : ℝ) ^ 3)⁻¹ * ((D : ℝ) * q.den) ^ 2 = (D : ℝ) ^ 2 / q.den := by
      field_simp
    rw [h6, lt_div_iff₀ hden0] at h5
    calc (q.den : ℝ) = 1 * q.den := (one_mul _).symm
      _ ≤ |(r : ℝ) - q| ^ 2 * ((D : ℝ) * q.den) ^ 2 * q.den :=
        mul_le_mul_of_nonneg_right h4 hden0.le
      _ < (D : ℝ) ^ 2 := h5
  have hden_nat : q.den < D ^ 2 := by exact_mod_cast hden_lt
  -- `|q| < |r| + 1 ≤ B`
  have hq1 : |(r : ℝ) - q| < 1 := by
    calc |(r : ℝ) - q| < (q.den : ℝ) ^ (-(3 / 2 : ℝ)) := hq
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast q.den_pos) (by norm_num)
  have hqB : |(q : ℝ)| ≤ B := by
    have h1 : |(q : ℝ)| ≤ |(r : ℝ)| + 1 := by
      have := abs_sub_abs_le_abs_sub (q : ℝ) r
      rw [abs_sub_comm] at hq1
      linarith
    have h2 : |(r : ℝ)| ≤ ⌈|(r : ℝ)|⌉₊ := Nat.le_ceil _
    simp only [B]
    push_cast
    linarith
  refine ⟨(q.num, q.den), ⟨?_, hden_nat⟩, by simp [Rat.num_div_den]⟩
  -- `|num q| = |q| den q ≤ B D²`
  have hnum : |(q.num : ℝ)| ≤ (B * D ^ 2 : ℕ) := by
    rw [← hqq, abs_mul, abs_of_pos hden0]
    push_cast
    have : (q.den : ℝ) ≤ D ^ 2 := hden_lt.le
    nlinarith [abs_nonneg (q : ℝ)]
  have hnum' : |q.num| ≤ ((B * D ^ 2 : ℕ) : ℤ) := by exact_mod_cast hnum
  exact ⟨by linarith [neg_abs_le q.num], by linarith [le_abs_self q.num]⟩

/-- **The irrationality exponent.** If `μ(x₂) ≥ 2` (the catalog's `μ(x₂) = 2`), Problem 1 holds. -/
theorem problem1_of_irrExponentGE (h : IrrExponentGE BinaryIrrational.centerBinary 2) :
    Rule30Prize.Problem1 := by
  rw [BinaryIrrational.problem1_iff_irrational_binary]
  rintro ⟨r, hr⟩
  apply h (3 / 2) (by norm_num)
  rw [← hr]
  exact finite_approx r

/-- `F` is `k`-Mahler over `ℚ`: `∑_{i ≤ d} pᵢ(z) F(z^(kⁱ)) = 0` for polynomials `pᵢ`, not all
`0`. -/
def IsMahler (k : ℕ) (hk : k ≠ 0) (F : PowerSeries ℚ) : Prop :=
  ∃ (d : ℕ) (p : Fin (d + 1) → Polynomial ℚ), (∃ i, p i ≠ 0) ∧
    ∑ i, (p i : PowerSeries ℚ) * PowerSeries.expand (k ^ (i : ℕ)) (pow_ne_zero _ hk) F = 0

/-- `X ↦ X^k` commutes with the inclusion of polynomials into power series. -/
theorem expand_coe (k : ℕ) (hk : k ≠ 0) (P : Polynomial ℚ) :
    PowerSeries.expand k hk (P : PowerSeries ℚ) = ((Polynomial.expand ℚ k P : Polynomial ℚ) :
      PowerSeries ℚ) := by
  have : (PowerSeries.expand k hk).comp (Polynomial.coeToPowerSeries.algHom ℚ) =
      (Polynomial.coeToPowerSeries.algHom ℚ).comp (Polynomial.expand ℚ k) := by
    apply Polynomial.algHom_ext
    simp
  exact congrArg (fun φ => φ P) this

/-- **Mahler functions.** If `∑ c(t) zᵗ` is not `k`-Mahler for some `k ≥ 1`, Problem 1 holds: a
rational function `P/Q` satisfies `P(z^k) Q(z) F(z) - P(z) Q(z^k) F(z^k) = 0`. -/
theorem problem1_of_not_isMahler {k : ℕ} (hk : k ≠ 0)
    (h : ¬ IsMahler k hk (LinearRelations.series ℚ c)) : Rule30Prize.Problem1 := by
  intro hep
  obtain ⟨P, Q, hQ, hPQ⟩ := (LinearRelations.eventuallyPeriodic_iff_rational (K := ℚ) c).1 hep
  apply h
  set F := LinearRelations.series ℚ c
  by_cases hP : P = 0
  · -- `F = 0`
    refine ⟨0, fun _ => 1, ⟨0, one_ne_zero⟩, ?_⟩
    have hF : F = 0 := by
      rw [hP, Polynomial.coe_zero] at hPQ
      exact (mul_eq_zero.1 hPQ).resolve_left (by exact_mod_cast hQ)
    simp [hF]
  · refine ⟨1, ![Polynomial.expand ℚ k P * Q, -(P * Polynomial.expand ℚ k Q)],
      ⟨0, mul_ne_zero ((Polynomial.expand_ne_zero (Nat.pos_of_ne_zero hk)).2 hP) hQ⟩, ?_⟩
    have hPQk := congrArg (PowerSeries.expand k hk) hPQ
    rw [map_mul, expand_coe, expand_coe] at hPQk
    show ∑ i : Fin 2, _ = 0
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one, pow_zero,
      pow_one, Polynomial.coe_mul, Polynomial.coe_neg]
    rw [show PowerSeries.expand 1 (pow_ne_zero 0 hk) F = F from
      PowerSeries.expand_one_apply F]
    linear_combination (↑(Polynomial.expand ℚ k P) : PowerSeries ℚ) * hPQ -
      (↑P : PowerSeries ℚ) * hPQk

/-- **Expansion complexity** (Diem; Mérai, Niederreiter and Winterhof). If for every `D` some
precision `n` admits no nonzero `h(X, Y)` over `𝔽₂` of degree at most `D` in each variable with
`h(X, G) ≡ 0 mod Xⁿ`, where `G = ∑ c(t) Xᵗ`, then Problem 1 holds: for an eventually periodic `c`,
`G = P/Q` and `Q(X) Y - P(X)` vanishes at `G` exactly. By Christol's theorem the hypothesis is
equivalent to `c` not being `2`-automatic. -/
theorem problem1_of_expansionComplexity_unbounded
    (h : ∀ D : ℕ, ∃ n : ℕ, ∀ g : Polynomial (Polynomial (ZMod 2)), g ≠ 0 → g.natDegree ≤ D →
      (∀ i, (g.coeff i).natDegree ≤ D) →
        PowerSeries.trunc n (g.eval₂ Polynomial.coeToPowerSeries.ringHom
          (LinearRelations.series (ZMod 2) c)) ≠ 0) :
    Rule30Prize.Problem1 := by
  intro hep
  obtain ⟨P, Q, hQ, hPQ⟩ := (LinearRelations.eventuallyPeriodic_iff_rational (K := ZMod 2) c).1 hep
  set g : Polynomial (Polynomial (ZMod 2)) := Polynomial.C Q * Polynomial.X - Polynomial.C P
  have hg : g ≠ 0 := by
    intro h0
    have := congrArg (fun q => q.coeff 1) h0
    simp [g] at this
    exact hQ this
  obtain ⟨n, hn⟩ := h (max (max Q.natDegree P.natDegree) 1)
  refine hn g hg ?_ ?_ ?_
  · calc g.natDegree ≤ max (Polynomial.C Q * Polynomial.X).natDegree (Polynomial.C P).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ ≤ max (max Q.natDegree P.natDegree) 1 := by
          refine max_le ((Polynomial.natDegree_C_mul_le _ _).trans ?_) ?_
          · rw [Polynomial.natDegree_X]; exact le_max_right _ _
          · rw [Polynomial.natDegree_C]; exact Nat.zero_le _
  · intro i
    simp only [g, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C]
    split_ifs <;> simp only [mul_one, mul_zero, sub_zero, zero_sub, Polynomial.natDegree_neg,
      Polynomial.natDegree_zero] <;>
      omega
  · simp only [g, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, Polynomial.coeToPowerSeries.ringHom_apply, hPQ, sub_self,
      map_zero]

/-- `b` is morphic: a coding `τ` of a fixed point `x` of a non-erasing morphism `σ` of a finite
alphabet. `x` is a fixed point: reading `σ(x 0) σ(x 1) σ(x 2) …` gives `x` back, so the block
`σ(x n)` sits at the position `∑_{i < n} |σ(x i)|`. -/
def IsMorphic (b : ℕ → Bool) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (σ : A → List A) (x : ℕ → A) (τ : A → Bool),
    (∀ a, σ a ≠ []) ∧
    (∀ n (j : ℕ) (hj : j < (σ (x n)).length),
      x (∑ i ∈ Finset.range n, (σ (x i)).length + j) = (σ (x n))[j]) ∧
    ∀ n, b n = τ (x n)

/-- The position of time `n` in a transient of length `T` followed by a period `Q`. -/
def posOf (T Q n : ℕ) : ℕ := if n < T + Q then n else T + (n - T) % Q

/-- The position after the position `i`. -/
def nxtOf (T Q i : ℕ) : ℕ := if i + 1 < T + Q then i + 1 else T

theorem posOf_lt {T Q : ℕ} (hQ : 0 < Q) (n : ℕ) : posOf T Q n < T + Q := by
  unfold posOf
  split_ifs
  · assumption
  · have := Nat.mod_lt (n - T) hQ; omega

theorem posOf_succ {T Q : ℕ} (hQ : 0 < Q) (n : ℕ) :
    posOf T Q (n + 1) = nxtOf T Q (posOf T Q n) := by
  unfold posOf nxtOf
  by_cases h1 : n + 1 < T + Q
  · rw [if_pos h1, if_pos (show n < T + Q by omega), if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : n < T + Q
    · rw [if_pos h2, if_neg h1, show n + 1 - T = Q by omega, Nat.mod_self, Nat.add_zero]
    · rw [if_neg h2]
      have hlt := Nat.mod_lt (n - T) hQ
      have e : (n + 1 - T) % Q = ((n - T) % Q + 1) % Q := by
        rw [show n + 1 - T = (n - T) + 1 by omega, Nat.add_mod (n - T)]
        rcases Nat.lt_or_ge 1 Q with hQ1 | hQ1
        · rw [Nat.mod_eq_of_lt hQ1]
        · obtain rfl : Q = 1 := by omega
          simp
      rw [e]
      by_cases h3 : (n - T) % Q + 1 < Q
      · rw [Nat.mod_eq_of_lt h3, if_pos (by omega)]
        omega
      · rw [show (n - T) % Q + 1 = Q by omega, Nat.mod_self, if_neg (by omega), Nat.add_zero]

/-- **Eventually periodic sequences are morphic.** The alphabet is the positions `0, …, T + Q - 1`
of a transient and a period, `σ(0) = 0 1` and `σ(i) = i + 1` for `i ≠ 0`, wrapping from the last
position back to the start `T ≥ 1` of the period. -/
theorem isMorphic_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    IsMorphic b := by
  obtain ⟨T₀, P, hP, hper⟩ := h
  -- a transient `T ≥ 1` and a period `Q ≥ 2`
  set T := T₀ + 1
  set Q := 2 * P
  have hQ : 0 < Q := by omega
  have hperQ : ∀ t, T ≤ t → b (t + Q) = b t := fun t ht => by
    rw [show Q = P + P by omega, ← add_assoc, hper (t + P) (by omega), hper t (by omega)]
  set N := T + Q
  have hN : 3 ≤ N := by omega
  have hpos0 : ∀ n, posOf T Q n = 0 ↔ n = 0 := fun n => by
    unfold posOf
    split_ifs <;> omega
  let σ : Fin N → List (Fin N) := fun i =>
    if (i : ℕ) = 0 then [⟨0, by omega⟩, ⟨1, by omega⟩]
    else [⟨nxtOf T Q i, by unfold nxtOf; split_ifs <;> omega⟩]
  let x : ℕ → Fin N := fun n => ⟨posOf T Q n, posOf_lt hQ n⟩
  have hlen : ∀ n, ∑ i ∈ Finset.range n, (σ (x i)).length = if n = 0 then 0 else n + 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : (σ (x n)).length = if n = 0 then 2 else 1 := by
        simp only [σ, x]
        by_cases hn : n = 0
        · rw [if_pos ((hpos0 n).2 hn), if_pos hn]; rfl
        · rw [if_neg (fun h => hn ((hpos0 n).1 h)), if_neg hn]; rfl
      rw [this]
      split_ifs <;> omega
  refine ⟨Fin N, inferInstance, σ, x, fun i => b i, fun a => ?_, fun n j hj => ?_, fun n => ?_⟩
  · simp only [σ]
    split_ifs <;> simp
  · rw [hlen]
    by_cases hn : n = 0
    · subst hn
      have hx0 : (x 0 : ℕ) = 0 := (hpos0 0).2 rfl
      have hσ : σ (x 0) = [⟨0, by omega⟩, ⟨1, by omega⟩] := by simp only [σ, if_pos hx0]
      rw [if_pos rfl, Nat.zero_add]
      simp only [hσ, List.length_cons, List.length_nil] at hj
      apply Fin.ext
      simp only [hσ, x]
      interval_cases j
      · simp [posOf]
      · simp [posOf]
        omega
    · have hxn : (x n : ℕ) ≠ 0 := fun h => hn ((hpos0 n).1 h)
      have hσ : σ (x n) = [⟨nxtOf T Q (x n), by unfold nxtOf; split_ifs <;> omega⟩] := by
        simp only [σ, if_neg hxn]
      simp only [hσ, List.length_cons, List.length_nil] at hj
      obtain rfl : j = 0 := by omega
      rw [if_neg hn, Nat.add_zero]
      apply Fin.ext
      simp only [hσ, List.getElem_cons_zero, x]
      exact posOf_succ hQ n
  · -- the coding: `b n = b (posOf n)`
    show b n = b (posOf T Q n)
    unfold posOf
    split_ifs with h
    · rfl
    · have key : ∀ k t, T ≤ t → b (t + k * Q) = b t := fun k => by
        induction k with
        | zero => intro t _; simp
        | succ k ih =>
          intro t ht
          rw [Nat.succ_mul, ← add_assoc, hperQ _ (by nlinarith), ih t ht]
      have hdiv := Nat.mod_add_div (n - T) Q
      have := key ((n - T) / Q) (T + (n - T) % Q) (by omega)
      rw [← this]
      congr 1
      rw [mul_comm]
      omega

/-- **Not morphic.** If `c` is not morphic, Problem 1 holds. -/
theorem problem1_of_not_isMorphic (h : ¬ IsMorphic c) : Rule30Prize.Problem1 :=
  fun hep => h (isMorphic_of_eventuallyPeriodic hep)

/-! ### Recurrence -/

/-- `b` is recurrent: every prefix occurs again at a positive position. -/
def IsRecurrent (b : ℕ → Bool) : Prop := ∀ n, ∃ s, 0 < s ∧ ∀ i < n, b (s + i) = b i

/-- In a recurrent sequence every prefix occurs arbitrarily far out. -/
theorem IsRecurrent.exists_ge {b : ℕ → Bool} (h : IsRecurrent b) (n : ℕ) :
    ∀ k, ∃ s, k ≤ s ∧ ∀ i < n, b (s + i) = b i
  | 0 => ⟨0, le_rfl, fun i _ => by rw [Nat.zero_add]⟩
  | k + 1 => by
    obtain ⟨s, hks, hs⟩ := h.exists_ge n k
    obtain ⟨s', hs'0, hs'⟩ := h (s + n)
    refine ⟨s' + s, by omega, fun i hi => ?_⟩
    rw [add_assoc, hs' (s + i) (by omega), hs i hi]

/-- **A recurrent eventually periodic sequence is purely periodic.** -/
theorem IsRecurrent.purelyPeriodic {b : ℕ → Bool} (h : IsRecurrent b) (hep : EventuallyPeriodic b) :
    ∃ P, 0 < P ∧ ∀ t, b (t + P) = b t := by
  obtain ⟨T, P, hP, hper⟩ := hep
  obtain ⟨s, hTs, hs⟩ := h.exists_ge (T + P) T
  refine ⟨P, hP, fun t => ?_⟩
  rcases le_or_gt T t with ht | ht
  · exact hper t ht
  · rw [← hs (t + P) (by omega), ← hs t (by omega), ← add_assoc]
    exact hper _ (by omega)

/-- **Recurrent and not purely periodic.** If `c` is recurrent and not purely periodic, Problem 1
holds. -/
theorem problem1_of_recurrent_not_purelyPeriodic (hrec : IsRecurrent c)
    (h : ¬ ∃ P, 0 < P ∧ ∀ t, c (t + P) = c t) : Rule30Prize.Problem1 :=
  fun hep => h (hrec.purelyPeriodic hep)

/-- **If `c` is recurrent, Problem 1 is the case `T = 0`**: it holds iff `c` is not purely
periodic. -/
theorem problem1_iff_not_purelyPeriodic_of_recurrent (hrec : IsRecurrent c) :
    Rule30Prize.Problem1 ↔ ¬ ∃ P, 0 < P ∧ ∀ t, c (t + P) = c t :=
  ⟨fun h1 ⟨P, hP, hper⟩ => h1 ⟨0, P, hP, fun t _ => hper t⟩,
    problem1_of_recurrent_not_purelyPeriodic hrec⟩

end Rule30Equivalents.StrongerStatements

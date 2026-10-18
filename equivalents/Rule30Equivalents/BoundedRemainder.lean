import Rule30Equivalents.Genericity
import Rule30Equivalents.BlackTimes

/-!
# Bounded remainder

Catalog Section 4. Let `N(n)` be the number of black cells among the first `n` cells of a bit
sequence. An eventually periodic sequence has a *bounded remainder*: `N(n) = α n + O(1)`, with
`α` the density of black cells in a period (`exists_abs_ones_sub_le_of_eventuallyPeriodic`).

* `problem1_of_unbounded_remainder`: **if the number of black cells among the first `n` cells of
  the center column is not `α n + O(1)` for any real `α`, Problem 1 holds.** This is strictly
  stronger than Problem 1: Sturmian sequences are not eventually periodic and have bounded
  remainder.
* `unbounded_remainder_of_disjunctive`: a disjunctive sequence (every word occurs) has unbounded
  remainder for every `α`: a run of `m` black cells raises `N(n) - α n` by `(1 - α) m`, and a run
  of `m` white cells lowers it by `α m`. So the new statement sits between "c is disjunctive" and
  Problem 1.
* `problem1_of_problem2_of_unbounded_discrepancy`: **if Problem 2 holds and the discrepancy
  `N(n) - n/2` of the center column is unbounded, Problem 1 holds**, since an eventually periodic
  sequence with density `1/2` has bounded discrepancy.
-/

namespace Rule30Equivalents.BoundedRemainder

open Filter Topology Ruliology.CellularAutomata Genericity

/-- The number of black cells among the first `n` cells of `b`. -/
def ones (b : ℕ → Bool) (n : ℕ) : ℕ := Nat.count (fun t => b t = true) n

theorem ones_add (b : ℕ → Bool) (a m : ℕ) :
    ones b (a + m) = ones b a + ones (fun j => b (a + j)) m :=
  Nat.count_add _ _ _

theorem ones_le (b : ℕ → Bool) (n : ℕ) : ones b n ≤ n := Nat.count_le _

theorem ones_of_forall_true {g : ℕ → Bool} : ∀ {m : ℕ}, (∀ j < m, g j = true) → ones g m = m
  | 0, _ => by simp [ones]
  | m + 1, h => by
    rw [ones, Nat.count_succ, ← ones, ones_of_forall_true fun j hj => h j (by omega),
      if_pos (h m (by omega))]

theorem ones_of_forall_false {g : ℕ → Bool} : ∀ {m : ℕ}, (∀ j < m, g j = false) → ones g m = 0
  | 0, _ => by simp [ones]
  | m + 1, h => by
    rw [ones, Nat.count_succ, ← ones, ones_of_forall_false fun j hj => h j (by omega),
      if_neg (by simp [h m (by omega)])]

/-- Along a sequence that is periodic from the start, `q` full periods contribute `q` times the
black cells of one period. -/
theorem ones_mul_add {g : ℕ → Bool} {P : ℕ} (hg : ∀ j, g (P + j) = g j) :
    ∀ q r, ones g (q * P + r) = q * ones g P + ones g r
  | 0, r => by simp
  | q + 1, r => by
    rw [show (q + 1) * P + r = P + (q * P + r) by ring, ones_add, show (fun j => g (P + j)) = g
      from funext hg, ones_mul_add hg q r]
    ring

/-- **An eventually periodic sequence has bounded remainder**: `N(n) = α n + O(1)`, with `α` the
density of black cells in one period. -/
theorem exists_abs_ones_sub_le_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ α C : ℝ, ∀ n, |(ones b n : ℝ) - α * n| ≤ C := by
  obtain ⟨T, P, hP, hper⟩ := h
  set g : ℕ → Bool := fun j => b (T + j) with hgdef
  have hg : ∀ j, g (P + j) = g j := fun j => by
    simp only [hgdef]
    rw [show T + (P + j) = T + j + P by ring]
    exact hper (T + j) (by omega)
  have hkP : ones g P ≤ P := ones_le g P
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  refine ⟨(ones g P : ℝ) / P, 2 * (T + P), fun n => ?_⟩
  have hα0 : 0 ≤ (ones g P : ℝ) / P := by positivity
  have hα1 : (ones g P : ℝ) / P ≤ 1 := by
    rw [div_le_one hP']
    exact_mod_cast hkP
  rcases Nat.lt_or_ge n T with hn | hn
  · -- before the periodic part both terms are at most `T`
    have h1 : (ones b n : ℝ) ≤ n := by exact_mod_cast ones_le b n
    have h2 : (n : ℝ) < T := by exact_mod_cast hn
    have h3 : (ones g P : ℝ) / P * n ≤ n := by nlinarith
    have h4 : 0 ≤ (ones g P : ℝ) / P * n := by positivity
    rw [abs_le]
    constructor <;> nlinarith
  · -- `n = T + q P + r` with `r < P`
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hdecomp := Nat.div_add_mod m P
    set q := m / P
    set r := m % P
    have hr : r < P := Nat.mod_lt m hP
    have hcount : ones b (T + m) = ones b T + q * ones g P + ones g r := by
      rw [ones_add, ← hdecomp, show P * q + r = q * P + r by ring, ones_mul_add hg, add_assoc]
    have hrT : (ones b T : ℝ) ≤ T := by exact_mod_cast ones_le b T
    have hrr : (ones g r : ℝ) ≤ r := by exact_mod_cast ones_le g r
    have hr' : (r : ℝ) < P := by exact_mod_cast hr
    have hm : (m : ℝ) = q * P + r := by exact_mod_cast (by rw [← hdecomp]; ring : m = q * P + r)
    have key : (ones b (T + m) : ℝ) - (ones g P : ℝ) / P * ((T + m : ℕ) : ℝ) =
        ones b T + ones g r - (ones g P : ℝ) / P * (T + r) := by
      rw [hcount]
      push_cast
      rw [hm]
      field_simp
      ring
    rw [key, abs_le]
    have h5 : (ones g P : ℝ) / P * (T + r) ≤ T + r := by
      have : (0 : ℝ) ≤ T + r := by positivity
      nlinarith
    have h6 : 0 ≤ (ones g P : ℝ) / P * (T + r) := by positivity
    have h7 : (0 : ℝ) ≤ ones b T := by positivity
    have h8 : (0 : ℝ) ≤ ones g r := by positivity
    constructor <;> nlinarith

/-- **Problem 1 from an unbounded remainder**: if the number of black cells among the first `n`
cells of the center column is not `α n + O(1)` for any real `α`, Problem 1 holds. -/
theorem problem1_of_unbounded_remainder
    (h : ∀ α C : ℝ, ∃ n, C < |(ones Rule30Prize.center n : ℝ) - α * n|) :
    Rule30Prize.Problem1 := fun hep => by
  obtain ⟨α, C, hC⟩ := exists_abs_ones_sub_le_of_eventuallyPeriodic hep
  obtain ⟨n, hn⟩ := h α C
  exact absurd (hC n) (not_le.2 hn)

/-- **A disjunctive sequence has unbounded remainder** for every `α`: a run of `m` black cells
raises `N(n) - α n` by `(1 - α) m`, a run of `m` white cells lowers it by `α m`, and one of the two
changes is at least `m/2`. -/
theorem unbounded_remainder_of_disjunctive {v : ℕ → Bool} (hv : Disjunctive v) (α C : ℝ) :
    ∃ n, C < |(ones v n : ℝ) - α * n| := by
  by_contra hcon
  push Not at hcon
  -- a run of `m` equal cells changes the remainder by `(1 - α) m` or by `-α m`
  set m := ⌈4 * C⌉₊ + 1
  have hm : 4 * C < m := by
    have := Nat.le_ceil (4 * C)
    push_cast [m]
    linarith
  obtain ⟨i, hi⟩ := hv m fun _ => true
  obtain ⟨i', hi'⟩ := hv m fun _ => false
  have h1 : ones v (i + m) = ones v i + m := by
    rw [ones_add, ones_of_forall_true fun j hj => hi ⟨j, hj⟩]
  have h0 : ones v (i' + m) = ones v i' := by
    rw [ones_add, ones_of_forall_false fun j hj => hi' ⟨j, hj⟩, add_zero]
  have e1 := abs_le.1 (hcon (i + m))
  have e2 := abs_le.1 (hcon i)
  have e3 := abs_le.1 (hcon (i' + m))
  have e4 := abs_le.1 (hcon i')
  rw [h1] at e1
  rw [h0] at e3
  push_cast at e1 e2 e3 e4
  -- `|1 - α| m ≤ 2C` and `|α| m ≤ 2C`, so `m ≤ 4C`
  have hA : (1 - α) * m ≤ 2 * C := by linarith
  have hB : -((1 - α) * m) ≤ 2 * C := by linarith
  have hC' : α * m ≤ 2 * C := by linarith
  have hD : -(α * m) ≤ 2 * C := by linarith
  have hmpos : (0 : ℝ) ≤ m := by positivity
  rcases le_total α (1 / 2) with hα | hα
  · nlinarith
  · nlinarith

/-- **Problem 1 from Problem 2 and an unbounded discrepancy**: if the center column has density
`1/2` and `N(n) - n/2` is unbounded, Problem 1 holds. An eventually periodic sequence has
`N(n) = α n + O(1)`, and density `1/2` forces `α = 1/2`. -/
theorem problem1_of_problem2_of_unbounded_discrepancy (h2 : Rule30Prize.Problem2)
    (h : ∀ C : ℝ, ∃ n, C < |(ones Rule30Prize.center n : ℝ) - n / 2|) :
    Rule30Prize.Problem1 := fun hep => by
  obtain ⟨α, C, hC⟩ := exists_abs_ones_sub_le_of_eventuallyPeriodic hep
  -- the density is `α`
  have hlim : Tendsto (fun n : ℕ => (ones Rule30Prize.center n : ℝ) / n) atTop (𝓝 α) := by
    have hbound : Tendsto (fun n : ℕ => ((ones Rule30Prize.center n : ℝ) - α * n) / n) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hn']
      exact div_le_div_of_nonneg_right (hC n) hn'.le
    have hadd := hbound.add_const α
    rw [zero_add] at hadd
    refine hadd.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  have h2' := ProblemTwo.problem2_iff_tendsto.1 h2
  have hα : α = 1 / 2 := by
    refine tendsto_nhds_unique hlim (h2'.congr fun n => ?_)
    rw [show (Rule30Prize.blackCount n : ℝ) = (ones Rule30Prize.center n : ℝ) by
      rw [ones, ← BlackTimes.length_filter_eq_count]
      rfl]
  obtain ⟨n, hn⟩ := h C
  have := hC n
  rw [hα, show (1 / 2 : ℝ) * n = n / 2 by ring] at this
  exact absurd this (not_le.2 hn)

end Rule30Equivalents.BoundedRemainder

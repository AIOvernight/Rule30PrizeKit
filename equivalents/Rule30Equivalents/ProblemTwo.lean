import Rule30Equivalents.Basic
import Rule30Equivalents.Tauberian

/-!
# Prize Problem 2: density 1/2

Catalog Section 6.1. `Rule30Prize.Problem2` says that the black cells have density `1/2` in the
center column, stated with integers: for every `k > 0`, eventually `k |2 b(n) - n| ≤ n`, where
`b(n)` counts the black cells among `c(0), …, c(n - 1)`. Two equivalent forms:

* `problem2_iff_tendsto`: `b(n) / n → 1/2`;
* `problem2_iff_abel`: the Abel mean `(1 - x) ∑ c(t) xᵗ` tends to `1/2` as `x → 1⁻`. The forward
  direction is Abelian (`Tauberian.tendsto_abel_of_tendsto_cesaro`); the converse is the
  Hardy–Littlewood–Karamata Tauberian theorem (`Tauberian.tendsto_cesaro_of_tendsto_abel`), which
  applies because the coefficients are nonnegative.
-/

namespace Rule30Equivalents.ProblemTwo

open Filter Topology Ruliology.CellularAutomata

/-- `b(n)` is the sum of the center column over `0, …, n - 1`. -/
theorem blackCount_eq_sum (n : ℕ) :
    (Rule30Prize.blackCount n : ℝ) =
      ∑ t ∈ Finset.range n, if Rule30Prize.center t then (1 : ℝ) else 0 := by
  induction n with
  | zero => simp [Rule30Prize.blackCount]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [Rule30Prize.blackCount, List.range_succ, List.filter_append, List.length_append]
    push_cast
    cases h : Rule30Prize.center n <;> simp [List.filter, h]

theorem le_iff_real (k n : ℕ) :
    k * (2 * (Rule30Prize.blackCount n : ℤ) - n).natAbs ≤ n ↔
      (k : ℝ) * |2 * (Rule30Prize.blackCount n : ℝ) - n| ≤ n := by
  have : ((((2 * (Rule30Prize.blackCount n : ℤ) - n).natAbs : ℕ)) : ℝ) =
      |2 * (Rule30Prize.blackCount n : ℝ) - n| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    ring_nf
  rw [← this, ← Nat.cast_mul, Nat.cast_le]

theorem abs_sub_half {n : ℕ} (hn : 0 < n) :
    |(Rule30Prize.blackCount n : ℝ) / n - 1 / 2| =
      |2 * (Rule30Prize.blackCount n : ℝ) - n| / (2 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (Rule30Prize.blackCount n : ℝ) / n - 1 / 2 =
      (2 * Rule30Prize.blackCount n - n) / (2 * n) by field_simp, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]

/-- **Problem 2 as a limit**: the proportion of black cells tends to `1/2`. -/
theorem problem2_iff_tendsto : Rule30Prize.Problem2 ↔
    Tendsto (fun n : ℕ => (Rule30Prize.blackCount n : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  constructor
  · intro h2
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    have hk' : (0 : ℝ) < k := lt_trans (by positivity) hk
    obtain ⟨N, hN⟩ := h2 k (by exact_mod_cast hk')
    refine ⟨N + 1, fun n hn => ?_⟩
    have hn0 : 0 < n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 := (le_iff_real k n).1 (hN n (by omega))
    rw [Real.dist_eq, abs_sub_half hn0, div_lt_iff₀ (by positivity)]
    have hεk : 1 < ε * k := by rwa [div_lt_iff₀ hε, mul_comm] at hk
    nlinarith [abs_nonneg (2 * (Rule30Prize.blackCount n : ℝ) - n)]
  · intro h k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h (1 / (2 * k)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 := hN n hn
    rw [Real.dist_eq, abs_sub_half hn0, div_lt_div_iff₀ (by positivity) (by positivity)] at h1
    rw [le_iff_real]
    nlinarith

/-- **Problem 2 as an Abel limit**: `(1 - x) ∑ c(t) xᵗ → 1/2` as `x → 1⁻`. -/
theorem problem2_iff_abel : Rule30Prize.Problem2 ↔
    Tendsto (fun x : ℝ => (1 - x) * ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) * x ^ t)
      (𝓝[<] 1) (𝓝 (1 / 2)) := by
  have hcesaro : Rule30Prize.Problem2 ↔ Tendsto (fun N : ℕ =>
      (∑ t ∈ Finset.range N, if Rule30Prize.center t then (1 : ℝ) else 0) / N) atTop
        (𝓝 (1 / 2)) := by
    rw [problem2_iff_tendsto]
    simp only [blackCount_eq_sum]
  rw [hcesaro]
  constructor
  · intro h
    refine Tauberian.tendsto_abel_of_tendsto_cesaro (B := 1) (fun t => ?_) h
    split_ifs <;> simp
  · intro h
    refine Tauberian.tendsto_cesaro_of_tendsto_abel (fun t => ?_) (fun x hx0 hx1 => ?_) h
    · split_ifs <;> simp
    · refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_)
        (summable_geometric_of_lt_one hx0 hx1)
      · split_ifs <;> simp [pow_nonneg hx0]
      · split_ifs <;> simp [pow_nonneg hx0]

end Rule30Equivalents.ProblemTwo

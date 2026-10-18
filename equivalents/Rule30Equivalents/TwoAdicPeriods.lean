import Rule30Equivalents.LinearRelations
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Periods that are powers of two: the 2-adic and Mahler forms

Catalog Section 5, "no eventual period `2^k`". This weaker statement follows from Problem 1 and
includes periods `2` and `4`, so it is open. Its two equivalent forms in the catalog are proved
here, for every bit sequence.

* **2-adic continuity** (`exists_continuous_extension_iff`): `u : ℕ → Bool` has a period `2^k` iff
  it extends to a continuous function `ℤ₂ → Bool`. On the compact `ℤ₂` such a function is constant
  on all balls of some radius `δ` (Lebesgue's number lemma), so it reads only `α mod 2^k` once
  `2^-k < δ`. Conversely `α ↦ u (α mod 2^k)` is locally constant.
* **Mahler coefficients over `𝔽₂`** (`exists_fwdDiff_eq_zero_iff`): `u : ℕ → 𝔽₂` has a period
  `2^k` iff its forward differences `Δⁿu(0) = ∑_{j ≤ n} C(n, j) u(j)` (`fwdDiff_iter_zero`), its
  Mahler coefficients, vanish for all large `n`. In characteristic `2`,
  `Δ^(2^k) u (t) = u (t + 2^k) - u t` (`fwdDiff_iter_two_pow`), and Newton's forward formula
  (Mathlib's `shift_eq_sum_fwdDiff_iter`) writes `Δ^(2^k) u (t)` through the coefficients
  `Δ^(j + 2^k) u (0)`.

For the center column (`noTwoPowPeriod_iff_not_continuous`, `noTwoPowPeriod_iff_fwdDiff`): `c` has
no eventual period `2^k` iff no tail of `c` extends continuously to `ℤ₂`, iff the `𝔽₂` Mahler
coefficients of every tail are not eventually `0`.
-/

namespace Rule30Equivalents.TwoAdicPeriods

open Ruliology.CellularAutomata LinearRelations
open scoped fwdDiff

/-! ### 2-adic continuity -/

/-- A continuous function on `ℤ₂` with values in `Bool` restricts to a sequence with a period
`2^k`. -/
theorem exists_period_of_continuous {u : ℕ → Bool} {F : ℤ_[2] → Bool} (hF : Continuous F)
    (hFu : ∀ n : ℕ, F n = u n) : ∃ k, ∀ t, u (t + 2 ^ k) = u t := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := Set.univ)
    (c := fun b : Bool => F ⁻¹' {b}) isCompact_univ
    (fun b => hF.isOpen_preimage _ (isOpen_discrete _))
    (fun α _ => Set.mem_iUnion.2 ⟨F α, rfl⟩)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, fun t => ?_⟩
  obtain ⟨b, hb⟩ := hball (t : ℤ_[2]) (Set.mem_univ _)
  have h1 : (t : ℤ_[2]) ∈ Metric.ball (t : ℤ_[2]) δ := Metric.mem_ball_self hδ
  have h2 : ((t + 2 ^ k : ℕ) : ℤ_[2]) ∈ Metric.ball (t : ℤ_[2]) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have e : ((t + 2 ^ k : ℕ) : ℤ_[2]) - (t : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ k := by
      push_cast
      ring
    rw [e, PadicInt.norm_p_pow]
    calc ((2 : ℕ) : ℝ) ^ (-(k : ℤ)) = (1 / 2 : ℝ) ^ k := by
          rw [zpow_neg, zpow_natCast, one_div, inv_pow]
          norm_num
      _ < δ := hk
  have e1 := hb h1
  have e2 := hb h2
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at e1 e2
  rw [← hFu, ← hFu, e1, e2]

/-- A sequence with period `2^k` extends to the locally constant `α ↦ u (α mod 2^k)` on `ℤ₂`. -/
theorem exists_continuous_of_period {u : ℕ → Bool} {k : ℕ} (hk : ∀ t, u (t + 2 ^ k) = u t) :
    ∃ F : ℤ_[2] → Bool, Continuous F ∧ ∀ n : ℕ, F n = u n := by
  refine ⟨fun α => u (PadicInt.toZModPow k α).val, IsLocallyConstant.continuous ?_, fun n => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro α
    filter_upwards [Metric.closedBall_mem_nhds α (zpow_pos (by norm_num : (0 : ℝ) < 2) (-(k : ℤ)))]
      with β hβ
    have hmem : β - α ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ k} := by
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      rw [Metric.mem_closedBall, dist_eq_norm] at hβ
      exact_mod_cast hβ
    have h0 : PadicInt.toZModPow k (β - α) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact_mod_cast hmem
    rw [map_sub, sub_eq_zero] at h0
    simp only [h0]
  · show u (PadicInt.toZModPow k (n : ℤ_[2])).val = u n
    rw [map_natCast, ZMod.val_natCast]
    exact Function.Periodic.map_mod_nat (f := u) hk n

/-- **2-adic form.** A bit sequence has a period that is a power of `2` iff it extends to a
continuous function on the `2`-adic integers. -/
theorem exists_continuous_extension_iff (u : ℕ → Bool) :
    (∃ F : ℤ_[2] → Bool, Continuous F ∧ ∀ n : ℕ, F n = u n) ↔ ∃ k, ∀ t, u (t + 2 ^ k) = u t :=
  ⟨fun ⟨_, hF, hFu⟩ => exists_period_of_continuous hF hFu,
    fun ⟨_, hk⟩ => exists_continuous_of_period hk⟩

/-! ### Mahler coefficients over `𝔽₂` -/

/-- The `n`-th Mahler coefficient over `𝔽₂`: `Δⁿu(0) = ∑_{j ≤ n} C(n, j) u(j)`. -/
theorem fwdDiff_iter_zero (u : ℕ → ZMod 2) (n : ℕ) :
    Δ_[1]^[n] u 0 = ∑ j ∈ Finset.range (n + 1), (n.choose j : ZMod 2) * u j := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zero_add, smul_eq_mul, mul_one, zsmul_eq_mul]
  push_cast
  rw [show (-1 : ZMod 2) = 1 by decide, one_pow, one_mul]

/-- In characteristic `2`, the `2^k`-th forward difference is the difference at distance `2^k`. -/
theorem fwdDiff_iter_two_pow (k : ℕ) :
    ∀ (u : ℕ → ZMod 2) (t : ℕ), Δ_[1]^[2 ^ k] u t = u (t + 2 ^ k) - u t := by
  induction k with
  | zero => intro u t; simp [fwdDiff]
  | succ k ih =>
    intro u t
    rw [pow_succ, mul_two, Function.iterate_add_apply, ih (Δ_[1]^[2 ^ k] u) t, ih u (t + 2 ^ k),
      ih u t, ← add_assoc]
    have h2 : (2 : ZMod 2) = 0 := rfl
    linear_combination (u t - u (t + 2 ^ k)) * h2

/-- **Mahler form.** A sequence in `𝔽₂` has a period that is a power of `2` iff its Mahler
coefficients `Δⁿu(0)` vanish for all large `n`. -/
theorem exists_fwdDiff_eq_zero_iff (u : ℕ → ZMod 2) :
    (∃ N, ∀ n, N ≤ n → Δ_[1]^[n] u 0 = 0) ↔ ∃ k, ∀ t, u (t + 2 ^ k) = u t := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun t => ?_⟩
    have hN2 : N ≤ 2 ^ N := Nat.lt_two_pow_self.le
    rw [← sub_eq_zero, ← fwdDiff_iter_two_pow]
    have hnewton := shift_eq_sum_fwdDiff_iter 1 (Δ_[1]^[2 ^ N] u) t 0
    rw [smul_eq_mul, mul_one, zero_add] at hnewton
    rw [hnewton]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Function.iterate_add_apply, hN _ (by omega), smul_zero]
  · rintro ⟨k, hk⟩
    refine ⟨2 ^ k, fun n hn => ?_⟩
    have h0 : Δ_[1]^[2 ^ k] u = 0 := funext fun t => by
      rw [fwdDiff_iter_two_pow, hk, sub_self, Pi.zero_apply]
    have hfix : fwdDiff 1 (0 : ℕ → ZMod 2) = 0 := funext fun _ => sub_self _
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 ^ k := ⟨n - 2 ^ k, by omega⟩
    rw [Function.iterate_add_apply, h0, Function.iterate_fixed hfix, Pi.zero_apply]

/-! ### The center column -/

/-- `c` has no eventual period that is a power of `2`. Problem 1 implies it; it includes the
periods `2` and `4`, so it is open. -/
def NoTwoPowPeriod : Prop := ∀ T k : ℕ, ¬ ∀ t, T ≤ t → c (t + 2 ^ k) = c t

theorem noTwoPowPeriod_of_problem1 (h : Rule30Prize.Problem1) : NoTwoPowPeriod :=
  fun T k hk => h ⟨T, 2 ^ k, by positivity, hk⟩

/-- A period `2^k` of the tail from `T` is an eventual period from `T`. -/
theorem tail_period_iff (T k : ℕ) :
    (∀ t, c (T + (t + 2 ^ k)) = c (T + t)) ↔ ∀ t, T ≤ t → c (t + 2 ^ k) = c t := by
  constructor
  · intro h t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = T + s := ⟨t - T, by omega⟩
    rw [add_assoc]
    exact h s
  · intro h s
    rw [← add_assoc]
    exact h (T + s) (by omega)

/-- **No eventual period `2^k`, 2-adic form**: no tail of `c` extends continuously to `ℤ₂`. -/
theorem noTwoPowPeriod_iff_not_continuous : NoTwoPowPeriod ↔
    ∀ T, ¬ ∃ F : ℤ_[2] → Bool, Continuous F ∧ ∀ n : ℕ, F n = c (T + n) := by
  refine forall_congr' fun T => ?_
  rw [exists_continuous_extension_iff (fun n => c (T + n)), not_exists]
  exact forall_congr' fun k => not_congr (tail_period_iff T k).symm

/-- **No eventual period `2^k`, Mahler form**: for every tail of `c`, read in `𝔽₂`, the Mahler
coefficients `Δⁿ(0) = ∑_{j ≤ n} C(n, j) c(T + j)` are not eventually `0`. -/
theorem noTwoPowPeriod_iff_fwdDiff : NoTwoPowPeriod ↔
    ∀ T N, ∃ n, N ≤ n ∧ Δ_[1]^[n] (fun t => toK (ZMod 2) c (T + t)) 0 ≠ 0 := by
  refine forall_congr' fun T => ?_
  have h := exists_fwdDiff_eq_zero_iff (fun t => toK (ZMod 2) c (T + t))
  simp only [toK_eq_toK_iff] at h
  have h' : (∀ N, ∃ n, N ≤ n ∧ Δ_[1]^[n] (fun t => toK (ZMod 2) c (T + t)) 0 ≠ 0) ↔
      ¬ ∃ N, ∀ n, N ≤ n → Δ_[1]^[n] (fun t => toK (ZMod 2) c (T + t)) 0 = 0 :=
    ⟨fun H ⟨N, hN⟩ => by
      obtain ⟨n, hn, hne⟩ := H N
      exact hne (hN n hn),
     fun H N => by
      by_contra hc
      push Not at hc
      exact H ⟨N, hc⟩⟩
  rw [h', h, not_exists]
  exact forall_congr' fun k => not_congr (tail_period_iff T k).symm

end Rule30Equivalents.TwoAdicPeriods

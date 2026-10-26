import Rule30Equivalents.AutomatonGroup
import Ruliology.CellularAutomata.Rule30RightPeriods
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

namespace Rule30RecordCharge

def threshold (nu : Nat) : Nat → Nat
  | 0 => 1
  | q + 1 => threshold nu q + 2 ^ (nu + threshold nu q + q)

theorem threshold_step_le (nu q : Nat) : threshold nu q ≤ threshold nu (q + 1) := by
  exact Nat.le_add_right _ _

structure Path (nu : Nat) where
  weight : Nat → Nat
  exponent : Nat → Nat
  resource : Nat → Nat
  exponent_zero : exponent 0 = 0
  exponent_step : ∀ i, exponent (i + 1) = exponent i + weight i
  weight_le_two : ∀ i, weight i ≤ 2
  reset_before : ∀ i, weight i = 2 → resource i = 0
  reset_after : ∀ i, weight i = 2 → resource (i + 1) + 1 = 2 ^ (nu + exponent (i + 1) - 1)
  countdown : ∀ i, weight i = 1 → resource i ≤ resource (i + 1) + 1

theorem record_potential {nu : Nat} (p : Path nu) :
    ∀ i q, i + q + 1 ≤ p.exponent i →
      threshold nu q ≤ i ∧ threshold nu (q + 1) ≤ i + p.resource i + 1 := by
  intro i
  induction i with
  | zero =>
    intro q h
    have hz := p.exponent_zero
    omega
  | succ i ih =>
    intro q h
    have he := p.exponent_step i
    have hk := p.weight_le_two i
    have cases : p.weight i = 0 ∨ p.weight i = 1 ∨ p.weight i = 2 := by omega
    rcases cases with h0 | h1 | h2
    · have old := ih (q + 1) (by omega)
      have mono := threshold_step_le nu q
      constructor <;> omega
    · have old := ih q (by omega)
      have drop := p.countdown i h1
      constructor <;> omega
    · have before := p.reset_before i h2
      have after := p.reset_after i h2
      have paid : threshold nu q ≤ i + 1 := by
        cases q with
        | zero => simp only [threshold]; omega
        | succ q =>
          have old := ih q (by omega)
          omega
      refine ⟨paid, ?_⟩
      have exp_le : nu + threshold nu q + q ≤ nu + p.exponent (i + 1) - 1 := by omega
      have pow_le := Nat.pow_le_pow_right (n := 2) (by decide) exp_le
      simp only [threshold]
      omega

theorem record_time_lower_bound {nu : Nat} (p : Path nu) (i q : Nat)
    (h : i + q + 1 ≤ p.exponent i) : threshold nu q ≤ i :=
  (record_potential p i q h).1

theorem exponent_bound_before_threshold {nu : Nat} (p : Path nu) (i q : Nat)
    (h : i < threshold nu q) : p.exponent i ≤ i + q := by
  have hnot : ¬ i + q + 1 ≤ p.exponent i := by
    intro hc
    have := record_time_lower_bound p i q hc
    omega
  omega

theorem threshold_tower_step (nu q : Nat) : 2 ^ (threshold nu q) ≤ threshold nu (q + 1) := by
  have hp := Nat.pow_le_pow_right (n := 2) (by decide)
    (show threshold nu q ≤ nu + threshold nu q + q by omega)
  simp only [threshold]
  omega

def recordR (nu : Nat) : Nat → Nat
  | 0 => 0
  | q + 1 => threshold nu q

theorem recordR_one (nu : Nat) : recordR nu 1 = 1 := rfl

theorem recordR_succ (nu q : Nat) (hq : 1 ≤ q) :
    recordR nu (q + 1) = recordR nu q + 2 ^ (nu + recordR nu q + q - 1) := by
  cases q with
  | zero => omega
  | succ q =>
    simp only [recordR, threshold]
    congr 1

theorem recordR_lower_bound {nu : Nat} (p : Path nu) (i q : Nat)
    (hq : 1 ≤ q) (h : i + q ≤ p.exponent i) : recordR nu q ≤ i := by
  cases q with
  | zero => omega
  | succ q => exact record_time_lower_bound p i q (by omega)

theorem recordR_potential {nu : Nat} (p : Path nu) (i q : Nat)
    (hq : 1 ≤ q) (h : i + q ≤ p.exponent i) : recordR nu (q + 1) ≤ i + p.resource i + 1 := by
  cases q with
  | zero => omega
  | succ q => exact (record_potential p i q (by omega)).2

end Rule30RecordCharge

set_option autoImplicit false

namespace Rule30OrderBridge

open Rule30Equivalents
open TFunction (low low_congr orbit)
open TFunctionCycles (mod_two_pow_eq_iff)
open AutomatonGroup (PhiS orbit_one_eq_wall testBit_two_mul_add_one)
open Ruliology.CellularAutomata
open Rule30Diagonals (R)
open Rule30RightPeriods (Per IsE)

theorem PhiS_bit (s i x : Nat) :
    (PhiS s x).testBit i = xor (x.testBit i)
      (low (x % 2 ^ i) i || s.testBit i) := by
  have hl : low x i = low (x % 2 ^ i) i := by
    apply low_congr
    intro k hk
    simp [Nat.testBit_mod_two_pow, hk]
  simp only [PhiS, Nat.testBit_xor, Nat.testBit_or,
    IntegerRows.testBit_two_mul, IntegerRows.testBit_four_mul]
  change xor (x.testBit i) (low x i || s.testBit i) = _
  rw [hl]

def FiniteOrder (f : Nat → Nat) (n p : Nat) : Prop :=
  ∀ x, x < 2 ^ n → f^[p] x % 2 ^ n = x

theorem finiteOrder_all {s n p : Nat} (h : FiniteOrder (PhiS s) n p) (x : Nat) :
    (PhiS s)^[p] x % 2 ^ n = x % 2 ^ n := by
  have hm : x % 2 ^ n = (x % 2 ^ n) % 2 ^ n := by simp
  have hc := TFunctionCycles.iterate_mod_eq (ψ := fun i y => low y i || s.testBit i) (PhiS_bit s) hm p
  exact hc.trans (h _ (Nat.mod_lt _ (Nat.two_pow_pos _)))

theorem finiteOrder_orbit_mod {s n p : Nat} (h : FiniteOrder (PhiS s) n p)
    (x t : Nat) :
    (PhiS s)^[t + p] x % 2 ^ n = (PhiS s)^[t] x % 2 ^ n := by
  rw [Nat.add_comm t p, Function.iterate_add_apply]
  exact finiteOrder_all h _

theorem right_succ_eq_wall (j t : Nat) :
    R (j + 1) t = ((PhiS 3)^[t] 0).testBit j := by
  have h : R (j + 1) t = (orbit 1 t).testBit (j + 1) := by
    rw [TFunction.orbit_one_eq_a]
    exact (IntegerRows.testBit_a t (j + 1)).symm
  rw [h, orbit_one_eq_wall, testBit_two_mul_add_one]
  simp

theorem per_of_finiteOrder {j p : Nat} (h : FiniteOrder (PhiS 3) j p) : Per j p := by
  cases j with
  | zero => exact Rule30RightPeriods.per_zero p
  | succ j =>
    intro t
    rw [right_succ_eq_wall, right_succ_eq_wall]
    exact (mod_two_pow_eq_iff _ _ _).1 (finiteOrder_orbit_mod h 0 t) j (by omega)

theorem per_of_wall_return {j p : Nat}
    (h : (PhiS 3)^[p] 0 % 2 ^ j = 0) : Per j p := by
  cases j with
  | zero => exact Rule30RightPeriods.per_zero p
  | succ j =>
    intro t
    rw [right_succ_eq_wall, right_succ_eq_wall]
    have hm : (PhiS 3)^[p] 0 % 2 ^ (j + 1) = 0 % 2 ^ (j + 1) := by simpa using h
    have hc := TFunctionCycles.iterate_mod_eq
      (ψ := fun i y => low y i || (3 : Nat).testBit i) (PhiS_bit 3) hm t
    rw [← Function.iterate_add_apply] at hc
    exact (mod_two_pow_eq_iff _ _ _).1 hc j (by omega)

theorem exponent_le_of_finiteOrder {j e b : Nat} (he : IsE j e)
    (h : FiniteOrder (PhiS 3) j (2 ^ b)) : e ≤ b :=
  he.le (per_of_finiteOrder h)

theorem threshold_strict (nu q : Nat) :
    Rule30RecordCharge.threshold nu q < Rule30RecordCharge.threshold nu (q + 1) := by
  have hp := Nat.two_pow_pos (nu + Rule30RecordCharge.threshold nu q + q)
  simp only [Rule30RecordCharge.threshold]
  omega

theorem threshold_ge (nu q : Nat) : q + 1 ≤ Rule30RecordCharge.threshold nu q := by
  induction q with
  | zero => rfl
  | succ q ih => have := threshold_strict nu q; omega

def Q (nu d : Nat) : Nat :=
  Nat.find (show ∃ q, d < Rule30RecordCharge.threshold nu q from
    ⟨d, threshold_ge nu d⟩)

theorem Q_spec (nu d : Nat) : d < Rule30RecordCharge.threshold nu (Q nu d) := by
  unfold Q
  exact Nat.find_spec (p := fun q => d < Rule30RecordCharge.threshold nu q) _

theorem Q_zero (nu : Nat) : Q nu 0 = 0 := by
  unfold Q
  apply Nat.le_zero.mp
  apply Nat.find_min'
  simp [Rule30RecordCharge.threshold]

theorem threshold_mono (nu : Nat) : Monotone (Rule30RecordCharge.threshold nu) := by
  apply monotone_nat_of_le_succ
  exact Rule30RecordCharge.threshold_step_le nu

theorem record_le_iff (nu d q : Nat) :
    Rule30RecordCharge.recordR nu q ≤ d ↔ q ≤ Q nu d := by
  cases q with
  | zero => simp [Rule30RecordCharge.recordR]
  | succ q =>
    change Rule30RecordCharge.threshold nu q ≤ d ↔ q + 1 ≤ Q nu d
    constructor
    · intro h
      by_contra hn
      have hq : Q nu d ≤ q := by omega
      have := threshold_mono nu hq
      have := Q_spec nu d
      omega
    · intro h
      have hn : ¬ d < Rule30RecordCharge.threshold nu q := by
        exact Nat.find_min (p := fun k => d < Rule30RecordCharge.threshold nu k) _ (by
          change q < Q nu d
          omega)
      omega

def B (j : Nat) : Nat := (j + 1) / 2 + Q 0 (j / 2)

theorem B_zero : B 0 = 0 := by simp [B, Q_zero]
theorem B_one : B 1 = 1 := by simp [B, Q_zero]

theorem per_of_order_bound
    (horder : ∀ j, 2 ≤ j → FiniteOrder (PhiS 3) j (2 ^ B j)) :
    ∀ j, Per j (2 ^ B j) := by
  intro j
  rcases j with _ | _ | j
  · exact Rule30RightPeriods.per_zero _
  · rw [B_one]
    exact Rule30RightPeriods.per_one 0
  · exact per_of_finiteOrder (horder _ (by omega))

theorem exponent_le_B
    (horder : ∀ j, 2 ≤ j → FiniteOrder (PhiS 3) j (2 ^ B j))
    {j e : Nat} (he : IsE j e) : e ≤ B j :=
  he.le (per_of_order_bound horder j)

theorem exponent_le_min
    (horder : ∀ j, 2 ≤ j → FiniteOrder (PhiS 3) j (2 ^ B j))
    {j e : Nat} (hj : 2 ≤ j) (he : IsE j e) :
    e ≤ min ((2 * j + 1) / 3) (B j) :=
  Nat.le_min.mpr ⟨he.le (Rule30RightPeriods.per_upper j hj), exponent_le_B horder he⟩

end Rule30OrderBridge

set_option autoImplicit false

namespace Rule30CycleAccounting

open Rule30Equivalents
open TFunctionCycles (per par)

def bitWeight (f : Nat → Nat) (ψ : Nat → Nat → Bool) (x n : Nat) : Nat :=
  if par f ψ n x (per f ψ x n) then 1 else 0

def exponent (f : Nat → Nat) (ψ : Nat → Nat → Bool) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => exponent f ψ x n + bitWeight f ψ x n

theorem bitWeight_le_one (f : Nat → Nat) (ψ : Nat → Nat → Bool) (x n : Nat) :
    bitWeight f ψ x n ≤ 1 := by
  unfold bitWeight
  split <;> omega

theorem per_eq_pow (f : Nat → Nat) (ψ : Nat → Nat → Bool) (x : Nat) :
    ∀ n, per f ψ x n = 2 ^ exponent f ψ x n
  | 0 => rfl
  | n + 1 => by
    simp only [per, exponent, bitWeight]
    split
    · rw [per_eq_pow f ψ x n, Nat.pow_succ, Nat.mul_comm]
    · simpa using per_eq_pow f ψ x n

def pairWeight (f : Nat → Nat) (ψ : Nat → Nat → Bool) (x i : Nat) : Nat :=
  bitWeight f ψ x (2 * i) + bitWeight f ψ x (2 * i + 1)

theorem pairWeight_le_two (f : Nat → Nat) (ψ : Nat → Nat → Bool) (x i : Nat) :
    pairWeight f ψ x i ≤ 2 := by
  have := bitWeight_le_one f ψ x (2 * i)
  have := bitWeight_le_one f ψ x (2 * i + 1)
  unfold pairWeight
  omega

theorem pair_exponent_step (f : Nat → Nat) (ψ : Nat → Nat → Bool) (x i : Nat) :
    exponent f ψ x (2 * (i + 1)) = exponent f ψ x (2 * i) + pairWeight f ψ x i := by
  rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
  simp only [exponent, pairWeight]
  omega

structure Resource (f : Nat → Nat) (ψ : Nat → Nat → Bool) (x nu : Nat) where
  value : Nat → Nat
  reset_before : ∀ i, pairWeight f ψ x i = 2 → value i = 0
  reset_after : ∀ i, pairWeight f ψ x i = 2 →
    value (i + 1) + 1 = 2 ^ (nu + exponent f ψ x (2 * (i + 1)) - 1)
  countdown : ∀ i, pairWeight f ψ x i = 1 → value i ≤ value (i + 1) + 1

def Resource.path {f : Nat → Nat} {ψ : Nat → Nat → Bool} {x nu : Nat}
    (r : Resource f ψ x nu) : Rule30RecordCharge.Path nu where
  weight := pairWeight f ψ x
  exponent := fun i => exponent f ψ x (2 * i)
  resource := r.value
  exponent_zero := rfl
  exponent_step := pair_exponent_step f ψ x
  weight_le_two := pairWeight_le_two f ψ x
  reset_before := r.reset_before
  reset_after := r.reset_after
  countdown := r.countdown

theorem pair_exponent_bound {f : Nat → Nat} {ψ : Nat → Nat → Bool} {x nu : Nat}
    (r : Resource f ψ x nu) (d : Nat) :
    exponent f ψ x (2 * d) ≤ d + Rule30OrderBridge.Q nu d :=
  Rule30RecordCharge.exponent_bound_before_threshold r.path d _ (Rule30OrderBridge.Q_spec nu d)

theorem exponent_bound {f : Nat → Nat} {ψ : Nat → Nat → Bool} {x nu : Nat}
    (r : Resource f ψ x nu) (n : Nat) :
    exponent f ψ x n ≤ (n + 1) / 2 + Rule30OrderBridge.Q nu (n / 2) := by
  have he := pair_exponent_bound r (n / 2)
  have hb := bitWeight_le_one f ψ x (2 * (n / 2))
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hn' : n = 2 * (n / 2) := by omega
    conv_lhs => rw [hn']
    omega
  · have hn' : n = 2 * (n / 2) + 1 := by omega
    conv_lhs => rw [hn', exponent]
    omega

theorem return_of_resource {f : Nat → Nat} {ψ : Nat → Nat → Bool} {x nu : Nat}
    (hf : ∀ i x, (f x).testBit i = xor (x.testBit i) (ψ i (x % 2 ^ i)))
    (r : Resource f ψ x nu) (n : Nat) :
    f^[2 ^ ((n + 1) / 2 + Rule30OrderBridge.Q nu (n / 2))] x % 2 ^ n = x % 2 ^ n := by
  apply (TFunctionCycles.iterate_mod_iff_dvd hf x n _).2
  rw [per_eq_pow]
  exact Nat.pow_dvd_pow 2 (exponent_bound r n)

theorem finiteOrder_of_resources {f : Nat → Nat} {ψ : Nat → Nat → Bool} {nu n : Nat}
    (hf : ∀ i x, (f x).testBit i = xor (x.testBit i) (ψ i (x % 2 ^ i)))
    (hres : ∀ x, x < 2 ^ n → Nonempty (Resource f ψ x nu)) :
    Rule30OrderBridge.FiniteOrder f n (2 ^ ((n + 1) / 2 + Rule30OrderBridge.Q nu (n / 2))) := by
  intro x hx
  obtain ⟨r⟩ := hres x hx
  simpa [Nat.mod_eq_of_lt hx] using return_of_resource hf r n

def WallResource (x : Nat) := Resource (AutomatonGroup.PhiS 3)
  (fun i y => TFunction.low y i || (3 : Nat).testBit i) x 0

theorem wall_per_of_resources (hres : ∀ x, Nonempty (WallResource x)) :
    ∀ j, Ruliology.CellularAutomata.Rule30RightPeriods.Per j (2 ^ Rule30OrderBridge.B j) := by
  apply Rule30OrderBridge.per_of_order_bound
  intro j _
  exact finiteOrder_of_resources (Rule30OrderBridge.PhiS_bit 3) (fun x _ => hres x)

theorem wall_exponent_of_resources (hres : ∀ x, Nonempty (WallResource x))
    {j e : Nat} (he : Ruliology.CellularAutomata.Rule30RightPeriods.IsE j e) :
    e ≤ Rule30OrderBridge.B j :=
  he.le (wall_per_of_resources hres j)

theorem wall_per_of_zero_resource (r : WallResource 0) :
    ∀ j, Ruliology.CellularAutomata.Rule30RightPeriods.Per j (2 ^ Rule30OrderBridge.B j) := by
  intro j
  apply Rule30OrderBridge.per_of_wall_return
  simpa [Rule30OrderBridge.B] using return_of_resource (Rule30OrderBridge.PhiS_bit 3) r j

theorem wall_exponent_of_zero_resource (r : WallResource 0)
    {j e : Nat} (he : Ruliology.CellularAutomata.Rule30RightPeriods.IsE j e) :
    e ≤ Rule30OrderBridge.B j :=
  he.le (wall_per_of_zero_resource r j)

end Rule30CycleAccounting

set_option autoImplicit false

namespace Rule30TemporalCycles

open Rule30Equivalents.TFunctionCycles
open Rule30CycleAccounting

section
variable {f : Nat → Nat} {ψ : Nat → Nat → Bool}
  (hf : ∀ i x, (f x).testBit i = xor (x.testBit i) (ψ i (x % 2 ^ i)))
include hf

theorem bit_period_below (x n k : Nat) (hk : k < n) (t : Nat) :
    (f^[per f ψ x n + t] x).testBit k = (f^[t] x).testBit k := by
  have h := iterate_mod_eq hf (iterate_per_mod hf x n) t
  rw [← Function.iterate_add_apply] at h
  rw [Nat.add_comm (per f ψ x n) t]
  exact (mod_two_pow_eq_iff _ _ _).1 h k hk

theorem bit_period (x n t : Nat) :
    (f^[per f ψ x (n + 1) + t] x).testBit n = (f^[t] x).testBit n :=
  bit_period_below hf x (n + 1) n (by omega) t

theorem bit_antiperiod (x n : Nat) (hw : bitWeight f ψ x n = 1) (t : Nat) :
    (f^[per f ψ x n + t] x).testBit n = !(f^[t] x).testBit n := by
  have hpar : par f ψ n x (per f ψ x n) = true := by
    unfold bitWeight at hw
    split at hw <;> simp_all
  have hp := par_congr hf (iterate_per_mod hf x n) t
  rw [Nat.add_comm (per f ψ x n) t, Function.iterate_add_apply,
    testBit_iterate hf, hp, testBit_iterate hf, hpar, testBit_iterate hf]
  cases x.testBit n <;> cases par f ψ n x t <;> rfl

theorem bit_period_below_pow (x n k : Nat) (hk : k < n) (t : Nat) :
    (f^[2 ^ exponent f ψ x n + t] x).testBit k = (f^[t] x).testBit k := by
  simpa only [per_eq_pow] using bit_period_below hf x n k hk t

theorem bit_period_pow (x n t : Nat) :
    (f^[2 ^ exponent f ψ x (n + 1) + t] x).testBit n = (f^[t] x).testBit n := by
  simpa only [per_eq_pow] using bit_period hf x n t

theorem bit_antiperiod_pow (x n : Nat) (hw : bitWeight f ψ x n = 1) (t : Nat) :
    (f^[2 ^ exponent f ψ x n + t] x).testBit n = !(f^[t] x).testBit n := by
  simpa only [per_eq_pow] using bit_antiperiod hf x n hw t

omit hf in

theorem pair_two_weights (x i : Nat) (hw : pairWeight f ψ x i = 2) :
    bitWeight f ψ x (2 * i) = 1 ∧ bitWeight f ψ x (2 * i + 1) = 1 := by
  have := bitWeight_le_one f ψ x (2 * i)
  have := bitWeight_le_one f ψ x (2 * i + 1)
  unfold pairWeight at hw
  omega

theorem pair_two_low_anti (x i : Nat) (hw : pairWeight f ψ x i = 2) (t : Nat) :
    (f^[2 ^ exponent f ψ x (2 * i) + t] x).testBit (2 * i) =
      !(f^[t] x).testBit (2 * i) :=
  bit_antiperiod_pow hf x (2 * i) (pair_two_weights x i hw).1 t

theorem pair_two_high_anti (x i : Nat) (hw : pairWeight f ψ x i = 2) (t : Nat) :
    (f^[2 * 2 ^ exponent f ψ x (2 * i) + t] x).testBit (2 * i + 1) =
      !(f^[t] x).testBit (2 * i + 1) := by
  have h := bit_antiperiod_pow hf x (2 * i + 1) (pair_two_weights x i hw).2 t
  rw [exponent, (pair_two_weights x i hw).1] at h
  simpa only [Nat.pow_succ, Nat.mul_comm] using h

theorem pair_one_cases (x i : Nat) (hw : pairWeight f ψ x i = 1) :
    (∀ t, (f^[2 ^ exponent f ψ x (2 * i) + t] x).testBit (2 * i + 1) =
      !(f^[t] x).testBit (2 * i + 1)) ∨
    ((∀ t, (f^[2 ^ exponent f ψ x (2 * i) + t] x).testBit (2 * i) =
      !(f^[t] x).testBit (2 * i)) ∧
    (f^[2 * 2 ^ exponent f ψ x (2 * i)] x).testBit (2 * i + 1) =
      x.testBit (2 * i + 1)) := by
  have h0 := bitWeight_le_one f ψ x (2 * i)
  have h1 := bitWeight_le_one f ψ x (2 * i + 1)
  unfold pairWeight at hw
  by_cases hl : bitWeight f ψ x (2 * i) = 0
  · have hh : bitWeight f ψ x (2 * i + 1) = 1 := by omega
    left
    intro t
    simpa only [exponent, hl, Nat.add_zero] using bit_antiperiod_pow hf x (2 * i + 1) hh t
  · have hl' : bitWeight f ψ x (2 * i) = 1 := by omega
    have hh : bitWeight f ψ x (2 * i + 1) = 0 := by omega
    right
    refine ⟨fun t => bit_antiperiod_pow hf x (2 * i) hl' t, ?_⟩
    have h := bit_period_pow hf x (2 * i + 1) 0
    rw [exponent, hh, exponent, hl', Nat.add_zero] at h
    simpa only [Nat.add_zero, Nat.pow_succ, Nat.mul_comm,
      Function.iterate_zero_apply] using h

end

end Rule30TemporalCycles

set_option autoImplicit false
noncomputable section
namespace Rule30PolynomialResource
open Polynomial
abbrev F := ZMod 2
abbrev P := Polynomial F
def p : P := X + 1
def U (n : ℕ) : P := ∑ i ∈ Finset.range n, X ^ i

def AtLeast (r : ℕ) (A : P) : Prop := p ^ r ∣ A

def Exact (r : ℕ) (A : P) : Prop := AtLeast r A ∧ ¬ AtLeast (r + 1) A

lemma p_ne : p ≠ 0 := by
  simpa [p, sub_eq_add_neg, CharTwo.neg_eq] using (X_sub_C_ne_zero (1 : F))
lemma sub_eq_add (A B : P) : A - B = A + B := by simp [sub_eq_add_neg, CharTwo.neg_eq]
lemma geom_identity (n : ℕ) : p * U n = X ^ n + 1 := by
  simpa [p, U, sub_eq_add_neg, CharTwo.neg_eq] using (mul_geom_sum (X : P) n)
lemma eval_U (n : ℕ) : (U n).eval 1 = (n : F) := by simp [U]
lemma eval_odd_U (t : ℕ) : (U (2 * t + 1)).eval 1 = 1 := by
  rw [eval_U, Nat.cast_add, Nat.cast_mul]
  have h : (2 : F) = 0 := by decide
  simp [h]
lemma p_dvd_iff (A : P) : p ∣ A ↔ A.eval 1 = 0 := by
  simpa [p, sub_eq_add_neg, CharTwo.neg_eq, IsRoot] using (dvd_iff_isRoot (p := A) (a := (1 : F)))
lemma exact_factor (r : ℕ) (Q : P) (hq : Q.eval 1 ≠ 0) : Exact r (p ^ r * Q) := by
  constructor
  · exact dvd_mul_right _ _
  · intro h
    have h' : p ∣ Q := by
      apply (mul_dvd_mul_iff_left (pow_ne_zero r p_ne)).mp
      simpa [AtLeast, pow_succ] using h
    exact hq ((p_dvd_iff Q).mp h')

theorem binomial_exact (t v : ℕ) : Exact (2 ^ v) (X ^ ((2*t+1)*2^v) + 1) := by
  have hpow : (X ^ (2*t+1) + (1 : P)) ^ (2^v) = X ^ ((2*t+1)*2^v) + 1 := by
    rw [add_pow_char_pow, ← pow_mul, one_pow]
  rw [← hpow, ← geom_identity, mul_pow]
  apply exact_factor
  simp only [eval_pow, eval_odd_U, one_pow, ne_eq, one_ne_zero, not_false_eq_true]

theorem geometric_exact (t v : ℕ) : Exact (2^v-1) (U ((2*t+1)*2^v)) := by
  have hs : 0 < 2^v := pow_pos (by decide) _
  have h := binomial_exact t v
  rw [← geom_identity] at h
  constructor
  · apply (mul_dvd_mul_iff_left p_ne).mp
    simpa [AtLeast, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2^v)] using h.1
  · intro hh
    apply h.2
    have hm := mul_dvd_mul_left p hh
    simpa [AtLeast, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2^v)] using hm

def rho (cap : ℕ) (A : P) : ℕ := if A = 0 then cap else min cap (A.rootMultiplicity 1)

lemma rho_le_cap (cap : ℕ) (A : P) : rho cap A ≤ cap := by
  unfold rho; split_ifs <;> simp

lemma le_rho_iff (cap r : ℕ) (A : P) (hr : r ≤ cap) :
    r ≤ rho cap A ↔ AtLeast r A := by
  unfold rho
  split_ifs with h
  · simp [h, AtLeast, hr]
  · rw [le_min_iff, and_iff_right hr, le_rootMultiplicity_iff h]
    simp only [AtLeast, p, sub_eq_add_neg, CharTwo.neg_eq, map_one]

lemma rho_divides (cap : ℕ) (A : P) : AtLeast (rho cap A) A :=
  (le_rho_iff cap (rho cap A) A (rho_le_cap cap A)).mp le_rfl

lemma rho_of_exact (cap r : ℕ) (A : P) (hr : r ≤ cap) (h : Exact r A) :
    rho cap A = r := by
  apply Nat.le_antisymm
  · by_contra hh
    have hl : r+1 ≤ rho cap A := by omega
    exact h.2 ((le_rho_iff cap (r+1) A (by have := rho_le_cap cap A; omega)).mp hl)
  · exact (le_rho_iff cap r A hr).mpr h.1

lemma exact_add_high (r : ℕ) (A B : P) (ha : Exact r A) (hb : AtLeast (r+1) B) :
    Exact r (A + B) := by
  have hlo : AtLeast r B := (pow_dvd_pow p (by omega : r ≤ r+1)).trans hb
  refine ⟨dvd_add ha.1 hlo, ?_⟩
  intro h
  have hd := dvd_sub h hb
  simp only [add_sub_cancel_right] at hd
  exact ha.2 hd

lemma exact_mul_unit (r : ℕ) (A Q : P) (ha : Exact r A) (hq : Q.eval 1 ≠ 0) :
    Exact r (Q * A) := by
  obtain ⟨T, ht⟩ := ha.1
  have htunit : T.eval 1 ≠ 0 := by
    intro hz
    have hd := (p_dvd_iff T).mpr hz
    apply ha.2
    rw [ht]
    simpa [AtLeast, pow_succ] using (mul_dvd_mul_left (p^r) hd)
  rw [ht]
  have he := exact_factor r (Q*T) (by simpa using mul_ne_zero hq htunit)
  convert he using 1; ring

theorem complement_reset (t v : ℕ) (H : P) :
    Exact (2^v-1)
      ((1 + X ^ ((2*t+1)*2^v)) * H + X ^ ((2*t+1)*2^v) * U ((2*t+1)*2^v)) := by
  have hu := geometric_exact t v
  have hh := binomial_exact t v
  have hhigh : AtLeast (2^v-1+1) ((1+X^((2*t+1)*2^v))*H) := by
    have hs : 1 ≤ 2^v := Nat.one_le_two_pow
    simpa [AtLeast, Nat.sub_add_cancel hs, add_comm] using (dvd_mul_of_dvd_left hh.1 H)
  have hlow := exact_mul_unit (2^v-1) _ (X^((2*t+1)*2^v)) hu (by simp)
  simpa [add_comm] using exact_add_high _ _ _ hlow hhigh

lemma cancel_difference (r : ℕ) (D : P) (h : AtLeast r (p * D)) : AtLeast (r-1) D := by
  cases r with
  | zero => simp [AtLeast]
  | succ r =>
    apply (mul_dvd_mul_iff_left p_ne).mp
    simpa [AtLeast, pow_succ'] using h

theorem cyclic_countdown (S r : ℕ) (A D B W Z Q T : P)
    (hrS : r ≤ S) (ha : AtLeast r A) (hw : AtLeast r W)
    (hz : AtLeast S Z)
    (hd : p * D = X * (W + A) + Z * Q)
    (hb : B = D + Z * T) : AtLeast (r-1) B := by
  have hzr : AtLeast r Z := (pow_dvd_pow p hrS).trans hz
  have hpd : AtLeast r (p*D) := by
    rw [hd]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_add hw ha) X) (dvd_mul_of_dvd_left hzr Q)
  have hD := cancel_difference r D hpd
  rw [hb]
  exact dvd_add hD (dvd_mul_of_dvd_left ((pow_dvd_pow p (by omega : r-1 ≤ r)).trans hzr) T)

def encode (f : ℕ → F) (M : ℕ) : P := ∑ i ∈ Finset.range M, C (f i) * X^i

lemma encode_succ (f : ℕ → F) (M : ℕ) :
    encode f (M+1) = encode f M + C (f M)*X^M := by
  simp [encode, Finset.sum_range_succ]

lemma encode_add (f g : ℕ → F) (M : ℕ) :
    encode (fun i => f i + g i) M = encode f M + encode g M := by
  simp [encode, map_add, add_mul, Finset.sum_add_distrib]

lemma encode_one (M : ℕ) : encode (fun _ => 1) M = U M := by simp [encode, U]

theorem stream_difference (f : ℕ → F) (M : ℕ) :
    p * encode f M = X * encode (fun i => f (i+1)+f i) M +
      C (f 0) + C (f M) * X^M := by
  induction M with
  | zero => simp [encode, CharTwo.add_self_eq_zero]
  | succ M ih =>
    rw [encode_succ, encode_succ, mul_add, ih]
    simp only [map_add, pow_succ, p]
    ring_nf
    simp [CharTwo.two_eq_zero]

theorem cyclic_difference (f : ℕ → F) (M : ℕ) (hf : f M = f 0) :
    p * encode f M = X * encode (fun i => f (i+1)+f i) M +
      (X^M+1)*C (f 0) := by
  rw [stream_difference, hf]
  ring

lemma encode_append (f : ℕ → F) (M N : ℕ) :
    encode f (M+N) = encode f M + X^M * encode (fun i => f (M+i)) N := by
  simp only [encode, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring

theorem stream_complement (f : ℕ → F) (M : ℕ)
    (hf : ∀ i < M, f (M+i) = f i + 1) :
    encode f (2*M) = (1+X^M)*encode f M + X^M * U M := by
  have he : encode (fun i => f (M+i)) M = encode (fun i => f i+1) M := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [hf i (Finset.mem_range.mp hi)]
  rw [show 2*M = M+M by omega, encode_append, he, encode_add, encode_one]
  ring

theorem stream_reset (f : ℕ → F) (t v : ℕ)
    (hf : ∀ i < (2*t+1)*2^v, f ((2*t+1)*2^v+i) = f i + 1) :
    Exact (2^v-1) (encode f (2*((2*t+1)*2^v))) := by
  rw [stream_complement f _ hf]
  exact complement_reset t v _

theorem stream_countdown (f a : ℕ → F) (t v : ℕ)
    (hcycle : f (2*((2*t+1)*2^v)) = f 0)
    (hforce : ∀ i < (2*t+1)*2^v,
      (f (((2*t+1)*2^v)+(i+1)) + f (i+1)) +
      (f (((2*t+1)*2^v)+i) + f i) = 1 + a i) :
    rho (2^v-1) (encode a ((2*t+1)*2^v)) ≤
      rho (2*2^v-1) (encode f (2*((2*t+1)*2^v))) + 1 := by
  let M := (2*t+1)*2^v
  let D : ℕ → F := fun i => f (M+i) + f i
  let r := rho (2^v-1) (encode a M)
  have hr : r ≤ 2^v-1 := rho_le_cap _ _
  have hs : 1 ≤ 2^v := Nat.one_le_two_pow
  have hDcycle : D M = D 0 := by
    dsimp [D]
    rw [show M+M = 2*((2*t+1)*2^v) by dsimp [M]; omega, hcycle]
    exact add_comm _ _
  have hdiff : encode (fun i => D (i+1)+D i) M = U M + encode a M := by
    rw [← encode_one, ← encode_add]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [D, M]
    rw [hforce i (Finset.mem_range.mp hi)]
  have hd := cyclic_difference D M hDcycle
  rw [hdiff] at hd
  have hb : encode f (2*M) = encode D M + (X^M+1)*encode (fun i => f (M+i)) M := by
    rw [show 2*M = M+M by omega, encode_append]
    dsimp [D]
    rw [encode_add]
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hu : AtLeast r (U M) :=
    (pow_dvd_pow p hr).trans (geometric_exact t v).1
  have hout := cyclic_countdown (2^v) r (encode a M) (encode D M)
    (encode f (2*M)) (U M) (X^M+1) (C (D 0))
    (encode (fun i => f (M+i)) M) (by omega) (rho_divides _ _) hu
    (binomial_exact t v).1 hd hb
  have hc : r-1 ≤ 2*2^v-1 := by omega
  have hbnd := (le_rho_iff (2*2^v-1) (r-1) (encode f (2*M)) hc).mpr hout
  dsimp [r, M] at hbnd
  omega

theorem high_force_difference (aa ell h0 h1 hM hM1 : F)
    (hfirst : h1+h0 = aa+(1+aa)*ell)
    (hsecond : hM1+hM = aa+(1+aa)*(ell+1)) :
    (hM1+h1)+(hM+h0) = 1+aa := by
  have h : (hM1+hM)+(h1+h0) =
      (aa+(1+aa)*(ell+1))+(aa+(1+aa)*ell) := congrArg₂ (·+·) hsecond hfirst
  have hh : (aa+(1+aa)*(ell+1))+(aa+(1+aa)*ell) = 1+aa := by
    ring_nf
    simp [CharTwo.two_eq_zero, show (3 : F) = 1 by decide]
  rw [hh] at h
  convert h using 1; ring

theorem reset_before (cap : ℕ) (A : P) (h : cap = 0 ∨ A.eval 1 ≠ 0) : rho cap A = 0 := by
  rcases h with h | h
  · subst cap; exact Nat.eq_zero_of_le_zero (rho_le_cap 0 A)
  · have hex : Exact 0 A := by
      constructor
      · simp [AtLeast]
      · simpa [AtLeast, p_dvd_iff] using h
    exact rho_of_exact cap 0 A (Nat.zero_le _) hex

@[simp] theorem rho_zero (cap : ℕ) : rho cap 0 = cap := by simp [rho]
@[simp] theorem rho_cap_zero (A : P) : rho 0 A = 0 := by simp [rho]

theorem stream_reset_resource (f : ℕ → F) (t v : ℕ) (cap : ℕ)
    (hcap : 2^v-1 ≤ cap)
    (hf : ∀ i < (2*t+1)*2^v, f ((2*t+1)*2^v+i) = f i + 1) :
    rho cap (encode f (2*((2*t+1)*2^v))) = 2^v-1 :=
  rho_of_exact cap _ _ hcap (stream_reset f t v hf)

end Rule30PolynomialResource
end

set_option autoImplicit false
noncomputable section
namespace Rule30TemporalResource
open Polynomial Rule30PolynomialResource

def bit (b : Bool) : F := if b then 1 else 0

lemma bit_xor (a b : Bool) : bit (xor a b) = bit a + bit b := by
  cases a <;> cases b <;> decide
lemma bit_or (a b : Bool) : bit (a || b) = bit a + bit b + bit a * bit b := by
  cases a <;> cases b <;> decide
lemma bit_not (a : Bool) : bit (!a) = bit a + 1 := by cases a <;> decide

theorem or_force_difference (b s h0 h1 hM hM1 : Bool)
    (hfirst : h1 = xor h0 (b || s))
    (hsecond : hM1 = xor hM ((!b) || s)) :
    (bit hM1+bit h1)+(bit hM+bit h0) = 1+bit s := by
  subst h1; subst hM1
  cases b <;> cases s <;> cases h0 <;> cases hM <;> decide

lemma eval_encode (f : ℕ → F) (M : ℕ) : (encode f M).eval 1 = ∑ i ∈ Finset.range M, f i := by
  simp [encode, Polynomial.eval_finsetSum]

theorem anticycle_parent_parity (f a : ℕ → F) (M : ℕ)
    (hcycle : f (2*M) = f 0+1)
    (hforce : ∀ i < M,
      (f (M+(i+1)) + f (i+1)) + (f (M+i) + f i) = 1+a i) :
    (encode a M).eval 1 = 1+(M : F) := by
  let D : ℕ → F := fun i => f (M+i)+f i
  have hdiff : encode (fun i => D (i+1)+D i) M = U M + encode a M := by
    rw [← encode_one, ← encode_add]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [D]
    rw [hforce i (Finset.mem_range.mp hi)]
  have h := congrArg (Polynomial.eval (1 : F)) (stream_difference D M)
  rw [hdiff] at h
  simp only [eval_mul, eval_add, p, eval_X, eval_one, one_add_one_eq_two,
    CharTwo.two_eq_zero, zero_mul, one_mul, eval_U, eval_C, eval_pow, one_pow,
    mul_one] at h
  have hd : D M = D 0+1 := by
    dsimp [D]
    rw [show M+M = 2*M by omega, hcycle]
    ring
  rw [hd] at h
  have hcancel : D 0 + (D 0+1) = (1 : F) := by ring_nf; simp [CharTwo.two_eq_zero]
  have heq : (M : F)+(encode a M).eval 1+1 = 0 := by
    have hh : (M : F)+(encode a M).eval 1+(D 0+(D 0+1)) = 0 := by
      simpa only [add_assoc] using h.symm
    rwa [hcancel] at hh
  have hh := congrArg (fun x : F => x+(M : F)+1) heq
  ring_nf at hh ⊢
  simpa [CharTwo.two_eq_zero, show (3 : F)=1 by decide] using hh

theorem anticycle_reset_before (f a : ℕ → F) (v : ℕ)
    (hcycle : f (2*2^v) = f 0+1)
    (hforce : ∀ i < 2^v,
      (f (2^v+(i+1)) + f (i+1)) + (f (2^v+i) + f i) = 1+a i) :
    rho (2^v-1) (encode a (2^v)) = 0 := by
  apply reset_before
  cases v with
  | zero => exact Or.inl rfl
  | succ v =>
    right
    rw [anticycle_parent_parity f a _ hcycle hforce]
    have hcast : ((2^(v+1) : ℕ) : F) = 0 := by
      rw [Nat.cast_pow]
      have htwo : (2 : F) = 0 := by decide
      simp [htwo]
    simp [hcast]

theorem stream_or_force (s b h : ℕ → Bool) (M : ℕ)
    (hs : ∀ i, s (M+i) = s i)
    (hb : ∀ i, b (M+i) = !(b i))
    (hh : ∀ i, h (i+1) = xor (h i) (b i || s i)) :
    ∀ i, (bit (h (M+(i+1)))+bit (h (i+1)))+
      (bit (h (M+i))+bit (h i)) = 1+bit (s i) := by
  intro i
  apply or_force_difference (b i) (s i) (h i) (h (i+1)) (h (M+i)) (h (M+(i+1))) (hh i)
  have ht := hh (M+i)
  rw [hs i, hb i] at ht
  simpa [Nat.add_assoc] using ht

theorem dyadic_reset_after (h : ℕ → Bool) (v : ℕ)
    (hh : ∀ i < 2*2^v, h (2*2^v+i) = !(h i)) :
    rho (4*2^v-1) (encode (fun i => bit (h i)) (4*2^v)) + 1 = 2*2^v := by
  have ht : ∀ i < (2*0+1)*2^(v+1),
      bit (h ((2*0+1)*2^(v+1)+i)) = bit (h i)+1 := by
    intro i hi
    have hpow : (2*0+1)*2^(v+1) = 2*2^v := by simp [pow_succ]; omega
    rw [hpow] at hi ⊢
    rw [hh i hi, bit_not]
  have hpow : 2^(v+1) = 2*2^v := by rw [pow_succ]; omega
  have hr := stream_reset_resource (fun i => bit (h i)) 0 (v+1) (4*2^v-1) (by rw [hpow]; omega) ht
  simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] at hr
  rw [hpow] at hr
  rw [show 2*(2*2^v) = 4*2^v by omega] at hr
  rw [hr]
  have hs : 1 ≤ 2^v := Nat.one_le_two_pow
  omega

theorem dyadic_fixed_countdown (s h : ℕ → Bool) (v : ℕ)
    (hh : ∀ i < 2^v, h (2^v+i) = !(h i)) :
    rho (2^v-1) (encode (fun i => bit (s i)) (2^v)) ≤
      rho (2*2^v-1) (encode (fun i => bit (h i)) (2*2^v))+1 := by
  have ht : ∀ i < (2*0+1)*2^v,
      bit (h ((2*0+1)*2^v+i)) = bit (h i)+1 := by
    simpa only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] using
      (fun i hi => (congrArg bit (hh i hi)).trans (bit_not (h i)))
  have hr := stream_reset_resource (fun i => bit (h i)) 0 v (2*2^v-1) (by omega) ht
  simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] at hr
  have hp := rho_le_cap (2^v-1) (encode (fun i => bit (s i)) (2^v))
  omega

theorem dyadic_flipping_countdown (s b h : ℕ → Bool) (v : ℕ)
    (hs : ∀ i, s (2^v+i) = s i)
    (hb : ∀ i, b (2^v+i) = !(b i))
    (hh : ∀ i, h (i+1) = xor (h i) (b i || s i))
    (hcycle : h (2*2^v) = h 0) :
    rho (2^v-1) (encode (fun i => bit (s i)) (2^v)) ≤
      rho (2*2^v-1) (encode (fun i => bit (h i)) (2*2^v))+1 := by
  have hf := stream_or_force s b h (2^v) hs hb hh
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] using
    stream_countdown (fun i => bit (h i)) (fun i => bit (s i)) 0 v
      (by simpa using congrArg bit hcycle) (fun i _ => by simpa only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] using hf i)

theorem dyadic_reset_before (s b h : ℕ → Bool) (v : ℕ)
    (hs : ∀ i, s (2^v+i) = s i)
    (hb : ∀ i, b (2^v+i) = !(b i))
    (hh : ∀ i, h (i+1) = xor (h i) (b i || s i))
    (hcycle : h (2*2^v) = !(h 0)) :
    rho (2^v-1) (encode (fun i => bit (s i)) (2^v)) = 0 := by
  apply anticycle_reset_before (fun i => bit (h i)) (fun i => bit (s i)) v
  · rw [hcycle, bit_not]
  · intro i _
    exact stream_or_force s b h (2^v) hs hb hh i

end Rule30TemporalResource
end

set_option autoImplicit false
noncomputable section
namespace Rule30WallResource
open Rule30Equivalents Rule30CycleAccounting Rule30TemporalResource Rule30PolynomialResource
open Polynomial

def state (t : ℕ) : ℕ := (AutomatonGroup.PhiS 3)^[t] 0
def source (i t : ℕ) : Bool := if i=0 then true else (state t).testBit (2*i-1)
def lowbit (i t : ℕ) : Bool := (state t).testBit (2*i)
def highbit (i t : ℕ) : Bool := (state t).testBit (2*i+1)
def exp (i : ℕ) : ℕ := exponent (AutomatonGroup.PhiS 3)
  (fun i y => TFunction.low y i || (3 : Nat).testBit i) 0 (2*i)
def value (i : ℕ) : ℕ := rho (2^exp i-1)
  (encode (fun t => bit (source i t)) (2^exp i))

theorem high_step (i t : ℕ) :
    highbit i (t+1) = xor (highbit i t) (lowbit i t || source i t) := by
  unfold highbit state
  rw [Function.iterate_succ_apply']
  rw [Rule30OrderBridge.PhiS_bit]
  have hlow : TFunction.low (state t % 2^(2*i+1)) (2*i+1) =
      TFunction.low (state t) (2*i+1) := by
    apply TFunction.low_congr
    intro k hk
    simp [Nat.testBit_mod_two_pow, hk]
  change xor ((state t).testBit (2*i+1))
    (TFunction.low (state t % 2^(2*i+1)) (2*i+1) || (3 : ℕ).testBit (2*i+1)) = _
  rw [hlow, AutomatonGroup.testBit_three_eq]
  unfold TFunction.low lowbit source
  cases i with
  | zero => simp [state]
  | succ i =>
    have hge : 2 ≤ 2*(i+1)+1 := by omega
    simp only [show 1 ≤ 2*(i+1)+1 by omega, show 2 ≤ 2*(i+1)+1 by omega,
      decide_true, Bool.true_and, show ¬ 2*(i+1)+1 < 2 by omega, decide_false,
      Bool.or_false, show i+1 ≠ 0 by omega, ite_false]
    congr 2

theorem value_zero : value 0 = 0 := by simp [value, exp, exponent]

lemma source_succ (i t : ℕ) : source (i+1) t = highbit i t := by
  simp only [source, highbit, show i+1 ≠ 0 by omega, ite_false]
  congr 1

lemma exp_step (i : ℕ) : exp (i+1) = exp i +
    pairWeight (AutomatonGroup.PhiS 3)
      (fun i y => TFunction.low y i || (3 : Nat).testBit i) 0 i := by
  exact pair_exponent_step _ _ _ _

lemma value_succ_of_weight (i k : ℕ)
    (hw : pairWeight (AutomatonGroup.PhiS 3)
      (fun i y => TFunction.low y i || (3 : Nat).testBit i) 0 i = k) :
    value (i+1) = rho (2^(exp i+k)-1)
      (encode (fun t => bit (highbit i t)) (2^(exp i+k))) := by
  unfold value
  rw [exp_step, hw]
  congr 2

theorem reset_before_of_streams (i : ℕ)
    (hs : ∀ t, source i (2^exp i+t) = source i t)
    (hb : ∀ t, lowbit i (2^exp i+t) = !(lowbit i t))
    (hh : highbit i (2*2^exp i) = !(highbit i 0)) : value i = 0 := by
  exact dyadic_reset_before (source i) (lowbit i) (highbit i) (exp i) hs hb (high_step i) hh

theorem reset_after_of_streams (i : ℕ)
    (hw : pairWeight (AutomatonGroup.PhiS 3)
      (fun i y => TFunction.low y i || (3 : Nat).testBit i) 0 i = 2)
    (hh : ∀ t < 2*2^exp i, highbit i (2*2^exp i+t) = !(highbit i t)) :
    value (i+1)+1 = 2^(exp (i+1)-1) := by
  rw [value_succ_of_weight i 2 hw, exp_step, hw]
  have hp : 2^(exp i+2) = 4*2^exp i := by rw [pow_add]; norm_num; omega
  have hp' : 2^(exp i+2-1) = 2*2^exp i := by
    rw [show exp i+2-1 = exp i+1 by omega, pow_succ]; omega
  rw [hp, hp']
  exact dyadic_reset_after (highbit i) (exp i) hh

theorem countdown_fixed_of_streams (i : ℕ)
    (hw : pairWeight (AutomatonGroup.PhiS 3)
      (fun i y => TFunction.low y i || (3 : Nat).testBit i) 0 i = 1)
    (hh : ∀ t < 2^exp i, highbit i (2^exp i+t) = !(highbit i t)) :
    value i ≤ value (i+1)+1 := by
  rw [value_succ_of_weight i 1 hw]
  have hp : 2^(exp i+1) = 2*2^exp i := by rw [pow_succ]; omega
  rw [hp]
  exact dyadic_fixed_countdown (source i) (highbit i) (exp i) hh

theorem countdown_flipping_of_streams (i : ℕ)
    (hw : pairWeight (AutomatonGroup.PhiS 3)
      (fun i y => TFunction.low y i || (3 : Nat).testBit i) 0 i = 1)
    (hs : ∀ t, source i (2^exp i+t) = source i t)
    (hb : ∀ t, lowbit i (2^exp i+t) = !(lowbit i t))
    (hh : highbit i (2*2^exp i) = highbit i 0) :
    value i ≤ value (i+1)+1 := by
  rw [value_succ_of_weight i 1 hw]
  have hp : 2^(exp i+1) = 2*2^exp i := by rw [pow_succ]; omega
  rw [hp]
  exact dyadic_flipping_countdown (source i) (lowbit i) (highbit i) (exp i) hs hb (high_step i) hh

def ofStreams
    (hs : ∀ i t, source i (2^exp i+t) = source i t)
    (hlo : ∀ i, pairWeight (AutomatonGroup.PhiS 3)
      (fun i y => TFunction.low y i || (3 : Nat).testBit i) 0 i = 2 →
      ∀ t, lowbit i (2^exp i+t) = !(lowbit i t))
    (hhi : ∀ i, pairWeight (AutomatonGroup.PhiS 3)
      (fun i y => TFunction.low y i || (3 : Nat).testBit i) 0 i = 2 →
      ∀ t, highbit i (2*2^exp i+t) = !(highbit i t))
    (hone : ∀ i, pairWeight (AutomatonGroup.PhiS 3)
      (fun i y => TFunction.low y i || (3 : Nat).testBit i) 0 i = 1 →
      (∀ t, highbit i (2^exp i+t) = !(highbit i t)) ∨
      ((∀ t, lowbit i (2^exp i+t) = !(lowbit i t)) ∧
        highbit i (2*2^exp i) = highbit i 0)) : WallResource 0 where
  value := value
  reset_before := by
    intro i hw
    apply reset_before_of_streams i (hs i) (hlo i hw)
    simpa using hhi i hw 0
  reset_after := by
    intro i hw
    have h := reset_after_of_streams i hw (fun t _ => hhi i hw t)
    simpa only [exp, Nat.zero_add] using h
  countdown := by
    intro i hw
    rcases hone i hw with h | ⟨hb, hh⟩
    · exact countdown_fixed_of_streams i hw (fun t _ => h t)
    · exact countdown_flipping_of_streams i hw (hs i) hb hh

theorem source_period (i t : ℕ) : source i (2^exp i+t) = source i t := by
  by_cases hi : i=0
  · simp [source, hi]
  · unfold source
    simp only [hi, ite_false]
    exact Rule30TemporalCycles.bit_period_below_pow (Rule30OrderBridge.PhiS_bit 3) 0 (2*i) (2*i-1)
      (by omega) t

def actual : WallResource 0 := ofStreams source_period
  (fun i hw t => Rule30TemporalCycles.pair_two_low_anti (Rule30OrderBridge.PhiS_bit 3) 0 i hw t)
  (fun i hw t => Rule30TemporalCycles.pair_two_high_anti (Rule30OrderBridge.PhiS_bit 3) 0 i hw t)
  (fun i hw => by
    have h := Rule30TemporalCycles.pair_one_cases (Rule30OrderBridge.PhiS_bit 3) 0 i hw
    simpa only [highbit, lowbit, state, exp, Function.iterate_zero_apply] using h)

theorem right_period (j : ℕ) : Ruliology.CellularAutomata.Rule30RightPeriods.Per j
    (2 ^ Rule30OrderBridge.B j) := wall_per_of_zero_resource actual j

theorem right_exponent {j e : ℕ}
    (he : Ruliology.CellularAutomata.Rule30RightPeriods.IsE j e) : e ≤ Rule30OrderBridge.B j :=
  wall_exponent_of_zero_resource actual he

theorem wall_return (n : ℕ) :
    (AutomatonGroup.PhiS 3)^[2^((n+1)/2+Rule30OrderBridge.Q 0 (n/2))] 0 % 2^n = 0 := by
  simpa using return_of_resource (Rule30OrderBridge.PhiS_bit 3) actual n

end Rule30WallResource
end

namespace Rule30Submission

theorem right_period (j : ℕ) :
    Ruliology.CellularAutomata.Rule30RightPeriods.Per j
      (2 ^ Rule30OrderBridge.B j) := Rule30WallResource.right_period j

theorem right_exponent {j e : ℕ}
    (he : Ruliology.CellularAutomata.Rule30RightPeriods.IsE j e) :
    e ≤ Rule30OrderBridge.B j := Rule30WallResource.right_exponent he

theorem wall_return (n : ℕ) :
    (Rule30Equivalents.AutomatonGroup.PhiS 3)^[2^((n+1)/2+Rule30OrderBridge.Q 0 (n/2))]
      0 % 2^n = 0 := Rule30WallResource.wall_return n

end Rule30Submission

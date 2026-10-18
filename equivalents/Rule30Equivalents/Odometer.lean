import Ruliology.CellularAutomata.Rule30RightPeriods
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The right edge of rule 30 is a 2-adic odometer

Catalog Section 3.3 ([25], [26]) and Section 7, item 9, which cite Coven, Pivato and Yassawi
[CPY07]: in the frame of the right edge, the orbit closure of the single seed is the 2-adic
odometer. Read row `t` leftward from its right edge: `row t j = R j t = cell(t, t - j)`.

* `G_row`: in these coordinates rule 30 is `G(y)_j = y_j ⊕ (y_{j-1} ∨ y_{j-2})`, with
  `y_{-1} = y_{-2} = 0`, and the seed is `row 0 = (1, 0, 0, …)`.
* `G_bijective`, `agree_G_iff`: `G` is a bijection, and `G y`, `G y'` agree below `n` iff `y`, `y'`
  do. So `G` is an isometry of `{0,1}^ℕ` for the metric `2^-(first difference)`.
* `ψ α j = R j (α mod 2^j)` for a 2-adic integer `α` (each `R j` has period `2^j`):
  `ψ_natCast` (`ψ t = row t`), `ψ_add_one` (`ψ (α + 1) = G (ψ α)`), `continuous_ψ`,
  `ψ_injective`, `range_ψ` (`range ψ = closure (range row)`), and `isClosedEmbedding_ψ`.
  **So `ψ` is a homeomorphism from `ℤ₂` onto the orbit closure of the seed that conjugates
  `α ↦ α + 1` to rule 30.** Injectivity is where rule 30 enters: if `ψ α = ψ β` with
  `α - β ∉ 2^m ℤ₂`, every diagonal would have period `2^(m-1)`, but the periods of the diagonals
  are unbounded (`Rule30RightPeriods.not_per_small`).

The finite levels are in `TFunctionCycles` (`seed_rows_return_iff`, `per_unbounded`). None of this
reaches the center column, which reads the moving coordinate `row t t`.
-/

namespace Rule30Equivalents.Odometer

open Ruliology.CellularAutomata Rule30Diagonals Rule30RightPeriods

/-! ### Rule 30 in the frame of the right edge -/

/-- Rule 30 in the frame of its right edge: `G(y)_j = y_j ⊕ (y_{j-1} ∨ y_{j-2})`. -/
def G (y : ℕ → Bool) : ℕ → Bool
  | 0 => y 0
  | 1 => xor (y 1) (y 0)
  | j + 2 => xor (y (j + 2)) (y (j + 1) || y j)

/-- The inverse of `G`, solved from the lowest coordinate up. -/
def Ginv (z : ℕ → Bool) : ℕ → Bool
  | 0 => z 0
  | 1 => xor (z 1) (Ginv z 0)
  | j + 2 => xor (z (j + 2)) (Ginv z (j + 1) || Ginv z j)

theorem Ginv_one (z : ℕ → Bool) : Ginv z 1 = xor (z 1) (z 0) := rfl

theorem Ginv_add_two (z : ℕ → Bool) (j : ℕ) :
    Ginv z (j + 2) = xor (z (j + 2)) (Ginv z (j + 1) || Ginv z j) := rfl

theorem G_Ginv (z : ℕ → Bool) : G (Ginv z) = z := by
  funext j
  match j with
  | 0 => rfl
  | 1 => simp [G, Ginv]
  | j + 2 => simp [G, Ginv]

theorem Ginv_G_apply (y : ℕ → Bool) : ∀ j, Ginv (G y) j = y j
  | 0 => rfl
  | 1 => by rw [Ginv, Ginv_G_apply y 0]; simp [G]
  | j + 2 => by rw [Ginv, Ginv_G_apply y (j + 1), Ginv_G_apply y j]; simp [G]

theorem G_bijective : Function.Bijective G :=
  Function.bijective_iff_has_inverse.2
    ⟨Ginv, fun y => funext (Ginv_G_apply y), G_Ginv⟩

theorem Ginv_agree {z z' : ℕ → Bool} {n : ℕ} (h : ∀ j < n, z j = z' j) :
    ∀ j < n, Ginv z j = Ginv z' j
  | 0, hj => h 0 hj
  | 1, hj => by rw [Ginv_one, Ginv_one, h 1 hj, h 0 (by omega)]
  | j + 2, hj => by
    rw [Ginv_add_two, Ginv_add_two, h _ hj, Ginv_agree h (j + 1) (by omega),
      Ginv_agree h j (by omega)]

/-- **`G` is an isometry**: `G y` and `G y'` agree below `n` iff `y` and `y'` do. -/
theorem agree_G_iff (y y' : ℕ → Bool) (n : ℕ) :
    (∀ j < n, G y j = G y' j) ↔ ∀ j < n, y j = y' j := by
  constructor
  · intro h j hj
    have := Ginv_agree h j hj
    rwa [Ginv_G_apply, Ginv_G_apply] at this
  · intro h j hj
    match j with
    | 0 => exact h 0 hj
    | 1 => simp only [G]; rw [h 1 hj, h 0 (by omega)]
    | j + 2 => simp only [G]; rw [h _ hj, h (j + 1) (by omega), h j (by omega)]

/-- Row `t`, read leftward from its right edge. -/
def row (t : ℕ) : ℕ → Bool := fun j => R j t

theorem R_one_succ (t : ℕ) : R 1 (t + 1) = xor (R 1 t) (R 0 t) := by
  rw [R_one_eq, R_one_eq, R_zero]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have : (t + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (t + 1) % 2 = 0 := by omega
    simp [h, this]

/-- **Rule 30 acts on the rows as `G`.** -/
theorem G_row (t : ℕ) : G (row t) = row (t + 1) := by
  funext j
  match j with
  | 0 => simp [G, row, R_zero]
  | 1 => exact (R_one_succ t).symm
  | j + 2 => exact (R_step j t).symm

theorem row_zero : row 0 = fun j => decide (j = 0) := by
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [row, R_zero]
  · simp [row, R_init hj]
    omega

/-! ### The 2-adic parametrization -/

/-- `R j` only sees its time modulo `2^j`. -/
theorem R_mod (j n : ℕ) : R j (n % 2 ^ j) = R j n := by
  have h := (per_R_periodic j).mul (n / 2 ^ j) (n % 2 ^ j)
  rw [mul_comm, Nat.mod_add_div] at h
  exact h.symm

theorem R_val_eq {j : ℕ} {x : ZMod (2 ^ j)} {y : ℕ} (h : x = y) : R j x.val = R j y := by
  rw [h, ZMod.val_natCast, R_mod]

theorem val_toZModPow_mod {m n : ℕ} (h : m ≤ n) (α : ℤ_[2]) :
    (PadicInt.toZModPow m α).val = (PadicInt.toZModPow n α).val % 2 ^ m := by
  rw [← PadicInt.cast_toZModPow m n h, ZMod.cast_eq_val, ZMod.val_natCast]

/-- The point of the orbit closure at the 2-adic time `α`: diagonal `j` read at `α mod 2^j`. -/
noncomputable def ψ (α : ℤ_[2]) : ℕ → Bool := fun j => R j (PadicInt.toZModPow j α).val

/-- At natural times `ψ` is the orbit of the seed. -/
theorem ψ_natCast (t : ℕ) : ψ (t : ℤ_[2]) = row t := by
  funext j
  simp only [ψ, row, map_natCast, ZMod.val_natCast, R_mod]

/-- **`ψ` conjugates `α ↦ α + 1` to rule 30.** -/
theorem ψ_add_one (α : ℤ_[2]) : ψ (α + 1) = G (ψ α) := by
  have hsucc : ∀ j, ψ (α + 1) j = R j ((PadicInt.toZModPow j α).val + 1) := fun j =>
    R_val_eq (by rw [map_add, map_one]; push_cast; rw [ZMod.natCast_zmod_val])
  have hlow : ∀ i j, i ≤ j → ψ α i = R i (PadicInt.toZModPow j α).val := fun i j hij => by
    simp only [ψ]
    rw [val_toZModPow_mod hij, R_mod]
  funext j
  rw [hsucc]
  match j with
  | 0 => simp [G, ψ, R_zero]
  | 1 => rw [R_one_succ]; simp only [G]; rw [hlow 1 1 le_rfl, hlow 0 1 (by omega)]
  | j + 2 =>
    rw [R_step]
    simp only [G]
    rw [hlow (j + 2) (j + 2) le_rfl, hlow (j + 1) (j + 2) (by omega), hlow j (j + 2) (by omega)]

theorem ψ_zero : ψ 0 = fun j => decide (j = 0) := by
  have := ψ_natCast 0
  rw [Nat.cast_zero] at this
  rw [this, row_zero]

theorem continuous_ψ : Continuous ψ := by
  refine continuous_pi fun j => IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro α
  filter_upwards [Metric.closedBall_mem_nhds α (zpow_pos (by norm_num : (0 : ℝ) < 2) (-(j : ℤ)))]
    with β hβ
  have hmem : β - α ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ j} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [Metric.mem_closedBall, dist_eq_norm] at hβ
    exact_mod_cast hβ
  have h0 : PadicInt.toZModPow j (β - α) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact_mod_cast hmem
  rw [map_sub, sub_eq_zero] at h0
  simp only [ψ, h0]

/-- **`ψ` is injective**, because the periods of the right diagonals are unbounded. -/
theorem ψ_injective : Function.Injective ψ := by
  intro α β hαβ
  by_contra hne
  -- `ψ (α + n) = ψ (β + n)` for every natural `n`
  have hn : ∀ n : ℕ, ψ (α + n) = ψ (β + n) := by
    intro n
    induction n with
    | zero => simpa using hαβ
    | succ n ih => rw [Nat.cast_succ, ← add_assoc, ← add_assoc, ψ_add_one, ψ_add_one, ih]
  -- a level `2^m` that separates `α` and `β`
  obtain ⟨m, hm⟩ : ∃ m, α - β ∉ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ m} := by
    by_contra hall
    push Not at hall
    apply hne
    have hle : ∀ m : ℕ, ‖α - β‖ ≤ (1 / 2 : ℝ) ^ m := fun m => by
      have := (PadicInt.norm_le_pow_iff_mem_span_pow (α - β) m).2 (hall m)
      rw [zpow_neg, zpow_natCast] at this
      rw [one_div, inv_pow]
      exact_mod_cast this
    have h0 : ‖α - β‖ = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
      linarith [hle m]
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hm
    · exact h
  -- every diagonal `R j`, `j ≥ m`, has period `2^(m - 1)`
  have hper : ∀ j, m ≤ j → Per j (2 ^ (m - 1)) := by
    intro j hj
    set A := PadicInt.toZModPow j α with hA
    set B := PadicInt.toZModPow j β with hB
    set D := PadicInt.toZModPow j (α - β) with hD
    have hDAB : D = A - B := by rw [hD, map_sub]
    have hBlt : B.val < 2 ^ j := ZMod.val_lt B
    -- `R j` is invariant under the shift by `D`
    have hinv : ∀ t, R j (t + D.val) = R j t := by
      intro t
      have h := congrFun (hn (t + (2 ^ j - B.val))) j
      simp only [ψ, map_add, map_natCast] at h
      rw [← hA, ← hB] at h
      have h2j : ((2 ^ j : ℕ) : ZMod (2 ^ j)) = 0 := ZMod.natCast_self _
      rw [R_val_eq (y := t + D.val) (by
          rw [hDAB, Nat.cast_add, Nat.cast_sub hBlt.le, h2j, Nat.cast_add, ZMod.natCast_zmod_val,
            ZMod.natCast_zmod_val]
          ring),
        R_val_eq (y := t + 2 ^ j) (by
          rw [Nat.cast_add, Nat.cast_sub hBlt.le, h2j, Nat.cast_add, h2j, ZMod.natCast_zmod_val]
          ring)] at h
      rw [h, per_R_periodic j t]
    -- the gcd of `D.val` and `2^j` is a power of two below `2^m`
    have hg := PerF.gcd (f := R j) D.val (2 ^ j) hinv (per_R_periodic j)
    obtain ⟨w, hwj, hw⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.gcd_dvd_right D.val (2 ^ j))
    have hwm : w ≤ m - 1 := by
      by_contra hwm
      apply hm
      have hdvd : 2 ^ m ∣ D.val :=
        (pow_dvd_pow 2 (by omega)).trans (hw ▸ Nat.gcd_dvd_left D.val (2 ^ j))
      have h0 : PadicInt.toZModPow m (α - β) = 0 := by
        rw [← PadicInt.cast_toZModPow m j hj, ← hD, ZMod.cast_eq_val,
          ZMod.natCast_eq_zero_iff]
        exact_mod_cast hdvd
      rw [← PadicInt.ker_toZModPow]
      exact h0
    rw [hw] at hg
    exact Per.pow_mono hg hwm
  exact not_per_small (j := 2 ^ m) (k := m - 1) Nat.one_le_two_pow
    (by rw [Nat.sub_add_cancel hm1]) (hper (2 ^ m) Nat.lt_two_pow_self.le)

/-- **The orbit closure.** The image of `ψ` is the closure of the orbit of the seed. -/
theorem range_ψ : Set.range ψ = closure (Set.range row) := by
  apply le_antisymm
  · rintro _ ⟨α, rfl⟩
    have hd := PadicInt.denseRange_natCast (p := 2)
    have : ψ α ∈ closure (ψ '' Set.range (Nat.cast : ℕ → ℤ_[2])) :=
      image_closure_subset_closure_image continuous_ψ
        ⟨α, by rw [hd.closure_eq]; exact Set.mem_univ α, rfl⟩
    rwa [← Set.range_comp, show ψ ∘ (Nat.cast : ℕ → ℤ_[2]) = row from funext ψ_natCast] at this
  · refine closure_minimal ?_ (isCompact_range continuous_ψ).isClosed
    rintro _ ⟨t, rfl⟩
    exact ⟨t, ψ_natCast t⟩

/-- **The 2-adic odometer**: `ψ` is a closed embedding of `ℤ₂` onto the orbit closure of the seed
in the frame of the right edge, conjugating `α ↦ α + 1` to rule 30. -/
theorem isClosedEmbedding_ψ : Topology.IsClosedEmbedding ψ :=
  continuous_ψ.isClosedEmbedding ψ_injective

end Rule30Equivalents.Odometer

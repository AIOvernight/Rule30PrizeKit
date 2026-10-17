import Rule30Equivalents.Lagrange
import Rule30Equivalents.WordForms

/-!
# Problem 1 through Minkowski's question-mark function

Let `r₁, r₂, …` be the run lengths of the center column (OEIS A327983: 2, 1, 3, 2, 2, 3, 1, 1, …)
and `y = [0; 1, r₁, r₂, …] ≈ 0.7349760786`. By Denjoy's formula
`?([0; a₁, a₂, …]) = 0.0^(a₁ - 1) 1^(a₂) 0^(a₃) …₂` for Minkowski's function, `y = ?⁻¹(x₂)`, because
the center column starts with a black run. That identification is classical and is not formalized
here: Mathlib has no `?`. The form itself is about `y`.

* `problem1_iff_minkowski_not_quadratic` (catalog [49]): Problem 1 holds iff `y` is not a quadratic
  irrational. `y` is the reciprocal of `[1; r₁, r₂, …]`, so it is a quadratic irrational iff that
  number is. By `Lagrange.quadratic_cfValue_iff` this happens iff the run lengths are eventually
  periodic, which by `WordForms.problem1_iff_run_lengths` ([29]) is the negation of Problem 1.

Sources: H. Minkowski, *Zur Geometrie der Zahlen* (1904); A. Denjoy, *Sur une fonction réelle de
Minkowski*, J. Math. Pures Appl. 17 (1938) 105–151; R. Salem, *On some singular monotonic
functions which are strictly increasing*, Trans. AMS 53 (1943) 427–439. Catalog entry [49].
-/

namespace Rule30Equivalents.Minkowski

open Ruliology.CellularAutomata
open Lagrange (cfValue quadratic_cfValue_iff one_le_cfValue)

/-- The run lengths `r₁, r₂, …` of the center column: the first run, then
`WordForms.runLength`. -/
noncomputable def runLen : ℕ → ℕ
  | 0 => Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) 0 + 1
  | k + 1 => WordForms.runLength k

theorem one_le_runLen : ∀ k, 1 ≤ runLen k
  | 0 => by simp [runLen]
  | k + 1 => by
    show 1 ≤ WordForms.runLength k
    rw [WordForms.runLength_eq]
    unfold WordForms.gap WordForms.trueTime
    have := Nat.nth_strictMono WordForms.infinite_changes (show k < k + 1 by omega)
    omega

/-- The digits `1, r₁, r₂, …` of `1 / y`. -/
noncomputable def yDigits (k : ℕ) : ℤ := if k = 0 then 1 else (runLen (k - 1) : ℤ)

theorem one_le_yDigits (k : ℕ) : 1 ≤ yDigits k := by
  unfold yDigits
  split_ifs
  · exact le_rfl
  · exact_mod_cast one_le_runLen (k - 1)

/-- `y = [0; 1, r₁, r₂, …]`, which is `?⁻¹(x₂)` by Denjoy's formula. -/
noncomputable def yMink : ℝ := (cfValue yDigits)⁻¹

theorem quadratic_inv_iff {X : ℝ} (hX : X ≠ 0) :
    (∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * X⁻¹ ^ 2 + B * X⁻¹ + C = 0) ↔
      ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * X ^ 2 + B * X + C = 0 := by
  constructor
  · rintro ⟨A, B, C, hne, h⟩
    refine ⟨C, B, A, fun h0 => hne ?_, ?_⟩
    · simp only [Prod.mk.injEq] at h0 ⊢
      exact ⟨h0.2.2, h0.2.1, h0.1⟩
    · have := congrArg (· * X ^ 2) h
      simp only [zero_mul] at this
      field_simp at this
      linear_combination this
  · rintro ⟨A, B, C, hne, h⟩
    refine ⟨C, B, A, fun h0 => hne ?_, ?_⟩
    · simp only [Prod.mk.injEq] at h0 ⊢
      exact ⟨h0.2.2, h0.2.1, h0.1⟩
    · have := congrArg (· * X⁻¹ ^ 2) h
      simp only [zero_mul] at this
      field_simp at this ⊢
      linear_combination this

/-- **Problem 1 ⟺ `y = ?⁻¹(x₂) = [0; 1, r₁, r₂, …]` is not a quadratic irrational** (catalog
[49]). -/
theorem problem1_iff_minkowski_not_quadratic : Rule30Prize.Problem1 ↔
    ¬ ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * yMink ^ 2 + B * yMink + C = 0 := by
  have hpos : cfValue yDigits ≠ 0 := by linarith [one_le_cfValue one_le_yDigits]
  unfold yMink
  rw [quadratic_inv_iff hpos, quadratic_cfValue_iff one_le_yDigits,
    WordForms.problem1_iff_run_lengths]
  refine not_congr ⟨fun ⟨T, P, hP, h⟩ => ⟨T + 2, P, hP, fun n hn => ?_⟩,
    fun ⟨K, T, hT, h⟩ => ⟨K, T, hT, fun k hk => ?_⟩⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have := h m (by omega)
    simp only [yDigits, show m + 2 + P ≠ 0 by omega, show m + 2 ≠ 0 by omega, if_false,
      show m + 2 + P - 1 = (m + P) + 1 by omega, show m + 2 - 1 = m + 1 by omega, runLen, this]
  · have := h (k + 2) (by omega)
    simp only [yDigits, show k + 2 + T ≠ 0 by omega, show k + 2 ≠ 0 by omega, if_false,
      show k + 2 + T - 1 = (k + T) + 1 by omega, show k + 2 - 1 = k + 1 by omega, runLen] at this
    exact_mod_cast this

end Rule30Equivalents.Minkowski

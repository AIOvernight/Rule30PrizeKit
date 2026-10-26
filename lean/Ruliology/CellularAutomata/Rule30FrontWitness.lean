module
public import Ruliology.CellularAutomata.Rule30StripCertificates
/-! General witness and uniqueness lemmas for physical Rule 30 windows.
No trap-block enumeration or cone certificate is imported. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30FrontWitness
open Rule30StripCertificates Rule30Jen

/-- A bounded physical window has a unique integer encoding, at any spatial origin. -/
theorem enc_unique {K t a b : Nat} {p : Int}
    (ha : Enc K t p a) (hb : Enc K t p b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [ha.2 i hi, hb.2 i hi]
  · have hp : 2^K ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha.1 hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb.1 hp)]

/-- Failure of an all-black right window supplies a white cell in that window. -/
theorem white_witness (t : Nat) {N : Nat}
    (h : ¬ (∀ i : Nat, i < N → cell t (1 + (i : Int)) = true)) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ N ∧ cell t (p : Int) = false := by
  apply Classical.byContradiction
  intro hn
  apply h
  intro i hi
  cases hb : cell t (1 + (i : Int))
  · exact False.elim (hn ⟨i+1, by omega, by omega, by simpa [Int.add_comm] using hb⟩)
  · rfl

end Ruliology.CellularAutomata.Rule30FrontWitness

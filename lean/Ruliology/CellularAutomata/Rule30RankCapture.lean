module
public import Ruliology.CellularAutomata.Rule30RunEnvelopes

/-! A rank certificate for capture of every odd state under a white driver.
Ranks may be represented by any function; the theorem assumes only the checked
local inequalities and rechecks both values of the unknown right boundary. -/
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Ruliology.CellularAutomata.Rule30RankCapture
open Rule30StripCertificates Rule30RunEnvelopes

def edgeOK (K target : Nat) (rank : Nat → Nat) (s a : Nat) (z : Bool) : Bool :=
  let t := stripStep K false z s
  t % 2 == 1 && (if a == 0 then target.testBit s && rank t == 0 else rank t < a)

def point (K H target : Nat) (rank : Nat → Nat) (i : Nat) : Bool :=
  let s := 2*i+1
  let a := rank s
  a ≤ H && edgeOK K target rank s a false && edgeOK K target rank s a true

theorem checked_state {K H target N : Nat} {rank : Nat → Nat}
    (h : allBelow (point K H target rank) N = true)
    {s : Nat} (hs : s < 2*N) (ho : s % 2 = 1) :
    rank s ≤ H ∧ ∀ z, (stripStep K false z s) % 2 = 1 ∧
      (rank s = 0 → target.testBit s = true ∧ rank (stripStep K false z s) = 0) ∧
      (0 < rank s → rank (stripStep K false z s) < rank s) := by
  have hh := allBelow_spec h (s/2) (by omega)
  have he : 2*(s/2)+1 = s := by omega
  simp only [point, he, Bool.and_eq_true] at hh
  refine ⟨of_decide_eq_true hh.1.1, ?_⟩
  intro z
  have hz : edgeOK K target rank s (rank s) z = true := by
    cases z
    · exact hh.1.2
    · exact hh.2
  simp only [edgeOK, Bool.and_eq_true] at hz
  refine ⟨by simpa using hz.1, ?_, ?_⟩
  · intro ha
    simpa [ha] using hz.2
  · intro ha
    simpa [show rank s ≠ 0 by omega] using hz.2

/-- Every initial odd state is in `target` after `H` white steps.  The rank-zero
condition includes invariance, so a path arriving early can safely be padded. -/
theorem capture {K H target N A : Nat} {rank : Nat → Nat}
    (h : allBelow (point K H target rank) N = true)
    (hK : 2^K ≤ 2*N)
    (hA : ∀ s, A.testBit s = true → s < 2*N ∧ s % 2 = 1) :
    Sub (applyWord K (List.replicate H false) A) target := by
  have aux : ∀ n B, (∀ s, B.testBit s = true →
      s < 2*N ∧ s % 2 = 1 ∧ rank s ≤ n) →
      Sub (applyWord K (List.replicate n false) B) target := by
    intro n
    induction n with
    | zero =>
      intro B hb s hs
      have hp := hb s hs
      exact ((checked_state h hp.1 hp.2.1).2 false).2.1 (by omega) |>.1
    | succ n ih =>
      intro B hb
      rw [List.replicate_succ, applyWord]
      apply ih
      apply imageAux_forall K false B
        (fun t => t < 2*N ∧ t % 2 = 1 ∧ rank t ≤ n) _ (2^K) (by omega)
      intro s _ hs z
      have hp := hb s hs
      have ht := (checked_state h hp.1 hp.2.1).2 z
      refine ⟨Nat.lt_of_lt_of_le (stripStep_lt K false z s) hK, ht.1, ?_⟩
      by_cases hz : rank s = 0
      · have := (ht.2.1 hz).2
        omega
      · have := ht.2.2 (by omega)
        omega
  apply aux H A
  intro s hs
  have hp := hA s hs
  exact ⟨hp.1, hp.2, (checked_state h hp.1 hp.2).1⟩

end Ruliology.CellularAutomata.Rule30RankCapture

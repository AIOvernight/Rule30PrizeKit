module
public import Ruliology.CellularAutomata.Rule30FrontClockCore
/-! The front-anchored map updates the actual rule-30 cells while the leftmost black cell right of a white center moves left (`physical_clock`). -/
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Ruliology.CellularAutomata.Rule30FrontFrame
open Rule30StripCertificates Rule30Jen Rule30FrontClock

theorem f_bit (x i : Nat) : (f x).testBit i =
    rule (if i<2 then false else x.testBit (i-2))
      (if i<1 then false else x.testBit (i-1)) (x.testBit i) := by
  simp only [f,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft,rule]
  by_cases h2 : i<2
  · by_cases h1 : i<1
    · have he : i=0 := by omega
      subst i;simp
    · have he : i=1 := by omega
      subst i;simp
  · simp [h2, show 2≤i by omega, show 1≤i by omega, show ¬i<1 by omega]

/-- While the two cells immediately before a window are white, shifting the
window one cell left updates it by the autonomous triangular diagonal map. -/
theorem enc_front_step {K t : Nat} {j : Int} {r : Nat} (he : Enc K t j r)
    (h0 : cell t j = false) (h1 : cell t (j-1) = false) :
    Enc K (t+1) (j-1) (f r %2^K) := by
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), fun i hi => ?_⟩
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,f_bit]
  show _ = rule (cell t (j-1+1+(i:Int)-1))
    (cell t (j-1+1+i)) (cell t (j-1+1+i+1))
  have hr : r.testBit i = cell t (j-1+1+(i:Int)+1) := by
    rw [he.2 i hi];congr 1;omega
  rw [hr]
  have hl : (if i<2 then false else r.testBit (i-2)) = cell t (j-1+1+(i:Int)-1) := by
    split
    · rename_i h
      obtain hz | hz : i=0 ∨ i=1 := by omega
      · subst i;simpa using h1.symm
      · subst i;simpa using h0.symm
    · rename_i h
      rw [he.2 (i-2) (by omega)];congr 1;omega
  have hc : (if i<1 then false else r.testBit (i-1)) = cell t (j-1+1+(i:Int)) := by
    split
    · rename_i h
      have hz : i=0 := by omega
      subst i;simpa using h0.symm
    · rename_i h
      rw [he.2 (i-1) (by omega)];congr 1;omega
  rw [hl,hc]

/-- A right-hand front, with every strictly intermediate positive cell white. -/
def Front (t : Nat) (d : Int) : Prop :=
  cell t d = true ∧ ∀ p : Int, 0<p → p<d → cell t p=false

theorem front_zero {t : Nat} {d : Int} (hf : Front t d)
    (hc : cell t 0=false) (p : Int) (h0 : 0≤p) (hd : p<d) : cell t p=false := by
  by_cases hp : p=0
  · simpa [hp] using hc
  · exact hf.2 p (by omega) hd

theorem front_step {t : Nat} {d : Int} (hd : 2≤d) (hf : Front t d)
    (hc : cell t 0=false) : Front (t+1) (d-1) := by
  constructor
  · change rule (cell t (d-1-1)) (cell t (d-1)) (cell t (d-1+1))=true
    rw [front_zero hf hc _ (by omega) (by omega),
      front_zero hf hc _ (by omega) (by omega),show d-1+1=d by omega,hf.1]
    rfl
  · intro p hp hpd
    change rule (cell t (p-1)) (cell t p) (cell t (p+1))=false
    rw [front_zero hf hc _ (by omega) (by omega),
      front_zero hf hc _ (by omega) (by omega),front_zero hf hc _ (by omega) (by omega)]
    rfl

theorem front_iter (t n : Nat) (d : Int) (hd : (n:Int)<d) (hf : Front t d)
    (hc : ∀ i, i<n → cell (t+i) 0=false) : Front (t+n) (d-n) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have hh := ih (by omega) (fun i hi => hc i (by omega))
    have hs := front_step (by omega : 2≤d-(n:Int)) hh (hc n (by omega))
    rw [show t+(n+1)=t+n+1 by omega, show d-((n+1:Nat):Int)=d-(n:Int)-1 by omega]
    exact hs

/-- Exact diagonal dynamics along a front before it reaches column1. -/
theorem enc_front_iter {K t n : Nat} {d : Int} {r : Nat}
    (hd : (n:Int)<d) (hf : Front t d) (he : Enc K t (d-1) r)
    (hc : ∀ i, i<n → cell (t+i) 0=false) :
    Enc K (t+n) (d-(n:Int)-1) (evolve n r %2^K) := by
  induction n with
  | zero => simpa [evolve,Nat.mod_eq_of_lt he.1] using he
  | succ n ih =>
    have hen := ih (by omega) (fun i hi => hc i (by omega))
    have hfn := front_iter t n d (by omega) hf (fun i hi => hc i (by omega))
    have hcn := hc n (by omega)
    have hz0 := front_zero hfn hcn (d-(n:Int)-1) (by omega) (by omega)
    have hz1 := front_zero hfn hcn (d-(n:Int)-1-1) (by omega) (by omega)
    have hs := enc_front_step hen hz0 hz1
    rw [f_mod] at hs
    rw [show t+(n+1)=t+n+1 by omega, show d-((n+1:Nat):Int)-1=d-(n:Int)-1-1 by omega]
    exact hs

/-- Shift an encoded front back into a window based at column1. -/
theorem enc_shift_front {K t e r : Nat} (he : 1≤e) (hf : Front t (e:Int))
    (hr : Enc K t ((e:Int)-1) r) :
    Enc K t 0 ((r <<< (e-1)) %2^K) := by
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), fun i hi => ?_⟩
  rw [Nat.testBit_mod_two_pow,decide_eq_true hi,Bool.true_and,Nat.testBit_shiftLeft]
  by_cases hlow : i<e-1
  · have hz := hf.2 (1+(i:Int)) (by omega) (by omega)
    simp only [show ¬e-1≤i by omega,decide_false,Bool.false_and]
    simpa using hz.symm
  · have hri := hr.2 (i-(e-1)) (by omega)
    simp only [show e-1≤i by omega,decide_true,Bool.true_and]
    rw [hri]
    congr 1
    omega

end Ruliology.CellularAutomata.Rule30FrontFrame

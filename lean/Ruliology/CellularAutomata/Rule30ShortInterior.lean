module
public import Ruliology.CellularAutomata.Rule30FrontWitness
public import Ruliology.CellularAutomata.Rule30SparseFrontSets
/-! The interior light cone: a window of `K` known cells determines `K - 2` cells one tick later, independently of the center (`enc_core_step`). -/
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Ruliology.CellularAutomata.Rule30ShortInterior
open Rule30StripCertificates Rule30Jen Rule30SparseFrontSets

def coreStep (K r : Nat) : Nat := (r ^^^ ((r >>> 1) ||| (r >>> 2))) % 2^(K-2)

theorem enc_core_step {K t : Nat} {p : Int} {r : Nat} (he : Enc K t p r) :
    Enc (K-2) (t+1) (p+1) (coreStep K r) := by
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _),fun i hi => ?_⟩
  simp only [coreStep,Nat.testBit_mod_two_pow,decide_eq_true hi,Bool.true_and,
    Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftRight]
  rw [he.2 i (by omega), he.2 (1+i) (by omega), he.2 (2+i) (by omega)]
  change rule _ _ _ = rule _ _ _
  congr 1 <;> congr 1 <;> omega

def coreCovers (K : Nat) (A B : Tree) : Bool := all (fun r => mem (coreStep K r) B) A

theorem core_sound {K r : Nat} {A B : Tree} (h : coreCovers K A B=true)
    (hr : mem r A=true) : mem (coreStep K r) B=true := all_sound _ _ h r hr

def noBlack (N : Nat) (A : Tree) : Bool := all (fun r => (r%2^N) != (2^N-1)) A

theorem noBlack_sound {K t j r N : Nat} {A : Tree} (hNK : N≤K) (hj : j+N≤14)
    (he : Enc K t (j:Int) r) (hr : mem r A=true) (hc : noBlack N A=true) :
    ¬ (∀ i : Nat, i<14 → cell t (1+(i:Int))=true) := by
  intro h
  have hh := all_sound _ _ hc r hr
  have heq : r%2^N=2^N-1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow r N i,Nat.testBit_two_pow_sub_one N i]
    by_cases hi : i<N
    · simp only [decide_eq_true hi,Bool.true_and]
      rw [he.2 i (by omega)]
      have hx := h (j+i) (by omega)
      have hp : (j:Int)+1+(i:Int)=1+((j+i:Nat):Int) := by omega
      rw [hp];exact hx
    · simp only [decide_eq_false hi,Bool.false_and]
  simp [heq] at hh
end Ruliology.CellularAutomata.Rule30ShortInterior

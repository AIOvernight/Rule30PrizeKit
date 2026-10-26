module
public import Ruliology.CellularAutomata.Rule30FrontFrame
/-! Sparse sets of windows as search trees, with sound inclusion, cover and exact light-cone checks. -/
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Ruliology.CellularAutomata.Rule30SparseFrontSets
open Rule30StripCertificates Rule30Jen

inductive Tree where
  | nil : Tree
  | node : Nat → Tree → Tree → Tree

def mem (s : Nat) : Tree → Bool
  | .nil => false
  | .node v l r => if s=v then true else if s<v then mem s l else mem s r

def all (P : Nat → Bool) : Tree → Bool
  | .nil => true
  | .node v l r => P v && all P l && all P r

/-- Compose independently checked subtrees without reducing a large conjunction. -/
theorem all_node {P : Nat → Bool} {v : Nat} {l r : Tree}
    (hv : P v = true) (hl : all P l = true) (hr : all P r = true) :
    all P (.node v l r) = true := by simp only [all, hv, hl, hr]; rfl

theorem all_sound (P : Nat → Bool) (T : Tree) (hh : all P T = true) :
    ∀ s, mem s T=true → P s=true := by
  induction T with
  | nil => intro s hs;simp [mem] at hs
  | node v l r il ir =>
    simp only [all,Bool.and_eq_true] at hh
    intro s hs
    simp only [mem] at hs
    split at hs
    · rename_i he;subst s;exact hh.1.1
    · split at hs
      · exact il hh.1.2 s hs
      · exact ir hh.2 s hs

def incl (A B : Tree) : Bool := all (fun s => mem s B) A
theorem incl_sound {A B : Tree} (hc : incl A B=true) {s : Nat} (hs : mem s A=true) : mem s B=true := all_sound _ _ hc s hs

def covers (K : Nat) (c : Bool) (A B : Tree) : Bool :=
  all (fun s => mem (stripStep K c false s) B && mem (stripStep K c true s) B) A

theorem covers_sound {K : Nat} {c : Bool} {A B : Tree} (hc : covers K c A B=true)
    {s : Nat} (hs : mem s A=true) (z : Bool) : mem (stripStep K c z s) B=true := by
  have hh := all_sound _ _ hc s hs
  simp only [Bool.and_eq_true] at hh
  cases z
  · exact hh.1
  · exact hh.2

def coneStep (K : Nat) (c : Bool) (s : Nat) : Nat :=
  (((s <<< 1) ||| c.toNat) ^^^ (s ||| (s >>> 1))) % 2^(K-1)

def coneCovers (K : Nat) (c : Bool) (A B : Tree) : Bool :=
  all (fun s => mem (coneStep K c s) B) A

theorem cone_sound {K : Nat} {c : Bool} {A B : Tree} (hc : coneCovers K c A B=true)
    {s : Nat} (hs : mem s A=true) : mem (coneStep K c s) B=true :=
  all_sound _ _ hc s hs

/-- An exact finite light cone shrinks by one known cell at each step. -/
theorem enc_cone_step {K t : Nat} {r : Nat} (hK : 1≤K) (he : Enc K t 0 r)
    (c : Bool) (hc : cell t 0=c) : Enc (K-1) (t+1) 0 (coneStep K c r) := by
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _),fun i hi => ?_⟩
  have hh := (enc_step he).2 i (by omega : i<K)
  rw [hc] at hh
  rw [← hh]
  simp only [coneStep,stripStep,Nat.testBit_mod_two_pow,Nat.testBit_xor,
    Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  simp [hi,show i<K by omega,show ¬K-1≤i by omega]

def noBlack14 (A : Tree) : Bool := all (fun s => (s %2^14) != (2^14-1)) A

theorem noBlack14_sound {K t r : Nat} {A : Tree} (hK : 14≤K)
    (he : Enc K t 0 r) (hr : mem r A=true) (ha : noBlack14 A=true) :
    ¬ (∀ i : Nat, i<14 → cell t (1+(i:Int))=true) := by
  intro h
  have hh := all_sound _ _ ha r hr
  have heq : r%2^14=2^14-1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow r 14 i, Nat.testBit_two_pow_sub_one 14 i]
    by_cases hi : i<14
    · simp only [decide_eq_true hi,Bool.true_and]
      simpa using (he.2 i (by omega)).trans (h i hi)
    · simp only [decide_eq_false hi,Bool.false_and]
  simp [heq] at hh

end Ruliology.CellularAutomata.Rule30SparseFrontSets

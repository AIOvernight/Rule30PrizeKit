module
public import Ruliology.CellularAutomata.Rule30SparseFrontSets
public import Ruliology.CellularAutomata.Rule30RunEnvelopes

/-! Sparse certificates for controlled return, with explicit white ranks and word budgets.
All data are ordinary inductive values; the executable check is proved sound below. -/
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Ruliology.CellularAutomata.Rule30SparseGraph
open Rule30StripCertificates Rule30RunEnvelopes
open Rule30SparseFrontSets (Tree mem all incl)

/-- The ordinary finite-set meaning of a sparse tree. Search-tree ordering is not a
logical assumption: successful searches imply occurrence, and every occurrence is checked. -/
def mask : Tree → Nat
  | .nil => 0
  | .node v l r => (1 <<< v) ||| mask l ||| mask r

theorem mem_mask {s : Nat} {T : Tree} (h : mem s T = true) :
    (mask T).testBit s = true := by
  induction T with
  | nil => simp [mem] at h
  | node v l r il ir =>
    simp only [mem] at h
    simp only [mask, Nat.testBit_or, testBit_one_shiftLeft]
    split at h
    · rename_i e; simp [e]
    · split at h
      · simp [il h]
      · simp [ir h]

theorem mask_all (P : Nat → Bool) (T : Tree) (h : all P T = true)
    (s : Nat) (hs : (mask T).testBit s = true) : P s = true := by
  induction T with
  | nil => simp [mask] at hs
  | node v l r il ir =>
    simp only [all, Bool.and_eq_true] at h
    simp only [mask, Nat.testBit_or, testBit_one_shiftLeft, Bool.or_eq_true_iff] at hs
    rcases hs with (he | hl) | hr
    · have he : v = s := by simpa using he
      subst s; exact h.1.1
    · exact il h.1.2 hl
    · exact ir h.2 hr

theorem incl_mask {A B : Tree} (h : incl A B = true) : Sub (mask A) (mask B) := by
  intro s hs
  exact mem_mask (mask_all _ _ h s hs)

theorem covers_mask {K : Nat} {c : Bool} {A B : Tree}
    (h : Rule30SparseFrontSets.covers K c A B = true) :
    Sub (image K c (mask A)) (mask B) := by
  apply imageAux_forall K c (mask A) (fun y => (mask B).testBit y = true) _ (2^K) (by omega)
  intro s _ hs z
  have hh := mask_all _ _ h s hs
  simp only [Bool.and_eq_true] at hh
  cases z
  · exact mem_mask hh.1
  · exact mem_mask hh.2

def Obs (K A : Nat) (c : Bool) : Prop :=
  ∃ b : Bool, ∀ r, r < 2^K → A.testBit r = true → (c || r.testBit 0) = b

def Ctl (K A : Nat) (w : List Bool) (C : Nat) : Prop :=
  Sub (applyWord K w A) C ∧
    ∀ i, i < w.length → Obs K (applyWord K (w.take i) A) (w.getD i false)

theorem ctl_nil {K A B : Nat} (h : Sub A B) : Ctl K A [] B := by
  exact ⟨h, fun i hi => by simp at hi⟩

theorem obs_black (K A : Nat) : Obs K A true := ⟨true, fun _ _ _ => rfl⟩

def obsCheck (A : Tree) : Bool :=
  all (fun s => s.testBit 0) A || all (fun s => !(s.testBit 0)) A

theorem obsCheck_sound {K : Nat} {A : Tree} (h : obsCheck A = true) :
    Obs K (mask A) false := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact ⟨true, fun r _ hr => by simpa using mask_all _ _ h r hr⟩
  · refine ⟨false, fun r _ hr => ?_⟩
    have hh := mask_all _ _ h r hr
    simpa using hh

theorem ctl_cons {K A B C : Nat} {c : Bool} {w : List Bool}
    (hc : Sub (image K c A) B) (ho : Obs K A c) (ht : Ctl K B w C) :
    Ctl K A (c::w) C := by
  constructor
  · exact sub_trans (applyWord_mono K w hc) ht.1
  · intro i hi
    cases i with
    | zero => simpa [applyWord] using ho
    | succ i =>
      obtain ⟨b,hb⟩ := ht.2 i (by simpa using hi)
      refine ⟨b,fun r hr hs => ?_⟩
      apply hb r hr
      apply applyWord_mono K (w.take i) hc r
      simpa only [List.take_succ_cons,applyWord] using hs

theorem ctl_append {K A B C : Nat} {u v : List Bool}
    (hu : Ctl K A u B) (hv : Ctl K B v C) : Ctl K A (u++v) C := by
  constructor
  · rw [apply_append]
    exact sub_trans (applyWord_mono K v hu.1) hv.1
  · intro i hi
    by_cases h : i < u.length
    · simpa only [List.take_append_of_le_length (Nat.le_of_lt h),
        List.getD_eq_getElem?_getD,List.getElem?_append_left h] using hu.2 i h
    · have ht : (u++v).take i = u ++ v.take (i-u.length) := by
        rw [List.take_append,List.take_of_length_le (by omega)]
      have hg : (u++v).getD i false = v.getD (i-u.length) false := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
        rfl
      obtain ⟨b,hb⟩ := hv.2 (i-u.length) (by simp only [List.length_append] at hi;omega)
      refine ⟨b,fun r hr hs => ?_⟩
      rw [ht,apply_append] at hs
      rw [hg]
      exact hb r hr (applyWord_mono K _ hu.1 r hs)

theorem ctl_whites {K R : Nat} (hc : Sub (image K false R) R) (ho : Obs K R false)
    (n : Nat) : Ctl K R (List.replicate n false) R := by
  induction n with
  | zero => exact ctl_nil (sub_refl R)
  | succ n ih => simpa only [List.replicate_succ] using ctl_cons hc ho ih

theorem ctl_pad {K A R n H : Nat} (hn : n ≤ H)
    (h : Ctl K A (List.replicate n false) R)
    (hw : ∀ m, Ctl K R (List.replicate m false) R) :
    Ctl K A (List.replicate H false) R := by
  have hh := ctl_append h (hw (H-n))
  simpa only [List.replicate_append_replicate, Nat.add_sub_of_le hn] using hh

structure Node where
  states : Tree
  rank : Nat
  white : Nat
  black : Nat
  depth : Nat

inductive Graph where
  | nil : Graph
  | node : Nat → Node → Graph → Graph → Graph

def get (i : Nat) : Graph → Option Node
  | .nil => none
  | .node j v l r => if i = j then some v else if i < j then get i l else get i r

def every (P : Node → Bool) : Graph → Bool
  | .nil => true
  | .node _ v l r => P v && every P l && every P r

theorem every_sound (P : Node → Bool) (G : Graph) (h : every P G = true)
    {i : Nat} {v : Node} (hv : get i G = some v) : P v = true := by
  induction G with
  | nil => simp [get] at hv
  | node j v' l r il ir =>
    simp only [every, Bool.and_eq_true] at h
    simp only [get] at hv
    split at hv
    · cases hv; exact h.1.1
    · split at hv
      · exact il h.1.2 hv
      · exact ir h.2 hv

def nodeCheck (K H : Nat) (root : Tree) (G : Graph) (v : Node) : Bool :=
  match get v.white G with
  | none => false
  | some w =>
    decide (v.rank ≤ H) && obsCheck v.states &&
    Rule30SparseFrontSets.covers K false v.states w.states &&
    (if v.rank = 0 then incl v.states root else decide (w.rank < v.rank)) &&
    (if v.depth = 0 then true else
      decide (v.depth ≤ w.depth + 1) &&
      match get v.black G with
      | none => false
      | some b => decide (v.depth ≤ b.depth + 1) &&
          Rule30SparseFrontSets.covers K true v.states b.states)

def check (K H : Nat) (root : Tree) (G : Graph) : Bool := every (nodeCheck K H root G) G


/-- Logical obligations extracted from one checked node. -/
def Valid (K H : Nat) (root : Tree) (G : Graph) (v : Node) : Prop :=
  ∃ w, get v.white G = some w ∧ v.rank ≤ H ∧ Obs K (mask v.states) false ∧
    Sub (image K false (mask v.states)) (mask w.states) ∧
    (v.rank = 0 → Sub (mask v.states) (mask root)) ∧
    (0 < v.rank → w.rank < v.rank) ∧
    (0 < v.depth → v.depth ≤ w.depth + 1 ∧
      ∃ b, get v.black G = some b ∧ v.depth ≤ b.depth + 1 ∧
        Sub (image K true (mask v.states)) (mask b.states))

theorem nodeCheck_sound {K H : Nat} {root : Tree} {G : Graph} {v : Node}
    (h : nodeCheck K H root G v = true) : Valid K H root G v := by
  cases hw : get v.white G with
  | none => simp [nodeCheck,hw] at h
  | some w =>
    simp only [nodeCheck,hw,Bool.and_eq_true] at h
    refine ⟨w,hw,of_decide_eq_true h.1.1.1.1,obsCheck_sound h.1.1.1.2,
      covers_mask h.1.1.2,?_,?_,?_⟩
    · intro hz
      exact incl_mask (by simpa [hz] using h.1.2)
    · intro hp
      exact of_decide_eq_true (by simpa [show v.rank ≠ 0 by omega] using h.1.2)
    · intro hp
      have hd := h.2
      simp only [ite_eq_right (show v.depth ≠ 0 by omega),Bool.and_eq_true] at hd
      refine ⟨of_decide_eq_true hd.1,?_⟩
      cases hb : get v.black G with
      | none => simp [hb] at hd
      | some b =>
        have hbb := hd.2
        simp only [hb,Bool.and_eq_true] at hbb
        exact ⟨b,rfl,of_decide_eq_true hbb.1,covers_mask hbb.2⟩

theorem check_sound {K H : Nat} {root : Tree} {G : Graph}
    (h : check K H root G = true) {i : Nat} {v : Node} (hv : get i G = some v) :
    Valid K H root G v := nodeCheck_sound (every_sound _ _ h hv)

/-- White ranks certify controlled return in at most the declared number of steps. -/
theorem heal {K H : Nat} {root : Tree} {G : Graph}
    (h : check K H root G = true)
    (hw : ∀ n, Ctl K (mask root) (List.replicate n false) (mask root)) :
    ∀ n i v, get i G = some v → v.rank = n →
      Ctl K (mask v.states) (List.replicate n false) (mask root) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i v hv hn
    obtain ⟨w,hwg,_,ho,hc,hzero,hr,_⟩ := check_sound h hv
    by_cases hz : v.rank = 0
    · have hn0 : n = 0 := by omega
      subst n
      simpa only [hz, List.replicate_zero] using (ctl_nil (K := K) (hzero hz))
    · have hlt := hr (by omega)
      have ht := ih w.rank (by omega) v.white w hwg rfl
      have ht' := ctl_cons hc ho ht
      have hn' : w.rank + 1 ≤ n := by omega
      apply ctl_pad hn' _ hw
      simpa only [List.replicate_succ] using ht'

/-- A checked depth budget controls every word up to that length, followed by H whites. -/
theorem good {K H : Nat} {root : Tree} {G : Graph}
    (h : check K H root G = true)
    (hw : ∀ n, Ctl K (mask root) (List.replicate n false) (mask root)) :
    ∀ u : List Bool, ∀ i v, get i G = some v → u.length ≤ v.depth →
      Ctl K (mask v.states) (u ++ List.replicate H false) (mask root) := by
  intro u
  induction u with
  | nil =>
    intro i v hv _
    obtain ⟨_,_,hr,_⟩ := check_sound h hv
    exact ctl_pad hr (heal h hw v.rank i v hv rfl) hw
  | cons c u ih =>
    intro i v hv hlen
    obtain ⟨w,hwg,_,ho,hc,_,_,hd⟩ := check_sound h hv
    obtain ⟨hdw,b,hbg,hdb,hcb⟩ := hd (by simp only [List.length_cons] at hlen;omega)
    have huw : u.length ≤ w.depth := by simp only [List.length_cons] at hlen;omega
    have hub : u.length ≤ b.depth := by simp only [List.length_cons] at hlen;omega
    cases c
    · exact ctl_cons hc ho (ih v.white w hwg huw)
    · exact ctl_cons hcb (obs_black K (mask v.states)) (ih v.black b hbg hub)


/-- At a white-closed root, all semantic premises come from the same checked graph. -/
theorem root_good {K H : Nat} {root : Tree} {G : Graph}
    (h : check K H root G = true) {i : Nat} {v : Node}
    (hv : get i G = some v) (hs : v.states = root) (hi : v.white = i)
    (u : List Bool) (hu : u.length ≤ v.depth) :
    Ctl K (mask root) (u ++ List.replicate H false) (mask root) := by
  obtain ⟨w,hwg,_,ho,hc,_⟩ := check_sound h hv
  rw [hi,hv] at hwg
  have hwv : w = v := (Option.some.inj hwg).symm
  subst w
  rw [hs] at hc ho
  have hh := good h (ctl_whites hc ho) u i v hv hu
  simpa only [hs] using hh

end Ruliology.CellularAutomata.Rule30SparseGraph



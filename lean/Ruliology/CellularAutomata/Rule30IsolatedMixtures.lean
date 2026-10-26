module
public import Ruliology.CellularAutomata.Rule30WhitePad10111
/-!
# Mixtures of isolated ones with white gaps of at least ten

**Partial result.** For every nonempty list `qs` with every entry `≥ 10`, the single-seed center column
is not eventually the repeating word `1 0^(q₁) 1 0^(q₂) … 1 0^(qₖ)`, whatever the transient
(`not_eventually_isolated_mixtures`). The number of blocks and the gaps are unbounded, and the gaps may
differ. `Rule30WhiteEnd` is the case of a single gap.

In the eight-cell strip relaxation of `Rule30WhitePad10111`, a black step followed by ten white steps
moves every strip set into `A1`, and then into `A2`, and `A2` is closed under every such block (`stage0`,
`stage1`, `stage2`); longer white runs stay inside because the targets are closed under white steps.
From `A2`, column `1` reads `0 0 1 1 …` after each black cell, so `orCol 0` is eventually periodic,
which masked Jen forbids (`Rule30WhitePad10111.no_word_of_invariant`). All checks are `decide +kernel`.
-/
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Ruliology.CellularAutomata.Rule30IsolatedMixtures
open Rule30StripCertificates Rule30WhitePad10111
def A0 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def A1 : Nat := 0x2868302aa120302920290022a128222b2868202b2120102220290062a028222b
def A2 : Nat := 0x2028202820202028202800202020202820282028202000202028002020202028

def driver (q : Nat) : List Bool := true :: List.replicate q false
def mac (q A : Nat) : Nat := wp q (image 8 true A)
theorem driver_length (q : Nat) : (driver q).length = q+1 := by simp [driver]
theorem mac_eq (q A : Nat) : mac q A = applyWord 8 (driver q) A := by
  rw [driver, applyWord, ← wp_eq]; rfl

theorem capture {A B : Nat} (entry : Sub (wp 10 (image 8 true A)) B)
    (closed : Sub (image 8 false B) B) {q : Nat} (hq : 10 ≤ q) : Sub (mac q A) B := by
  unfold mac
  rw [show q = (q-10)+10 by omega, wp_add]
  exact sub_trans (wp_mono entry (q-10)) (wp_closed closed (q-10))

theorem entry0 : wp 10 (image 8 true A0) &&& A1 = wp 10 (image 8 true A0) := by decide +kernel

theorem closed1 : image 8 false A1 &&& A1 = image 8 false A1 := by decide +kernel

theorem entry1 : wp 10 (image 8 true A1) &&& A2 = wp 10 (image 8 true A1) := by decide +kernel

theorem closed2 : image 8 false A2 &&& A2 = image 8 false A2 := by decide +kernel

theorem entry2 : wp 10 (image 8 true A2) &&& A2 = wp 10 (image 8 true A2) := by decide +kernel

theorem nested : A2 &&& A1 = A2 := by decide +kernel

theorem full_A0 : fullSet 8 = A0 := by decide +kernel

theorem white0 : colConst 8 (image 8 true A2) false = true := by decide +kernel

theorem white1 : colConst 8 (wp 1 (image 8 true A2)) false = true := by decide +kernel

theorem white2 : wp 2 (image 8 true A2) &&& oddMask = wp 2 (image 8 true A2) := by decide +kernel

theorem stage0 {q : Nat} (hq : 10 ≤ q) : Sub (mac q A0) A1 :=
  capture (sub_of_and entry0) (sub_of_and closed1) hq

theorem stage1 {q : Nat} (hq : 10 ≤ q) : Sub (mac q A1) A2 :=
  capture (sub_of_and entry1) (sub_of_and closed2) hq

theorem stage2 {q : Nat} (hq : 10 ≤ q) : Sub (mac q A2) A2 :=
  capture (sub_of_and entry2) (sub_of_and closed2) hq

theorem stable1 {q : Nat} (hq : 10 ≤ q) : Sub (mac q A1) A1 :=
  sub_trans (stage1 hq) (sub_of_and nested)

theorem white_positive {n : Nat} (hn : 2 ≤ n) :
    Sub (wp n (image 8 true A2)) oddMask := by
  rw [show n = (n-2)+2 by omega, wp_add]
  exact sub_trans (wp_mono (sub_of_and white2) (n-2))
    (wp_closed (sub_of_and white_odd_closed) (n-2))

def Controlled (w : List Bool) : Prop := ∀ i, i < w.length → ∃ b : Bool,
  ∀ r, r < 2^8 → (applyWord 8 (w.take i) A2).testBit r = true →
    (w.getD i false || r.testBit 0) = b

theorem controlled_driver (q : Nat) : Controlled (driver q) := by
  intro i hi
  cases i with
  | zero => exact ⟨true, by intros; rfl⟩
  | succ j =>
    have ht : (driver q).take (j+1) = true :: List.replicate j false := by
      have hj : j ≤ q := by rw [driver_length] at hi; omega
      simp [driver, List.take_replicate, Nat.min_eq_left hj]
    have hg : (driver q).getD (j+1) false = false := by
      have hj : j < q := by rw [driver_length] at hi; omega
      simp [driver, List.getD_eq_getElem?_getD, hj]
    have hw : applyWord 8 ((driver q).take (j+1)) A2 = wp j (image 8 true A2) := by
      rw [ht, applyWord, ← wp_eq]
    rcases Nat.lt_or_ge j 2 with hj | hj
    · cases j with
      | zero =>
        refine ⟨false, fun r hr hm => ?_⟩
        rw [hw] at hm
        rw [hg, const_mem white0 hr hm]
        rfl
      | succ j =>
        have he : j = 0 := by omega
        subst j
        refine ⟨false, fun r hr hm => ?_⟩
        rw [hw] at hm
        rw [hg, const_mem white1 hr hm]
        rfl
    · refine ⟨true, fun r hr hm => ?_⟩
      rw [hw] at hm
      rw [hg, const_mem odd_bit hr (white_positive hj r hm)]
      rfl

theorem controlled_append (u v : List Bool) (hu : Controlled u) (hv : Controlled v)
    (hclosed : Sub (applyWord 8 u A2) A2) : Controlled (u++v) := by
  intro i hi
  by_cases hleft : i < u.length
  · obtain ⟨b,hb⟩ := hu i hleft
    refine ⟨b, fun r hr hm => ?_⟩
    have ht : (u++v).take i = u.take i := by
      simp [List.take_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hleft)]
    have hg : (u++v).getD i false = u.getD i false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hleft]
    rw [ht] at hm
    rw [hg]
    exact hb r hr hm
  · have hlen : u.length ≤ i := by omega
    have hright : i-u.length < v.length := by simp only [List.length_append] at hi; omega
    obtain ⟨b,hb⟩ := hv (i-u.length) hright
    refine ⟨b, fun r hr hm => ?_⟩
    have ht : (u++v).take i = u ++ v.take (i-u.length) := by
      simp [List.take_append, List.take_of_length_le hlen]
    have hg : (u++v).getD i false = v.getD (i-u.length) false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hleft]
    rw [ht, apply_append] at hm
    have hs := word_mono hclosed (v.take (i-u.length)) r hm
    rw [hg]
    exact hb r hr hs

def blocks (qs : List Nat) : List Bool := qs.flatMap driver
def Admissible (qs : List Nat) : Prop := ∀ q ∈ qs, 10 ≤ q

theorem blocks_cons (q : Nat) (qs : List Nat) : blocks (q::qs) = driver q ++ blocks qs := rfl

theorem all_blocks_stable (B : Nat) (one : ∀ q, 10 ≤ q → Sub (mac q B) B)
    (qs : List Nat) (ha : Admissible qs) : Sub (applyWord 8 (blocks qs) B) B := by
  induction qs with
  | nil => exact sub_refl B
  | cons q qs ih =>
    have ha0 := ha q (by simp)
    have has : Admissible qs := fun r hr => ha r (by simp [hr])
    rw [blocks_cons, apply_append, ← mac_eq]
    exact sub_trans (word_mono (one q ha0) (blocks qs)) (ih has)

theorem blocks_progress (A B : Nat) (one : ∀ q, 10 ≤ q → Sub (mac q A) B)
    (stable : ∀ q, 10 ≤ q → Sub (mac q B) B)
    (qs : List Nat) (hne : qs ≠ []) (ha : Admissible qs) :
    Sub (applyWord 8 (blocks qs) A) B := by
  cases qs with
  | nil => exact (hne rfl).elim
  | cons q qs =>
    rw [blocks_cons, apply_append, ← mac_eq]
    exact sub_trans (word_mono (one q (ha q (by simp))) (blocks qs))
      (all_blocks_stable B stable qs (fun r hr => ha r (by simp [hr])))

theorem blocks_warm (qs : List Nat) (hne : qs ≠ []) (ha : Admissible qs) :
    Sub (iterW 8 (blocks qs) 2 (fullSet 8)) A2 := by
  have h0 := blocks_progress A0 A1 (fun _ => stage0) (fun _ => stable1) qs hne ha
  have h1 := blocks_progress A1 A2 (fun _ => stage1) (fun _ => stage2) qs hne ha
  simpa only [iterW, full_A0] using sub_trans (word_mono h0 (blocks qs)) h1

theorem controlled_blocks (qs : List Nat) (ha : Admissible qs) : Controlled (blocks qs) := by
  induction qs with
  | nil => intro i hi; exact (Nat.not_lt_zero _ hi).elim
  | cons q qs ih =>
    rw [blocks_cons]
    have ha0 := ha q (by simp)
    have has : Admissible qs := fun r hr => ha r (by simp [hr])
    exact controlled_append _ _ (controlled_driver q) (ih has)
      (by rw [← mac_eq]; exact stage2 ha0)

theorem blocks_length_pos (qs : List Nat) (hne : qs ≠ []) : 0 < (blocks qs).length := by
  cases qs with
  | nil => exact (hne rfl).elim
  | cons q qs => rw [blocks_cons, List.length_append, driver_length]; omega

/-- Every nonempty periodic mixture of isolated ones with white gaps >=10 is excluded. -/
theorem not_eventually_isolated_mixtures (qs : List Nat) (hne : qs ≠ []) (ha : Admissible qs) :
    ¬ EventuallyWord (qs.flatMap (fun q => true :: List.replicate q false)) := by
  classical
  have hc := controlled_blocks qs ha
  let g : Nat → Bool := fun i => if h : i < (blocks qs).length then Classical.choose (hc i h) else false
  apply no_word_of_invariant (blocks qs) A2 2 g (blocks_length_pos qs hne)
    (blocks_warm qs hne ha) (all_blocks_stable A2 (fun _ => stage2) qs ha)
  intro i hi
  simpa only [g, dite_eq_left hi] using Classical.choose_spec (hc i hi)

end Ruliology.CellularAutomata.Rule30IsolatedMixtures

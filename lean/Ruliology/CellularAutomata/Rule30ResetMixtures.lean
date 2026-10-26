module
public import Ruliology.CellularAutomata.Rule30WhitePad10111
/-! Periodic mixtures of isolated ones with all white gaps at least nine and one gap at least
seventeen, in any order and number. Width-eight strip envelopes certify a general regular language, never a finite word table. -/
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Ruliology.CellularAutomata.Rule30ResetMixtures
open Rule30StripCertificates Rule30WhitePad10111
def A0 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def A1 : Nat := 0xa868b02aa120302920298022a128222ba868a02b2120102220298062a028222b
def A2 : Nat := 0x2868302aa120302920290022a128222b2868202b2120102220290062a028222b
def A3 : Nat := 0x2028202a20202028202800222020202a2028202a20200022202800222020202a
def G : Nat := 0x2020000000202000202000000020202020200000002000000020000000202020

def driver (q : Nat) : List Bool := true :: List.replicate q false
def mac (q A : Nat) : Nat := wp q (image 8 true A)
theorem driver_length (q : Nat) : (driver q).length = q+1 := by simp [driver]
theorem mac_eq (q A : Nat) : mac q A = applyWord 8 (driver q) A := by
  rw [driver, applyWord, ← wp_eq]; rfl

theorem capture {A B : Nat} {n : Nat} (entry : Sub (wp n (image 8 true A)) B)
    (closed : Sub (image 8 false B) B) {q : Nat} (hq : n ≤ q) : Sub (mac q A) B := by
  unfold mac
  rw [show q = (q-n)+n by omega, wp_add]
  exact sub_trans (wp_mono entry (q-n)) (wp_closed closed (q-n))

theorem full_A0 : fullSet 8 = A0 := by decide +kernel

theorem entry0 : wp 9 (image 8 true A0) &&& A1 = wp 9 (image 8 true A0) := by decide +kernel
theorem closed1 : image 8 false A1 &&& A1 = image 8 false A1 := by decide +kernel
theorem entry1 : wp 9 (image 8 true A1) &&& A2 = wp 9 (image 8 true A1) := by decide +kernel
theorem closed2 : image 8 false A2 &&& A2 = image 8 false A2 := by decide +kernel
theorem entry2 : wp 9 (image 8 true A2) &&& A3 = wp 9 (image 8 true A2) := by decide +kernel
theorem closed3 : image 8 false A3 &&& A3 = image 8 false A3 := by decide +kernel
theorem entry3 : wp 9 (image 8 true A3) &&& A3 = wp 9 (image 8 true A3) := by decide +kernel
theorem nested21 : A2 &&& A1 = A2 := by decide +kernel
theorem nested32 : A3 &&& A2 = A3 := by decide +kernel
/-- The reset: one gap of length at least seventeen sends the captured set into `G`. -/
theorem reset17 : wp 17 (image 8 true A3) &&& G = wp 17 (image 8 true A3) := by decide +kernel
theorem closedG : image 8 false G &&& G = image 8 false G := by decide +kernel
theorem entryG : wp 9 (image 8 true G) &&& G = wp 9 (image 8 true G) := by decide +kernel

theorem white0 : colConst 8 (image 8 true G) false = true := by decide +kernel
theorem white1 : colConst 8 (wp 1 (image 8 true G)) false = true := by decide +kernel
theorem white2 : wp 2 (image 8 true G) &&& oddMask = wp 2 (image 8 true G) := by decide +kernel

theorem stage0 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A0) A1 :=
  capture (sub_of_and entry0) (sub_of_and closed1) hq
theorem stage1 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A1) A2 :=
  capture (sub_of_and entry1) (sub_of_and closed2) hq
theorem stage2 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A2) A3 :=
  capture (sub_of_and entry2) (sub_of_and closed3) hq
theorem stage3 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A3) A3 :=
  capture (sub_of_and entry3) (sub_of_and closed3) hq
theorem stage_reset {q : Nat} (hq : 17 ≤ q) : Sub (mac q A3) G :=
  capture (sub_of_and reset17) (sub_of_and closedG) hq
theorem stageG {q : Nat} (hq : 9 ≤ q) : Sub (mac q G) G :=
  capture (sub_of_and entryG) (sub_of_and closedG) hq

theorem stable1 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A1) A1 :=
  sub_trans (stage1 hq) (sub_of_and nested21)
theorem stable2 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A2) A2 :=
  sub_trans (stage2 hq) (sub_of_and nested32)

theorem white_positive {n : Nat} (hn : 2 ≤ n) :
    Sub (wp n (image 8 true G)) oddMask := by
  rw [show n = (n-2)+2 by omega, wp_add]
  exact sub_trans (wp_mono (sub_of_and white2) (n-2))
    (wp_closed (sub_of_and white_odd_closed) (n-2))

def Controlled (w : List Bool) : Prop := ∀ i, i < w.length → ∃ b : Bool,
  ∀ r, r < 2^8 → (applyWord 8 (w.take i) G).testBit r = true →
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
    have hw : applyWord 8 ((driver q).take (j+1)) G = wp j (image 8 true G) := by
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
    (hclosed : Sub (applyWord 8 u G) G) : Controlled (u++v) := by
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
def Admissible (qs : List Nat) : Prop := ∀ q ∈ qs, 9 ≤ q

theorem blocks_cons (q : Nat) (qs : List Nat) : blocks (q::qs) = driver q ++ blocks qs := rfl

theorem all_blocks_stable (B : Nat) (one : ∀ q, 9 ≤ q → Sub (mac q B) B)
    (qs : List Nat) (ha : Admissible qs) : Sub (applyWord 8 (blocks qs) B) B := by
  induction qs with
  | nil => exact sub_refl B
  | cons q qs ih =>
    have ha0 := ha q (by simp)
    have has : Admissible qs := fun r hr => ha r (by simp [hr])
    rw [blocks_cons, apply_append, ← mac_eq]
    exact sub_trans (word_mono (one q ha0) (blocks qs)) (ih has)

theorem blocks_progress (A B : Nat) (one : ∀ q, 9 ≤ q → Sub (mac q A) B)
    (stable : ∀ q, 9 ≤ q → Sub (mac q B) B)
    (qs : List Nat) (hne : qs ≠ []) (ha : Admissible qs) :
    Sub (applyWord 8 (blocks qs) A) B := by
  cases qs with
  | nil => exact (hne rfl).elim
  | cons q qs =>
    rw [blocks_cons, apply_append, ← mac_eq]
    exact sub_trans (word_mono (one q (ha q (by simp))) (blocks qs))
      (all_blocks_stable B stable qs (fun r hr => ha r (by simp [hr])))

/-- One full period containing a gap of length at least seventeen sends `A3` into `G`. -/
theorem blocks_reset (qs : List Nat) (ha : Admissible qs) (hr : ∃ q ∈ qs, 17 ≤ q) :
    Sub (applyWord 8 (blocks qs) A3) G := by
  induction qs with
  | nil => obtain ⟨q, hq, _⟩ := hr; simp at hq
  | cons q qs ih =>
    have ha0 := ha q (by simp)
    have has : Admissible qs := fun r hr => ha r (by simp [hr])
    rw [blocks_cons, apply_append, ← mac_eq]
    by_cases h17 : 17 ≤ q
    · exact sub_trans (word_mono (stage_reset h17) (blocks qs))
        (all_blocks_stable G (fun _ => stageG) qs has)
    · have hr' : ∃ p ∈ qs, 17 ≤ p := by
        obtain ⟨p, hp, hp17⟩ := hr
        rcases List.mem_cons.mp hp with h | h
        · subst h; exact absurd hp17 h17
        · exact ⟨p, h, hp17⟩
      exact sub_trans (word_mono (stage3 ha0) (blocks qs)) (ih has hr')

theorem nonempty_of_reset {qs : List Nat} (hr : ∃ q ∈ qs, 17 ≤ q) : qs ≠ [] := by
  rintro rfl; obtain ⟨q, hq, _⟩ := hr; simp at hq

/-- Three periods capture `A3`; the fourth, containing the reset gap, enters `G`. -/
theorem blocks_warm (qs : List Nat) (ha : Admissible qs) (hr : ∃ q ∈ qs, 17 ≤ q) :
    Sub (iterW 8 (blocks qs) 4 (fullSet 8)) G := by
  have hne := nonempty_of_reset hr
  have h0 := blocks_progress A0 A1 (fun _ => stage0) (fun _ => stable1) qs hne ha
  have h1 := blocks_progress A1 A2 (fun _ => stage1) (fun _ => stable2) qs hne ha
  have h2 := blocks_progress A2 A3 (fun _ => stage2) (fun _ => stage3) qs hne ha
  have h3 := blocks_reset qs ha hr
  simpa only [iterW, full_A0] using
    sub_trans (word_mono (sub_trans (word_mono (sub_trans (word_mono h0 (blocks qs)) h1)
      (blocks qs)) h2) (blocks qs)) h3

theorem controlled_blocks (qs : List Nat) (ha : Admissible qs) : Controlled (blocks qs) := by
  induction qs with
  | nil => intro i hi; exact (Nat.not_lt_zero _ hi).elim
  | cons q qs ih =>
    rw [blocks_cons]
    have ha0 := ha q (by simp)
    have has : Admissible qs := fun r hr => ha r (by simp [hr])
    exact controlled_append _ _ (controlled_driver q) (ih has)
      (by rw [← mac_eq]; exact stageG ha0)

theorem blocks_length_pos (qs : List Nat) (hne : qs ≠ []) : 0 < (blocks qs).length := by
  cases qs with
  | nil => exact (hne rfl).elim
  | cons q qs => rw [blocks_cons, List.length_append, driver_length]; omega

/-- Every periodic mixture of isolated ones whose white gaps are all at least nine, at least one
of them at least seventeen, is excluded as an eventual center column. -/
theorem not_eventually_reset_mixtures (qs : List Nat) (ha : ∀ q ∈ qs, 9 ≤ q)
    (hr : ∃ q ∈ qs, 17 ≤ q) :
    ¬ EventuallyWord (qs.flatMap (fun q => true :: List.replicate q false)) := by
  classical
  have hc := controlled_blocks qs ha
  let g : Nat → Bool := fun i => if h : i < (blocks qs).length then Classical.choose (hc i h) else false
  apply no_word_of_invariant (blocks qs) G 4 g (blocks_length_pos qs (nonempty_of_reset hr))
    (blocks_warm qs ha hr) (all_blocks_stable G (fun _ => stageG) qs ha)
  intro i hi
  simpa only [g, dite_eq_left hi] using Classical.choose_spec (hc i hi)

end Ruliology.CellularAutomata.Rule30ResetMixtures

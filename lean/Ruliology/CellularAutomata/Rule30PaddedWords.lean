module

public import Ruliology.CellularAutomata.Rule30SixTailSharpened
public import Ruliology.CellularAutomata.Rule30WhitePad10111
public import Ruliology.CellularAutomata.Rule30WhiteEnd
public import Ruliology.CellularAutomata.Rule30WhiteRunEight
public import Ruliology.CellularAutomata.Rule30WordRotation
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30Certificates.ShortBlocks

/-!
# Padded words: one bound for each short tail

The center column of the single seed is never eventually the repeating word `0^r u`, a white run
of length `r` followed by a tail `u`, once `r` reaches a bound that depends on `u`.
`paddedBound u` is the least such bound the catalog proves for a tail of at most nine cells, and
`no_padded_word_nine` states them all at once; `no_padded_word` retains its original six-cell API:

| Tail `u` | Bound | Proof |
|---|---|---|
| `11` | 8 | `Rule30WhiteRunEight.no_white_run_11_ge8` |
| `10111` | 9 | `Rule30WhitePad10111.not_eventually_zeros_10111` |
| `1` | 10 | `Rule30WhiteEnd.not_eventuallyWord_white_end`, rotated |
| any other of at most four cells | 49 | `Rule30ShortTail.no_short_tail_seed` |
| any other of five cells | 69 | `Rule30FiveTail.no_five_tail_seed` |
| any other of six cells | 74 | `Rule30SixTailSharpened.no_six_tail_seed` |
| any other of seven to nine cells | 102 | `not_eventually_short`, rotated |

For tails of every length ending in `011`, `001001` or `111001`, `Rule30SuffixFamilies` gives the
bounds `10 · |v| + 41` and `10 · |v| + 71`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PaddedWords

open Rule30StripCertificates Rule30Jen

theorem controlled_short (u : List Bool) (hu : u.length ≤ 9) :
    Rule30SparseGraph.Ctl 14 Rule30FrontBound.Sstar
      (u ++ List.replicate 50 false) Rule30FrontBound.Sstar := by
  have hh := Rule30SparseGraph.root_good Rule30ShortBlocksData.verified
    (i := 0) (v := ⟨Rule30ShortBlocksData.root,0,0,166,9⟩) rfl rfl rfl u hu
  have he : Rule30SparseGraph.mask Rule30ShortBlocksData.root = Rule30FrontBound.Sstar := by decide +kernel
  rw [he] at hh
  exact hh

theorem not_eventually_short_nonzero (u : List Bool) (hu : u.length≤9)
    (hblack : ∃ j, j<u.length ∧ u.getD j false=true) (q : Nat) (hq : 102≤q) :
    ¬ EventuallyWord (u++List.replicate q false) := by
  have hc := controlled_short u hu
  exact Rule30FrontBound.not_eventually_of_blockBound u q hq hblack (Rule30ShortBlockBound.block_bound u hu)
    hc.1 hc.2 Rule30FrontArrivalCapture.hcap

/-- Includes the all-white block, already excluded by the kit's constant-center theorem. -/
theorem not_eventually_short (u : List Bool) (hu : u.length≤9) (q : Nat) (hq : 102≤q) :
    ¬ EventuallyWord (u++List.replicate q false) := by
  by_cases hb : ∃ j, j<u.length ∧ u.getD j false=true
  · exact not_eventually_short_nonzero u hu hb q hq
  · intro he
    obtain ⟨T,hT⟩ := he
    apply Rule30Prize.center_not_eventually_constant
    refine ⟨T,false,fun t ht => ?_⟩
    have hf : ∀ j, u.getD j false=false := by
      intro j
      by_cases hj : j<u.length
      · cases hc : u.getD j false
        · rfl
        · exact False.elim (hb ⟨j,hj,hc⟩)
      · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)];rfl
    change cell t 0=false
    rw [hT t ht]
    rw [List.getD_eq_getElem?_getD]
    by_cases hj : (t-T)%(u++List.replicate q false).length<u.length
    · rw [List.getElem?_append_left hj]
      exact hf _
    · rw [List.getElem?_append_right (by omega),List.getElem?_replicate]
      split <;> rfl



/-- The least `r` from which the catalog excludes `0^r u`, for a tail `u` of at most nine cells. -/
def paddedBound (u : List Bool) : Nat :=
  if u = [true, true] then 8
  else if u = [true, false, true, true, true] then 9
  else if u = [true] then 10
  else if u.length ≤ 4 then 49
  else if u.length ≤ 5 then 69
  else if u.length ≤ 6 then 74
  else 102

/-- An eventual word of the single seed's center column may start at any of its cells. -/
theorem eventuallyWord_swap {u v : List Bool} (hpos : 0 < (u ++ v).length)
    (h : EventuallyWord (u ++ v)) : EventuallyWord (v ++ u) := by
  have h' : Rule30FiniteStrips.EventuallyWord Rule30Realization.seed 0 (u ++ v) := by
    simpa only [Rule30FiniteStrips.EventuallyWord, EventuallyWord, Rule30Realization.evol_seed]
      using h
  simpa only [Rule30FiniteStrips.EventuallyWord, EventuallyWord, Rule30Realization.evol_seed] using
    Rule30WordRotation.eventuallyWord_swap hpos h'

/-- `0^q 1` is the white end `1 0^q`, read from its white run. -/
theorem not_eventuallyWord_zeros_one (q : Nat) (hq : 10 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ [true]) := fun h =>
  Rule30WhiteEnd.not_eventuallyWord_white_end q hq (eventuallyWord_swap (by simp) h)

/-- `0^r 1 1` as an eventual word: its white run and its two black cells, with period `r + 2`. -/
theorem not_eventuallyWord_zeros_11 (r : Nat) (hr : 8 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ [true, true]) := by
  rintro ⟨T, hT⟩
  have hlen : (List.replicate r false ++ [true, true]).length = r + 2 := by simp
  have at_ : ∀ i, i < r + 2 →
      Rule30Prize.center (T + i) = (List.replicate r false ++ [true, true]).getD i false := by
    intro i hi
    have := hT (T + i) (by omega)
    rw [hlen, show T + i - T = i by omega, Nat.mod_eq_of_lt hi] at this
    exact this
  refine Rule30WhiteRunEight.no_white_run_11_ge8 T r T hr (fun t ht => ?_) (Nat.le_refl T)
    (fun i hi => ?_) ?_ ?_
  · show Rule30Jen.cell (t + (r + 2)) 0 = Rule30Jen.cell t 0
    rw [hT _ (by omega), hT t ht, hlen, show t + (r + 2) - T = (t - T) + (r + 2) by omega,
      Nat.add_mod_right]
  · rw [at_ i (by omega), List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
    simp [hi]
  · rw [at_ r (by omega), List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  · rw [show T + r + 1 = T + (r + 1) by omega, at_ (r + 1) (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp)]
    simp

/-- **No padded word**: for a tail `u` of at most nine cells, the center column of the single seed is
not eventually the repeating word `0^r u` once `paddedBound u ≤ r`, whatever the transient. -/
theorem no_padded_word_nine (u : List Bool) (hu : u.length ≤ 9) (r : Nat) (hr : paddedBound u ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ u) := by
  by_cases h11 : u = [true, true]
  · subst h11; exact not_eventuallyWord_zeros_11 r (by simpa [paddedBound] using hr)
  by_cases h10111 : u = [true, false, true, true, true]
  · subst h10111
    exact Rule30WhitePad10111.not_eventually_zeros_10111 r (by simpa [paddedBound] using hr)
  by_cases h1 : u = [true]
  · subst h1; exact not_eventuallyWord_zeros_one r (by simpa [paddedBound] using hr)
  by_cases h4 : u.length ≤ 4
  · exact Rule30ShortTail.no_short_tail_seed u h4 r
      (by simpa [paddedBound, h11, h10111, h1, h4] using hr)
  by_cases h5 : u.length ≤ 5
  · exact Rule30FiveTail.no_five_tail_seed u h5 r
      (by simpa [paddedBound, h11, h10111, h1, h4, h5] using hr)
  by_cases h6 : u.length ≤ 6
  · exact Rule30SixTailSharpened.no_six_tail_seed u h6 r
      (by simpa [paddedBound, h11, h10111, h1, h4, h5, h6] using hr)
  · have hr102 : 102 ≤ r := by
      simpa [paddedBound, h11, h10111, h1, h4, h5, h6] using hr
    exact not_eventually_short u hu r hr102 ∘
      eventuallyWord_swap (by simp; omega)

/-- Original six-cell catalog API, retaining its sharper bound for every such tail. -/
theorem no_padded_word (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : paddedBound u ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ u) :=
  no_padded_word_nine u (Nat.le_trans hu (by decide)) r hr

end Ruliology.CellularAutomata.Rule30PaddedWords

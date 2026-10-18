import Rule30Equivalents.Genericity

/-!
# Preimages under rule 30

Rule 30 is onto (`Genericity.surjective_evol_one`) and not one-to-one. This file bounds the
preimages, using only left-permutivity: `F(x)_q = x_{q-1} ⊕ (x_q ∨ x_{q+1})`, so `x_{q-1}` is
determined by `F(x)_q`, `x_q` and `x_{q+1}`.

* `eq_of_evol_one_eq`: two configurations with the same image that agree on two adjacent cells
  `k`, `k + 1` agree at every cell left of them; locally, down to the cell `p` when the images
  agree on the cells from `p + 1` to `k + 1` (`eq_of_evol_one_eq_on`).
* `eq_of_evol_one_eq_of_right`: so rule 30 is injective on configurations that agree far to the
  right, in particular pre-injective (as the Garden of Eden theorem requires of an onto map).
* `card_le_four`: **every configuration has at most four preimages** (Hedlund's bound
  `|A|^(2r)` for rule 30). Among five preimages, two agree on the cells `k`, `k + 1` for
  infinitely many `k`, hence everywhere.
* `preimage_white`: the all-white configuration has exactly two preimages, all white and all
  black.
* `eq_of_evol_one_eq_of_frequently`: **a configuration that shows `010` arbitrarily far to the
  right has exactly one preimage**. An image showing `010` at `q, q + 1, q + 2` forces the
  preimage to be black at `q - 1` (`eq_true_of_window`), and then the image at `q - 1` fixes the
  cell `q - 2`. Almost every configuration, and a comeager set of them, show `010` so
  (`Mixing.ae_existsUnique_preimage`, `Mixing.residual_existsUnique_preimage`). The inverse looks
  only to the right: the cell `p` of the preimage is determined by the image on the cells
  `p + 1, …, q + 2` for any such `q > p` (`eq_of_evol_one_eq_on_of_window`).
* `exists_ne_left_eq`: rule 30 is not injective on left-asymptotic configurations. Black only at
  `0` on the left, then `(0110)^∞` against `(1000)^∞` from the cell `1` on, have the same
  image. A preimage can branch only after a black cell, and these two branches run around a cycle
  of length `4` of pairs of states. So `not_positivelyExpansive`: **rule 30 is not positively
  expansive**; for every window `[-n, n]` two different configurations have orbits that agree on
  it at all times.
-/

namespace Rule30Equivalents.Preimages

open Ruliology.CellularAutomata Rule30Realization

/-- One step of rule 30, cell by cell. -/
theorem evol_one (x : ℤ → Bool) (q : ℤ) : evol x 1 q = xor (x (q - 1)) (x q || x (q + 1)) := rfl

/-- **Left determinism, locally**: configurations whose images agree on the cells `j` with
`p < j ≤ k + 1`, and which agree on `k` and `k + 1`, agree on every cell from `p` to `k + 1`. -/
theorem eq_of_evol_one_eq_on {x y : ℤ → Bool} {p k : ℤ}
    (h : ∀ j, p < j → j ≤ k + 1 → evol x 1 j = evol y 1 j) (hk : x k = y k)
    (hk1 : x (k + 1) = y (k + 1)) : ∀ q, p ≤ q → q ≤ k + 1 → x q = y q := by
  have step : ∀ n : ℕ, p ≤ k - n → x (k - n) = y (k - n) ∧ x (k - n + 1) = y (k - n + 1) := by
    intro n
    induction n with
    | zero => intro _; simpa using ⟨hk, hk1⟩
    | succ n ih =>
      intro hn
      have ih' := ih (by push_cast at hn; omega)
      have e := h (k - n) (by push_cast at hn; omega) (by omega)
      rw [evol_one, evol_one, ih'.1, ih'.2] at e
      refine ⟨?_, ?_⟩
      · have : x (k - n - 1) = y (k - n - 1) := by
          generalize (y (k - n) || y (k - n + 1)) = c at e
          cases c <;> simpa using e
        rwa [show k - ((n + 1 : ℕ) : ℤ) = k - n - 1 by push_cast; ring]
      · rw [show k - ((n + 1 : ℕ) : ℤ) + 1 = k - n by push_cast; ring]
        exact ih'.1
  intro q hpq hq
  rcases eq_or_lt_of_le hq with rfl | hlt
  · exact hk1
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, q = k - n := ⟨(k - q).toNat, by omega⟩
    rw [hn]
    exact (step n (by omega)).1

/-- **Left determinism**: configurations with the same image that agree on `k` and `k + 1` agree
at every cell `q ≤ k + 1`. -/
theorem eq_of_evol_one_eq {x y : ℤ → Bool} (h : evol x 1 = evol y 1) {k : ℤ}
    (hk : x k = y k) (hk1 : x (k + 1) = y (k + 1)) : ∀ q, q ≤ k + 1 → x q = y q := fun q hq =>
  eq_of_evol_one_eq_on (p := q) (fun j _ _ => congrFun h j) hk hk1 q le_rfl hq

/-- **Rule 30 is injective on right-asymptotic configurations**: two configurations with the same
image that agree right of some cell are equal. In particular rule 30 is pre-injective. -/
theorem eq_of_evol_one_eq_of_right {x y : ℤ → Bool} (h : evol x 1 = evol y 1) {k : ℤ}
    (hr : ∀ q, k ≤ q → x q = y q) : x = y := by
  funext q
  rcases le_or_gt q (k + 1) with hq | hq
  · exact eq_of_evol_one_eq h (hr k le_rfl) (hr (k + 1) (by omega)) q hq
  · exact hr q (by omega)

/-- **Every configuration has at most four preimages.** -/
theorem card_le_four (y : ℤ → Bool) (s : Finset (ℤ → Bool)) (hs : ∀ x ∈ s, evol x 1 = y) :
    s.card ≤ 4 := by
  by_contra hcard
  push Not at hcard
  -- five distinct preimages
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 5 ≤ s.card by omega)
  let e : Fin 5 ≃ t := (Fintype.equivFinOfCardEq (by simp [htc])).symm
  let x : Fin 5 → ℤ → Bool := fun j => (e j).1
  have hx : ∀ j, evol (x j) 1 = y := fun j => hs _ (hts (e j).2)
  have hinj : Function.Injective x := fun j j' h => e.injective (Subtype.ext h)
  -- at every `k ≥ 0`, two of them agree on `k` and `k + 1`
  have hpair : ∀ k : ℕ, ∃ p : Fin 5 × Fin 5, p.1 ≠ p.2 ∧
      x p.1 k = x p.2 k ∧ x p.1 (k + 1) = x p.2 (k + 1) := by
    intro k
    obtain ⟨j, j', hne, hjj⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun j => (x j k, x j (k + 1))) (by simp)
    exact ⟨(j, j'), hne, (Prod.ext_iff.1 hjj).1, (Prod.ext_iff.1 hjj).2⟩
  choose p hp using hpair
  -- one pair occurs for infinitely many `k`
  obtain ⟨p₀, hp₀⟩ := Finite.exists_infinite_fiber p
  have hinf : (p ⁻¹' {p₀}).Infinite := Set.infinite_coe_iff.1 hp₀
  have heq : x p₀.1 = x p₀.2 := by
    funext q
    obtain ⟨k, hk, hkq⟩ := hinf.exists_gt q.toNat
    have hpk : p k = p₀ := hk
    have := hp k
    rw [hpk] at this
    exact eq_of_evol_one_eq ((hx _).trans (hx _).symm) this.2.1 this.2.2 q (by omega)
  obtain ⟨hne, -⟩ : p₀.1 ≠ p₀.2 ∧ True := by
    obtain ⟨k, hk⟩ := hinf.nonempty
    have hpk : p k = p₀ := hk
    have := (hp k).1
    rw [hpk] at this
    exact ⟨this, trivial⟩
  exact hne (hinj heq)

/-- **The all-white configuration has exactly two preimages**: all white and all black. -/
theorem preimage_white (x : ℤ → Bool) :
    evol x 1 = (fun _ => false) ↔ x = (fun _ => false) ∨ x = (fun _ => true) := by
  constructor
  · intro h
    -- the image is white iff `x_{q-1} = x_q ∨ x_{q+1}` for all `q`
    have hq : ∀ q, x (q - 1) = (x q || x (q + 1)) := fun q => by
      have := congrFun h q
      rw [evol_one] at this
      cases ha : x (q - 1) <;> cases hb : (x q || x (q + 1)) <;> simp_all
    by_cases hall : ∀ q, x q = false
    · exact Or.inl (funext hall)
    push Not at hall
    obtain ⟨q₀, hq₀⟩ := hall
    have hq₀' : x q₀ = true := by simpa using hq₀
    -- a black cell has a black right neighbour
    have hright : ∀ q, x q = true → x (q + 1) = true := by
      intro q hxq
      by_contra hne
      have h1 : x (q + 1) = false := by simpa using hne
      have h2 := hq (q + 1)
      rw [show q + 1 - 1 = q by ring, hxq, h1, Bool.false_or, show q + 1 + 1 = q + 2 by ring] at h2
      have h3 := hq (q + 2)
      rw [show q + 2 - 1 = q + 1 by ring, h1, ← h2, Bool.true_or] at h3
      exact Bool.false_ne_true h3
    -- and a black left neighbour
    have hleft : ∀ q, x q = true → x (q - 1) = true := by
      intro q hxq
      rw [hq q, hxq, Bool.true_or]
    refine Or.inr (funext fun q => ?_)
    rcases le_or_gt q₀ q with hle | hlt
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = q₀ + n := ⟨(q - q₀).toNat, by omega⟩
      induction n with
      | zero => simpa using hq₀'
      | succ n ih =>
        rw [show q₀ + ((n + 1 : ℕ) : ℤ) = q₀ + n + 1 by push_cast; ring]
        exact hright _ (ih (by omega))
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = q₀ - n := ⟨(q₀ - q).toNat, by omega⟩
      induction n with
      | zero => simpa using hq₀'
      | succ n ih =>
        rw [show q₀ - ((n + 1 : ℕ) : ℤ) = q₀ - n - 1 by push_cast; ring]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simpa using hleft _ hq₀'
        · exact hleft _ (ih (by omega))
  · rintro (rfl | rfl)
    · funext q
      rfl
    · funext q
      rfl

/-! ### Configurations with a unique preimage -/

/-- **The word `010` pins its left neighbour**: if the image of `x` shows `0, 1, 0` at the cells
`q, q + 1, q + 2`, then `x` is black at `q - 1`. Were it white, `F(x)_q = 0` would make `x_q` and
`x_{q+1}` white, then `F(x)_{q+1} = 1` would make `x_{q+2}` black and `F(x)_{q+2} = 1`. -/
theorem eq_true_of_window {x : ℤ → Bool} {q : ℤ} (h0 : evol x 1 q = false)
    (h1 : evol x 1 (q + 1) = true) (h2 : evol x 1 (q + 2) = false) : x (q - 1) = true := by
  rw [evol_one] at h0
  rw [evol_one, show q + 1 - 1 = q by ring, show q + 1 + 1 = q + 2 by ring] at h1
  rw [evol_one, show q + 2 - 1 = q + 1 by ring] at h2
  revert h0 h1 h2
  cases x (q - 1) <;> cases x q <;> cases x (q + 1) <;> cases x (q + 2) <;>
    cases x (q + 2 + 1) <;> decide

/-- **The inverse of rule 30 looks only to the right**: if the image of `x` shows `010` at the
cells `q, q + 1, q + 2` with `p < q`, then the cell `p` of `x` is determined by the image on the
cells `p + 1, …, q + 2`. Both preimages are black at `q - 1` (`eq_true_of_window`), so the image
at `q - 1` fixes the cell `q - 2`, and left determinism runs down to `p`. -/
theorem eq_of_evol_one_eq_on_of_window {x y : ℤ → Bool} {p q : ℤ} (hpq : p < q)
    (h : ∀ j, p < j → j ≤ q + 2 → evol x 1 j = evol y 1 j)
    (h0 : evol x 1 q = false) (h1 : evol x 1 (q + 1) = true) (h2 : evol x 1 (q + 2) = false) :
    x p = y p := by
  have hx := eq_true_of_window h0 h1 h2
  have hy := eq_true_of_window (x := y) (q := q) (by rw [← h q hpq (by omega)]; exact h0)
    (by rw [← h (q + 1) (by omega) (by omega)]; exact h1)
    (by rw [← h (q + 2) (by omega) le_rfl]; exact h2)
  rcases eq_or_lt_of_le (show p ≤ q - 1 by omega) with hp | hp
  · rw [hp, hx, hy]
  have h2' : x (q - 2) = y (q - 2) := by
    have e := h (q - 1) hp (by omega)
    rw [evol_one, evol_one, show q - 1 - 1 = q - 2 by ring, hx, hy] at e
    simpa using e
  exact eq_of_evol_one_eq_on (k := q - 2) (fun j hj hj' => h j hj (by omega)) h2'
    (by rw [show q - 2 + 1 = q - 1 by ring, hx, hy]) p le_rfl (by omega)

/-- Two preimages of a configuration agree at every cell left of an occurrence of `010` in it. -/
theorem eq_of_evol_one_eq_of_window {x y : ℤ → Bool} (h : evol x 1 = evol y 1) {q : ℤ}
    (h0 : evol x 1 q = false) (h1 : evol x 1 (q + 1) = true) (h2 : evol x 1 (q + 2) = false) :
    ∀ p, p ≤ q - 1 → x p = y p := fun p hp =>
  eq_of_evol_one_eq_on_of_window (by omega) (fun j _ _ => congrFun h j) h0 h1 h2

/-- **Unique preimages**: a configuration that shows `010` arbitrarily far to the right has
exactly one preimage. -/
theorem eq_of_evol_one_eq_of_frequently {x y : ℤ → Bool} (h : evol x 1 = evol y 1)
    (hw : ∀ n : ℤ, ∃ q ≥ n,
      evol x 1 q = false ∧ evol x 1 (q + 1) = true ∧ evol x 1 (q + 2) = false) :
    x = y := by
  funext p
  obtain ⟨q, hq, h0, h1, h2⟩ := hw (p + 1)
  exact eq_of_evol_one_eq_of_window h h0 h1 h2 p (by omega)

/-! ### Left-asymptotic pairs -/

/-- Black only at `0` on the left, then `(0110)^∞` from the cell `1` on. -/
def pairL (q : ℤ) : Bool := if q ≤ 0 then decide (q = 0) else decide (q % 4 = 2 ∨ q % 4 = 3)

/-- Black only at `0` on the left, then `(1000)^∞` from the cell `1` on. -/
def pairR (q : ℤ) : Bool := if q ≤ 0 then decide (q = 0) else decide (q % 4 = 1)

theorem evol_one_pairL_eq : evol pairL 1 = evol pairR 1 := by
  funext q
  rw [evol_one, evol_one]
  rcases le_or_gt q (-1) with hq | hq
  · simp only [pairL, pairR, if_pos (show q - 1 ≤ 0 by omega), if_pos (show q ≤ 0 by omega),
      if_pos (show q + 1 ≤ 0 by omega)]
  rcases (show q = 0 ∨ q = 1 ∨ 2 ≤ q by omega) with rfl | rfl | hq2
  · decide
  · decide
  · have h4 : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3 := by omega
    simp only [pairL, pairR, if_neg (show ¬ q - 1 ≤ 0 by omega), if_neg (show ¬ q ≤ 0 by omega),
      if_neg (show ¬ q + 1 ≤ 0 by omega)]
    rcases h4 with h | h | h | h
    · rw [show (q - 1) % 4 = 3 by omega, show (q + 1) % 4 = 1 by omega, h]
      decide
    · rw [show (q - 1) % 4 = 0 by omega, show (q + 1) % 4 = 2 by omega, h]
      decide
    · rw [show (q - 1) % 4 = 1 by omega, show (q + 1) % 4 = 3 by omega, h]
      decide
    · rw [show (q - 1) % 4 = 2 by omega, show (q + 1) % 4 = 0 by omega, h]
      decide

/-- **Rule 30 is not injective on left-asymptotic configurations**: two different configurations
that agree at every cell `q ≤ 0` have the same image. -/
theorem exists_ne_left_eq :
    ∃ x y : ℤ → Bool, x ≠ y ∧ (∀ q, q ≤ 0 → x q = y q) ∧ evol x 1 = evol y 1 :=
  ⟨pairL, pairR, fun h => absurd (congrFun h 1) (by decide), fun q hq => by
    simp [pairL, pairR, hq], evol_one_pairL_eq⟩

/-- **Rule 30 is not positively expansive**: for every window `[-n, n]`, two different
configurations have orbits that agree on the window at all times. -/
theorem not_positivelyExpansive (n : ℕ) :
    ∃ x y : ℤ → Bool, x ≠ y ∧
      ∀ (t : ℕ) (p : ℤ), -(n : ℤ) ≤ p → p ≤ n → evol x t p = evol y t p := by
  obtain ⟨x, y, hne, hleft, himg⟩ := exists_ne_left_eq
  -- shift the pair `n` cells to the right
  let x' : ℤ → Bool := fun q => x (q - n)
  let y' : ℤ → Bool := fun q => y (q - n)
  have hshift : ∀ (z : ℤ → Bool) (t : ℕ) (q : ℤ),
      evol (fun q => z (q - n)) t q = evol z t (q - n) := fun z t q => by
    have := Rule30ZeroBoundaryBarriers.evol_shift_all (x := z) (x' := fun q => z (q - n))
      (d := n) (fun p => by simp) t (q - n)
    rwa [sub_add_cancel] at this
  have h1 : evol x' 1 = evol y' 1 := funext fun q => by
    rw [hshift x 1 q, hshift y 1 q, himg]
  refine ⟨x', y', fun h => hne (funext fun q => by
    have := congrFun h (q + n)
    simpa [x', y'] using this), fun t p _ hp2 => ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact hleft (p - n) (by omega)
  · obtain ⟨s, rfl⟩ : ∃ s, t = 1 + s := ⟨t - 1, by omega⟩
    rw [← Rule30ZeroBoundaryBarriers.evol_restart x' 1 s p,
      ← Rule30ZeroBoundaryBarriers.evol_restart y' 1 s p]
    show evol (fun p => evol x' 1 p) s p = evol (fun p => evol y' 1 p) s p
    rw [show (fun p => evol x' 1 p) = evol y' 1 from h1]

end Rule30Equivalents.Preimages

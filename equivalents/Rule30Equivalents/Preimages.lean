import Rule30Equivalents.Genericity

/-!
# Preimages under rule 30

Rule 30 is onto (`Genericity.surjective_evol_one`) and not one-to-one. This file bounds the
preimages, using only left-permutivity: `F(x)_q = x_{q-1} ⊕ (x_q ∨ x_{q+1})`, so `x_{q-1}` is
determined by `F(x)_q`, `x_q` and `x_{q+1}`.

* `eq_of_evol_one_eq`: two configurations with the same image that agree on two adjacent cells
  `k`, `k + 1` agree at every cell left of them.
* `eq_of_evol_one_eq_of_right`: so rule 30 is injective on configurations that agree far to the
  right, in particular pre-injective (as the Garden of Eden theorem requires of an onto map).
* `card_le_four`: **every configuration has at most four preimages** (Hedlund's bound
  `|A|^(2r)` for rule 30). Among five preimages, two agree on the cells `k`, `k + 1` for
  infinitely many `k`, hence everywhere.
* `preimage_white`: the all-white configuration has exactly two preimages, all white and all
  black.
-/

namespace Rule30Equivalents.Preimages

open Ruliology.CellularAutomata Rule30Realization

/-- One step of rule 30, cell by cell. -/
theorem evol_one (x : ℤ → Bool) (q : ℤ) : evol x 1 q = xor (x (q - 1)) (x q || x (q + 1)) := rfl

/-- **Left determinism**: configurations with the same image that agree on `k` and `k + 1` agree
at every cell `q ≤ k + 1`. -/
theorem eq_of_evol_one_eq {x y : ℤ → Bool} (h : evol x 1 = evol y 1) {k : ℤ}
    (hk : x k = y k) (hk1 : x (k + 1) = y (k + 1)) : ∀ q, q ≤ k + 1 → x q = y q := by
  -- agreement on `k - n` and `k - n + 1`, by induction on `n`
  have step : ∀ n : ℕ, x (k - n) = y (k - n) ∧ x (k - n + 1) = y (k - n + 1) := by
    intro n
    induction n with
    | zero => simpa using ⟨hk, hk1⟩
    | succ n ih =>
      have e := congrFun h (k - n)
      rw [evol_one, evol_one, ih.1, ih.2] at e
      refine ⟨?_, ?_⟩
      · have : x (k - n - 1) = y (k - n - 1) := by
          generalize (y (k - n) || y (k - n + 1)) = c at e
          cases c <;> simpa using e
        rwa [show k - ((n + 1 : ℕ) : ℤ) = k - n - 1 by push_cast; ring]
      · rw [show k - ((n + 1 : ℕ) : ℤ) + 1 = k - n by push_cast; ring]
        exact ih.1
  intro q hq
  rcases eq_or_lt_of_le hq with rfl | hlt
  · exact hk1
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, q = k - n := ⟨(k - q).toNat, by omega⟩
    rw [hn]
    exact (step n).1

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

end Rule30Equivalents.Preimages

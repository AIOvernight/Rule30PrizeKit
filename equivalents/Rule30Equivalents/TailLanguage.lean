import Rule30Equivalents.WordsAutomata

/-!
# The tail language: no flat step, no Rauzy cycle

`WordsAutomata.tailFactors b n` is the set of words of length `n` that occur in `b` infinitely
often, the tail language `L∞(b)`; write `p∞(n)` for its size.

* `eventually_factors_eq_tailFactors`: past some time, the windows of a given length that occur
  in `b` are exactly the words of `L∞(b)`.
* `eventuallyPeriodic_iff_tail_flat`: `b` is eventually periodic iff `p∞` has a flat step,
  `p∞(m + 1) ≤ p∞(m)` for some `m`. A flat step is a flat step of the factor complexity of a tail
  of `b`, so Morse–Hedlund applies (`ShiftOrbit.eventuallyPeriodic_of_ncard_factors_succ_le`).
* `problem1_iff_tail_strictMono` (catalog [35], Rauzy form): Problem 1 holds iff `p∞` is strictly
  increasing.

The Rauzy graph `Γ_m` of `L∞(c)` has the words of `L∞(c)` of length `m` as vertices and one edge
`u → v` for each word of `L∞(c)` of length `m + 1` with prefix `u` and suffix `v`. Every vertex has
an outgoing edge and `Γ_m` is strongly connected, so `Γ_m` is a single cycle exactly when it has as
many edges as vertices, `p∞(m + 1) = p∞(m)`. So `problem1_iff_tail_strictMono` says that no Rauzy
graph of the tail language of the center column is a single cycle. The graphs themselves are not
formalized here.

Sources: G. Rauzy, *Suites à termes dans un alphabet fini*, Sém. Théorie des Nombres de Bordeaux
(1983); J. Cassaigne and F. Nicolas, *Factor complexity*, in Combinatorics, Automata and Number
Theory (2010). Catalog entry [35].
-/

namespace Rule30Equivalents.TailLanguage

open Ruliology.CellularAutomata WordsAutomata

/-- **Past some time, the windows of length `n` are exactly the tail factors.** -/
theorem eventually_factors_eq_tailFactors (b : ℕ → Bool) (n : ℕ) :
    ∃ N, ∀ M, N ≤ M → ShiftOrbit.factors (fun t => b (M + t)) n = tailFactors b n := by
  have hev : ∀ u : Fin n → Bool, ∀ᶠ i in Filter.atTop,
      (fun j : Fin n => b (i + j)) = u → u ∈ tailFactors b n := by
    intro u
    by_cases hu : u ∈ tailFactors b n
    · exact Filter.Eventually.of_forall fun _ _ => hu
    · have hu' : ¬ ∃ᶠ i in Filter.atTop, (fun j : Fin n => b (i + j)) = u := hu
      exact (Filter.not_frequently.1 hu').mono fun i hi he => absurd he hi
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 hev)
  refine ⟨N, fun M hM => Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨i, rfl⟩
    have := hN (M + i) (by omega) _ rfl
    simpa only [Nat.add_assoc] using this
  · intro w hw
    obtain ⟨i, hi, hiw⟩ := Filter.frequently_atTop.1 hw M
    refine ⟨i - M, ?_⟩
    rw [← hiw]
    funext j
    simp only
    congr 1
    omega

/-- The empty word occurs at every position. -/
theorem ncard_tailFactors_zero (b : ℕ → Bool) : (tailFactors b 0).ncard = 1 := by
  have : tailFactors b 0 = Set.univ := by
    ext w
    simp only [Set.mem_univ, iff_true]
    exact Filter.Frequently.of_forall fun i => funext fun j => j.elim0
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, pow_zero]

/-- **`b` is eventually periodic iff its tail complexity has a flat step.** -/
theorem eventuallyPeriodic_iff_tail_flat (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ m, (tailFactors b (m + 1)).ncard ≤ (tailFactors b m).ncard := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (eventuallyPeriodic_iff_exists_ncard_tailFactors_le b).1 h
    by_contra hcon
    push Not at hcon
    have hgrow : ∀ k, k + 1 ≤ (tailFactors b k).ncard := by
      intro k
      induction k with
      | zero => rw [ncard_tailFactors_zero]
      | succ k ih => have := hcon k; omega
    have := hgrow n
    omega
  · rintro ⟨m, hm⟩
    obtain ⟨N₁, h₁⟩ := eventually_factors_eq_tailFactors b m
    obtain ⟨N₂, h₂⟩ := eventually_factors_eq_tailFactors b (m + 1)
    apply eventuallyPeriodic_of_tail (max N₁ N₂)
    apply ShiftOrbit.eventuallyPeriodic_of_ncard_factors_succ_le (n := m)
    rw [h₁ _ (le_max_left _ _), h₂ _ (le_max_right _ _)]
    exact hm

/-- **Problem 1 ⟺ the tail complexity of the center column is strictly increasing** (catalog [35]):
no Rauzy graph of its tail language is a single cycle. -/
theorem problem1_iff_tail_strictMono :
    Rule30Prize.Problem1 ↔ ∀ m, (tailFactors c m).ncard < (tailFactors c (m + 1)).ncard := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_tail_flat]
  push Not
  rfl

end Rule30Equivalents.TailLanguage

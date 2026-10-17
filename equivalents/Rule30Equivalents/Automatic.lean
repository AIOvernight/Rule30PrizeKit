import Rule30Equivalents.OmegaRegular
import Mathlib.Computability.DFA
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Finite.Range

/-!
# Automatic sequences and automatic complexity: two sufficient conditions

An eventually periodic sequence is as simple as possible for finite automata in two senses. This
gives the direction "the form implies Problem 1" of two catalog entries whose converses need deep
theorems.

* **k-automatic sequences** (catalog [42]). `IsAutomatic k f` says that the k-kernel
  `{n ↦ f(kᵉ n + r) : r < kᵉ}` is finite (Eilenberg's criterion).
  `isAutomatic_of_eventuallyPeriodic`: an eventually periodic sequence is k-automatic for every
  `k ≥ 2`. So `problem1_of_not_automatic`: if the center column is not k-automatic for some
  `k ≥ 2`, Problem 1 holds; `problem1_of_not_two_three_automatic`: the same if it is not both 2- and
  3-automatic. The converse of the second is Cobham's theorem (1969).
* **Automatic complexity** (catalog [52]). `AutComplexityLE x K` says that some DFA with `K` states
  accepts `x` and no other word of the same length (Shallit and Wang).
  `autComplexityLE_of_eventuallyPeriodic`: for an eventually periodic sequence with period `P` from
  `T`, every prefix has automatic complexity at most `T + P + 1`, through the lasso automaton with a
  dead state (`lassoDFA`). So `problem1_of_automaticComplexity_tendsto_top`: if the automatic
  complexity of the prefixes of the center column tends to infinity, Problem 1 holds. The converse
  needs the Lyndon–Schützenberger theorem on commuting words.

Sources: A. Cobham, *On the base-dependence of sets of numbers recognizable by finite automata*,
Math. Systems Theory 3 (1969) 186–192; S. Eilenberg, *Automata, Languages, and Machines* A (1974);
J. Shallit and M.-w. Wang, *Automatic complexity of strings*, J. Autom. Lang. Comb. 6 (2001)
537–554. Catalog entries [42] and [52].
-/

namespace Rule30Equivalents.Automatic

open Ruliology.CellularAutomata OmegaRegular

/-! ### k-automatic sequences -/

/-- The k-kernel of `f`: the subsequences `n ↦ f(kᵉ n + r)` with `r < kᵉ`. -/
def kernel (k : ℕ) (f : ℕ → Bool) : Set (ℕ → Bool) :=
  {g | ∃ e r, r < k ^ e ∧ g = fun n => f (k ^ e * n + r)}

/-- `f` is k-automatic: its k-kernel is finite. -/
def IsAutomatic (k : ℕ) (f : ℕ → Bool) : Prop := (kernel k f).Finite

/-- On the periodic part, the value depends only on the residue mod `P`. -/
theorem eq_of_mod_eq {b : ℕ → Bool} {T P : ℕ} (hper : ∀ t, T ≤ t → b (t + P) = b t)
    {m m' : ℕ} (hm : T ≤ m) (hm' : T ≤ m') (hmod : m % P = m' % P) : b m = b m' := by
  wlog hle : m ≤ m' generalizing m m'
  · exact (this hm' hm hmod.symm (by omega)).symm
  obtain ⟨k, hk⟩ : P ∣ m' - m := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
  rw [Nat.mul_comm] at hk
  rw [show m' = m + k * P by omega]
  exact (periodic_add_mul b T P hper hm k).symm

/-- **An eventually periodic sequence is k-automatic for every `k ≥ 2`.** -/
theorem isAutomatic_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) {k : ℕ}
    (hk : 2 ≤ k) : IsAutomatic k b := by
  obtain ⟨T, P, hP, hper⟩ := h
  let F : ℕ → Bool := fun j => b (j + T * P)
  have hF : ∀ m, T ≤ m → b m = F (m % P) := fun m hm =>
    eq_of_mod_eq hper hm (by have := Nat.le_mul_of_pos_right T hP; omega)
      (by rw [Nat.add_mul_mod_self_right, Nat.mod_mod])
  let Φ : Bool × Fin P × Fin P → ℕ → Bool := fun x n =>
    if n = 0 then x.1 else F ((x.2.1 * n + x.2.2) % P)
  refine (((Finset.range T ×ˢ Finset.range T : Finset (ℕ × ℕ)).finite_toSet.image
    fun er : ℕ × ℕ => fun n => b (k ^ er.1 * n + er.2)).union (Set.finite_range Φ)).subset ?_
  rintro g ⟨e, r, hr, rfl⟩
  by_cases hsmall : k ^ e ≤ T
  · left
    have he : e < T :=
      lt_of_lt_of_le (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hk e)) hsmall
    refine ⟨(e, r), ?_, rfl⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio]
    omega
  · right
    refine ⟨(b r, ⟨k ^ e % P, Nat.mod_lt _ hP⟩, ⟨r % P, Nat.mod_lt _ hP⟩), ?_⟩
    funext n
    simp only [Φ]
    split_ifs with hn
    · subst hn; simp
    · have hke : k ^ e ≤ k ^ e * n := Nat.le_mul_of_pos_right _ (by omega)
      rw [hF _ (by omega)]
      congr 1
      simp [Nat.add_mod, Nat.mul_mod]

/-- **A sufficient condition** (catalog [42]): if the center column is not k-automatic for some
`k ≥ 2`, Problem 1 holds. -/
theorem problem1_of_not_automatic {k : ℕ} (hk : 2 ≤ k) (h : ¬ IsAutomatic k c) :
    Rule30Prize.Problem1 :=
  fun hep => h (isAutomatic_of_eventuallyPeriodic hep hk)

/-- **A sufficient condition** (catalog [42]): if the center column is not both 2-automatic and
3-automatic, Problem 1 holds. The converse is Cobham's theorem. -/
theorem problem1_of_not_two_three_automatic
    (h : ¬ (IsAutomatic 2 Rule30Prize.center ∧ IsAutomatic 3 Rule30Prize.center)) :
    Rule30Prize.Problem1 :=
  fun hep => h ⟨isAutomatic_of_eventuallyPeriodic hep le_rfl,
    isAutomatic_of_eventuallyPeriodic hep (by norm_num)⟩

/-! ### Automatic complexity -/

/-- `M` accepts `x` and no other word of the same length. -/
def UniquelyAccepts {σ : Type} (M : DFA Bool σ) (x : List Bool) : Prop :=
  x ∈ M.accepts ∧ ∀ y : List Bool, y.length = x.length → y ∈ M.accepts → y = x

/-- The automatic complexity of `x` is at most `K`. -/
def AutComplexityLE (x : List Bool) (K : ℕ) : Prop :=
  ∃ M : DFA Bool (Fin K), UniquelyAccepts M x

section Lasso
variable (b : ℕ → Bool) (T P : ℕ) (hP : 0 < P)

/-- The prefix of length `n`. -/
def prefixOf (n : ℕ) : List Bool := (List.range n).map b

theorem prefixOf_succ (n : ℕ) : prefixOf b (n + 1) = prefixOf b n ++ [b n] := by
  simp [prefixOf, List.range_succ]

/-- The live state at the lasso position of time `n`. -/
def posState (n : ℕ) : Fin (T + P + 1) := ⟨pos T P n, by have := pos_lt T P hP n; omega⟩

/-- The lasso automaton with a dead state `T + P`, accepting at the lasso position of time `n`. -/
def lassoDFA (n : ℕ) : DFA Bool (Fin (T + P + 1)) where
  step s a := if h : (s : ℕ) < T + P then
      (if a = b s then ⟨succPos T P s, by have := succPos_lt T P hP s; omega⟩ else Fin.last _)
    else Fin.last _
  start := posState T P hP 0
  accept := {posState T P hP n}

theorem lassoDFA_step_pos (n m : ℕ) (a : Bool) :
    (lassoDFA b T P hP n).step (posState T P hP m) a =
      if a = b (pos T P m) then posState T P hP (m + 1) else Fin.last _ := by
  simp only [lassoDFA, posState, dif_pos (pos_lt T P hP m)]
  rfl

theorem lassoDFA_step_last (n : ℕ) (a : Bool) :
    (lassoDFA b T P hP n).step (Fin.last _) a = Fin.last _ := by
  simp [lassoDFA]

theorem lassoDFA_eval (hper : ∀ t, T ≤ t → b (t + P) = b t) (n : ℕ) (y : List Bool) :
    (lassoDFA b T P hP n).eval y =
      if y = prefixOf b y.length then posState T P hP y.length else Fin.last _ := by
  induction y using List.reverseRecOn with
  | nil => simp [DFA.eval_nil, lassoDFA, prefixOf]
  | append_singleton z a ih =>
    rw [DFA.eval_append_singleton, ih, List.length_append, List.length_singleton, prefixOf_succ]
    by_cases hz : z = prefixOf b z.length
    · rw [if_pos hz, lassoDFA_step_pos, b_pos b T P hP hper]
      by_cases ha : a = b z.length
      · rw [if_pos ha, if_pos (by rw [← hz, ha])]
      · rw [if_neg ha, if_neg (fun h => ha (by
          have := List.append_inj' h rfl; simpa using this.2))]
    · rw [if_neg hz, if_neg (show ¬ (z ++ [a] = prefixOf b z.length ++ [b z.length]) from
        fun h => hz (List.append_inj' h rfl).1), lassoDFA_step_last]

theorem lassoDFA_uniquelyAccepts (hper : ∀ t, T ≤ t → b (t + P) = b t) (n : ℕ) :
    UniquelyAccepts (lassoDFA b T P hP n) (prefixOf b n) := by
  have hlen : (prefixOf b n).length = n := by simp [prefixOf]
  refine ⟨?_, fun y hy hacc => ?_⟩
  · rw [DFA.mem_accepts, lassoDFA_eval b T P hP hper, hlen, if_pos rfl]
    rfl
  · rw [hlen] at hy
    rw [DFA.mem_accepts, lassoDFA_eval b T P hP hper, hy] at hacc
    by_contra hne
    rw [if_neg hne] at hacc
    have hlt := pos_lt T P hP n
    simp only [lassoDFA, posState, Set.mem_singleton_iff, Fin.ext_iff, Fin.val_last] at hacc
    omega

end Lasso

/-- **Eventually periodic sequences have prefixes of bounded automatic complexity.** -/
theorem autComplexityLE_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ K, ∀ n, AutComplexityLE ((List.range n).map b) K := by
  obtain ⟨T, P, hP, hper⟩ := h
  exact ⟨T + P + 1, fun n => ⟨lassoDFA b T P hP n, lassoDFA_uniquelyAccepts b T P hP hper n⟩⟩

/-- **A sufficient condition** (catalog [52]): if the automatic complexity of the prefixes of the
center column tends to infinity, Problem 1 holds. -/
theorem problem1_of_automaticComplexity_tendsto_top
    (h : ∀ K : ℕ, ∀ᶠ n in Filter.atTop,
      ¬ AutComplexityLE ((List.range n).map Rule30Prize.center) K) :
    Rule30Prize.Problem1 := by
  intro hep
  obtain ⟨K, hK⟩ := autComplexityLE_of_eventuallyPeriodic hep
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h K)
  exact hN N le_rfl (hK N)

end Rule30Equivalents.Automatic

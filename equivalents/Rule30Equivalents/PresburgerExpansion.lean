import Ruliology.CellularAutomata.Rule30Jen
import Rule30Equivalents.Basic
import Mathlib.ModelTheory.Arithmetic.Presburger.Definability

/-!
# Multiplication in Presburger arithmetic with the black times

Catalog Section 4, the logic rung "Th(ℕ, +, S) is undecidable", in a definable form. Let
`S = {t : c(t) = 1}`. **If multiplication is first-order definable in `(ℕ, 0, 1, +, S)`, with any
parameters, then Problem 1 holds** (`problem1_of_mul_definable`).

* `presburgerS`: the language `(0, 1, +)` of Presburger arithmetic with one unary relation symbol,
  interpreted in `ℕ` as a set `S` (`structS S`).
* `isSemilinearSet_of_definable`: if `S` is semilinear (eventually periodic), every set definable in
  `(ℕ, +, S)` is semilinear. This is Mathlib's induction for Presburger arithmetic
  (`presburger.definable_iff_isSemilinearSet`) with one more atomic case: a term is `k + u ⬝ v`, and
  `{v | k + u ⬝ v ∈ S}` is the preimage of the semilinear set `{x | k + x ∈ S}` under the additive
  map `v ↦ u ⬝ v`.
* The graph of multiplication is not semilinear (Mathlib's `presburger.mul_not_definable`).

If `c` is disjunctive, multiplication is definable in `(ℕ, +, S)` (catalog Section 4,
"Undecidability from disjunctiveness"); that direction is not proved here.
-/

namespace Rule30Equivalents.PresburgerExpansion

open Set FirstOrder Language Ruliology.CellularAutomata

/-- The relation symbols of `(ℕ, +, S)`: one unary relation. -/
inductive RelS : ℕ → Type
  | mem : RelS 1

/-- The language of Presburger arithmetic `(0, 1, +)` with one unary relation symbol. -/
def presburgerS : Language := ⟨presburgerFunc, RelS⟩

/-- `ℕ` as a structure for `(ℕ, +, S)`. -/
@[reducible] def structS (S : Set ℕ) : presburgerS.Structure ℕ where
  funMap {n} f v := Structure.funMap (L := presburger) (show presburgerFunc n from f) v
  RelMap {n} r v := match n, (show RelS n from r) with
    | _, .mem => v 0 ∈ S

variable {α : Type*} {S A : Set ℕ}

lemma term_realize_eq_add_dotProduct [Fintype α] (S : Set ℕ) (t : presburgerS[[A]].Term α) :
    letI := structS S
    ∃ (k : ℕ) (u : α → ℕ), ∀ (v : α → ℕ), t.realize v = k + u ⬝ᵥ v := by
  letI := structS S
  classical
  induction t with simp only [Term.realize]
  | var i =>
    exact ⟨0, Pi.single i 1, by simp⟩
  | @func l f ts ih =>
    cases f with
    | inl f =>
      choose k u ih using ih
      cases f with
      | zero =>
        refine ⟨0, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp
        rfl
      | one =>
        refine ⟨1, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp
        rfl
      | add =>
        refine ⟨k 0 + k 1, u 0 + u 1, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        show (ts 0).realize v + (ts 1).realize v = _
        rw [ih 0, ih 1, add_dotProduct]
        ring
    | inr f =>
      cases l with
      | zero =>
        refine ⟨f, 0, fun v => ?_⟩
        rw [zero_dotProduct, add_zero]
        rfl
      | succ => nomatch f

/-- The preimage of a semilinear set under `v ↦ k + u ⬝ v` is semilinear. -/
lemma isSemilinearSet_setOf_add_dotProduct_mem [Fintype α] (hS : IsSemilinearSet S) (k : ℕ)
    (u : α → ℕ) : IsSemilinearSet {v : α → ℕ | k + u ⬝ᵥ v ∈ S} := by
  have hS' : IsSemilinearSet {x : ℕ | k + x ∈ S} := by
    rw [Nat.isSemilinearSet_iff_ultimately_periodic] at hS ⊢
    obtain ⟨m, p, hp, h⟩ := hS
    exact ⟨m, p, hp, fun x hx => by rw [mem_setOf, mem_setOf, ← add_assoc]; exact h _ (by omega)⟩
  let f : (α → ℕ) →+ ℕ :=
    { toFun := fun v => u ⬝ᵥ v, map_zero' := dotProduct_zero u, map_add' := dotProduct_add u }
  exact hS'.preimage f

variable [Finite α]

lemma isSemilinearSet_boundedFormula_realize (hS : IsSemilinearSet S) {n}
    (φ : presburgerS[[A]].BoundedFormula α n) :
    letI := structS S
    IsSemilinearSet {v : α ⊕ Fin n → ℕ | φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)} := by
  letI := structS S
  haveI := Fintype.ofFinite α
  induction φ with simp only [BoundedFormula.Realize]
  | equal t₁ t₂ =>
    rcases term_realize_eq_add_dotProduct S t₁ with ⟨k₁, u₁, ht₁⟩
    rcases term_realize_eq_add_dotProduct S t₂ with ⟨k₂, u₂, ht₂⟩
    convert! Nat.isSemilinearSet_setOf_mulVec_eq ![k₁] ![k₂] (.of ![u₁]) (.of ![u₂])
    simp [ht₁, ht₂]
  | rel R ts =>
    cases R with
    | inl R =>
      cases R with
      | mem =>
        rcases term_realize_eq_add_dotProduct S (ts 0) with ⟨k, u, ht⟩
        convert! isSemilinearSet_setOf_add_dotProduct_mem hS k u using 1
        ext v
        show (ts 0).realize _ ∈ S ↔ _
        rw [ht, Sum.elim_comp_inl_inr]
        rfl
    | inr R => nomatch R
  | falsum => exact .empty
  | imp _ _ ih₁ ih₂ =>
    convert! (ih₂.compl.inter ih₁).compl using 1
    simp [setOf_inter_eq_sep, imp_iff_not_or, compl_setOf]
  | @all n φ ih =>
    let e := (Equiv.sumAssoc α (Fin n) (Fin 1)).trans (Equiv.sumCongr (.refl α) finSumFinEquiv)
    rw [← isSemilinearSet_image_iff (LinearEquiv.funCongrLeft ℕ ℕ e)] at ih
    convert! ih.compl.proj.compl using 1
    simp_rw [compl_setOf, not_exists, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi,
      mem_compl_iff, mem_image, not_not, ← LinearEquiv.eq_symm_apply, LinearEquiv.funCongrLeft_symm,
      exists_eq_right, mem_setOf, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr! 4
    ext i
    cases i using Fin.lastCases <;> simp [e]

/-- **Definable in `(ℕ, +, S)` with `S` semilinear ⟹ semilinear.** -/
theorem isSemilinearSet_of_definable (hS : IsSemilinearSet S) {s : Set (α → ℕ)}
    (h : letI := structS S; A.Definable presburgerS s) : IsSemilinearSet s := by
  letI := structS S
  obtain ⟨φ, rfl⟩ := h
  let e := Equiv.sumEmpty α (Fin 0)
  convert! (isSemilinearSet_boundedFormula_realize hS φ).image (LinearMap.funLeft ℕ ℕ e.symm)
  ext x
  simp only [mem_setOf_eq, mem_image]
  rw [(e.arrowCongr (.refl ℕ)).exists_congr_left]
  simp [Formula.Realize, Unique.eq_default, Function.comp_def, LinearMap.funLeft, e]

/-- An eventually periodic set of naturals is semilinear. -/
theorem isSemilinearSet_of_eventuallyPeriodic {b : ℕ → Bool} (hb : EventuallyPeriodic b) :
    IsSemilinearSet {t | b t = true} := by
  obtain ⟨T, P, hP, hper⟩ := hb
  rw [Nat.isSemilinearSet_iff_ultimately_periodic]
  exact ⟨T, P, hP, fun x hx => by rw [mem_setOf, mem_setOf, hper x hx]⟩

/-- **Multiplication is not definable from an eventually periodic set.** -/
theorem mul_not_definable_of_eventuallyPeriodic {b : ℕ → Bool} (hb : EventuallyPeriodic b) :
    letI := structS {t | b t = true}
    ¬ A.Definable presburgerS {v : Fin 3 → ℕ | v 0 = v 1 * v 2} := fun h =>
  presburger.mul_not_definable (A := ∅) (presburger.definable_iff_isSemilinearSet.2
    (isSemilinearSet_of_definable (isSemilinearSet_of_eventuallyPeriodic hb) h))

/-- **Multiplication definable in `(ℕ, +, S)` ⟹ Problem 1**, for `S` the black times of the center
column, with any parameters `A`. -/
theorem problem1_of_mul_definable
    (h : letI := structS {t | c t = true}
      A.Definable presburgerS {v : Fin 3 → ℕ | v 0 = v 1 * v 2}) :
    Rule30Prize.Problem1 := fun hep => mul_not_definable_of_eventuallyPeriodic hep h

end Rule30Equivalents.PresburgerExpansion

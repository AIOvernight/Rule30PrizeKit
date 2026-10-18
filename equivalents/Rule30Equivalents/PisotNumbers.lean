import Rule30Equivalents.ShiftOrbit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Problem 1 in every Pisot base `β > 2`

Catalog entry [48]. Read the center column as the digits of `x_β = ∑ c(t) β^-(t+1)`. **For every
Pisot number `β > 2`, Problem 1 holds iff `x_β ∉ ℚ(β)`** (`problem1_iff_not_mem_adjoin`); more
generally, a `Bool` sequence is eventually periodic iff its value in base `β` lies in `ℚ(β)`
(`eventuallyPeriodic_iff_mem_adjoin`). A Pisot number is a real algebraic integer `β > 1` whose
other conjugates lie in the open unit disk (`IsPisot`).

**Expansions in a base `β > 2`.** Write `x_t` for the value of the tail `b(t), b(t + 1), …`. Then
`x_{t+1} = β x_t - b(t)` (`tailValue_succ`), and `0 ≤ x_t ≤ 1/(β - 1) < 1`, so the digit `b(t)` is
`1` exactly when `β x_t ≥ 1` (`digit_iff`): the digits are the greedy β-expansion of `x_β`, and
finitely many tail values make `b` eventually periodic (`eventuallyPeriodic_of_finite_tails`).

**Proof** (Bertrand, Schmidt).
* If `b` is eventually periodic, the geometric series puts `x_β` in every field that contains `β`
  (`mem_of_eventuallyPeriodic`).
* If `x_β ∈ K = ℚ(β)`, a number field, then `q x_β` is an algebraic integer for some integer
  `q ≠ 0`, and so is every `q x_t = βᵗ (q x_β) - q (b(0) β^(t-1) + ⋯ + b(t-1))`. An embedding
  `φ : K → ℂ` sends `β` to a conjugate: either `β` itself, and then `φ` is the inclusion and
  `φ(q x_t) = q x_t ∈ [0, q]`; or a conjugate `γ` with `‖γ‖ < 1`, and then
  `‖φ(q x_t)‖ ≤ q (‖φ x_β‖ + 1 / (1 - ‖γ‖))`. Algebraic integers of `K` with all conjugates bounded
  form a finite set (Mathlib's `NumberField.Embeddings.finite_of_norm_le`), so the `x_t` take
  finitely many values.

Sources: K. Schmidt, *On periodic expansions of Pisot numbers and Salem numbers*, Bull. London
Math. Soc. 12 (1980) 269–278; A. Bertrand, *Développements en base de Pisot et répartition
modulo 1*, C. R. Acad. Sci. Paris 285 (1977) 419–421.
-/

namespace Rule30Equivalents.PisotNumbers

open Ruliology.CellularAutomata

/-! ### Expansions in a base `β > 2` -/

/-- The value of the digits `b` in base `β`. -/
noncomputable def value (β : ℝ) (b : ℕ → Bool) : ℝ :=
  ∑' t, (if b t then (1 : ℝ) else 0) / β ^ (t + 1)

/-- The tail of `b` from `t`. -/
def tail (b : ℕ → Bool) (t : ℕ) : ℕ → Bool := fun s => b (s + t)

/-- The first `t` digits as an element of a semiring: `lead x b (t + 1) = x · lead x b t + b(t)`. -/
def lead {R : Type*} [Semiring R] (x : R) (b : ℕ → Bool) : ℕ → R
  | 0 => 0
  | t + 1 => x * lead x b t + (if b t then 1 else 0)

theorem map_lead {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (x : R) (b : ℕ → Bool) :
    ∀ t, f (lead x b t) = lead (f x) b t
  | 0 => map_zero f
  | t + 1 => by
    rw [lead, lead, map_add, map_mul, map_lead f x b t]
    split_ifs <;> simp

variable {β : ℝ}

section Base

variable (hβ : 2 < β)
include hβ

theorem β_pos : (0 : ℝ) < β := by linarith

theorem term_le (b : ℕ → Bool) (t : ℕ) :
    (if b t then (1 : ℝ) else 0) / β ^ (t + 1) ≤ (β⁻¹) ^ (t + 1) := by
  rw [inv_pow, ← one_div]
  have : (0 : ℝ) < β ^ (t + 1) := pow_pos (β_pos hβ) _
  split_ifs
  · exact le_refl _
  · rw [zero_div]; positivity

theorem term_nonneg (b : ℕ → Bool) (t : ℕ) :
    0 ≤ (if b t then (1 : ℝ) else 0) / β ^ (t + 1) := by
  have : (0 : ℝ) < β ^ (t + 1) := pow_pos (β_pos hβ) _
  split_ifs <;> positivity

theorem summable_geom : Summable fun t : ℕ => (β⁻¹) ^ (t + 1) := by
  have h : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  exact (summable_geometric_of_lt_one (inv_nonneg.2 (β_pos hβ).le) h).comp_injective
    (add_left_injective 1)

theorem summable_term (b : ℕ → Bool) :
    Summable fun t => (if b t then (1 : ℝ) else 0) / β ^ (t + 1) :=
  Summable.of_nonneg_of_le (term_nonneg hβ b) (term_le hβ b) (summable_geom hβ)

theorem value_nonneg (b : ℕ → Bool) : 0 ≤ value β b := tsum_nonneg (term_nonneg hβ b)

/-- `∑ β^-(t+1) = 1 / (β - 1)`. -/
theorem tsum_geom : ∑' t : ℕ, (β⁻¹) ^ (t + 1) = 1 / (β - 1) := by
  have h : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hs := tsum_geometric_of_lt_one (inv_nonneg.2 (β_pos hβ).le) h
  have : ∑' t : ℕ, (β⁻¹) ^ (t + 1) = β⁻¹ * ∑' t : ℕ, (β⁻¹) ^ t := by
    rw [← tsum_mul_left]; congr 1; funext t; ring
  rw [this, hs]
  have hb : β ≠ 0 := (β_pos hβ).ne'
  have h1 : β - 1 ≠ 0 := by linarith
  have h2 : 1 - β⁻¹ ≠ 0 := by
    have : β⁻¹ < 1 := h
    linarith
  field_simp

theorem value_le (b : ℕ → Bool) : value β b ≤ 1 / (β - 1) := by
  rw [← tsum_geom hβ]
  exact (summable_term hβ b).tsum_le_tsum (term_le hβ b) (summable_geom hβ)

theorem value_lt_one (b : ℕ → Bool) : value β b < 1 := by
  have h := value_le hβ b
  have h2 : 1 / (β - 1) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  linarith

/-- Peeling off the first digit: `β x = b(0) + x(tail)`. -/
theorem mul_value (b : ℕ → Bool) :
    β * value β b = (if b 0 then 1 else 0) + value β (tail b 1) := by
  have hb : β ≠ 0 := (β_pos hβ).ne'
  have e : value β (tail b 1) = ∑' n, (if b (n + 1) then (1 : ℝ) else 0) / β ^ (n + 1) := rfl
  rw [e, value, (summable_term hβ b).tsum_eq_zero_add]
  have h : ∀ n : ℕ, (if b (n + 1) then (1 : ℝ) else 0) / β ^ (n + 1 + 1) =
      β⁻¹ * ((if b (n + 1) then (1 : ℝ) else 0) / β ^ (n + 1)) := by
    intro n; rw [pow_succ]; field_simp
  simp only [h, tsum_mul_left]
  field_simp
  ring

/-- The tail recursion `x_{t+1} = β x_t - b(t)`. -/
theorem tailValue_succ (b : ℕ → Bool) (t : ℕ) :
    value β (tail b (t + 1)) = β * value β (tail b t) - (if b t then 1 else 0) := by
  have h1 := mul_value hβ (tail b t)
  have e1 : tail (tail b t) 1 = tail b (t + 1) := by
    funext s; simp only [tail]; rw [show s + 1 + t = s + (t + 1) by omega]
  have e2 : tail b t 0 = b t := by simp [tail]
  rw [e1, e2] at h1
  linarith

/-- **The greedy digit**: `b(t) = 1` iff `β x_t ≥ 1`. -/
theorem digit_iff (b : ℕ → Bool) (t : ℕ) : b t = true ↔ 1 ≤ β * value β (tail b t) := by
  have h1 := tailValue_succ hβ b t
  have h2 := value_nonneg hβ (tail b (t + 1))
  have h3 := value_lt_one hβ (tail b (t + 1))
  constructor
  · intro h; rw [h] at h1; simp at h1; linarith
  · intro h
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rw [hne] at h1; simp at h1; linarith

/-- Shifting by `t` digits: `βᵗ x = lead_t + x_t`. -/
theorem pow_mul_value (b : ℕ → Bool) : ∀ t, β ^ t * value β b = lead β b t + value β (tail b t)
  | 0 => by simp only [pow_zero, one_mul, lead, zero_add]; rfl
  | t + 1 => by
    rw [pow_succ, mul_comm (β ^ t) β, mul_assoc, pow_mul_value b t, mul_add,
      tailValue_succ hβ b t, lead]
    ring

/-- **The periodic direction.** An eventually periodic digit sequence has its value in every
subfield of `ℝ` that contains `β`. -/
theorem mem_of_eventuallyPeriodic (F : Subfield ℝ) (hF : β ∈ F) {b : ℕ → Bool}
    (h : EventuallyPeriodic b) : value β b ∈ F := by
  obtain ⟨T, P, hP, hper⟩ := h
  have hlead : ∀ (b' : ℕ → Bool) t, lead β b' t ∈ F := fun b' t => by
    induction t with
    | zero => exact F.zero_mem
    | succ t ih =>
      exact F.add_mem (F.mul_mem hF ih) (by split_ifs; exacts [F.one_mem, F.zero_mem])
  have htail : tail (tail b T) P = tail b T := by
    funext s; simp only [tail]; rw [show s + P + T = s + T + P by omega]; exact hper _ (by omega)
  have e1 := pow_mul_value hβ (tail b T) P
  rw [htail] at e1
  have e2 := pow_mul_value hβ b T
  have hβP : (1 : ℝ) < β ^ P := one_lt_pow₀ (by linarith) hP.ne'
  have hβT : (0 : ℝ) < β ^ T := pow_pos (β_pos hβ) T
  have hx : value β (tail b T) = lead β (tail b T) P / (β ^ P - 1) := by
    rw [eq_div_iff (by linarith)]; linarith
  have hv : value β b = (lead β b T + value β (tail b T)) / β ^ T := by
    rw [eq_div_iff hβT.ne']; linarith
  rw [hv, hx]
  exact F.div_mem (F.add_mem (hlead b T)
    (F.div_mem (hlead _ P) (F.sub_mem (F.pow_mem hF P) F.one_mem))) (F.pow_mem hF T)

/-- **Finitely many tail values give eventual periodicity**: the digit is read off the tail value,
and the next tail value is determined by it. -/
theorem eventuallyPeriodic_of_finite_tails {b : ℕ → Bool}
    (hfin : (Set.range fun t => value β (tail b t)).Finite) : EventuallyPeriodic b := by
  obtain ⟨s, t, hst, heq⟩ : ∃ s t, s < t ∧ value β (tail b s) = value β (tail b t) := by
    by_contra hne
    push Not at hne
    refine Set.infinite_range_of_injective (fun s t he => ?_) hfin
    rcases lt_trichotomy s t with h | h | h
    · exact absurd he (hne s t h)
    · exact h
    · exact absurd he.symm (hne t s h)
  have key : ∀ j, value β (tail b (s + j)) = value β (tail b (t + j)) := by
    intro j
    induction j with
    | zero => exact heq
    | succ j ih =>
      have hd : b (s + j) = b (t + j) := by
        rw [Bool.eq_iff_iff, digit_iff hβ, digit_iff hβ, ih]
      rw [← add_assoc, ← add_assoc, tailValue_succ hβ, tailValue_succ hβ, ih, hd]
  refine ShiftOrbit.eventuallyPeriodic_of_shift_eq hst fun j => ?_
  rw [Bool.eq_iff_iff, digit_iff hβ, digit_iff hβ, key]

end Base

/-! ### Pisot numbers -/

/-- A Pisot number: a real algebraic integer `β > 1` whose other conjugates, the other complex
roots of its minimal polynomial, lie in the open unit disk. -/
def IsPisot (β : ℝ) : Prop :=
  IsIntegral ℤ β ∧ 1 < β ∧
    ∀ z : ℂ, Polynomial.aeval z (minpoly ℤ β) = 0 → z ≠ (β : ℂ) → ‖z‖ < 1

/-- **The lattice direction** (Bertrand, Schmidt). If `β > 2` is a Pisot number and the value of
`b` lies in `ℚ(β)`, then `b` is eventually periodic. -/
theorem eventuallyPeriodic_of_mem_adjoin (hP : IsPisot β) (hβ : 2 < β) {b : ℕ → Bool}
    (h : value β b ∈ IntermediateField.adjoin ℚ ({β} : Set ℝ)) : EventuallyPeriodic b := by
  classical
  set K := IntermediateField.adjoin ℚ ({β} : Set ℝ)
  haveI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hP.1.tower_top
  haveI : NumberField K := ⟨⟩
  set βK : K := IntermediateField.AdjoinSimple.gen ℚ β
  set xK : K := ⟨value β b, h⟩
  have hval : ∀ y : K, (K.val : K →+* ℝ) y = y := fun _ => rfl
  -- the tails as elements of `K`
  set xt : ℕ → K := fun t => βK ^ t * xK - lead βK b t
  have hxt : ∀ t, ((xt t : K) : ℝ) = value β (tail b t) := fun t => by
    have e := pow_mul_value hβ b t
    have hl := map_lead (K.val : K →+* ℝ) βK b t
    rw [hval, hval] at hl
    show ((βK ^ t * xK - lead βK b t : K) : ℝ) = _
    push_cast
    rw [hl]
    show β ^ t * value β b - lead β b t = _
    linarith
  -- an integer multiple of `x_β` is an algebraic integer
  obtain ⟨q, hq0, hqint⟩ := exists_integral_multiples ℤ ℚ (L := K) {xK}
  have hqx : IsIntegral ℤ ((q : K) * xK) := by
    have := hqint xK (Finset.mem_singleton_self _)
    rwa [zsmul_eq_mul] at this
  have hβint : IsIntegral ℤ βK := by
    have hinj : Function.Injective ((K.val : K →+* ℝ).toIntAlgHom) := Subtype.val_injective
    exact (isIntegral_algHom_iff _ hinj).1 hP.1
  have hqK : IsIntegral ℤ ((q : ℤ) : K) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K q))
  have hleadint : ∀ t, IsIntegral ℤ (lead βK b t) := fun t => by
    induction t with
    | zero => exact isIntegral_zero
    | succ t ih =>
      refine (hβint.mul ih).add ?_
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
  have hint : ∀ t, IsIntegral ℤ ((q : K) * xt t) := fun t => by
    have e : (q : K) * xt t = βK ^ t * ((q : K) * xK) - (q : K) * lead βK b t := by
      simp only [xt]; ring
    rw [e]
    exact ((hβint.pow t).mul hqx).sub (hqK.mul (hleadint t))
  -- the embeddings of `K`: the inclusion, or a conjugate inside the unit disk
  have hroot : ∀ φ : K →+* ℂ, φ βK = (β : ℂ) ∨ ‖φ βK‖ < 1 := by
    intro φ
    have h0 : Polynomial.aeval βK (minpoly ℤ β) = 0 := by
      apply Subtype.val_injective
      have := Polynomial.aeval_algHom_apply ((K.val : K →+* ℝ).toIntAlgHom) βK (minpoly ℤ β)
      rw [show ((K.val : K →+* ℝ).toIntAlgHom) βK = β from rfl, minpoly.aeval] at this
      exact this.symm
    have h1 : Polynomial.aeval (φ βK) (minpoly ℤ β) = 0 := by
      rw [show φ βK = φ.toIntAlgHom βK from rfl, Polynomial.aeval_algHom_apply, h0, map_zero]
    by_cases hb : φ βK = (β : ℂ)
    · exact Or.inl hb
    · exact Or.inr (hP.2.2 _ h1 hb)
  have hreal : ∀ φ : K →+* ℂ, φ βK = (β : ℂ) → ∀ y : K, φ y = ((y : ℝ) : ℂ) := by
    intro φ hφ y
    have := IntermediateField.adjoin_algHom_ext ℚ (φ₁ := φ.toRatAlgHom)
      (φ₂ := (Complex.ofRealHom.comp (K.val : K →+* ℝ)).toRatAlgHom) fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hφ
    exact DFunLike.congr_fun this y
  -- a uniform bound on the conjugates of `q x_t`
  set B : ℝ := |(q : ℝ)| * (1 + ∑ φ : K →+* ℂ,
    (‖φ xK‖ + if ‖φ βK‖ < 1 then 1 / (1 - ‖φ βK‖) else 0))
  have hterm : ∀ φ : K →+* ℂ, 0 ≤ ‖φ xK‖ + if ‖φ βK‖ < 1 then 1 / (1 - ‖φ βK‖) else 0 :=
    fun φ => add_nonneg (norm_nonneg _) (by split_ifs with h1 <;> [exact (one_div_pos.2
      (by linarith)).le; exact le_rfl])
  have hbound : ∀ t (φ : K →+* ℂ), ‖φ ((q : K) * xt t)‖ ≤ B := by
    intro t φ
    rw [map_mul, norm_mul, map_intCast, Complex.norm_intCast]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hsum : ‖φ xK‖ + (if ‖φ βK‖ < 1 then 1 / (1 - ‖φ βK‖) else 0) ≤
        ∑ φ' : K →+* ℂ, (‖φ' xK‖ + if ‖φ' βK‖ < 1 then 1 / (1 - ‖φ' βK‖) else 0) :=
      Finset.single_le_sum (fun φ' _ => hterm φ') (Finset.mem_univ φ)
    rcases hroot φ with hb | hb
    · rw [hreal φ hb, Complex.norm_real, Real.norm_eq_abs, hxt,
        abs_of_nonneg (value_nonneg hβ _)]
      have := value_lt_one hβ (tail b t)
      linarith [hterm φ]
    · rw [if_pos hb] at hsum
      -- `φ(x_t) = γᵗ φ(x_β) - lead γ`
      have e : φ (xt t) = φ βK ^ t * φ xK - lead (φ βK) b t := by
        simp only [xt, map_sub, map_mul, map_pow, map_lead]
      have hγ : 0 ≤ ‖φ βK‖ := norm_nonneg _
      have hne : 1 - ‖φ βK‖ ≠ 0 := by linarith
      have hlead : ∀ s, ‖lead (φ βK) b s‖ ≤ 1 / (1 - ‖φ βK‖) := by
        intro s
        induction s with
        | zero => simp only [lead, norm_zero]; exact (one_div_pos.2 (by linarith)).le
        | succ s ih =>
          rw [lead]
          calc ‖φ βK * lead (φ βK) b s + (if b s then 1 else 0)‖
              ≤ ‖φ βK‖ * ‖lead (φ βK) b s‖ + 1 := by
                refine (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) ?_)
                split_ifs <;> simp
            _ ≤ ‖φ βK‖ * (1 / (1 - ‖φ βK‖)) + 1 := by gcongr
            _ = 1 / (1 - ‖φ βK‖) := by field_simp; ring
      calc ‖φ (xt t)‖ ≤ ‖φ βK‖ ^ t * ‖φ xK‖ + 1 / (1 - ‖φ βK‖) := by
            rw [e]
            refine (norm_sub_le _ _).trans (add_le_add ?_ (hlead t))
            rw [norm_mul, norm_pow]
        _ ≤ ‖φ xK‖ + 1 / (1 - ‖φ βK‖) := by
            have : ‖φ βK‖ ^ t ≤ 1 := pow_le_one₀ hγ hb.le
            nlinarith [norm_nonneg (φ xK)]
        _ ≤ 1 + ∑ φ' : K →+* ℂ, (‖φ' xK‖ + if ‖φ' βK‖ < 1 then 1 / (1 - ‖φ' βK‖) else 0) := by
            linarith
  -- so the tails take finitely many values
  have hfinK : (Set.range fun t => (q : K) * xt t).Finite :=
    (NumberField.Embeddings.finite_of_norm_le K ℂ B).subset (by
      rintro _ ⟨t, rfl⟩
      exact ⟨hint t, hbound t⟩)
  have hq : (q : K) ≠ 0 := by exact_mod_cast hq0
  have hfin : (Set.range fun t => value β (tail b t)).Finite := by
    have := (hfinK.image fun y => (((q : K)⁻¹ * y : K) : ℝ))
    refine this.subset ?_
    rintro _ ⟨t, rfl⟩
    refine ⟨(q : K) * xt t, ⟨t, rfl⟩, ?_⟩
    show (((q : K)⁻¹ * ((q : K) * xt t) : K) : ℝ) = value β (tail b t)
    rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul, hxt]
  exact eventuallyPeriodic_of_finite_tails hβ hfin

/-- **Schmidt's theorem for `0/1` digits.** For a Pisot number `β > 2`, a `Bool` sequence is
eventually periodic iff its value in base `β` lies in `ℚ(β)`. -/
theorem eventuallyPeriodic_iff_mem_adjoin (hP : IsPisot β) (hβ : 2 < β) (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ value β b ∈ IntermediateField.adjoin ℚ ({β} : Set ℝ) :=
  ⟨fun h => mem_of_eventuallyPeriodic hβ (IntermediateField.adjoin ℚ ({β} : Set ℝ)).toSubfield
      (IntermediateField.mem_adjoin_simple_self ℚ β) h,
    eventuallyPeriodic_of_mem_adjoin hP hβ⟩

/-- **[48] for every Pisot number `β > 2`.** Problem 1 holds iff `x_β = ∑ c(t) β^-(t+1)` does not
lie in `ℚ(β)`. -/
theorem problem1_iff_not_mem_adjoin (hP : IsPisot β) (hβ : 2 < β) :
    Rule30Prize.Problem1 ↔ value β c ∉ IntermediateField.adjoin ℚ ({β} : Set ℝ) :=
  not_congr (eventuallyPeriodic_iff_mem_adjoin hP hβ c)

end Rule30Equivalents.PisotNumbers

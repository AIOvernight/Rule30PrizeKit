import Rule30Equivalents.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Preorder.Finite

/-!
# Problem 1 in the Pisot base `1 + √2`

Read the center column as the digits of `x_β = ∑ c(t) β^-(t+1)` with `β = 1 + √2`, the Pisot number
whose conjugate is `1 - √2`.

* `problem1_iff_not_mem_Q_sqrt_two` (catalog [48]): Problem 1 holds iff `x_β` is not of the form
  `a + b √2` with `a, b` rational, that is, `x_β ∉ ℚ(√2)`.
* In general, `eventuallyPeriodic_iff_mem_qsqrt2`: a `Bool` sequence is eventually periodic iff its
  value in base `1 + √2` lies in `ℚ(√2)`.

**Proof.** Write `x_t` for the value of the tail `b(t), b(t + 1), …`. Then `x_{t+1} = β x_t - b(t)`
(`tailValue_succ`), and `0 ≤ x_t ≤ 1/√2 < 1` because `β > 2`, so the digit `b(t)` is `1` exactly when
`β x_t ≥ 1` (`digit_iff`): the digits are the greedy β-expansion of `x_β`.
* If `b` is eventually periodic, the geometric series puts `x_β` in the field `ℚ(√2)` (`qsqrt2`).
* If `x_β = a + b√2`, choose `q > 0` with `q a, q b` integers. By induction `q x_t = U_t + V_t √2`
  with integers `U_t, V_t` (`uv`), and the conjugates `Y_t = U_t - V_t √2` satisfy
  `Y_{t+1} = (1 - √2) Y_t - q b(t)`. Since `|1 - √2| < 1/2`, the `Y_t` stay bounded, and so do the
  `x_t`; so `(U_t, V_t)` takes finitely many values, two tails coincide, and the digits repeat.
This is Schmidt's argument (every element of `ℚ(β) ∩ [0, 1)` has an eventually periodic greedy
β-expansion when `β` is Pisot), specialized to `β = 1 + √2` with explicit coordinates.

Sources: K. Schmidt, *On periodic expansions of Pisot numbers and Salem numbers*, Bull. London
Math. Soc. 12 (1980) 269–278; A. Bertrand, *Développements en base de Pisot et répartition modulo 1*,
C. R. Acad. Sci. Paris 285 (1977) 419–421. Catalog entry [48].
-/

namespace Rule30Equivalents.PisotBase

open Ruliology.CellularAutomata

/-- The base `β = 1 + √2`. -/
noncomputable abbrev β : ℝ := 1 + Real.sqrt 2

theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt2_gt : (1.4 : ℝ) < Real.sqrt 2 := by
  rw [show (1.4 : ℝ) = Real.sqrt (1.4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt2_lt : Real.sqrt 2 < 1.5 := by
  rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem two_lt_β : (2 : ℝ) < β := by have := sqrt2_gt; simp only [β]; linarith

theorem β_pos : (0 : ℝ) < β := by linarith [two_lt_β]

/-- The value of the digits `b` in base `β`. -/
noncomputable def value (b : ℕ → Bool) : ℝ := ∑' t, (if b t then (1 : ℝ) else 0) / β ^ (t + 1)

/-- The tail of `b` from `t`. -/
def tail (b : ℕ → Bool) (t : ℕ) : ℕ → Bool := fun s => b (s + t)

theorem term_le (b : ℕ → Bool) (t : ℕ) :
    (if b t then (1 : ℝ) else 0) / β ^ (t + 1) ≤ (β⁻¹) ^ (t + 1) := by
  rw [inv_pow, ← one_div]
  have : (0 : ℝ) < β ^ (t + 1) := pow_pos β_pos _
  split_ifs
  · exact le_refl _
  · rw [zero_div]; positivity

theorem term_nonneg (b : ℕ → Bool) (t : ℕ) : 0 ≤ (if b t then (1 : ℝ) else 0) / β ^ (t + 1) := by
  have : (0 : ℝ) < β ^ (t + 1) := pow_pos β_pos _
  split_ifs <;> positivity

theorem summable_geom : Summable fun t : ℕ => (β⁻¹) ^ (t + 1) := by
  have h : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [two_lt_β])
  exact (summable_geometric_of_lt_one (inv_nonneg.2 β_pos.le) h).comp_injective (add_left_injective 1)

theorem summable_term (b : ℕ → Bool) :
    Summable fun t => (if b t then (1 : ℝ) else 0) / β ^ (t + 1) :=
  Summable.of_nonneg_of_le (term_nonneg b) (term_le b) summable_geom

theorem value_nonneg (b : ℕ → Bool) : 0 ≤ value b := tsum_nonneg (term_nonneg b)

/-- `∑ β^-(t+1) = 1 / (β - 1) = 1 / √2`. -/
theorem tsum_geom : ∑' t : ℕ, (β⁻¹) ^ (t + 1) = 1 / Real.sqrt 2 := by
  have h : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [two_lt_β])
  have hs := tsum_geometric_of_lt_one (inv_nonneg.2 β_pos.le) h
  have : ∑' t : ℕ, (β⁻¹) ^ (t + 1) = β⁻¹ * ∑' t : ℕ, (β⁻¹) ^ t := by
    rw [← tsum_mul_left]; congr 1; funext t; ring
  rw [this, hs]
  have hb : β ≠ 0 := β_pos.ne'
  have h2 : Real.sqrt 2 ≠ 0 := by have := sqrt2_gt; linarith
  field_simp
  ring

theorem value_le (b : ℕ → Bool) : value b ≤ 1 / Real.sqrt 2 := by
  rw [← tsum_geom]
  exact (summable_term b).tsum_le_tsum (term_le b) summable_geom

theorem value_lt_one (b : ℕ → Bool) : value b < 1 := by
  have h := value_le b
  have h2 : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one (by linarith [sqrt2_gt])]; linarith [sqrt2_gt]
  linarith

/-- Peeling off the first digit: `β x = b(0) + x(tail)`. -/
theorem mul_value (b : ℕ → Bool) : β * value b = (if b 0 then 1 else 0) + value (tail b 1) := by
  have hb : β ≠ 0 := β_pos.ne'
  have e : value (tail b 1) = ∑' n, (if b (n + 1) then (1 : ℝ) else 0) / β ^ (n + 1) := rfl
  rw [e, value, (summable_term b).tsum_eq_zero_add]
  have h : ∀ n : ℕ, (if b (n + 1) then (1 : ℝ) else 0) / β ^ (n + 1 + 1) =
      β⁻¹ * ((if b (n + 1) then (1 : ℝ) else 0) / β ^ (n + 1)) := by
    intro n; rw [pow_succ]; field_simp
  simp only [h, tsum_mul_left]
  field_simp
  ring

/-- The tail recursion `x_{t+1} = β x_t - b(t)`. -/
theorem tailValue_succ (b : ℕ → Bool) (t : ℕ) :
    value (tail b (t + 1)) = β * value (tail b t) - (if b t then 1 else 0) := by
  have h1 := mul_value (tail b t)
  have e1 : tail (tail b t) 1 = tail b (t + 1) := by
    funext s; simp only [tail]; rw [show s + 1 + t = s + (t + 1) by omega]
  have e2 : tail b t 0 = b t := by simp [tail]
  rw [e1, e2] at h1
  linarith

/-- **The greedy digit**: `b(t) = 1` iff `β x_t ≥ 1`. -/
theorem digit_iff (b : ℕ → Bool) (t : ℕ) : b t = true ↔ 1 ≤ β * value (tail b t) := by
  have h1 := tailValue_succ b t
  have h2 := value_nonneg (tail b (t + 1))
  have h3 := value_lt_one (tail b (t + 1))
  constructor
  · intro h; rw [h] at h1; simp at h1; linarith
  · intro h
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rw [hne] at h1; simp at h1; linarith

/-! ### The field `ℚ(√2)` and the periodic direction -/

/-- `ℚ(√2)` as a subfield of `ℝ`: the numbers `a + b √2` with `a, b` rational. -/
noncomputable def qsqrt2 : Subfield ℝ where
  carrier := {x | ∃ a b : ℚ, x = a + b * Real.sqrt 2}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c + 2 * b * d, a * d + b * c, ?_⟩
    push_cast
    linear_combination (b : ℝ) * d * sqrt2_sq
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    by_cases h : (a : ℝ) + b * Real.sqrt 2 = 0
    · rw [h, inv_zero]; exact ⟨0, 0, by simp⟩
    · have hprod : ((a : ℝ) + b * Real.sqrt 2) * ((a : ℝ) - b * Real.sqrt 2) =
          ((a ^ 2 - 2 * b ^ 2 : ℚ) : ℝ) := by
        push_cast; linear_combination -(b : ℝ) ^ 2 * sqrt2_sq
      have hy : (a : ℝ) - b * Real.sqrt 2 ≠ 0 := by
        intro h'
        by_cases hb : b = 0
        · subst hb; simp at h h'; exact h h'
        · apply irrational_sqrt_two
          refine ⟨a / b, ?_⟩
          have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
          push_cast
          field_simp
          linarith
      refine ⟨a / (a ^ 2 - 2 * b ^ 2), -b / (a ^ 2 - 2 * b ^ 2), ?_⟩
      rw [show ((a / (a ^ 2 - 2 * b ^ 2) : ℚ) : ℝ) + ((-b / (a ^ 2 - 2 * b ^ 2) : ℚ) : ℝ) *
          Real.sqrt 2 = ((a : ℝ) - b * Real.sqrt 2) / ((a ^ 2 - 2 * b ^ 2 : ℚ) : ℝ) by
        push_cast; ring, ← hprod]
      field_simp

theorem mem_qsqrt2 {x : ℝ} : x ∈ qsqrt2 ↔ ∃ a b : ℚ, x = a + b * Real.sqrt 2 := Iff.rfl

theorem β_mem : β ∈ qsqrt2 := ⟨1, 1, by simp⟩

/-- The first `t` digits as a number: `lead b (t + 1) = β · lead b t + b(t)`. -/
noncomputable def lead (b : ℕ → Bool) : ℕ → ℝ
  | 0 => 0
  | t + 1 => β * lead b t + (if b t then 1 else 0)

theorem lead_mem (b : ℕ → Bool) : ∀ t, lead b t ∈ qsqrt2
  | 0 => qsqrt2.zero_mem
  | t + 1 => qsqrt2.add_mem (qsqrt2.mul_mem β_mem (lead_mem b t))
      (by split_ifs; exacts [qsqrt2.one_mem, qsqrt2.zero_mem])

/-- Shifting by `t` digits: `β^t x = lead_t + x_t`. -/
theorem pow_mul_value (b : ℕ → Bool) : ∀ t, β ^ t * value b = lead b t + value (tail b t)
  | 0 => by simp only [pow_zero, one_mul, lead, zero_add]; rfl
  | t + 1 => by
    rw [pow_succ, mul_comm (β ^ t) β, mul_assoc, pow_mul_value b t, mul_add,
      tailValue_succ b t, lead]
    ring

/-- **(⇐)** An eventually periodic digit sequence has its value in `ℚ(√2)`. -/
theorem mem_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) : value b ∈ qsqrt2 := by
  obtain ⟨T, P, hP, hper⟩ := h
  have htail : tail (tail b T) P = tail b T := by
    funext s; simp only [tail]; rw [show s + P + T = s + T + P by omega]; exact hper _ (by omega)
  have e1 := pow_mul_value (tail b T) P
  rw [htail] at e1
  have e2 := pow_mul_value b T
  have hβP : (1 : ℝ) < β ^ P := one_lt_pow₀ (by linarith [two_lt_β]) hP.ne'
  have hβT : (0 : ℝ) < β ^ T := pow_pos β_pos T
  have hx : value (tail b T) = lead (tail b T) P / (β ^ P - 1) := by
    rw [eq_div_iff (by linarith)]; linarith
  have hv : value b = (lead b T + value (tail b T)) / β ^ T := by
    rw [eq_div_iff hβT.ne']; linarith
  rw [hv, hx]
  exact qsqrt2.div_mem (qsqrt2.add_mem (lead_mem b T)
    (qsqrt2.div_mem (lead_mem _ P) (qsqrt2.sub_mem (qsqrt2.pow_mem β_mem P) qsqrt2.one_mem)))
    (qsqrt2.pow_mem β_mem T)

/-! ### The lattice direction -/

/-- Integer coordinates `(U_t, V_t)` with `q x_t = U_t + V_t √2`. -/
def uv (A B q : ℤ) (b : ℕ → Bool) : ℕ → ℤ × ℤ
  | 0 => (A, B)
  | t + 1 => ((uv A B q b t).1 + 2 * (uv A B q b t).2 - q * (if b t then 1 else 0),
      (uv A B q b t).1 + (uv A B q b t).2)

theorem uv_value {b : ℕ → Bool} {A B q : ℤ} (h0 : (q : ℝ) * value b = A + B * Real.sqrt 2) :
    ∀ t, (q : ℝ) * value (tail b t) = (uv A B q b t).1 + (uv A B q b t).2 * Real.sqrt 2
  | 0 => by show (q : ℝ) * value b = _; simpa [uv] using h0
  | t + 1 => by
    have ih := uv_value h0 t
    have e : (q : ℝ) * value (tail b (t + 1)) =
        β * ((q : ℝ) * value (tail b t)) - q * (if b t then 1 else 0) := by
      rw [tailValue_succ]; ring
    rw [e, ih]
    simp only [uv]
    push_cast
    linear_combination ((uv A B q b t).2 : ℝ) * sqrt2_sq

/-- The conjugate `Y_t = U_t - V_t √2`. -/
noncomputable def conj (A B q : ℤ) (b : ℕ → Bool) (t : ℕ) : ℝ :=
  (uv A B q b t).1 - (uv A B q b t).2 * Real.sqrt 2

theorem conj_succ (A B q : ℤ) (b : ℕ → Bool) (t : ℕ) :
    conj A B q b (t + 1) = (1 - Real.sqrt 2) * conj A B q b t - q * (if b t then 1 else 0) := by
  simp only [conj, uv]
  push_cast
  linear_combination -((uv A B q b t).2 : ℝ) * sqrt2_sq

/-- The conjugates stay bounded, because `|1 - √2| < 1/2`. -/
theorem conj_bound (A B q : ℤ) (hq : 0 ≤ q) (b : ℕ → Bool) :
    ∀ t, |conj A B q b t| ≤ |conj A B q b 0| + 2 * q
  | 0 => by have : (0 : ℝ) ≤ q := by exact_mod_cast hq
            linarith
  | t + 1 => by
    have ih := conj_bound A B q hq b t
    have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    have hs : |1 - Real.sqrt 2| ≤ 1 / 2 := by
      rw [abs_sub_comm, abs_of_pos (by linarith [sqrt2_gt])]; linarith [sqrt2_lt]
    have hd : |(q : ℝ) * (if b t then 1 else 0)| ≤ q := by
      split_ifs
      · rw [mul_one, abs_of_nonneg hq']
      · rw [mul_zero, abs_zero]; exact hq'
    rw [conj_succ]
    calc |(1 - Real.sqrt 2) * conj A B q b t - q * (if b t then 1 else 0)|
        ≤ |1 - Real.sqrt 2| * |conj A B q b t| + |(q : ℝ) * (if b t then 1 else 0)| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 1 / 2 * (|conj A B q b 0| + 2 * q) + q := by
          gcongr
      _ ≤ |conj A B q b 0| + 2 * q := by linarith [abs_nonneg (conj A B q b 0)]

/-- **(⇒)** A value in `ℚ(√2)` forces an eventually periodic digit sequence. -/
theorem eventuallyPeriodic_of_mem {b : ℕ → Bool} (h : value b ∈ qsqrt2) : EventuallyPeriodic b := by
  obtain ⟨r, s, hrs⟩ := h
  -- clear denominators: `q x = A + B √2`
  let q : ℤ := (r.den * s.den : ℕ)
  let A : ℤ := r.num * s.den
  let B : ℤ := s.num * r.den
  have hq : 0 < q := by positivity
  have h0 : (q : ℝ) * value b = A + B * Real.sqrt 2 := by
    rw [hrs]
    have hr : (r : ℝ) = r.num / r.den := Rat.cast_def r
    have hs : (s : ℝ) = s.num / s.den := Rat.cast_def s
    have hrd : (r.den : ℝ) ≠ 0 := by positivity
    have hsd : (s.den : ℝ) ≠ 0 := by positivity
    rw [hr, hs]
    simp only [q, A, B]
    push_cast
    field_simp
  -- the coordinates live in a finite box
  let M : ℝ := |conj A B q b 0| + 2 * q
  let K : ℤ := ⌈(q : ℝ) + M⌉
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hbox : ∀ t, uv A B q b t ∈
      ((Finset.Icc (-K) K ×ˢ Finset.Icc (-K) K : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    intro t
    have hv := uv_value h0 t
    have hY := conj_bound A B q hq.le b t
    have hx0 := value_nonneg (tail b t)
    have hx1 := value_lt_one (tail b t)
    have hX0 : 0 ≤ (q : ℝ) * value (tail b t) := mul_nonneg hq'.le hx0
    have hX1 : (q : ℝ) * value (tail b t) ≤ q := by nlinarith
    have hYabs := abs_le.1 (hY.trans (le_refl M))
    have hs1 := sqrt2_gt
    have hKR : (q : ℝ) + M ≤ K := Int.le_ceil _
    have hU : |((uv A B q b t).1 : ℝ)| ≤ K := by
      have e : ((uv A B q b t).1 : ℝ) = ((q : ℝ) * value (tail b t) + conj A B q b t) / 2 := by
        rw [hv]; simp only [conj]; ring
      rw [e, abs_le]
      constructor <;> (simp only [conj] at hYabs ⊢; linarith [hYabs.1, hYabs.2])
    have hV : |((uv A B q b t).2 : ℝ)| ≤ K := by
      have e : ((uv A B q b t).2 : ℝ) * (2 * Real.sqrt 2) =
          (q : ℝ) * value (tail b t) - conj A B q b t := by
        rw [hv]; simp only [conj]; ring
      have hV2 : |((uv A B q b t).2 : ℝ)| * (2 * Real.sqrt 2) ≤ (q : ℝ) + M := by
        rw [← abs_of_pos (show (0 : ℝ) < 2 * Real.sqrt 2 by linarith), ← abs_mul, e, abs_le]
        constructor <;> linarith [hYabs.1, hYabs.2]
      nlinarith [abs_nonneg ((uv A B q b t).2 : ℝ)]
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc]
    rw [abs_le] at hU hV
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [skip; skip; skip; skip]
    · exact_mod_cast hU.1
    · exact_mod_cast hU.2
    · exact_mod_cast hV.1
    · exact_mod_cast hV.2
  obtain ⟨t, t', htt', heq⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem (f := uv A B q b) hbox (Finset.finite_toSet _)
  -- two equal tails
  have hxeq : value (tail b t) = value (tail b t') := by
    have e := uv_value h0 t
    rw [heq, ← uv_value h0 t'] at e
    exact mul_left_cancel₀ hq'.ne' e
  have key : ∀ j, value (tail b (t + j)) = value (tail b (t' + j)) ∧ b (t + j) = b (t' + j) := by
    intro j
    induction j with
    | zero =>
      refine ⟨hxeq, ?_⟩
      have h1 := digit_iff b t
      have h2 := digit_iff b t'
      rw [hxeq] at h1
      cases hb : b t <;> cases hb' : b t' <;> simp_all
      all_goals linarith
    | succ j ih =>
      have hv : value (tail b (t + (j + 1))) = value (tail b (t' + (j + 1))) := by
        rw [show t + (j + 1) = (t + j) + 1 by omega, show t' + (j + 1) = (t' + j) + 1 by omega,
          tailValue_succ, tailValue_succ, ih.1, ih.2]
      refine ⟨hv, ?_⟩
      have h1 := digit_iff b (t + (j + 1))
      have h2 := digit_iff b (t' + (j + 1))
      rw [hv] at h1
      cases hb : b (t + (j + 1)) <;> cases hb' : b (t' + (j + 1)) <;> simp_all
      all_goals linarith
  refine ⟨t, t' - t, by omega, fun n hn => ?_⟩
  have := (key (n - t)).2
  rw [show t + (n - t) = n by omega, show t' + (n - t) = n + (t' - t) by omega] at this
  exact this.symm

/-- **A digit sequence is eventually periodic iff its value in base `1 + √2` lies in `ℚ(√2)`.** -/
theorem eventuallyPeriodic_iff_mem_qsqrt2 (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ value b ∈ qsqrt2 :=
  ⟨mem_of_eventuallyPeriodic, eventuallyPeriodic_of_mem⟩

/-- **Problem 1 ⟺ `x_β ∉ ℚ(√2)` for `β = 1 + √2`** (catalog [48]). -/
theorem problem1_iff_not_mem_Q_sqrt_two : Rule30Prize.Problem1 ↔
    ¬ ∃ a b : ℚ, ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / (1 + Real.sqrt 2) ^ (t + 1) =
      a + b * Real.sqrt 2 :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_iff_mem_qsqrt2 c))

end Rule30Equivalents.PisotBase

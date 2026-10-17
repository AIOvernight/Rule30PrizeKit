import Rule30Equivalents.BinaryIrrational

/-!
# Problem 1 through the Engel and Sylvester expansions of `x₂`

`x₂ = 0.c(0)c(1)c(2)…` in base 2 (`BinaryIrrational.centerBinary`).

* **Engel.** `engelRem x` is the sequence of remainders of the Engel expansion
  `x = 1/a₁ + 1/(a₁a₂) + 1/(a₁a₂a₃) + ⋯`: a nonzero remainder `r` is followed by `⌈1/r⌉ r - 1`.
  `irrational_iff_engelRem_ne_zero`: for `x ≥ 0`, the expansion is infinite exactly when `x` is
  irrational. `problem1_iff_engel_infinite` (catalog [50]): Problem 1 holds iff the Engel expansion
  of `x₂` is infinite.
* **Sylvester.** `sylvesterRem x` is the sequence of remainders of the greedy Egyptian-fraction
  expansion: a nonzero remainder `r` is followed by `r - 1/⌈1/r⌉`.
  `problem1_iff_sylvester_infinite`: Problem 1 holds iff the Sylvester expansion of `x₂` is
  infinite.

**Proof.** For a rational remainder `m / d` with `m > 0`, let `a = ⌈d / m⌉`. Then
`d ≤ a m < d + m`, so the next remainder is `(a m - d) / d` (Engel) or `(a m - d) / (a d)`
(Sylvester), with a smaller numerator: rational inputs terminate. An irrational positive remainder
`r` has `a ≥ 1`, and `a r - 1` and `r - 1/a` are irrational and positive: irrational inputs never
reach `0`. Then apply `BinaryIrrational.problem1_iff_irrational_binary`.

Sources: P. Erdős, A. Rényi and P. Szüsz, *On Engel's and Sylvester's series*, Ann. Univ. Sci.
Budapest. Eötvös Sect. Math. 1 (1958) 7–32; J. Galambos, *Representations of Real Numbers by
Infinite Series*, Springer (1976). Catalog entry [50].
-/

namespace Rule30Equivalents.Expansions

open Ruliology.CellularAutomata

/-! ### The ceiling bound behind both algorithms -/

/-- For `m, d > 0` and `a = ⌈d / m⌉`: `d ≤ a m < d + m`, so `a m - d` is a natural number below
`m`, and `a ≥ 1`. -/
theorem ceil_bounds (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    (d : ℤ) ≤ ⌈((m : ℝ) / d)⁻¹⌉ * m ∧ ⌈((m : ℝ) / d)⁻¹⌉ * m < d + m ∧ 1 ≤ ⌈((m : ℝ) / d)⁻¹⌉ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hinv : ((m : ℝ) / d)⁻¹ = (d : ℝ) / m := inv_div _ _
  have h1 : (d : ℝ) / m ≤ ⌈((m : ℝ) / d)⁻¹⌉ := hinv ▸ Int.le_ceil _
  have h2 : (⌈((m : ℝ) / d)⁻¹⌉ : ℝ) < (d : ℝ) / m + 1 := hinv ▸ Int.ceil_lt_add_one _
  have h3 : (d : ℝ) ≤ ⌈((m : ℝ) / d)⁻¹⌉ * m := by rwa [div_le_iff₀ hm'] at h1
  have h4 : (⌈((m : ℝ) / d)⁻¹⌉ : ℝ) * m < d + m := by
    have := mul_lt_mul_of_pos_right h2 hm'
    rwa [add_mul, div_mul_cancel₀ _ hm'.ne', one_mul] at this
  have h5 : (0 : ℝ) < ⌈((m : ℝ) / d)⁻¹⌉ := lt_of_lt_of_le (div_pos hd' hm') h1
  refine ⟨by exact_mod_cast h3, by exact_mod_cast h4, ?_⟩
  have : (0 : ℤ) < ⌈((m : ℝ) / d)⁻¹⌉ := by exact_mod_cast h5
  omega

/-! ### Engel -/

/-- One step of the Engel algorithm. -/
noncomputable def engelStep (r : ℝ) : ℝ := if r = 0 then 0 else (⌈r⁻¹⌉ : ℝ) * r - 1

/-- The remainders of the Engel expansion of `x`. -/
noncomputable def engelRem (x : ℝ) (n : ℕ) : ℝ := engelStep^[n] x

theorem engelRem_zero (x : ℝ) : engelRem x 0 = x := rfl

theorem engelRem_succ (x : ℝ) (n : ℕ) : engelRem x (n + 1) =
    if engelRem x n = 0 then 0 else (⌈(engelRem x n)⁻¹⌉ : ℝ) * engelRem x n - 1 :=
  Function.iterate_succ_apply' engelStep n x

theorem engelStep_rat (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    ∃ m' : ℕ, m' < m ∧ engelStep ((m : ℝ) / d) = (m' : ℝ) / d := by
  obtain ⟨h3, h4, -⟩ := ceil_bounds m d hm hd
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨(⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat, by omega, ?_⟩
  unfold engelStep
  rw [if_neg (div_ne_zero (by exact_mod_cast hm.ne') hd')]
  have hcast : (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℕ) : ℝ) =
      ((⌈((m : ℝ) / d)⁻¹⌉ : ℝ) * m - d) := by
    rw [show (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℕ) : ℝ) =
      (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℤ) : ℝ) from rfl, Int.toNat_of_nonneg (by omega)]
    push_cast; ring
  rw [hcast]
  field_simp

theorem exists_engelRem_eq_zero (d : ℕ) (hd : 0 < d) :
    ∀ m : ℕ, ∃ n, engelRem ((m : ℝ) / d) n = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by simp [engelRem]⟩
    · obtain ⟨m', hlt, heq⟩ := engelStep_rat m d hm hd
      obtain ⟨n, hn⟩ := ih m' hlt
      exact ⟨n + 1, by rw [engelRem, Function.iterate_succ_apply, heq]; exact hn⟩

theorem engelStep_irrational {r : ℝ} (h : Irrational r) (hr : 0 < r) :
    Irrational (engelStep r) ∧ 0 < engelStep r := by
  have ha : 1 ≤ ⌈r⁻¹⌉ := Int.one_le_ceil_iff.2 (inv_pos.2 hr)
  have hirr : Irrational ((⌈r⁻¹⌉ : ℝ) * r - 1) := by
    simpa using (h.intCast_mul (m := ⌈r⁻¹⌉) (by omega)).sub_natCast 1
  have hge : 1 ≤ (⌈r⁻¹⌉ : ℝ) * r := by
    have := mul_le_mul_of_nonneg_right (Int.le_ceil r⁻¹) hr.le
    rwa [inv_mul_cancel₀ hr.ne'] at this
  unfold engelStep
  rw [if_neg hr.ne']
  exact ⟨hirr, lt_of_le_of_ne (by linarith) (Ne.symm hirr.ne_zero)⟩

/-- **For `x ≥ 0`, the Engel expansion is infinite iff `x` is irrational.** -/
theorem irrational_iff_engelRem_ne_zero {x : ℝ} (hx : 0 ≤ x) :
    Irrational x ↔ ∀ n, engelRem x n ≠ 0 := by
  constructor
  · intro h
    have key : ∀ n, Irrational (engelRem x n) ∧ 0 < engelRem x n := by
      intro n
      induction n with
      | zero => exact ⟨h, lt_of_le_of_ne hx (Ne.symm h.ne_zero)⟩
      | succ n ih =>
        rw [engelRem, Function.iterate_succ_apply']
        exact engelStep_irrational ih.1 ih.2
    exact fun n => (key n).1.ne_zero
  · intro h hq
    obtain ⟨q, rfl⟩ := hq
    have hq0 : 0 ≤ q := by exact_mod_cast hx
    obtain ⟨n, hn⟩ := exists_engelRem_eq_zero q.den q.den_pos q.num.toNat
    refine h n ?_
    have : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq0)]
      exact (Rat.cast_def q).symm
    rwa [this] at hn

/-- **Problem 1 ⟺ the Engel expansion of `x₂` is infinite** (catalog [50]). -/
theorem problem1_iff_engel_infinite :
    Rule30Prize.Problem1 ↔ ∀ n, engelRem BinaryIrrational.centerBinary n ≠ 0 := by
  rw [BinaryIrrational.problem1_iff_irrational_binary]
  refine irrational_iff_engelRem_ne_zero (tsum_nonneg fun t => ?_)
  split_ifs <;> positivity

/-! ### Sylvester -/

/-- One step of the greedy Egyptian-fraction (Sylvester) algorithm. -/
noncomputable def sylvesterStep (r : ℝ) : ℝ := if r = 0 then 0 else r - (⌈r⁻¹⌉ : ℝ)⁻¹

/-- The remainders of the Sylvester expansion of `x`. -/
noncomputable def sylvesterRem (x : ℝ) (n : ℕ) : ℝ := sylvesterStep^[n] x

theorem sylvesterStep_rat (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    ∃ m' d' : ℕ, m' < m ∧ 0 < d' ∧ sylvesterStep ((m : ℝ) / d) = (m' : ℝ) / d' := by
  obtain ⟨h3, h4, h1⟩ := ceil_bounds m d hm hd
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨(⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat, (⌈((m : ℝ) / d)⁻¹⌉ * d).toNat, by omega,
    by have : (0 : ℤ) < ⌈((m : ℝ) / d)⁻¹⌉ * d := by positivity
       omega, ?_⟩
  unfold sylvesterStep
  rw [if_neg (div_ne_zero (by exact_mod_cast hm.ne') hd')]
  have c1 : (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℕ) : ℝ) =
      ((⌈((m : ℝ) / d)⁻¹⌉ : ℝ) * m - d) := by
    rw [show (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℕ) : ℝ) =
      (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℤ) : ℝ) from rfl, Int.toNat_of_nonneg (by omega)]
    push_cast; ring
  have c2 : (((⌈((m : ℝ) / d)⁻¹⌉ * d).toNat : ℕ) : ℝ) = ((⌈((m : ℝ) / d)⁻¹⌉ : ℝ) * d) := by
    rw [show (((⌈((m : ℝ) / d)⁻¹⌉ * d).toNat : ℕ) : ℝ) =
      (((⌈((m : ℝ) / d)⁻¹⌉ * d).toNat : ℤ) : ℝ) from rfl,
      Int.toNat_of_nonneg (by have : (0 : ℤ) < ⌈((m : ℝ) / d)⁻¹⌉ * d := by positivity
                              omega)]
    push_cast; ring
  rw [c1, c2]
  field_simp

theorem exists_sylvesterRem_eq_zero : ∀ m d : ℕ, 0 < d → ∃ n, sylvesterRem ((m : ℝ) / d) n = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro d hd
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by simp [sylvesterRem]⟩
    · obtain ⟨m', d', hlt, hd', heq⟩ := sylvesterStep_rat m d hm hd
      obtain ⟨n, hn⟩ := ih m' hlt d' hd'
      exact ⟨n + 1, by rw [sylvesterRem, Function.iterate_succ_apply, heq]; exact hn⟩

theorem sylvesterStep_irrational {r : ℝ} (h : Irrational r) (hr : 0 < r) :
    Irrational (sylvesterStep r) ∧ 0 < sylvesterStep r := by
  have ha : 1 ≤ ⌈r⁻¹⌉ := Int.one_le_ceil_iff.2 (inv_pos.2 hr)
  have ha' : (0 : ℝ) < ⌈r⁻¹⌉ := by exact_mod_cast (show (0 : ℤ) < ⌈r⁻¹⌉ by omega)
  have hirr : Irrational (r - (⌈r⁻¹⌉ : ℝ)⁻¹) := by
    have := h.sub_ratCast (q := ((⌈r⁻¹⌉ : ℚ))⁻¹)
    simpa using this
  have hle : (⌈r⁻¹⌉ : ℝ)⁻¹ ≤ r := by
    rw [inv_le_comm₀ ha' hr]
    exact Int.le_ceil r⁻¹
  unfold sylvesterStep
  rw [if_neg hr.ne']
  exact ⟨hirr, lt_of_le_of_ne (by linarith) (Ne.symm hirr.ne_zero)⟩

/-- **For `x ≥ 0`, the Sylvester expansion is infinite iff `x` is irrational.** -/
theorem irrational_iff_sylvesterRem_ne_zero {x : ℝ} (hx : 0 ≤ x) :
    Irrational x ↔ ∀ n, sylvesterRem x n ≠ 0 := by
  constructor
  · intro h
    have key : ∀ n, Irrational (sylvesterRem x n) ∧ 0 < sylvesterRem x n := by
      intro n
      induction n with
      | zero => exact ⟨h, lt_of_le_of_ne hx (Ne.symm h.ne_zero)⟩
      | succ n ih =>
        rw [sylvesterRem, Function.iterate_succ_apply']
        exact sylvesterStep_irrational ih.1 ih.2
    exact fun n => (key n).1.ne_zero
  · intro h hq
    obtain ⟨q, rfl⟩ := hq
    have hq0 : 0 ≤ q := by exact_mod_cast hx
    obtain ⟨n, hn⟩ := exists_sylvesterRem_eq_zero q.num.toNat q.den q.den_pos
    refine h n ?_
    have : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq0)]
      exact (Rat.cast_def q).symm
    rwa [this] at hn

/-- **Problem 1 ⟺ the Sylvester expansion of `x₂` is infinite.** -/
theorem problem1_iff_sylvester_infinite :
    Rule30Prize.Problem1 ↔ ∀ n, sylvesterRem BinaryIrrational.centerBinary n ≠ 0 := by
  rw [BinaryIrrational.problem1_iff_irrational_binary]
  refine irrational_iff_sylvesterRem_ne_zero (tsum_nonneg fun t => ?_)
  split_ifs <;> positivity

end Rule30Equivalents.Expansions

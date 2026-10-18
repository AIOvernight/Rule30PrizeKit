import Rule30Equivalents.OneTapeGap
import Rule30Equivalents.Automatic
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Prize Problem 3 implies Problem 1

Wolfram's Problem 3 asks whether computing `c(n)` requires at least `O(n)` computational effort.
Its formal statement quantifies over Turing machines that read `n`. Here it is stated in the
one-tape Turing machine model of `OneTapeGap`, with the binary digits of `n` (least significant
first) as input:
* `Problem3`, the literal reading: no machine computes `c(n)` in time `O(n)`;
* `Problem3Verbal`, the verbal reading "at least of the order of `n`": no machine does it in time
  `o(n)`. The literal reading implies the verbal one (`problem3Verbal_of_problem3`).

`kernelTM` computes a `2`-automatic sequence in `|bin n| + 1 = O(log n)` steps: its states are the
`2`-kernel, and reading the digit `b` moves from `g` to `n ↦ g(2n + b)`. So Problem 3, even in the
verbal reading, implies that `c` is not `2`-automatic (`not_isAutomatic_of_problem3Verbal`), hence
Problem 1 (`problem1_of_problem3Verbal`). This is the chain "Problem 3 ⟹ no polylog-time digit
extraction ⟹ c is not automatic ⟹ Problem 1" of catalog Section 6.2.
-/

namespace Rule30Equivalents.ProblemThree

open Filter Ruliology.CellularAutomata OneTapeGap Automatic

/-- The binary digits of `n`, least significant first, as tape symbols: `M.one` for `1` and `zero`
for `0`. -/
def binWord (M : Machine) (zero : M.Γ) (n : ℕ) : List M.Γ :=
  (List.range n.size).map fun i => if n.testBit i then M.one else zero

/-- `M` computes `f` from the binary digits of `n` within time `T`: on the input `binWord n` it has
halted by step `T n`, in an accepting state iff `f n`. -/
def DecidesBinInTime (M : Machine) (zero : M.Γ) (f : ℕ → Bool) (T : ℕ → ℕ) : Prop :=
  ∀ n, M.halt (runW M id (binWord M zero n) (T n)).q = true ∧
    M.accept (runW M id (binWord M zero n) (T n)).q = f n

/-- **Problem 3**, literally: no one-tape Turing machine computes `c(n)` from the binary digits of
`n` in time `O(n)`. -/
def Problem3 : Prop :=
  ¬ ∃ (M : TM) (zero : M.Γ) (T : ℕ → ℕ),
    (fun n => (T n : ℝ)) =O[atTop] (fun n => (n : ℝ)) ∧ DecidesBinInTime M.toMachine zero c T

/-- **Problem 3**, verbally ("at least of the order of `n`"): no machine does it in time `o(n)`. -/
def Problem3Verbal : Prop :=
  ¬ ∃ (M : TM) (zero : M.Γ) (T : ℕ → ℕ),
    (fun n => (T n : ℝ)) =o[atTop] (fun n => (n : ℝ)) ∧ DecidesBinInTime M.toMachine zero c T

theorem problem3Verbal_of_problem3 (h : Problem3) : Problem3Verbal :=
  fun ⟨M, zero, T, hT, hM⟩ => h ⟨M, zero, T, hT.isBigO, hM⟩

/-! ### Automatic sequences in logarithmic time -/

/-- The low digits: `n mod 2^(t+1)` adds bit `t` to `n mod 2^t`. -/
theorem mod_two_pow_succ' (n t : ℕ) :
    n % 2 ^ (t + 1) = 2 ^ t * (if n.testBit t then 1 else 0) + n % 2 ^ t := by
  rw [pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
  have h2 := Nat.mod_two_eq_zero_or_one (n / 2 ^ t)
  rcases h2 with h2 | h2 <;> simp [h2]
  ring

/-- The machine with the `2`-kernel of `f` as states: reading the digit `b` moves from `g` to
`n ↦ g(2n + b)`, and at the first blank it answers `g 0`. -/
noncomputable def kernelTM (f : ℕ → Bool) (hf : IsAutomatic 2 f) : TM where
  Q := kernel 2 f ⊕ Bool
  Γ := Option Bool
  blank := none
  one := some true
  start := Sum.inl ⟨f, self_mem_kernel 2 f⟩
  halt := Sum.isRight
  accept := Sum.elim (fun _ => false) id
  δ := fun s x => match s, x with
    | Sum.inl g, some b =>
      (Sum.inl ⟨fun m => g.1 (2 * m + if b then 1 else 0),
        mem_kernel_step g.2 (by split <;> omega)⟩,
        some b, Move.right)
    | Sum.inl g, none => (Sum.inr (g.1 0), none, Move.right)
    | Sum.inr a, x => (Sum.inr a, x, Move.right)
  instFintype := by
    haveI := hf.fintype
    infer_instance

theorem mem_kernel_low (f : ℕ → Bool) (n t : ℕ) :
    (fun m => f (2 ^ t * m + n % 2 ^ t)) ∈ kernel 2 f :=
  ⟨t, n % 2 ^ t, Nat.mod_lt _ (by positivity), rfl⟩

theorem run_kernelTM {f : ℕ → Bool} (hf : IsAutomatic 2 f) (n : ℕ) {t : ℕ} (ht : t ≤ n.size) :
    runW (kernelTM f hf).toMachine id (binWord (kernelTM f hf).toMachine (some false) n) t =
      ⟨Sum.inl ⟨fun m => f (2 ^ t * m + n % 2 ^ t), mem_kernel_low f n t⟩, t,
        (initW (kernelTM f hf).toMachine id
          (binWord (kernelTM f hf).toMachine (some false) n)).tape⟩ := by
  induction t with
  | zero =>
    show initW _ id _ = _
    simp only [initW, pow_zero, one_mul, Nat.mod_one, add_zero, Nat.cast_zero]
    rfl
  | succ t ih =>
    rw [(isRun_runW (M := (kernelTM f hf).toMachine) id _) t, ih (by omega), step_eq rfl]
    have htape : (initW (kernelTM f hf).toMachine id
        (binWord (kernelTM f hf).toMachine (some false) n)).tape (t : ℤ) = some (n.testBit t) := by
      simp only [initW, binWord, List.length_map, List.length_range, id]
      rw [dif_pos (by omega)]
      simp only [List.getElem_map, List.getElem_range, Int.toNat_natCast]
      cases n.testBit t <;> rfl
    refine Cfg.ext' ?_ ?_ ?_
    · dsimp only
      rw [htape]
      show Sum.inl _ = Sum.inl _
      congr 1
      apply Subtype.ext
      funext m
      show f (2 ^ t * (2 * m + if n.testBit t then 1 else 0) + n % 2 ^ t) =
        f (2 ^ (t + 1) * m + n % 2 ^ (t + 1))
      rw [mod_two_pow_succ']
      congr 1
      ring
    · dsimp only
      rw [htape]
      push_cast
      rfl
    · dsimp only
      rw [htape]
      exact Function.update_eq_self_iff.2 htape.symm

/-- **A `2`-automatic sequence is computed in `|bin n| + 1` steps.** -/
theorem decidesBinInTime_kernelTM {f : ℕ → Bool} (hf : IsAutomatic 2 f) :
    DecidesBinInTime (kernelTM f hf).toMachine (some false) f fun n => n.size + 1 := by
  intro n
  rw [(isRun_runW (M := (kernelTM f hf).toMachine) id _) n.size, run_kernelTM hf n le_rfl,
    step_eq rfl]
  have htape : (initW (kernelTM f hf).toMachine id
      (binWord (kernelTM f hf).toMachine (some false) n)).tape (n.size : ℤ) = none := by
    simp only [initW, binWord, List.length_map, List.length_range]
    rw [dif_neg (by omega)]
    rfl
  dsimp only
  rw [htape]
  refine ⟨rfl, ?_⟩
  show f (2 ^ n.size * 0 + n % 2 ^ n.size) = f n
  rw [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt (Nat.lt_size_self n)]

/-- `|bin n| + 1 = o(n)`. -/
theorem isLittleO_size :
    (fun n : ℕ => ((n.size + 1 : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have hlog : (fun n : ℕ => Real.log n) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hconst : (fun _ : ℕ => (2 : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop (2 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun n : ℕ => 2 * Real.log n + 2) ?_
    ((hlog.const_mul_left 2).add hconst)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hpow : (2 : ℝ) ^ (n.size - 1) ≤ n := by
    have h1 : 2 ^ (n.size - 1) ≤ n := by
      rcases Nat.eq_zero_or_pos (n.size - 1) with h | h
      · rw [h, pow_zero]; exact hn
      · by_contra hlt
        push Not at hlt
        have := Nat.size_le.2 hlt
        omega
    exact_mod_cast h1
  have hlogn : ((n.size - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hsize : ((n.size + 1 : ℕ) : ℝ) ≤ 2 * Real.log n + 2 := by
    have hs : 1 ≤ n.size := Nat.size_pos.2 hn
    have : ((n.size + 1 : ℕ) : ℝ) = ((n.size - 1 : ℕ) : ℝ) + 2 := by
      rw [Nat.cast_sub hs]; push_cast; ring
    rw [this]
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), one_mul]
  exact hsize

/-! ### Problem 3 implies Problem 1 -/

/-- **Problem 3 implies that `c` is not `2`-automatic**, even in the verbal reading. -/
theorem not_isAutomatic_of_problem3Verbal (h : Problem3Verbal) : ¬ IsAutomatic 2 c := fun ha =>
  h ⟨kernelTM c ha, some false, fun n => n.size + 1, isLittleO_size, decidesBinInTime_kernelTM ha⟩

/-- **Problem 3 implies Problem 1**, in the verbal reading. -/
theorem problem1_of_problem3Verbal (h : Problem3Verbal) : Rule30Prize.Problem1 := fun hep =>
  not_isAutomatic_of_problem3Verbal h (isAutomatic_of_eventuallyPeriodic hep le_rfl)

/-- **Problem 3 implies Problem 1**, in the literal reading. -/
theorem problem1_of_problem3 (h : Problem3) : Rule30Prize.Problem1 :=
  problem1_of_problem3Verbal (problem3Verbal_of_problem3 h)

end Rule30Equivalents.ProblemThree

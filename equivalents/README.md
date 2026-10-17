# Rule 30 Problem 1: equivalent forms

Rule 30 Prize Problem 1 asks whether the center column of rule 30, started from a single black cell, is ever eventually periodic. It is open. This folder collects statements that are **proved equivalent** to it in Lean 4 + Mathlib. A proof of any one of them is a proof of Problem 1.

```lean
-- the center column read as the binary number 0.c(0)c(1)c(2)…
noncomputable def centerBinary : ℝ := ∑' t, (if c t then 1 else 0) / 2 ^ (t + 1)

theorem problem1_iff_irrational_binary : Rule30Prize.Problem1 ↔ Irrational centerBinary
```

**Status:**
- 41 of the 53 equivalent forms in [CATALOG.md](CATALOG.md) are proved here, as 118 theorems named `problem1_iff_*`.
- For 4 more forms, the direction "the form implies Problem 1" is proved: `problem1_of_*`.
- Every one uses only `propext`, `Classical.choice` and `Quot.sound`. None uses `sorry` or `native_decide`.
- For each module of the first two batches, an independent verifier recompiled the file, checked its axioms and restated its main theorems. The twelve later modules (IntegerRows, LogicAutomata, Realization, WordForms, Expansions, Holonomic, OmegaRegular, PisotBase, Automatic, Transcendence, LempelZiv and CoupledHalves) were compiled and axiom-checked by their author only.

## What is here

| Module | Problem 1 is equivalent to … | Headline theorems |
|---|---|---|
| [BinaryIrrational](Rule30Equivalents/BinaryIrrational.lean) | the irrationality of 0.c(0)c(1)… read in base 2, in base 10, or in any base B ≥ 2 | `problem1_iff_irrational_binary`, `problem1_iff_irrational_base` |
| [NumberTheory](Rule30Equivalents/NumberTheory.lean) | each of:<br>- the continued fraction of x₂ does not terminate;<br>- x₂ has infinitely many approximations with error below 1/q²;<br>- `LiouvilleWith 2 x₂`;<br>- x₂ has infinite order on the circle, and its multiples are dense there;<br>- x₂ is not preperiodic under doubling;<br>- no long division p/q produces the digits | `problem1_iff_cf_not_terminates`, `problem1_iff_dirichlet`, `problem1_iff_doubling_not_preperiodic`, `problem1_iff_not_rational_digits` |
| [TwoAdic](Rule30Equivalents/TwoAdic.lean) | the 2-adic number ∑ c(t) 2ᵗ is irrational; there is a congruence form for every base p ≥ 2; the 2-adic (FCSR) complexity is unbounded | `problem1_iff_padic_irrational`, `problem1_iff_padic_int`, `problem1_iff_two_adic_complexity` |
| [PowerSeriesF2](Rule30Equivalents/PowerSeriesF2.lean) | ∑ c(t) Xᵗ is not rational over F₂; no linear feedback shift register generates c; its linear complexity is unbounded | `problem1_iff_series_not_rational`, `problem1_iff_no_lfsr`, `problem1_iff_linear_complexity_unbounded` |
| [LinearRelations](Rule30Equivalents/LinearRelations.lean) | over any field: the series is not rational, and c solves no linear recurrence; the shifts of c are linearly independent; the Hankel rank is unbounded; Kronecker's determinant criterion holds over ℤ, F₂ and any field | `problem1_iff_shifts_linearIndependent`, `problem1_iff_hankel_rank_unbounded`, `problem1_iff_hankel_det_int` |
| [ShiftOrbit](Rule30Equivalents/ShiftOrbit.lean) | the shift orbit of c is infinite, and c is not preperiodic. Morse–Hedlund: c has at least n + 1 distinct blocks of every length n | `problem1_iff_infinite_shifts`, `problem1_iff_ncard_factors`, `problem1_iff_strictMono_ncard_factors` |
| [WordsAutomata](Rule30Equivalents/WordsAutomata.lean) | each of:<br>- no word repeats forever, and there is a right-special block of every length;<br>- the tail complexity is at least n + 1;<br>- the orbit closure and the ω-limit set are infinite;<br>- every finite-state predictor errs infinitely often, and no feedback shift register generates c | `problem1_iff_no_eventual_word`, `problem1_iff_right_special`, `problem1_iff_omegaLimit_infinite`, `problem1_iff_unpredictable` |
| [TransformsSeeds](Rule30Equivalents/TransformsSeeds.lean) | each of:<br>- the same for shifts of c, its XOR derivative, its running parity, and its decimations;<br>- the Π₂ form, and periods restricted to factorials;<br>- the formal-conjectures statement, and Wolfram's 2019 statement read as intended (the literal reading is degenerate);<br>- every stripe seed 1, 11, 101, 1011, … has exactly the center column c | `problem1_iff_xor_derivative`, `problem1_iff_decimation`, `problem1_iff_fc`, `problem1_iff_wolfram`, `problem1_iff_stripeSeed` |
| [IntegerRows](Rule30Equivalents/IntegerRows.lean) | the integer recurrence a(0) = 1, a(t+1) = a(t) XOR (2a(t) OR 4a(t)) (OEIS A110240): bit t of a(t) is not eventually periodic. Equivalently, the main diagonal of the bit array (j, t) ↦ bit j of a(t) is not eventually periodic, although every row j of that array is periodic with period dividing 2^j | `problem1_iff_integer_rows`, `problem1_iff_diagArray`, `diagArray_row_periodic` |
| [LogicAutomata](Rule30Equivalents/LogicAutomata.lean) | the black times are not definable in Presburger arithmetic (with any parameters) and do not form a semilinear set; the unary language {1ⁿ : c(n) = 1} and the language of prefixes of c are not regular | `problem1_iff_not_presburger`, `problem1_iff_not_semilinear`, `problem1_iff_unary_not_regular`, `problem1_iff_prefixes_not_regular` |
| [Realization](Rule30Equivalents/Realization.lean) | no eventually periodic column is realized by the single seed (the inverse problem); the irrationality of `Real.ofDigits` of the column in every base, and of the Cantor function `cantorFunction (1/b) c`. Also `problem1_iff_column_iff_both`: by Jen's theorem, an equivalence with the same question for another column would prove both | `problem1_iff_realization`, `problem1_iff_irrational_ofDigits` |
| [OmegaRegular](Rule30Equivalents/OmegaRegular.lean) | no Büchi automaton accepts exactly the center column: {c} is not ω-regular | `problem1_iff_not_omega_regular`, `eventuallyPeriodic_iff_omegaRegular_singleton` |
| [Holonomic](Rule30Equivalents/Holonomic.lean) | c satisfies no recurrence Σ pᵢ(n)·c(n + i) = 0, from any point on, with polynomial coefficients not all zero (c is not P-recursive) | `problem1_iff_not_pRecursive`, `eventuallyPeriodic_iff_pRecursive` |
| [CoupledHalves](Rule30Equivalents/CoupledHalves.lean) | no solution of the causal system u(t+1) = rule(left half driven by u at −1, u(t), right half driven by u at 1), u(0) = 1, is eventually periodic; its only solution is the center column | `problem1_iff_coupled_halves`, `eq_center_of_solves` |
| [LempelZiv](Rule30Equivalents/LempelZiv.lean) | the Lempel–Ziv (1976) complexity of the prefixes of c is unbounded | `problem1_iff_lz_unbounded`, `eventuallyPeriodic_iff_lz_bounded` |
| [Transcendence](Rule30Equivalents/Transcendence.lean) | sufficient conditions only: Σ c(t)Xᵗ is transcendental over K(X) for some field K, such as ℚ (the converse is Fatou's theorem), or over F₂(X) or F₃(X) | `problem1_of_transcendental`, `problem1_of_transcendental_F2_or_F3` |
| [Automatic](Rule30Equivalents/Automatic.lean) | the automatic complexity of the prefixes of c tends to ∞ (no DFA with K states uniquely accepts infinitely many prefixes). Sufficient conditions: c is not k-automatic for some k ≥ 2, or not both 2- and 3-automatic (the converse is Cobham's theorem) | `problem1_iff_automaticComplexity_tendsto_top`, `problem1_of_not_two_three_automatic` |
| [PisotBase](Rule30Equivalents/PisotBase.lean) | the value Σ c(t)·β^−(t+1) in the Pisot base β = 1 + √2 is not of the form a + b√2 with a, b rational | `problem1_iff_not_mem_Q_sqrt_two`, `eventuallyPeriodic_iff_mem_qsqrt2` |
| [Expansions](Rule30Equivalents/Expansions.lean) | the Engel expansion and the Sylvester (greedy Egyptian fraction) expansion of x₂ are infinite | `problem1_iff_engel_infinite`, `problem1_iff_sylvester_infinite`, `irrational_iff_engelRem_ne_zero` |
| [WordForms](Rule30Equivalents/WordForms.lean) | for every N, some finite prefix has more than N distinct factors of one length (finite certificates); the gaps between black cells, the gaps between white cells and the run lengths are not eventually periodic. Sufficient conditions: infinitely many prefixes without a repetition of exponent φ²; unbordered factors of unbounded length in every tail; unbounded Lempel–Ziv complexity | `problem1_iff_prefix_certificates`, `problem1_iff_black_gaps`, `problem1_iff_run_lengths`, `problem1_of_lz_unbounded` |
| [Symmetry](Rule30Equivalents/Symmetry.lean) | the same question for rule 86 (black seed), for rules 135 and 149 (white seed), and for the complemented column | `problem1_iff_rule86`, `problem1_iff_rule135`, `problem1_iff_rule149` |
| [Basic](Rule30Equivalents/Basic.lean) | — (shared definitions: the center column `c` and `EventuallyPeriodic`) | `problem1_iff_not_eventuallyPeriodic` |

Each module first proves a general theorem about every sequence `b : ℕ → Bool`, then specializes it to the center column. The general theorems hold for any 0/1 sequence. Some may be worth upstreaming to Mathlib, for example "`Real.ofDigits` is rational iff the digits are eventually periodic", Morse–Hedlund, `Irrational x → LiouvilleWith 2 x`, and Kronecker's Hankel criterion.

## Documents

- **[CATALOG.md](CATALOG.md)** covers all 53 known equivalent forms, grouped by field, with each one's statement, proof route, sources and Lean status. It also lists stronger statements (for example, transcendence or non-automaticity), weaker ones, related questions (Problems 2 and 3) and broader perspectives.

## Building

This is a Lake project on Lean 4.30.0. It pins Mathlib at commit `c5ea00351c` and depends on the core-Lean snapshot in [`../lean`](../lean) for `Rule30Prize.Problem1`.

From the kit root, which shares one Mathlib with this folder:

```sh
lake exe cache get        # prebuilt Mathlib (or sh setup.sh)
lake build                # builds the kit, the catalog and this library; about 1 minute here
lake env lean equivalents/scripts/CheckAxioms.lean   # axioms of all problem1_iff_* and problem1_of_* theorems
```

## Adding an equivalent form

1. Pick an entry from [CATALOG.md](CATALOG.md) whose status is *Stated*. Its suggested Lean statement is in the entry.
2. Prove a general theorem for every `b : ℕ → Bool`, then specialize it to `c` as `Rule30Prize.Problem1 ↔ X`.
3. Watch for:
   - double expansions in base 2;
   - eventually constant sequences (`Rule30Prize.center_not_eventually_constant` handles them for c);
   - `0 < P`.
4. Keep the file free of `sorry`, `native_decide` and new axioms. Add it to `Rule30Equivalents.lean`, and regenerate `scripts/CheckAxioms.lean` with `python3 equivalents/scripts/gen_check_axioms.py` from the kit root.
5. Have someone other than the author restate the main theorem from scratch and check that it says what it claims.

Next targets:
- Euler–Lagrange (eventually periodic continued fraction ⟺ quadratic irrational) for [39] and [49];
- factorial-base expansions [50].

The hard classical ones are Fatou/Pólya–Carlson (natural boundary), Skolem–Mahler–Lech (zero sets over ℚ), Cobham–Christol, and the one-tape time gap.

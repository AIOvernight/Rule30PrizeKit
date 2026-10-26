module
public import Ruliology.CellularAutomata.Rule30StripCertificates
/-! Finite-width synchronization of the exact front-anchored Rule30 map.
Only width24 is asserted; an all-width four-clock is false at width30. -/
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Ruliology.CellularAutomata.Rule30FrontClock

def f (x : Nat) : Nat := (x <<< 2) ^^^ ((x <<< 1) ||| x)
def evolve : Nat → Nat → Nat
  | 0,x => x
  | n+1,x => f (evolve n x)

theorem f_mod (x k : Nat) : f (x % 2^k) % 2^k = f x % 2^k := by
  simp only [f, Nat.xor_mod_two_pow, Nat.or_mod_two_pow,
    Nat.mod_two_pow_shiftLeft_mod_two_pow, Nat.mod_mod]

theorem extend_mod (x k : Nat) :
    x % 2^(k+1) = (x % 2^k) ||| (x.testBit k).toNat <<< k := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<k
  · simp [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, hi,
      show i<k+1 by omega, show ¬k≤i by omega]
  · by_cases he : i=k
    · subst i
      cases h : x.testBit k <;> simp [h,Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft,
        Rule30StripCertificates.testBit_toNat]
    · simp [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft,
        Rule30StripCertificates.testBit_toNat, hi, show ¬i<k+1 by omega,
        show i-k≠0 by omega]

def growCheck (k : Nat) (A B : List Nat) : Bool :=
  A.all (fun s => (B.contains (f s % 2^(k+1))) &&
    (B.contains (f (s ||| (1 <<< k)) % 2^(k+1))))

theorem grow_sound {k x : Nat} {A B : List Nat} (hc : growCheck k A B = true)
    (hm : x%2^k ∈ A) : f x %2^(k+1) ∈ B := by
  have hh := List.all_eq_true.mp hc (x%2^k) hm
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hh
  have he := f_mod x (k+1)
  rw [extend_mod x k] at he
  rw [← he]
  cases hz : x.testBit k
  · simpa [hz] using hh.1
  · simpa [hz] using hh.2

def fixedCheck (k : Nat) (A B : List Nat) : Bool :=
  A.all (fun s => B.contains (f s %2^k))
theorem fixed_sound {k x : Nat} {A B : List Nat} (hc : fixedCheck k A B = true)
    (hm : x%2^k ∈ A) : f x %2^k ∈ B := by
  have hh := List.all_eq_true.mp hc (x%2^k) hm
  simp only [List.contains_iff_mem] at hh
  simpa only [f_mod] using hh



end Ruliology.CellularAutomata.Rule30FrontClock

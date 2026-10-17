import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks0
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks1
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks2
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks3
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks4
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks5
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks6
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks7
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks8
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks9
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks10
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks11
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks12
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks13
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks14
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth56Chunks15

/-!
# `Q01` for every start of width at most `56` (kernel-checked)

Every start of the zero-boundary left half supported at depths `1, …, 56` has a white cell at
depth `1` (column `-1`) at some even time `≤ 100`. The 1024 chunk checks are in the namespaces
`Rule30ZeroBoundaryWidth56.C0` – `C63`, in the modules
`Rule30Certificates.ZeroBoundaryWidth56Chunks0` – `ZeroBoundaryWidth56Chunks15` (64 chunks each);
soundness is `Rule30ZeroBoundaryLanes.q01_of_chunks`.

* `q01_width_le_56`: the bound `100`, which is `D(56)` of the round-2 death-time table (its
  tightness is observed, not proved).
* `q01_width_le_56_linear`: the bound `2 W + 8`.
* `not_inX_of_width_le_56`: `Q01` restricted to widths `≤ 56` (`¬ Rule30ZeroBoundary.InX x`).

`Ruliology.lean` does not import this module: its chunk modules take about 6 minutes of kernel
time in all. Build it on its own with
`lake build Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1, `KC.Q01W56`); adversarially verified. Ported to the
kit's names on 2026-10-17.
-/

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes Rule30ZeroBoundary

theorem all_chunks : ChunksOK 56 101 18 0 1024 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C0.range C1.range) (chunksOK_append C2.range C3.range)) (chunksOK_append (chunksOK_append C4.range C5.range) (chunksOK_append C6.range C7.range))) (chunksOK_append (chunksOK_append (chunksOK_append C8.range C9.range) (chunksOK_append C10.range C11.range)) (chunksOK_append (chunksOK_append C12.range C13.range) (chunksOK_append C14.range C15.range)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C16.range C17.range) (chunksOK_append C18.range C19.range)) (chunksOK_append (chunksOK_append C20.range C21.range) (chunksOK_append C22.range C23.range))) (chunksOK_append (chunksOK_append (chunksOK_append C24.range C25.range) (chunksOK_append C26.range C27.range)) (chunksOK_append (chunksOK_append C28.range C29.range) (chunksOK_append C30.range C31.range))))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C32.range C33.range) (chunksOK_append C34.range C35.range)) (chunksOK_append (chunksOK_append C36.range C37.range) (chunksOK_append C38.range C39.range))) (chunksOK_append (chunksOK_append (chunksOK_append C40.range C41.range) (chunksOK_append C42.range C43.range)) (chunksOK_append (chunksOK_append C44.range C45.range) (chunksOK_append C46.range C47.range)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C48.range C49.range) (chunksOK_append C50.range C51.range)) (chunksOK_append (chunksOK_append C52.range C53.range) (chunksOK_append C54.range C55.range))) (chunksOK_append (chunksOK_append (chunksOK_append C56.range C57.range) (chunksOK_append C58.range C59.range)) (chunksOK_append (chunksOK_append C60.range C61.range) (chunksOK_append C62.range C63.range))))))

/-- **`Q01` for widths `≤ 56`**: every start supported at depths `≤ 56` has a white cell at
depth `1` at some even time `≤ 100`. -/
theorem q01_width_le_56 (x : Nat → Bool) (hx : ∀ k, 56 < k → x k = false) :
    ∃ t, t ≤ 100 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_of_chunks 56 101 18 (by decide) all_chunks x hx
  exact ⟨t, by omega, he, hz⟩

/-- The same with the bound `2 W + 8`. -/
theorem q01_width_le_56_linear (x : Nat → Bool) (hx : ∀ k, 56 < k → x k = false) :
    ∃ t, t ≤ 2 * 56 + 8 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_width_le_56 x hx
  exact ⟨t, by omega, he, hz⟩

/-- **`Q01` restricted to widths `≤ 56`**: no start supported at depths `≤ 56` is constrained. -/
theorem not_inX_of_width_le_56 (x : Nat → Bool) (hx : ∀ k, 56 < k → x k = false) : ¬ InX x := by
  intro hX
  obtain ⟨t, _, he, hz⟩ := q01_width_le_56 x hx
  have := hX (t / 2)
  rw [show 2 * (t / 2) = t by omega, hz] at this
  exact absurd this (by decide)

end Rule30ZeroBoundaryWidth56
end Ruliology.CellularAutomata

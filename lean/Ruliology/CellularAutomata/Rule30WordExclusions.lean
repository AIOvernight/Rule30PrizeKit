module

public import Ruliology.CellularAutomata.Rule30Certificates.WordExclusions

/-!
# Two eventual-word exclusions for the single-seed Rule 30 center column

The words `0000000001` and `00000001011` are impossible for every onset.
The two finite strip rank certificates and their kernel checks live in
`Rule30Certificates.WordExclusions`; this module applies the kit's soundness theorem.
These are @AIOvernight's previously submitted results, R30-20261023-30531b.
Research and formalization by OpenAI Codex for @AIOvernight.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Ruliology.CellularAutomata.Rule30WordExclusions
open Ruliology.CellularAutomata.Rule30StripCertificates
open Ruliology.CellularAutomata.Rule30Certificates.WordExclusions

theorem not_eventually_0000000001 : ¬ EventuallyWord c0000000001_w :=
  c0000000001.not_eventuallyWord c0000000001_check c0000000001_checkG (by decide) (by decide)

theorem not_eventually_00000001011 : ¬ EventuallyWord c00000001011_w :=
  c00000001011.not_eventuallyWord c00000001011_check c00000001011_checkG (by decide) (by decide)

end Ruliology.CellularAutomata.Rule30WordExclusions

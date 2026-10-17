import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `512` to `575`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 512, …, 575` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C32` –
`C35`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `512` to `527` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C32

theorem c512 : check 56 101 18 512 = true := by decide +kernel
theorem c513 : check 56 101 18 513 = true := by decide +kernel
theorem c514 : check 56 101 18 514 = true := by decide +kernel
theorem c515 : check 56 101 18 515 = true := by decide +kernel
theorem c516 : check 56 101 18 516 = true := by decide +kernel
theorem c517 : check 56 101 18 517 = true := by decide +kernel
theorem c518 : check 56 101 18 518 = true := by decide +kernel
theorem c519 : check 56 101 18 519 = true := by decide +kernel
theorem c520 : check 56 101 18 520 = true := by decide +kernel
theorem c521 : check 56 101 18 521 = true := by decide +kernel
theorem c522 : check 56 101 18 522 = true := by decide +kernel
theorem c523 : check 56 101 18 523 = true := by decide +kernel
theorem c524 : check 56 101 18 524 = true := by decide +kernel
theorem c525 : check 56 101 18 525 = true := by decide +kernel
theorem c526 : check 56 101 18 526 = true := by decide +kernel
theorem c527 : check 56 101 18 527 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 512 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c512) (chunksOK_one c513)) (chunksOK_append (chunksOK_one c514) (chunksOK_one c515))) (chunksOK_append (chunksOK_append (chunksOK_one c516) (chunksOK_one c517)) (chunksOK_append (chunksOK_one c518) (chunksOK_one c519)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c520) (chunksOK_one c521)) (chunksOK_append (chunksOK_one c522) (chunksOK_one c523))) (chunksOK_append (chunksOK_append (chunksOK_one c524) (chunksOK_one c525)) (chunksOK_append (chunksOK_one c526) (chunksOK_one c527)))))

end C32

/-! Kernel checks for `Q01` at width `56`: chunks `528` to `543` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C33

theorem c528 : check 56 101 18 528 = true := by decide +kernel
theorem c529 : check 56 101 18 529 = true := by decide +kernel
theorem c530 : check 56 101 18 530 = true := by decide +kernel
theorem c531 : check 56 101 18 531 = true := by decide +kernel
theorem c532 : check 56 101 18 532 = true := by decide +kernel
theorem c533 : check 56 101 18 533 = true := by decide +kernel
theorem c534 : check 56 101 18 534 = true := by decide +kernel
theorem c535 : check 56 101 18 535 = true := by decide +kernel
theorem c536 : check 56 101 18 536 = true := by decide +kernel
theorem c537 : check 56 101 18 537 = true := by decide +kernel
theorem c538 : check 56 101 18 538 = true := by decide +kernel
theorem c539 : check 56 101 18 539 = true := by decide +kernel
theorem c540 : check 56 101 18 540 = true := by decide +kernel
theorem c541 : check 56 101 18 541 = true := by decide +kernel
theorem c542 : check 56 101 18 542 = true := by decide +kernel
theorem c543 : check 56 101 18 543 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 528 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c528) (chunksOK_one c529)) (chunksOK_append (chunksOK_one c530) (chunksOK_one c531))) (chunksOK_append (chunksOK_append (chunksOK_one c532) (chunksOK_one c533)) (chunksOK_append (chunksOK_one c534) (chunksOK_one c535)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c536) (chunksOK_one c537)) (chunksOK_append (chunksOK_one c538) (chunksOK_one c539))) (chunksOK_append (chunksOK_append (chunksOK_one c540) (chunksOK_one c541)) (chunksOK_append (chunksOK_one c542) (chunksOK_one c543)))))

end C33

/-! Kernel checks for `Q01` at width `56`: chunks `544` to `559` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C34

theorem c544 : check 56 101 18 544 = true := by decide +kernel
theorem c545 : check 56 101 18 545 = true := by decide +kernel
theorem c546 : check 56 101 18 546 = true := by decide +kernel
theorem c547 : check 56 101 18 547 = true := by decide +kernel
theorem c548 : check 56 101 18 548 = true := by decide +kernel
theorem c549 : check 56 101 18 549 = true := by decide +kernel
theorem c550 : check 56 101 18 550 = true := by decide +kernel
theorem c551 : check 56 101 18 551 = true := by decide +kernel
theorem c552 : check 56 101 18 552 = true := by decide +kernel
theorem c553 : check 56 101 18 553 = true := by decide +kernel
theorem c554 : check 56 101 18 554 = true := by decide +kernel
theorem c555 : check 56 101 18 555 = true := by decide +kernel
theorem c556 : check 56 101 18 556 = true := by decide +kernel
theorem c557 : check 56 101 18 557 = true := by decide +kernel
theorem c558 : check 56 101 18 558 = true := by decide +kernel
theorem c559 : check 56 101 18 559 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 544 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c544) (chunksOK_one c545)) (chunksOK_append (chunksOK_one c546) (chunksOK_one c547))) (chunksOK_append (chunksOK_append (chunksOK_one c548) (chunksOK_one c549)) (chunksOK_append (chunksOK_one c550) (chunksOK_one c551)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c552) (chunksOK_one c553)) (chunksOK_append (chunksOK_one c554) (chunksOK_one c555))) (chunksOK_append (chunksOK_append (chunksOK_one c556) (chunksOK_one c557)) (chunksOK_append (chunksOK_one c558) (chunksOK_one c559)))))

end C34

/-! Kernel checks for `Q01` at width `56`: chunks `560` to `575` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C35

theorem c560 : check 56 101 18 560 = true := by decide +kernel
theorem c561 : check 56 101 18 561 = true := by decide +kernel
theorem c562 : check 56 101 18 562 = true := by decide +kernel
theorem c563 : check 56 101 18 563 = true := by decide +kernel
theorem c564 : check 56 101 18 564 = true := by decide +kernel
theorem c565 : check 56 101 18 565 = true := by decide +kernel
theorem c566 : check 56 101 18 566 = true := by decide +kernel
theorem c567 : check 56 101 18 567 = true := by decide +kernel
theorem c568 : check 56 101 18 568 = true := by decide +kernel
theorem c569 : check 56 101 18 569 = true := by decide +kernel
theorem c570 : check 56 101 18 570 = true := by decide +kernel
theorem c571 : check 56 101 18 571 = true := by decide +kernel
theorem c572 : check 56 101 18 572 = true := by decide +kernel
theorem c573 : check 56 101 18 573 = true := by decide +kernel
theorem c574 : check 56 101 18 574 = true := by decide +kernel
theorem c575 : check 56 101 18 575 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 560 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c560) (chunksOK_one c561)) (chunksOK_append (chunksOK_one c562) (chunksOK_one c563))) (chunksOK_append (chunksOK_append (chunksOK_one c564) (chunksOK_one c565)) (chunksOK_append (chunksOK_one c566) (chunksOK_one c567)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c568) (chunksOK_one c569)) (chunksOK_append (chunksOK_one c570) (chunksOK_one c571))) (chunksOK_append (chunksOK_append (chunksOK_one c572) (chunksOK_one c573)) (chunksOK_append (chunksOK_one c574) (chunksOK_one c575)))))

end C35

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

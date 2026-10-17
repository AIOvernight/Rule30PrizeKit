import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `576` to `639`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 576, …, 639` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C36` –
`C39`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `576` to `591` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C36

theorem c576 : check 56 101 18 576 = true := by decide +kernel
theorem c577 : check 56 101 18 577 = true := by decide +kernel
theorem c578 : check 56 101 18 578 = true := by decide +kernel
theorem c579 : check 56 101 18 579 = true := by decide +kernel
theorem c580 : check 56 101 18 580 = true := by decide +kernel
theorem c581 : check 56 101 18 581 = true := by decide +kernel
theorem c582 : check 56 101 18 582 = true := by decide +kernel
theorem c583 : check 56 101 18 583 = true := by decide +kernel
theorem c584 : check 56 101 18 584 = true := by decide +kernel
theorem c585 : check 56 101 18 585 = true := by decide +kernel
theorem c586 : check 56 101 18 586 = true := by decide +kernel
theorem c587 : check 56 101 18 587 = true := by decide +kernel
theorem c588 : check 56 101 18 588 = true := by decide +kernel
theorem c589 : check 56 101 18 589 = true := by decide +kernel
theorem c590 : check 56 101 18 590 = true := by decide +kernel
theorem c591 : check 56 101 18 591 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 576 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c576) (chunksOK_one c577)) (chunksOK_append (chunksOK_one c578) (chunksOK_one c579))) (chunksOK_append (chunksOK_append (chunksOK_one c580) (chunksOK_one c581)) (chunksOK_append (chunksOK_one c582) (chunksOK_one c583)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c584) (chunksOK_one c585)) (chunksOK_append (chunksOK_one c586) (chunksOK_one c587))) (chunksOK_append (chunksOK_append (chunksOK_one c588) (chunksOK_one c589)) (chunksOK_append (chunksOK_one c590) (chunksOK_one c591)))))

end C36

/-! Kernel checks for `Q01` at width `56`: chunks `592` to `607` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C37

theorem c592 : check 56 101 18 592 = true := by decide +kernel
theorem c593 : check 56 101 18 593 = true := by decide +kernel
theorem c594 : check 56 101 18 594 = true := by decide +kernel
theorem c595 : check 56 101 18 595 = true := by decide +kernel
theorem c596 : check 56 101 18 596 = true := by decide +kernel
theorem c597 : check 56 101 18 597 = true := by decide +kernel
theorem c598 : check 56 101 18 598 = true := by decide +kernel
theorem c599 : check 56 101 18 599 = true := by decide +kernel
theorem c600 : check 56 101 18 600 = true := by decide +kernel
theorem c601 : check 56 101 18 601 = true := by decide +kernel
theorem c602 : check 56 101 18 602 = true := by decide +kernel
theorem c603 : check 56 101 18 603 = true := by decide +kernel
theorem c604 : check 56 101 18 604 = true := by decide +kernel
theorem c605 : check 56 101 18 605 = true := by decide +kernel
theorem c606 : check 56 101 18 606 = true := by decide +kernel
theorem c607 : check 56 101 18 607 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 592 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c592) (chunksOK_one c593)) (chunksOK_append (chunksOK_one c594) (chunksOK_one c595))) (chunksOK_append (chunksOK_append (chunksOK_one c596) (chunksOK_one c597)) (chunksOK_append (chunksOK_one c598) (chunksOK_one c599)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c600) (chunksOK_one c601)) (chunksOK_append (chunksOK_one c602) (chunksOK_one c603))) (chunksOK_append (chunksOK_append (chunksOK_one c604) (chunksOK_one c605)) (chunksOK_append (chunksOK_one c606) (chunksOK_one c607)))))

end C37

/-! Kernel checks for `Q01` at width `56`: chunks `608` to `623` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C38

theorem c608 : check 56 101 18 608 = true := by decide +kernel
theorem c609 : check 56 101 18 609 = true := by decide +kernel
theorem c610 : check 56 101 18 610 = true := by decide +kernel
theorem c611 : check 56 101 18 611 = true := by decide +kernel
theorem c612 : check 56 101 18 612 = true := by decide +kernel
theorem c613 : check 56 101 18 613 = true := by decide +kernel
theorem c614 : check 56 101 18 614 = true := by decide +kernel
theorem c615 : check 56 101 18 615 = true := by decide +kernel
theorem c616 : check 56 101 18 616 = true := by decide +kernel
theorem c617 : check 56 101 18 617 = true := by decide +kernel
theorem c618 : check 56 101 18 618 = true := by decide +kernel
theorem c619 : check 56 101 18 619 = true := by decide +kernel
theorem c620 : check 56 101 18 620 = true := by decide +kernel
theorem c621 : check 56 101 18 621 = true := by decide +kernel
theorem c622 : check 56 101 18 622 = true := by decide +kernel
theorem c623 : check 56 101 18 623 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 608 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c608) (chunksOK_one c609)) (chunksOK_append (chunksOK_one c610) (chunksOK_one c611))) (chunksOK_append (chunksOK_append (chunksOK_one c612) (chunksOK_one c613)) (chunksOK_append (chunksOK_one c614) (chunksOK_one c615)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c616) (chunksOK_one c617)) (chunksOK_append (chunksOK_one c618) (chunksOK_one c619))) (chunksOK_append (chunksOK_append (chunksOK_one c620) (chunksOK_one c621)) (chunksOK_append (chunksOK_one c622) (chunksOK_one c623)))))

end C38

/-! Kernel checks for `Q01` at width `56`: chunks `624` to `639` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C39

theorem c624 : check 56 101 18 624 = true := by decide +kernel
theorem c625 : check 56 101 18 625 = true := by decide +kernel
theorem c626 : check 56 101 18 626 = true := by decide +kernel
theorem c627 : check 56 101 18 627 = true := by decide +kernel
theorem c628 : check 56 101 18 628 = true := by decide +kernel
theorem c629 : check 56 101 18 629 = true := by decide +kernel
theorem c630 : check 56 101 18 630 = true := by decide +kernel
theorem c631 : check 56 101 18 631 = true := by decide +kernel
theorem c632 : check 56 101 18 632 = true := by decide +kernel
theorem c633 : check 56 101 18 633 = true := by decide +kernel
theorem c634 : check 56 101 18 634 = true := by decide +kernel
theorem c635 : check 56 101 18 635 = true := by decide +kernel
theorem c636 : check 56 101 18 636 = true := by decide +kernel
theorem c637 : check 56 101 18 637 = true := by decide +kernel
theorem c638 : check 56 101 18 638 = true := by decide +kernel
theorem c639 : check 56 101 18 639 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 624 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c624) (chunksOK_one c625)) (chunksOK_append (chunksOK_one c626) (chunksOK_one c627))) (chunksOK_append (chunksOK_append (chunksOK_one c628) (chunksOK_one c629)) (chunksOK_append (chunksOK_one c630) (chunksOK_one c631)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c632) (chunksOK_one c633)) (chunksOK_append (chunksOK_one c634) (chunksOK_one c635))) (chunksOK_append (chunksOK_append (chunksOK_one c636) (chunksOK_one c637)) (chunksOK_append (chunksOK_one c638) (chunksOK_one c639)))))

end C39

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

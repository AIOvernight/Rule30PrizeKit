import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `640` to `703`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 640, …, 703` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C40` –
`C43`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `640` to `655` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C40

theorem c640 : check 56 101 18 640 = true := by decide +kernel
theorem c641 : check 56 101 18 641 = true := by decide +kernel
theorem c642 : check 56 101 18 642 = true := by decide +kernel
theorem c643 : check 56 101 18 643 = true := by decide +kernel
theorem c644 : check 56 101 18 644 = true := by decide +kernel
theorem c645 : check 56 101 18 645 = true := by decide +kernel
theorem c646 : check 56 101 18 646 = true := by decide +kernel
theorem c647 : check 56 101 18 647 = true := by decide +kernel
theorem c648 : check 56 101 18 648 = true := by decide +kernel
theorem c649 : check 56 101 18 649 = true := by decide +kernel
theorem c650 : check 56 101 18 650 = true := by decide +kernel
theorem c651 : check 56 101 18 651 = true := by decide +kernel
theorem c652 : check 56 101 18 652 = true := by decide +kernel
theorem c653 : check 56 101 18 653 = true := by decide +kernel
theorem c654 : check 56 101 18 654 = true := by decide +kernel
theorem c655 : check 56 101 18 655 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 640 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c640) (chunksOK_one c641)) (chunksOK_append (chunksOK_one c642) (chunksOK_one c643))) (chunksOK_append (chunksOK_append (chunksOK_one c644) (chunksOK_one c645)) (chunksOK_append (chunksOK_one c646) (chunksOK_one c647)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c648) (chunksOK_one c649)) (chunksOK_append (chunksOK_one c650) (chunksOK_one c651))) (chunksOK_append (chunksOK_append (chunksOK_one c652) (chunksOK_one c653)) (chunksOK_append (chunksOK_one c654) (chunksOK_one c655)))))

end C40

/-! Kernel checks for `Q01` at width `56`: chunks `656` to `671` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C41

theorem c656 : check 56 101 18 656 = true := by decide +kernel
theorem c657 : check 56 101 18 657 = true := by decide +kernel
theorem c658 : check 56 101 18 658 = true := by decide +kernel
theorem c659 : check 56 101 18 659 = true := by decide +kernel
theorem c660 : check 56 101 18 660 = true := by decide +kernel
theorem c661 : check 56 101 18 661 = true := by decide +kernel
theorem c662 : check 56 101 18 662 = true := by decide +kernel
theorem c663 : check 56 101 18 663 = true := by decide +kernel
theorem c664 : check 56 101 18 664 = true := by decide +kernel
theorem c665 : check 56 101 18 665 = true := by decide +kernel
theorem c666 : check 56 101 18 666 = true := by decide +kernel
theorem c667 : check 56 101 18 667 = true := by decide +kernel
theorem c668 : check 56 101 18 668 = true := by decide +kernel
theorem c669 : check 56 101 18 669 = true := by decide +kernel
theorem c670 : check 56 101 18 670 = true := by decide +kernel
theorem c671 : check 56 101 18 671 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 656 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c656) (chunksOK_one c657)) (chunksOK_append (chunksOK_one c658) (chunksOK_one c659))) (chunksOK_append (chunksOK_append (chunksOK_one c660) (chunksOK_one c661)) (chunksOK_append (chunksOK_one c662) (chunksOK_one c663)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c664) (chunksOK_one c665)) (chunksOK_append (chunksOK_one c666) (chunksOK_one c667))) (chunksOK_append (chunksOK_append (chunksOK_one c668) (chunksOK_one c669)) (chunksOK_append (chunksOK_one c670) (chunksOK_one c671)))))

end C41

/-! Kernel checks for `Q01` at width `56`: chunks `672` to `687` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C42

theorem c672 : check 56 101 18 672 = true := by decide +kernel
theorem c673 : check 56 101 18 673 = true := by decide +kernel
theorem c674 : check 56 101 18 674 = true := by decide +kernel
theorem c675 : check 56 101 18 675 = true := by decide +kernel
theorem c676 : check 56 101 18 676 = true := by decide +kernel
theorem c677 : check 56 101 18 677 = true := by decide +kernel
theorem c678 : check 56 101 18 678 = true := by decide +kernel
theorem c679 : check 56 101 18 679 = true := by decide +kernel
theorem c680 : check 56 101 18 680 = true := by decide +kernel
theorem c681 : check 56 101 18 681 = true := by decide +kernel
theorem c682 : check 56 101 18 682 = true := by decide +kernel
theorem c683 : check 56 101 18 683 = true := by decide +kernel
theorem c684 : check 56 101 18 684 = true := by decide +kernel
theorem c685 : check 56 101 18 685 = true := by decide +kernel
theorem c686 : check 56 101 18 686 = true := by decide +kernel
theorem c687 : check 56 101 18 687 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 672 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c672) (chunksOK_one c673)) (chunksOK_append (chunksOK_one c674) (chunksOK_one c675))) (chunksOK_append (chunksOK_append (chunksOK_one c676) (chunksOK_one c677)) (chunksOK_append (chunksOK_one c678) (chunksOK_one c679)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c680) (chunksOK_one c681)) (chunksOK_append (chunksOK_one c682) (chunksOK_one c683))) (chunksOK_append (chunksOK_append (chunksOK_one c684) (chunksOK_one c685)) (chunksOK_append (chunksOK_one c686) (chunksOK_one c687)))))

end C42

/-! Kernel checks for `Q01` at width `56`: chunks `688` to `703` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C43

theorem c688 : check 56 101 18 688 = true := by decide +kernel
theorem c689 : check 56 101 18 689 = true := by decide +kernel
theorem c690 : check 56 101 18 690 = true := by decide +kernel
theorem c691 : check 56 101 18 691 = true := by decide +kernel
theorem c692 : check 56 101 18 692 = true := by decide +kernel
theorem c693 : check 56 101 18 693 = true := by decide +kernel
theorem c694 : check 56 101 18 694 = true := by decide +kernel
theorem c695 : check 56 101 18 695 = true := by decide +kernel
theorem c696 : check 56 101 18 696 = true := by decide +kernel
theorem c697 : check 56 101 18 697 = true := by decide +kernel
theorem c698 : check 56 101 18 698 = true := by decide +kernel
theorem c699 : check 56 101 18 699 = true := by decide +kernel
theorem c700 : check 56 101 18 700 = true := by decide +kernel
theorem c701 : check 56 101 18 701 = true := by decide +kernel
theorem c702 : check 56 101 18 702 = true := by decide +kernel
theorem c703 : check 56 101 18 703 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 688 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c688) (chunksOK_one c689)) (chunksOK_append (chunksOK_one c690) (chunksOK_one c691))) (chunksOK_append (chunksOK_append (chunksOK_one c692) (chunksOK_one c693)) (chunksOK_append (chunksOK_one c694) (chunksOK_one c695)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c696) (chunksOK_one c697)) (chunksOK_append (chunksOK_one c698) (chunksOK_one c699))) (chunksOK_append (chunksOK_append (chunksOK_one c700) (chunksOK_one c701)) (chunksOK_append (chunksOK_one c702) (chunksOK_one c703)))))

end C43

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

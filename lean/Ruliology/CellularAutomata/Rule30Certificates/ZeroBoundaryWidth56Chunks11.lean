import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `704` to `767`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 704, …, 767` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C44` –
`C47`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `704` to `719` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C44

theorem c704 : check 56 101 18 704 = true := by decide +kernel
theorem c705 : check 56 101 18 705 = true := by decide +kernel
theorem c706 : check 56 101 18 706 = true := by decide +kernel
theorem c707 : check 56 101 18 707 = true := by decide +kernel
theorem c708 : check 56 101 18 708 = true := by decide +kernel
theorem c709 : check 56 101 18 709 = true := by decide +kernel
theorem c710 : check 56 101 18 710 = true := by decide +kernel
theorem c711 : check 56 101 18 711 = true := by decide +kernel
theorem c712 : check 56 101 18 712 = true := by decide +kernel
theorem c713 : check 56 101 18 713 = true := by decide +kernel
theorem c714 : check 56 101 18 714 = true := by decide +kernel
theorem c715 : check 56 101 18 715 = true := by decide +kernel
theorem c716 : check 56 101 18 716 = true := by decide +kernel
theorem c717 : check 56 101 18 717 = true := by decide +kernel
theorem c718 : check 56 101 18 718 = true := by decide +kernel
theorem c719 : check 56 101 18 719 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 704 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c704) (chunksOK_one c705)) (chunksOK_append (chunksOK_one c706) (chunksOK_one c707))) (chunksOK_append (chunksOK_append (chunksOK_one c708) (chunksOK_one c709)) (chunksOK_append (chunksOK_one c710) (chunksOK_one c711)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c712) (chunksOK_one c713)) (chunksOK_append (chunksOK_one c714) (chunksOK_one c715))) (chunksOK_append (chunksOK_append (chunksOK_one c716) (chunksOK_one c717)) (chunksOK_append (chunksOK_one c718) (chunksOK_one c719)))))

end C44

/-! Kernel checks for `Q01` at width `56`: chunks `720` to `735` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C45

theorem c720 : check 56 101 18 720 = true := by decide +kernel
theorem c721 : check 56 101 18 721 = true := by decide +kernel
theorem c722 : check 56 101 18 722 = true := by decide +kernel
theorem c723 : check 56 101 18 723 = true := by decide +kernel
theorem c724 : check 56 101 18 724 = true := by decide +kernel
theorem c725 : check 56 101 18 725 = true := by decide +kernel
theorem c726 : check 56 101 18 726 = true := by decide +kernel
theorem c727 : check 56 101 18 727 = true := by decide +kernel
theorem c728 : check 56 101 18 728 = true := by decide +kernel
theorem c729 : check 56 101 18 729 = true := by decide +kernel
theorem c730 : check 56 101 18 730 = true := by decide +kernel
theorem c731 : check 56 101 18 731 = true := by decide +kernel
theorem c732 : check 56 101 18 732 = true := by decide +kernel
theorem c733 : check 56 101 18 733 = true := by decide +kernel
theorem c734 : check 56 101 18 734 = true := by decide +kernel
theorem c735 : check 56 101 18 735 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 720 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c720) (chunksOK_one c721)) (chunksOK_append (chunksOK_one c722) (chunksOK_one c723))) (chunksOK_append (chunksOK_append (chunksOK_one c724) (chunksOK_one c725)) (chunksOK_append (chunksOK_one c726) (chunksOK_one c727)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c728) (chunksOK_one c729)) (chunksOK_append (chunksOK_one c730) (chunksOK_one c731))) (chunksOK_append (chunksOK_append (chunksOK_one c732) (chunksOK_one c733)) (chunksOK_append (chunksOK_one c734) (chunksOK_one c735)))))

end C45

/-! Kernel checks for `Q01` at width `56`: chunks `736` to `751` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C46

theorem c736 : check 56 101 18 736 = true := by decide +kernel
theorem c737 : check 56 101 18 737 = true := by decide +kernel
theorem c738 : check 56 101 18 738 = true := by decide +kernel
theorem c739 : check 56 101 18 739 = true := by decide +kernel
theorem c740 : check 56 101 18 740 = true := by decide +kernel
theorem c741 : check 56 101 18 741 = true := by decide +kernel
theorem c742 : check 56 101 18 742 = true := by decide +kernel
theorem c743 : check 56 101 18 743 = true := by decide +kernel
theorem c744 : check 56 101 18 744 = true := by decide +kernel
theorem c745 : check 56 101 18 745 = true := by decide +kernel
theorem c746 : check 56 101 18 746 = true := by decide +kernel
theorem c747 : check 56 101 18 747 = true := by decide +kernel
theorem c748 : check 56 101 18 748 = true := by decide +kernel
theorem c749 : check 56 101 18 749 = true := by decide +kernel
theorem c750 : check 56 101 18 750 = true := by decide +kernel
theorem c751 : check 56 101 18 751 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 736 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c736) (chunksOK_one c737)) (chunksOK_append (chunksOK_one c738) (chunksOK_one c739))) (chunksOK_append (chunksOK_append (chunksOK_one c740) (chunksOK_one c741)) (chunksOK_append (chunksOK_one c742) (chunksOK_one c743)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c744) (chunksOK_one c745)) (chunksOK_append (chunksOK_one c746) (chunksOK_one c747))) (chunksOK_append (chunksOK_append (chunksOK_one c748) (chunksOK_one c749)) (chunksOK_append (chunksOK_one c750) (chunksOK_one c751)))))

end C46

/-! Kernel checks for `Q01` at width `56`: chunks `752` to `767` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C47

theorem c752 : check 56 101 18 752 = true := by decide +kernel
theorem c753 : check 56 101 18 753 = true := by decide +kernel
theorem c754 : check 56 101 18 754 = true := by decide +kernel
theorem c755 : check 56 101 18 755 = true := by decide +kernel
theorem c756 : check 56 101 18 756 = true := by decide +kernel
theorem c757 : check 56 101 18 757 = true := by decide +kernel
theorem c758 : check 56 101 18 758 = true := by decide +kernel
theorem c759 : check 56 101 18 759 = true := by decide +kernel
theorem c760 : check 56 101 18 760 = true := by decide +kernel
theorem c761 : check 56 101 18 761 = true := by decide +kernel
theorem c762 : check 56 101 18 762 = true := by decide +kernel
theorem c763 : check 56 101 18 763 = true := by decide +kernel
theorem c764 : check 56 101 18 764 = true := by decide +kernel
theorem c765 : check 56 101 18 765 = true := by decide +kernel
theorem c766 : check 56 101 18 766 = true := by decide +kernel
theorem c767 : check 56 101 18 767 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 752 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c752) (chunksOK_one c753)) (chunksOK_append (chunksOK_one c754) (chunksOK_one c755))) (chunksOK_append (chunksOK_append (chunksOK_one c756) (chunksOK_one c757)) (chunksOK_append (chunksOK_one c758) (chunksOK_one c759)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c760) (chunksOK_one c761)) (chunksOK_append (chunksOK_one c762) (chunksOK_one c763))) (chunksOK_append (chunksOK_append (chunksOK_one c764) (chunksOK_one c765)) (chunksOK_append (chunksOK_one c766) (chunksOK_one c767)))))

end C47

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

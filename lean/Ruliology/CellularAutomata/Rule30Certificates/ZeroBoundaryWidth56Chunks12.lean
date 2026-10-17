import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `768` to `831`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 768, …, 831` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C48` –
`C51`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `768` to `783` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C48

theorem c768 : check 56 101 18 768 = true := by decide +kernel
theorem c769 : check 56 101 18 769 = true := by decide +kernel
theorem c770 : check 56 101 18 770 = true := by decide +kernel
theorem c771 : check 56 101 18 771 = true := by decide +kernel
theorem c772 : check 56 101 18 772 = true := by decide +kernel
theorem c773 : check 56 101 18 773 = true := by decide +kernel
theorem c774 : check 56 101 18 774 = true := by decide +kernel
theorem c775 : check 56 101 18 775 = true := by decide +kernel
theorem c776 : check 56 101 18 776 = true := by decide +kernel
theorem c777 : check 56 101 18 777 = true := by decide +kernel
theorem c778 : check 56 101 18 778 = true := by decide +kernel
theorem c779 : check 56 101 18 779 = true := by decide +kernel
theorem c780 : check 56 101 18 780 = true := by decide +kernel
theorem c781 : check 56 101 18 781 = true := by decide +kernel
theorem c782 : check 56 101 18 782 = true := by decide +kernel
theorem c783 : check 56 101 18 783 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 768 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c768) (chunksOK_one c769)) (chunksOK_append (chunksOK_one c770) (chunksOK_one c771))) (chunksOK_append (chunksOK_append (chunksOK_one c772) (chunksOK_one c773)) (chunksOK_append (chunksOK_one c774) (chunksOK_one c775)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c776) (chunksOK_one c777)) (chunksOK_append (chunksOK_one c778) (chunksOK_one c779))) (chunksOK_append (chunksOK_append (chunksOK_one c780) (chunksOK_one c781)) (chunksOK_append (chunksOK_one c782) (chunksOK_one c783)))))

end C48

/-! Kernel checks for `Q01` at width `56`: chunks `784` to `799` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C49

theorem c784 : check 56 101 18 784 = true := by decide +kernel
theorem c785 : check 56 101 18 785 = true := by decide +kernel
theorem c786 : check 56 101 18 786 = true := by decide +kernel
theorem c787 : check 56 101 18 787 = true := by decide +kernel
theorem c788 : check 56 101 18 788 = true := by decide +kernel
theorem c789 : check 56 101 18 789 = true := by decide +kernel
theorem c790 : check 56 101 18 790 = true := by decide +kernel
theorem c791 : check 56 101 18 791 = true := by decide +kernel
theorem c792 : check 56 101 18 792 = true := by decide +kernel
theorem c793 : check 56 101 18 793 = true := by decide +kernel
theorem c794 : check 56 101 18 794 = true := by decide +kernel
theorem c795 : check 56 101 18 795 = true := by decide +kernel
theorem c796 : check 56 101 18 796 = true := by decide +kernel
theorem c797 : check 56 101 18 797 = true := by decide +kernel
theorem c798 : check 56 101 18 798 = true := by decide +kernel
theorem c799 : check 56 101 18 799 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 784 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c784) (chunksOK_one c785)) (chunksOK_append (chunksOK_one c786) (chunksOK_one c787))) (chunksOK_append (chunksOK_append (chunksOK_one c788) (chunksOK_one c789)) (chunksOK_append (chunksOK_one c790) (chunksOK_one c791)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c792) (chunksOK_one c793)) (chunksOK_append (chunksOK_one c794) (chunksOK_one c795))) (chunksOK_append (chunksOK_append (chunksOK_one c796) (chunksOK_one c797)) (chunksOK_append (chunksOK_one c798) (chunksOK_one c799)))))

end C49

/-! Kernel checks for `Q01` at width `56`: chunks `800` to `815` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C50

theorem c800 : check 56 101 18 800 = true := by decide +kernel
theorem c801 : check 56 101 18 801 = true := by decide +kernel
theorem c802 : check 56 101 18 802 = true := by decide +kernel
theorem c803 : check 56 101 18 803 = true := by decide +kernel
theorem c804 : check 56 101 18 804 = true := by decide +kernel
theorem c805 : check 56 101 18 805 = true := by decide +kernel
theorem c806 : check 56 101 18 806 = true := by decide +kernel
theorem c807 : check 56 101 18 807 = true := by decide +kernel
theorem c808 : check 56 101 18 808 = true := by decide +kernel
theorem c809 : check 56 101 18 809 = true := by decide +kernel
theorem c810 : check 56 101 18 810 = true := by decide +kernel
theorem c811 : check 56 101 18 811 = true := by decide +kernel
theorem c812 : check 56 101 18 812 = true := by decide +kernel
theorem c813 : check 56 101 18 813 = true := by decide +kernel
theorem c814 : check 56 101 18 814 = true := by decide +kernel
theorem c815 : check 56 101 18 815 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 800 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c800) (chunksOK_one c801)) (chunksOK_append (chunksOK_one c802) (chunksOK_one c803))) (chunksOK_append (chunksOK_append (chunksOK_one c804) (chunksOK_one c805)) (chunksOK_append (chunksOK_one c806) (chunksOK_one c807)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c808) (chunksOK_one c809)) (chunksOK_append (chunksOK_one c810) (chunksOK_one c811))) (chunksOK_append (chunksOK_append (chunksOK_one c812) (chunksOK_one c813)) (chunksOK_append (chunksOK_one c814) (chunksOK_one c815)))))

end C50

/-! Kernel checks for `Q01` at width `56`: chunks `816` to `831` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C51

theorem c816 : check 56 101 18 816 = true := by decide +kernel
theorem c817 : check 56 101 18 817 = true := by decide +kernel
theorem c818 : check 56 101 18 818 = true := by decide +kernel
theorem c819 : check 56 101 18 819 = true := by decide +kernel
theorem c820 : check 56 101 18 820 = true := by decide +kernel
theorem c821 : check 56 101 18 821 = true := by decide +kernel
theorem c822 : check 56 101 18 822 = true := by decide +kernel
theorem c823 : check 56 101 18 823 = true := by decide +kernel
theorem c824 : check 56 101 18 824 = true := by decide +kernel
theorem c825 : check 56 101 18 825 = true := by decide +kernel
theorem c826 : check 56 101 18 826 = true := by decide +kernel
theorem c827 : check 56 101 18 827 = true := by decide +kernel
theorem c828 : check 56 101 18 828 = true := by decide +kernel
theorem c829 : check 56 101 18 829 = true := by decide +kernel
theorem c830 : check 56 101 18 830 = true := by decide +kernel
theorem c831 : check 56 101 18 831 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 816 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c816) (chunksOK_one c817)) (chunksOK_append (chunksOK_one c818) (chunksOK_one c819))) (chunksOK_append (chunksOK_append (chunksOK_one c820) (chunksOK_one c821)) (chunksOK_append (chunksOK_one c822) (chunksOK_one c823)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c824) (chunksOK_one c825)) (chunksOK_append (chunksOK_one c826) (chunksOK_one c827))) (chunksOK_append (chunksOK_append (chunksOK_one c828) (chunksOK_one c829)) (chunksOK_append (chunksOK_one c830) (chunksOK_one c831)))))

end C51

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

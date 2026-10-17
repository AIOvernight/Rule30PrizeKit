import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `832` to `895`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 832, …, 895` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C52` –
`C55`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `832` to `847` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C52

theorem c832 : check 56 101 18 832 = true := by decide +kernel
theorem c833 : check 56 101 18 833 = true := by decide +kernel
theorem c834 : check 56 101 18 834 = true := by decide +kernel
theorem c835 : check 56 101 18 835 = true := by decide +kernel
theorem c836 : check 56 101 18 836 = true := by decide +kernel
theorem c837 : check 56 101 18 837 = true := by decide +kernel
theorem c838 : check 56 101 18 838 = true := by decide +kernel
theorem c839 : check 56 101 18 839 = true := by decide +kernel
theorem c840 : check 56 101 18 840 = true := by decide +kernel
theorem c841 : check 56 101 18 841 = true := by decide +kernel
theorem c842 : check 56 101 18 842 = true := by decide +kernel
theorem c843 : check 56 101 18 843 = true := by decide +kernel
theorem c844 : check 56 101 18 844 = true := by decide +kernel
theorem c845 : check 56 101 18 845 = true := by decide +kernel
theorem c846 : check 56 101 18 846 = true := by decide +kernel
theorem c847 : check 56 101 18 847 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 832 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c832) (chunksOK_one c833)) (chunksOK_append (chunksOK_one c834) (chunksOK_one c835))) (chunksOK_append (chunksOK_append (chunksOK_one c836) (chunksOK_one c837)) (chunksOK_append (chunksOK_one c838) (chunksOK_one c839)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c840) (chunksOK_one c841)) (chunksOK_append (chunksOK_one c842) (chunksOK_one c843))) (chunksOK_append (chunksOK_append (chunksOK_one c844) (chunksOK_one c845)) (chunksOK_append (chunksOK_one c846) (chunksOK_one c847)))))

end C52

/-! Kernel checks for `Q01` at width `56`: chunks `848` to `863` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C53

theorem c848 : check 56 101 18 848 = true := by decide +kernel
theorem c849 : check 56 101 18 849 = true := by decide +kernel
theorem c850 : check 56 101 18 850 = true := by decide +kernel
theorem c851 : check 56 101 18 851 = true := by decide +kernel
theorem c852 : check 56 101 18 852 = true := by decide +kernel
theorem c853 : check 56 101 18 853 = true := by decide +kernel
theorem c854 : check 56 101 18 854 = true := by decide +kernel
theorem c855 : check 56 101 18 855 = true := by decide +kernel
theorem c856 : check 56 101 18 856 = true := by decide +kernel
theorem c857 : check 56 101 18 857 = true := by decide +kernel
theorem c858 : check 56 101 18 858 = true := by decide +kernel
theorem c859 : check 56 101 18 859 = true := by decide +kernel
theorem c860 : check 56 101 18 860 = true := by decide +kernel
theorem c861 : check 56 101 18 861 = true := by decide +kernel
theorem c862 : check 56 101 18 862 = true := by decide +kernel
theorem c863 : check 56 101 18 863 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 848 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c848) (chunksOK_one c849)) (chunksOK_append (chunksOK_one c850) (chunksOK_one c851))) (chunksOK_append (chunksOK_append (chunksOK_one c852) (chunksOK_one c853)) (chunksOK_append (chunksOK_one c854) (chunksOK_one c855)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c856) (chunksOK_one c857)) (chunksOK_append (chunksOK_one c858) (chunksOK_one c859))) (chunksOK_append (chunksOK_append (chunksOK_one c860) (chunksOK_one c861)) (chunksOK_append (chunksOK_one c862) (chunksOK_one c863)))))

end C53

/-! Kernel checks for `Q01` at width `56`: chunks `864` to `879` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C54

theorem c864 : check 56 101 18 864 = true := by decide +kernel
theorem c865 : check 56 101 18 865 = true := by decide +kernel
theorem c866 : check 56 101 18 866 = true := by decide +kernel
theorem c867 : check 56 101 18 867 = true := by decide +kernel
theorem c868 : check 56 101 18 868 = true := by decide +kernel
theorem c869 : check 56 101 18 869 = true := by decide +kernel
theorem c870 : check 56 101 18 870 = true := by decide +kernel
theorem c871 : check 56 101 18 871 = true := by decide +kernel
theorem c872 : check 56 101 18 872 = true := by decide +kernel
theorem c873 : check 56 101 18 873 = true := by decide +kernel
theorem c874 : check 56 101 18 874 = true := by decide +kernel
theorem c875 : check 56 101 18 875 = true := by decide +kernel
theorem c876 : check 56 101 18 876 = true := by decide +kernel
theorem c877 : check 56 101 18 877 = true := by decide +kernel
theorem c878 : check 56 101 18 878 = true := by decide +kernel
theorem c879 : check 56 101 18 879 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 864 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c864) (chunksOK_one c865)) (chunksOK_append (chunksOK_one c866) (chunksOK_one c867))) (chunksOK_append (chunksOK_append (chunksOK_one c868) (chunksOK_one c869)) (chunksOK_append (chunksOK_one c870) (chunksOK_one c871)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c872) (chunksOK_one c873)) (chunksOK_append (chunksOK_one c874) (chunksOK_one c875))) (chunksOK_append (chunksOK_append (chunksOK_one c876) (chunksOK_one c877)) (chunksOK_append (chunksOK_one c878) (chunksOK_one c879)))))

end C54

/-! Kernel checks for `Q01` at width `56`: chunks `880` to `895` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C55

theorem c880 : check 56 101 18 880 = true := by decide +kernel
theorem c881 : check 56 101 18 881 = true := by decide +kernel
theorem c882 : check 56 101 18 882 = true := by decide +kernel
theorem c883 : check 56 101 18 883 = true := by decide +kernel
theorem c884 : check 56 101 18 884 = true := by decide +kernel
theorem c885 : check 56 101 18 885 = true := by decide +kernel
theorem c886 : check 56 101 18 886 = true := by decide +kernel
theorem c887 : check 56 101 18 887 = true := by decide +kernel
theorem c888 : check 56 101 18 888 = true := by decide +kernel
theorem c889 : check 56 101 18 889 = true := by decide +kernel
theorem c890 : check 56 101 18 890 = true := by decide +kernel
theorem c891 : check 56 101 18 891 = true := by decide +kernel
theorem c892 : check 56 101 18 892 = true := by decide +kernel
theorem c893 : check 56 101 18 893 = true := by decide +kernel
theorem c894 : check 56 101 18 894 = true := by decide +kernel
theorem c895 : check 56 101 18 895 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 880 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c880) (chunksOK_one c881)) (chunksOK_append (chunksOK_one c882) (chunksOK_one c883))) (chunksOK_append (chunksOK_append (chunksOK_one c884) (chunksOK_one c885)) (chunksOK_append (chunksOK_one c886) (chunksOK_one c887)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c888) (chunksOK_one c889)) (chunksOK_append (chunksOK_one c890) (chunksOK_one c891))) (chunksOK_append (chunksOK_append (chunksOK_one c892) (chunksOK_one c893)) (chunksOK_append (chunksOK_one c894) (chunksOK_one c895)))))

end C55

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

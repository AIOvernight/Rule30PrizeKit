import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `896` to `959`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 896, …, 959` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C56` –
`C59`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `896` to `911` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C56

theorem c896 : check 56 101 18 896 = true := by decide +kernel
theorem c897 : check 56 101 18 897 = true := by decide +kernel
theorem c898 : check 56 101 18 898 = true := by decide +kernel
theorem c899 : check 56 101 18 899 = true := by decide +kernel
theorem c900 : check 56 101 18 900 = true := by decide +kernel
theorem c901 : check 56 101 18 901 = true := by decide +kernel
theorem c902 : check 56 101 18 902 = true := by decide +kernel
theorem c903 : check 56 101 18 903 = true := by decide +kernel
theorem c904 : check 56 101 18 904 = true := by decide +kernel
theorem c905 : check 56 101 18 905 = true := by decide +kernel
theorem c906 : check 56 101 18 906 = true := by decide +kernel
theorem c907 : check 56 101 18 907 = true := by decide +kernel
theorem c908 : check 56 101 18 908 = true := by decide +kernel
theorem c909 : check 56 101 18 909 = true := by decide +kernel
theorem c910 : check 56 101 18 910 = true := by decide +kernel
theorem c911 : check 56 101 18 911 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 896 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c896) (chunksOK_one c897)) (chunksOK_append (chunksOK_one c898) (chunksOK_one c899))) (chunksOK_append (chunksOK_append (chunksOK_one c900) (chunksOK_one c901)) (chunksOK_append (chunksOK_one c902) (chunksOK_one c903)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c904) (chunksOK_one c905)) (chunksOK_append (chunksOK_one c906) (chunksOK_one c907))) (chunksOK_append (chunksOK_append (chunksOK_one c908) (chunksOK_one c909)) (chunksOK_append (chunksOK_one c910) (chunksOK_one c911)))))

end C56

/-! Kernel checks for `Q01` at width `56`: chunks `912` to `927` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C57

theorem c912 : check 56 101 18 912 = true := by decide +kernel
theorem c913 : check 56 101 18 913 = true := by decide +kernel
theorem c914 : check 56 101 18 914 = true := by decide +kernel
theorem c915 : check 56 101 18 915 = true := by decide +kernel
theorem c916 : check 56 101 18 916 = true := by decide +kernel
theorem c917 : check 56 101 18 917 = true := by decide +kernel
theorem c918 : check 56 101 18 918 = true := by decide +kernel
theorem c919 : check 56 101 18 919 = true := by decide +kernel
theorem c920 : check 56 101 18 920 = true := by decide +kernel
theorem c921 : check 56 101 18 921 = true := by decide +kernel
theorem c922 : check 56 101 18 922 = true := by decide +kernel
theorem c923 : check 56 101 18 923 = true := by decide +kernel
theorem c924 : check 56 101 18 924 = true := by decide +kernel
theorem c925 : check 56 101 18 925 = true := by decide +kernel
theorem c926 : check 56 101 18 926 = true := by decide +kernel
theorem c927 : check 56 101 18 927 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 912 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c912) (chunksOK_one c913)) (chunksOK_append (chunksOK_one c914) (chunksOK_one c915))) (chunksOK_append (chunksOK_append (chunksOK_one c916) (chunksOK_one c917)) (chunksOK_append (chunksOK_one c918) (chunksOK_one c919)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c920) (chunksOK_one c921)) (chunksOK_append (chunksOK_one c922) (chunksOK_one c923))) (chunksOK_append (chunksOK_append (chunksOK_one c924) (chunksOK_one c925)) (chunksOK_append (chunksOK_one c926) (chunksOK_one c927)))))

end C57

/-! Kernel checks for `Q01` at width `56`: chunks `928` to `943` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C58

theorem c928 : check 56 101 18 928 = true := by decide +kernel
theorem c929 : check 56 101 18 929 = true := by decide +kernel
theorem c930 : check 56 101 18 930 = true := by decide +kernel
theorem c931 : check 56 101 18 931 = true := by decide +kernel
theorem c932 : check 56 101 18 932 = true := by decide +kernel
theorem c933 : check 56 101 18 933 = true := by decide +kernel
theorem c934 : check 56 101 18 934 = true := by decide +kernel
theorem c935 : check 56 101 18 935 = true := by decide +kernel
theorem c936 : check 56 101 18 936 = true := by decide +kernel
theorem c937 : check 56 101 18 937 = true := by decide +kernel
theorem c938 : check 56 101 18 938 = true := by decide +kernel
theorem c939 : check 56 101 18 939 = true := by decide +kernel
theorem c940 : check 56 101 18 940 = true := by decide +kernel
theorem c941 : check 56 101 18 941 = true := by decide +kernel
theorem c942 : check 56 101 18 942 = true := by decide +kernel
theorem c943 : check 56 101 18 943 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 928 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c928) (chunksOK_one c929)) (chunksOK_append (chunksOK_one c930) (chunksOK_one c931))) (chunksOK_append (chunksOK_append (chunksOK_one c932) (chunksOK_one c933)) (chunksOK_append (chunksOK_one c934) (chunksOK_one c935)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c936) (chunksOK_one c937)) (chunksOK_append (chunksOK_one c938) (chunksOK_one c939))) (chunksOK_append (chunksOK_append (chunksOK_one c940) (chunksOK_one c941)) (chunksOK_append (chunksOK_one c942) (chunksOK_one c943)))))

end C58

/-! Kernel checks for `Q01` at width `56`: chunks `944` to `959` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C59

theorem c944 : check 56 101 18 944 = true := by decide +kernel
theorem c945 : check 56 101 18 945 = true := by decide +kernel
theorem c946 : check 56 101 18 946 = true := by decide +kernel
theorem c947 : check 56 101 18 947 = true := by decide +kernel
theorem c948 : check 56 101 18 948 = true := by decide +kernel
theorem c949 : check 56 101 18 949 = true := by decide +kernel
theorem c950 : check 56 101 18 950 = true := by decide +kernel
theorem c951 : check 56 101 18 951 = true := by decide +kernel
theorem c952 : check 56 101 18 952 = true := by decide +kernel
theorem c953 : check 56 101 18 953 = true := by decide +kernel
theorem c954 : check 56 101 18 954 = true := by decide +kernel
theorem c955 : check 56 101 18 955 = true := by decide +kernel
theorem c956 : check 56 101 18 956 = true := by decide +kernel
theorem c957 : check 56 101 18 957 = true := by decide +kernel
theorem c958 : check 56 101 18 958 = true := by decide +kernel
theorem c959 : check 56 101 18 959 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 944 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c944) (chunksOK_one c945)) (chunksOK_append (chunksOK_one c946) (chunksOK_one c947))) (chunksOK_append (chunksOK_append (chunksOK_one c948) (chunksOK_one c949)) (chunksOK_append (chunksOK_one c950) (chunksOK_one c951)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c952) (chunksOK_one c953)) (chunksOK_append (chunksOK_one c954) (chunksOK_one c955))) (chunksOK_append (chunksOK_append (chunksOK_one c956) (chunksOK_one c957)) (chunksOK_append (chunksOK_one c958) (chunksOK_one c959)))))

end C59

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

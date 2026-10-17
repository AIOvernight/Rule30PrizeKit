import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `960` to `1023`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 960, …, 1023` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C60` –
`C63`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `960` to `975` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C60

theorem c960 : check 56 101 18 960 = true := by decide +kernel
theorem c961 : check 56 101 18 961 = true := by decide +kernel
theorem c962 : check 56 101 18 962 = true := by decide +kernel
theorem c963 : check 56 101 18 963 = true := by decide +kernel
theorem c964 : check 56 101 18 964 = true := by decide +kernel
theorem c965 : check 56 101 18 965 = true := by decide +kernel
theorem c966 : check 56 101 18 966 = true := by decide +kernel
theorem c967 : check 56 101 18 967 = true := by decide +kernel
theorem c968 : check 56 101 18 968 = true := by decide +kernel
theorem c969 : check 56 101 18 969 = true := by decide +kernel
theorem c970 : check 56 101 18 970 = true := by decide +kernel
theorem c971 : check 56 101 18 971 = true := by decide +kernel
theorem c972 : check 56 101 18 972 = true := by decide +kernel
theorem c973 : check 56 101 18 973 = true := by decide +kernel
theorem c974 : check 56 101 18 974 = true := by decide +kernel
theorem c975 : check 56 101 18 975 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 960 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c960) (chunksOK_one c961)) (chunksOK_append (chunksOK_one c962) (chunksOK_one c963))) (chunksOK_append (chunksOK_append (chunksOK_one c964) (chunksOK_one c965)) (chunksOK_append (chunksOK_one c966) (chunksOK_one c967)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c968) (chunksOK_one c969)) (chunksOK_append (chunksOK_one c970) (chunksOK_one c971))) (chunksOK_append (chunksOK_append (chunksOK_one c972) (chunksOK_one c973)) (chunksOK_append (chunksOK_one c974) (chunksOK_one c975)))))

end C60

/-! Kernel checks for `Q01` at width `56`: chunks `976` to `991` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C61

theorem c976 : check 56 101 18 976 = true := by decide +kernel
theorem c977 : check 56 101 18 977 = true := by decide +kernel
theorem c978 : check 56 101 18 978 = true := by decide +kernel
theorem c979 : check 56 101 18 979 = true := by decide +kernel
theorem c980 : check 56 101 18 980 = true := by decide +kernel
theorem c981 : check 56 101 18 981 = true := by decide +kernel
theorem c982 : check 56 101 18 982 = true := by decide +kernel
theorem c983 : check 56 101 18 983 = true := by decide +kernel
theorem c984 : check 56 101 18 984 = true := by decide +kernel
theorem c985 : check 56 101 18 985 = true := by decide +kernel
theorem c986 : check 56 101 18 986 = true := by decide +kernel
theorem c987 : check 56 101 18 987 = true := by decide +kernel
theorem c988 : check 56 101 18 988 = true := by decide +kernel
theorem c989 : check 56 101 18 989 = true := by decide +kernel
theorem c990 : check 56 101 18 990 = true := by decide +kernel
theorem c991 : check 56 101 18 991 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 976 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c976) (chunksOK_one c977)) (chunksOK_append (chunksOK_one c978) (chunksOK_one c979))) (chunksOK_append (chunksOK_append (chunksOK_one c980) (chunksOK_one c981)) (chunksOK_append (chunksOK_one c982) (chunksOK_one c983)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c984) (chunksOK_one c985)) (chunksOK_append (chunksOK_one c986) (chunksOK_one c987))) (chunksOK_append (chunksOK_append (chunksOK_one c988) (chunksOK_one c989)) (chunksOK_append (chunksOK_one c990) (chunksOK_one c991)))))

end C61

/-! Kernel checks for `Q01` at width `56`: chunks `992` to `1007` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C62

theorem c992 : check 56 101 18 992 = true := by decide +kernel
theorem c993 : check 56 101 18 993 = true := by decide +kernel
theorem c994 : check 56 101 18 994 = true := by decide +kernel
theorem c995 : check 56 101 18 995 = true := by decide +kernel
theorem c996 : check 56 101 18 996 = true := by decide +kernel
theorem c997 : check 56 101 18 997 = true := by decide +kernel
theorem c998 : check 56 101 18 998 = true := by decide +kernel
theorem c999 : check 56 101 18 999 = true := by decide +kernel
theorem c1000 : check 56 101 18 1000 = true := by decide +kernel
theorem c1001 : check 56 101 18 1001 = true := by decide +kernel
theorem c1002 : check 56 101 18 1002 = true := by decide +kernel
theorem c1003 : check 56 101 18 1003 = true := by decide +kernel
theorem c1004 : check 56 101 18 1004 = true := by decide +kernel
theorem c1005 : check 56 101 18 1005 = true := by decide +kernel
theorem c1006 : check 56 101 18 1006 = true := by decide +kernel
theorem c1007 : check 56 101 18 1007 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 992 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c992) (chunksOK_one c993)) (chunksOK_append (chunksOK_one c994) (chunksOK_one c995))) (chunksOK_append (chunksOK_append (chunksOK_one c996) (chunksOK_one c997)) (chunksOK_append (chunksOK_one c998) (chunksOK_one c999)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c1000) (chunksOK_one c1001)) (chunksOK_append (chunksOK_one c1002) (chunksOK_one c1003))) (chunksOK_append (chunksOK_append (chunksOK_one c1004) (chunksOK_one c1005)) (chunksOK_append (chunksOK_one c1006) (chunksOK_one c1007)))))

end C62

/-! Kernel checks for `Q01` at width `56`: chunks `1008` to `1023` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C63

theorem c1008 : check 56 101 18 1008 = true := by decide +kernel
theorem c1009 : check 56 101 18 1009 = true := by decide +kernel
theorem c1010 : check 56 101 18 1010 = true := by decide +kernel
theorem c1011 : check 56 101 18 1011 = true := by decide +kernel
theorem c1012 : check 56 101 18 1012 = true := by decide +kernel
theorem c1013 : check 56 101 18 1013 = true := by decide +kernel
theorem c1014 : check 56 101 18 1014 = true := by decide +kernel
theorem c1015 : check 56 101 18 1015 = true := by decide +kernel
theorem c1016 : check 56 101 18 1016 = true := by decide +kernel
theorem c1017 : check 56 101 18 1017 = true := by decide +kernel
theorem c1018 : check 56 101 18 1018 = true := by decide +kernel
theorem c1019 : check 56 101 18 1019 = true := by decide +kernel
theorem c1020 : check 56 101 18 1020 = true := by decide +kernel
theorem c1021 : check 56 101 18 1021 = true := by decide +kernel
theorem c1022 : check 56 101 18 1022 = true := by decide +kernel
theorem c1023 : check 56 101 18 1023 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 1008 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c1008) (chunksOK_one c1009)) (chunksOK_append (chunksOK_one c1010) (chunksOK_one c1011))) (chunksOK_append (chunksOK_append (chunksOK_one c1012) (chunksOK_one c1013)) (chunksOK_append (chunksOK_one c1014) (chunksOK_one c1015)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c1016) (chunksOK_one c1017)) (chunksOK_append (chunksOK_one c1018) (chunksOK_one c1019))) (chunksOK_append (chunksOK_append (chunksOK_one c1020) (chunksOK_one c1021)) (chunksOK_append (chunksOK_one c1022) (chunksOK_one c1023)))))

end C63

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

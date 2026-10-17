import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `192` to `255`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 192, …, 255` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C12` –
`C15`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `192` to `207` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C12

theorem c192 : check 56 101 18 192 = true := by decide +kernel
theorem c193 : check 56 101 18 193 = true := by decide +kernel
theorem c194 : check 56 101 18 194 = true := by decide +kernel
theorem c195 : check 56 101 18 195 = true := by decide +kernel
theorem c196 : check 56 101 18 196 = true := by decide +kernel
theorem c197 : check 56 101 18 197 = true := by decide +kernel
theorem c198 : check 56 101 18 198 = true := by decide +kernel
theorem c199 : check 56 101 18 199 = true := by decide +kernel
theorem c200 : check 56 101 18 200 = true := by decide +kernel
theorem c201 : check 56 101 18 201 = true := by decide +kernel
theorem c202 : check 56 101 18 202 = true := by decide +kernel
theorem c203 : check 56 101 18 203 = true := by decide +kernel
theorem c204 : check 56 101 18 204 = true := by decide +kernel
theorem c205 : check 56 101 18 205 = true := by decide +kernel
theorem c206 : check 56 101 18 206 = true := by decide +kernel
theorem c207 : check 56 101 18 207 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 192 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c192) (chunksOK_one c193)) (chunksOK_append (chunksOK_one c194) (chunksOK_one c195))) (chunksOK_append (chunksOK_append (chunksOK_one c196) (chunksOK_one c197)) (chunksOK_append (chunksOK_one c198) (chunksOK_one c199)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c200) (chunksOK_one c201)) (chunksOK_append (chunksOK_one c202) (chunksOK_one c203))) (chunksOK_append (chunksOK_append (chunksOK_one c204) (chunksOK_one c205)) (chunksOK_append (chunksOK_one c206) (chunksOK_one c207)))))

end C12

/-! Kernel checks for `Q01` at width `56`: chunks `208` to `223` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C13

theorem c208 : check 56 101 18 208 = true := by decide +kernel
theorem c209 : check 56 101 18 209 = true := by decide +kernel
theorem c210 : check 56 101 18 210 = true := by decide +kernel
theorem c211 : check 56 101 18 211 = true := by decide +kernel
theorem c212 : check 56 101 18 212 = true := by decide +kernel
theorem c213 : check 56 101 18 213 = true := by decide +kernel
theorem c214 : check 56 101 18 214 = true := by decide +kernel
theorem c215 : check 56 101 18 215 = true := by decide +kernel
theorem c216 : check 56 101 18 216 = true := by decide +kernel
theorem c217 : check 56 101 18 217 = true := by decide +kernel
theorem c218 : check 56 101 18 218 = true := by decide +kernel
theorem c219 : check 56 101 18 219 = true := by decide +kernel
theorem c220 : check 56 101 18 220 = true := by decide +kernel
theorem c221 : check 56 101 18 221 = true := by decide +kernel
theorem c222 : check 56 101 18 222 = true := by decide +kernel
theorem c223 : check 56 101 18 223 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 208 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c208) (chunksOK_one c209)) (chunksOK_append (chunksOK_one c210) (chunksOK_one c211))) (chunksOK_append (chunksOK_append (chunksOK_one c212) (chunksOK_one c213)) (chunksOK_append (chunksOK_one c214) (chunksOK_one c215)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c216) (chunksOK_one c217)) (chunksOK_append (chunksOK_one c218) (chunksOK_one c219))) (chunksOK_append (chunksOK_append (chunksOK_one c220) (chunksOK_one c221)) (chunksOK_append (chunksOK_one c222) (chunksOK_one c223)))))

end C13

/-! Kernel checks for `Q01` at width `56`: chunks `224` to `239` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C14

theorem c224 : check 56 101 18 224 = true := by decide +kernel
theorem c225 : check 56 101 18 225 = true := by decide +kernel
theorem c226 : check 56 101 18 226 = true := by decide +kernel
theorem c227 : check 56 101 18 227 = true := by decide +kernel
theorem c228 : check 56 101 18 228 = true := by decide +kernel
theorem c229 : check 56 101 18 229 = true := by decide +kernel
theorem c230 : check 56 101 18 230 = true := by decide +kernel
theorem c231 : check 56 101 18 231 = true := by decide +kernel
theorem c232 : check 56 101 18 232 = true := by decide +kernel
theorem c233 : check 56 101 18 233 = true := by decide +kernel
theorem c234 : check 56 101 18 234 = true := by decide +kernel
theorem c235 : check 56 101 18 235 = true := by decide +kernel
theorem c236 : check 56 101 18 236 = true := by decide +kernel
theorem c237 : check 56 101 18 237 = true := by decide +kernel
theorem c238 : check 56 101 18 238 = true := by decide +kernel
theorem c239 : check 56 101 18 239 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 224 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c224) (chunksOK_one c225)) (chunksOK_append (chunksOK_one c226) (chunksOK_one c227))) (chunksOK_append (chunksOK_append (chunksOK_one c228) (chunksOK_one c229)) (chunksOK_append (chunksOK_one c230) (chunksOK_one c231)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c232) (chunksOK_one c233)) (chunksOK_append (chunksOK_one c234) (chunksOK_one c235))) (chunksOK_append (chunksOK_append (chunksOK_one c236) (chunksOK_one c237)) (chunksOK_append (chunksOK_one c238) (chunksOK_one c239)))))

end C14

/-! Kernel checks for `Q01` at width `56`: chunks `240` to `255` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C15

theorem c240 : check 56 101 18 240 = true := by decide +kernel
theorem c241 : check 56 101 18 241 = true := by decide +kernel
theorem c242 : check 56 101 18 242 = true := by decide +kernel
theorem c243 : check 56 101 18 243 = true := by decide +kernel
theorem c244 : check 56 101 18 244 = true := by decide +kernel
theorem c245 : check 56 101 18 245 = true := by decide +kernel
theorem c246 : check 56 101 18 246 = true := by decide +kernel
theorem c247 : check 56 101 18 247 = true := by decide +kernel
theorem c248 : check 56 101 18 248 = true := by decide +kernel
theorem c249 : check 56 101 18 249 = true := by decide +kernel
theorem c250 : check 56 101 18 250 = true := by decide +kernel
theorem c251 : check 56 101 18 251 = true := by decide +kernel
theorem c252 : check 56 101 18 252 = true := by decide +kernel
theorem c253 : check 56 101 18 253 = true := by decide +kernel
theorem c254 : check 56 101 18 254 = true := by decide +kernel
theorem c255 : check 56 101 18 255 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 240 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c240) (chunksOK_one c241)) (chunksOK_append (chunksOK_one c242) (chunksOK_one c243))) (chunksOK_append (chunksOK_append (chunksOK_one c244) (chunksOK_one c245)) (chunksOK_append (chunksOK_one c246) (chunksOK_one c247)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c248) (chunksOK_one c249)) (chunksOK_append (chunksOK_one c250) (chunksOK_one c251))) (chunksOK_append (chunksOK_append (chunksOK_one c252) (chunksOK_one c253)) (chunksOK_append (chunksOK_one c254) (chunksOK_one c255)))))

end C15

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

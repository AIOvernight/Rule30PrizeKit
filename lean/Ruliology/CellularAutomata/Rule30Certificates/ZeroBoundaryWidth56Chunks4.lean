import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `256` to `319`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 256, …, 319` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C16` –
`C19`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `256` to `271` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C16

theorem c256 : check 56 101 18 256 = true := by decide +kernel
theorem c257 : check 56 101 18 257 = true := by decide +kernel
theorem c258 : check 56 101 18 258 = true := by decide +kernel
theorem c259 : check 56 101 18 259 = true := by decide +kernel
theorem c260 : check 56 101 18 260 = true := by decide +kernel
theorem c261 : check 56 101 18 261 = true := by decide +kernel
theorem c262 : check 56 101 18 262 = true := by decide +kernel
theorem c263 : check 56 101 18 263 = true := by decide +kernel
theorem c264 : check 56 101 18 264 = true := by decide +kernel
theorem c265 : check 56 101 18 265 = true := by decide +kernel
theorem c266 : check 56 101 18 266 = true := by decide +kernel
theorem c267 : check 56 101 18 267 = true := by decide +kernel
theorem c268 : check 56 101 18 268 = true := by decide +kernel
theorem c269 : check 56 101 18 269 = true := by decide +kernel
theorem c270 : check 56 101 18 270 = true := by decide +kernel
theorem c271 : check 56 101 18 271 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 256 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c256) (chunksOK_one c257)) (chunksOK_append (chunksOK_one c258) (chunksOK_one c259))) (chunksOK_append (chunksOK_append (chunksOK_one c260) (chunksOK_one c261)) (chunksOK_append (chunksOK_one c262) (chunksOK_one c263)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c264) (chunksOK_one c265)) (chunksOK_append (chunksOK_one c266) (chunksOK_one c267))) (chunksOK_append (chunksOK_append (chunksOK_one c268) (chunksOK_one c269)) (chunksOK_append (chunksOK_one c270) (chunksOK_one c271)))))

end C16

/-! Kernel checks for `Q01` at width `56`: chunks `272` to `287` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C17

theorem c272 : check 56 101 18 272 = true := by decide +kernel
theorem c273 : check 56 101 18 273 = true := by decide +kernel
theorem c274 : check 56 101 18 274 = true := by decide +kernel
theorem c275 : check 56 101 18 275 = true := by decide +kernel
theorem c276 : check 56 101 18 276 = true := by decide +kernel
theorem c277 : check 56 101 18 277 = true := by decide +kernel
theorem c278 : check 56 101 18 278 = true := by decide +kernel
theorem c279 : check 56 101 18 279 = true := by decide +kernel
theorem c280 : check 56 101 18 280 = true := by decide +kernel
theorem c281 : check 56 101 18 281 = true := by decide +kernel
theorem c282 : check 56 101 18 282 = true := by decide +kernel
theorem c283 : check 56 101 18 283 = true := by decide +kernel
theorem c284 : check 56 101 18 284 = true := by decide +kernel
theorem c285 : check 56 101 18 285 = true := by decide +kernel
theorem c286 : check 56 101 18 286 = true := by decide +kernel
theorem c287 : check 56 101 18 287 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 272 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c272) (chunksOK_one c273)) (chunksOK_append (chunksOK_one c274) (chunksOK_one c275))) (chunksOK_append (chunksOK_append (chunksOK_one c276) (chunksOK_one c277)) (chunksOK_append (chunksOK_one c278) (chunksOK_one c279)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c280) (chunksOK_one c281)) (chunksOK_append (chunksOK_one c282) (chunksOK_one c283))) (chunksOK_append (chunksOK_append (chunksOK_one c284) (chunksOK_one c285)) (chunksOK_append (chunksOK_one c286) (chunksOK_one c287)))))

end C17

/-! Kernel checks for `Q01` at width `56`: chunks `288` to `303` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C18

theorem c288 : check 56 101 18 288 = true := by decide +kernel
theorem c289 : check 56 101 18 289 = true := by decide +kernel
theorem c290 : check 56 101 18 290 = true := by decide +kernel
theorem c291 : check 56 101 18 291 = true := by decide +kernel
theorem c292 : check 56 101 18 292 = true := by decide +kernel
theorem c293 : check 56 101 18 293 = true := by decide +kernel
theorem c294 : check 56 101 18 294 = true := by decide +kernel
theorem c295 : check 56 101 18 295 = true := by decide +kernel
theorem c296 : check 56 101 18 296 = true := by decide +kernel
theorem c297 : check 56 101 18 297 = true := by decide +kernel
theorem c298 : check 56 101 18 298 = true := by decide +kernel
theorem c299 : check 56 101 18 299 = true := by decide +kernel
theorem c300 : check 56 101 18 300 = true := by decide +kernel
theorem c301 : check 56 101 18 301 = true := by decide +kernel
theorem c302 : check 56 101 18 302 = true := by decide +kernel
theorem c303 : check 56 101 18 303 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 288 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c288) (chunksOK_one c289)) (chunksOK_append (chunksOK_one c290) (chunksOK_one c291))) (chunksOK_append (chunksOK_append (chunksOK_one c292) (chunksOK_one c293)) (chunksOK_append (chunksOK_one c294) (chunksOK_one c295)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c296) (chunksOK_one c297)) (chunksOK_append (chunksOK_one c298) (chunksOK_one c299))) (chunksOK_append (chunksOK_append (chunksOK_one c300) (chunksOK_one c301)) (chunksOK_append (chunksOK_one c302) (chunksOK_one c303)))))

end C18

/-! Kernel checks for `Q01` at width `56`: chunks `304` to `319` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C19

theorem c304 : check 56 101 18 304 = true := by decide +kernel
theorem c305 : check 56 101 18 305 = true := by decide +kernel
theorem c306 : check 56 101 18 306 = true := by decide +kernel
theorem c307 : check 56 101 18 307 = true := by decide +kernel
theorem c308 : check 56 101 18 308 = true := by decide +kernel
theorem c309 : check 56 101 18 309 = true := by decide +kernel
theorem c310 : check 56 101 18 310 = true := by decide +kernel
theorem c311 : check 56 101 18 311 = true := by decide +kernel
theorem c312 : check 56 101 18 312 = true := by decide +kernel
theorem c313 : check 56 101 18 313 = true := by decide +kernel
theorem c314 : check 56 101 18 314 = true := by decide +kernel
theorem c315 : check 56 101 18 315 = true := by decide +kernel
theorem c316 : check 56 101 18 316 = true := by decide +kernel
theorem c317 : check 56 101 18 317 = true := by decide +kernel
theorem c318 : check 56 101 18 318 = true := by decide +kernel
theorem c319 : check 56 101 18 319 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 304 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c304) (chunksOK_one c305)) (chunksOK_append (chunksOK_one c306) (chunksOK_one c307))) (chunksOK_append (chunksOK_append (chunksOK_one c308) (chunksOK_one c309)) (chunksOK_append (chunksOK_one c310) (chunksOK_one c311)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c312) (chunksOK_one c313)) (chunksOK_append (chunksOK_one c314) (chunksOK_one c315))) (chunksOK_append (chunksOK_append (chunksOK_one c316) (chunksOK_one c317)) (chunksOK_append (chunksOK_one c318) (chunksOK_one c319)))))

end C19

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

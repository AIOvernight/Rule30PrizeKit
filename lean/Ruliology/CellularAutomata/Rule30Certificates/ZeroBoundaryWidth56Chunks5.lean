import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `320` to `383`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 320, …, 383` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C20` –
`C23`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `320` to `335` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C20

theorem c320 : check 56 101 18 320 = true := by decide +kernel
theorem c321 : check 56 101 18 321 = true := by decide +kernel
theorem c322 : check 56 101 18 322 = true := by decide +kernel
theorem c323 : check 56 101 18 323 = true := by decide +kernel
theorem c324 : check 56 101 18 324 = true := by decide +kernel
theorem c325 : check 56 101 18 325 = true := by decide +kernel
theorem c326 : check 56 101 18 326 = true := by decide +kernel
theorem c327 : check 56 101 18 327 = true := by decide +kernel
theorem c328 : check 56 101 18 328 = true := by decide +kernel
theorem c329 : check 56 101 18 329 = true := by decide +kernel
theorem c330 : check 56 101 18 330 = true := by decide +kernel
theorem c331 : check 56 101 18 331 = true := by decide +kernel
theorem c332 : check 56 101 18 332 = true := by decide +kernel
theorem c333 : check 56 101 18 333 = true := by decide +kernel
theorem c334 : check 56 101 18 334 = true := by decide +kernel
theorem c335 : check 56 101 18 335 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 320 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c320) (chunksOK_one c321)) (chunksOK_append (chunksOK_one c322) (chunksOK_one c323))) (chunksOK_append (chunksOK_append (chunksOK_one c324) (chunksOK_one c325)) (chunksOK_append (chunksOK_one c326) (chunksOK_one c327)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c328) (chunksOK_one c329)) (chunksOK_append (chunksOK_one c330) (chunksOK_one c331))) (chunksOK_append (chunksOK_append (chunksOK_one c332) (chunksOK_one c333)) (chunksOK_append (chunksOK_one c334) (chunksOK_one c335)))))

end C20

/-! Kernel checks for `Q01` at width `56`: chunks `336` to `351` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C21

theorem c336 : check 56 101 18 336 = true := by decide +kernel
theorem c337 : check 56 101 18 337 = true := by decide +kernel
theorem c338 : check 56 101 18 338 = true := by decide +kernel
theorem c339 : check 56 101 18 339 = true := by decide +kernel
theorem c340 : check 56 101 18 340 = true := by decide +kernel
theorem c341 : check 56 101 18 341 = true := by decide +kernel
theorem c342 : check 56 101 18 342 = true := by decide +kernel
theorem c343 : check 56 101 18 343 = true := by decide +kernel
theorem c344 : check 56 101 18 344 = true := by decide +kernel
theorem c345 : check 56 101 18 345 = true := by decide +kernel
theorem c346 : check 56 101 18 346 = true := by decide +kernel
theorem c347 : check 56 101 18 347 = true := by decide +kernel
theorem c348 : check 56 101 18 348 = true := by decide +kernel
theorem c349 : check 56 101 18 349 = true := by decide +kernel
theorem c350 : check 56 101 18 350 = true := by decide +kernel
theorem c351 : check 56 101 18 351 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 336 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c336) (chunksOK_one c337)) (chunksOK_append (chunksOK_one c338) (chunksOK_one c339))) (chunksOK_append (chunksOK_append (chunksOK_one c340) (chunksOK_one c341)) (chunksOK_append (chunksOK_one c342) (chunksOK_one c343)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c344) (chunksOK_one c345)) (chunksOK_append (chunksOK_one c346) (chunksOK_one c347))) (chunksOK_append (chunksOK_append (chunksOK_one c348) (chunksOK_one c349)) (chunksOK_append (chunksOK_one c350) (chunksOK_one c351)))))

end C21

/-! Kernel checks for `Q01` at width `56`: chunks `352` to `367` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C22

theorem c352 : check 56 101 18 352 = true := by decide +kernel
theorem c353 : check 56 101 18 353 = true := by decide +kernel
theorem c354 : check 56 101 18 354 = true := by decide +kernel
theorem c355 : check 56 101 18 355 = true := by decide +kernel
theorem c356 : check 56 101 18 356 = true := by decide +kernel
theorem c357 : check 56 101 18 357 = true := by decide +kernel
theorem c358 : check 56 101 18 358 = true := by decide +kernel
theorem c359 : check 56 101 18 359 = true := by decide +kernel
theorem c360 : check 56 101 18 360 = true := by decide +kernel
theorem c361 : check 56 101 18 361 = true := by decide +kernel
theorem c362 : check 56 101 18 362 = true := by decide +kernel
theorem c363 : check 56 101 18 363 = true := by decide +kernel
theorem c364 : check 56 101 18 364 = true := by decide +kernel
theorem c365 : check 56 101 18 365 = true := by decide +kernel
theorem c366 : check 56 101 18 366 = true := by decide +kernel
theorem c367 : check 56 101 18 367 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 352 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c352) (chunksOK_one c353)) (chunksOK_append (chunksOK_one c354) (chunksOK_one c355))) (chunksOK_append (chunksOK_append (chunksOK_one c356) (chunksOK_one c357)) (chunksOK_append (chunksOK_one c358) (chunksOK_one c359)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c360) (chunksOK_one c361)) (chunksOK_append (chunksOK_one c362) (chunksOK_one c363))) (chunksOK_append (chunksOK_append (chunksOK_one c364) (chunksOK_one c365)) (chunksOK_append (chunksOK_one c366) (chunksOK_one c367)))))

end C22

/-! Kernel checks for `Q01` at width `56`: chunks `368` to `383` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C23

theorem c368 : check 56 101 18 368 = true := by decide +kernel
theorem c369 : check 56 101 18 369 = true := by decide +kernel
theorem c370 : check 56 101 18 370 = true := by decide +kernel
theorem c371 : check 56 101 18 371 = true := by decide +kernel
theorem c372 : check 56 101 18 372 = true := by decide +kernel
theorem c373 : check 56 101 18 373 = true := by decide +kernel
theorem c374 : check 56 101 18 374 = true := by decide +kernel
theorem c375 : check 56 101 18 375 = true := by decide +kernel
theorem c376 : check 56 101 18 376 = true := by decide +kernel
theorem c377 : check 56 101 18 377 = true := by decide +kernel
theorem c378 : check 56 101 18 378 = true := by decide +kernel
theorem c379 : check 56 101 18 379 = true := by decide +kernel
theorem c380 : check 56 101 18 380 = true := by decide +kernel
theorem c381 : check 56 101 18 381 = true := by decide +kernel
theorem c382 : check 56 101 18 382 = true := by decide +kernel
theorem c383 : check 56 101 18 383 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 368 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c368) (chunksOK_one c369)) (chunksOK_append (chunksOK_one c370) (chunksOK_one c371))) (chunksOK_append (chunksOK_append (chunksOK_one c372) (chunksOK_one c373)) (chunksOK_append (chunksOK_one c374) (chunksOK_one c375)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c376) (chunksOK_one c377)) (chunksOK_append (chunksOK_one c378) (chunksOK_one c379))) (chunksOK_append (chunksOK_append (chunksOK_one c380) (chunksOK_one c381)) (chunksOK_append (chunksOK_one c382) (chunksOK_one c383)))))

end C23

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

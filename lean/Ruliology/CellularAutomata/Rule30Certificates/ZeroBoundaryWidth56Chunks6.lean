import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `384` to `447`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 384, …, 447` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C24` –
`C27`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `384` to `399` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C24

theorem c384 : check 56 101 18 384 = true := by decide +kernel
theorem c385 : check 56 101 18 385 = true := by decide +kernel
theorem c386 : check 56 101 18 386 = true := by decide +kernel
theorem c387 : check 56 101 18 387 = true := by decide +kernel
theorem c388 : check 56 101 18 388 = true := by decide +kernel
theorem c389 : check 56 101 18 389 = true := by decide +kernel
theorem c390 : check 56 101 18 390 = true := by decide +kernel
theorem c391 : check 56 101 18 391 = true := by decide +kernel
theorem c392 : check 56 101 18 392 = true := by decide +kernel
theorem c393 : check 56 101 18 393 = true := by decide +kernel
theorem c394 : check 56 101 18 394 = true := by decide +kernel
theorem c395 : check 56 101 18 395 = true := by decide +kernel
theorem c396 : check 56 101 18 396 = true := by decide +kernel
theorem c397 : check 56 101 18 397 = true := by decide +kernel
theorem c398 : check 56 101 18 398 = true := by decide +kernel
theorem c399 : check 56 101 18 399 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 384 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c384) (chunksOK_one c385)) (chunksOK_append (chunksOK_one c386) (chunksOK_one c387))) (chunksOK_append (chunksOK_append (chunksOK_one c388) (chunksOK_one c389)) (chunksOK_append (chunksOK_one c390) (chunksOK_one c391)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c392) (chunksOK_one c393)) (chunksOK_append (chunksOK_one c394) (chunksOK_one c395))) (chunksOK_append (chunksOK_append (chunksOK_one c396) (chunksOK_one c397)) (chunksOK_append (chunksOK_one c398) (chunksOK_one c399)))))

end C24

/-! Kernel checks for `Q01` at width `56`: chunks `400` to `415` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C25

theorem c400 : check 56 101 18 400 = true := by decide +kernel
theorem c401 : check 56 101 18 401 = true := by decide +kernel
theorem c402 : check 56 101 18 402 = true := by decide +kernel
theorem c403 : check 56 101 18 403 = true := by decide +kernel
theorem c404 : check 56 101 18 404 = true := by decide +kernel
theorem c405 : check 56 101 18 405 = true := by decide +kernel
theorem c406 : check 56 101 18 406 = true := by decide +kernel
theorem c407 : check 56 101 18 407 = true := by decide +kernel
theorem c408 : check 56 101 18 408 = true := by decide +kernel
theorem c409 : check 56 101 18 409 = true := by decide +kernel
theorem c410 : check 56 101 18 410 = true := by decide +kernel
theorem c411 : check 56 101 18 411 = true := by decide +kernel
theorem c412 : check 56 101 18 412 = true := by decide +kernel
theorem c413 : check 56 101 18 413 = true := by decide +kernel
theorem c414 : check 56 101 18 414 = true := by decide +kernel
theorem c415 : check 56 101 18 415 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 400 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c400) (chunksOK_one c401)) (chunksOK_append (chunksOK_one c402) (chunksOK_one c403))) (chunksOK_append (chunksOK_append (chunksOK_one c404) (chunksOK_one c405)) (chunksOK_append (chunksOK_one c406) (chunksOK_one c407)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c408) (chunksOK_one c409)) (chunksOK_append (chunksOK_one c410) (chunksOK_one c411))) (chunksOK_append (chunksOK_append (chunksOK_one c412) (chunksOK_one c413)) (chunksOK_append (chunksOK_one c414) (chunksOK_one c415)))))

end C25

/-! Kernel checks for `Q01` at width `56`: chunks `416` to `431` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C26

theorem c416 : check 56 101 18 416 = true := by decide +kernel
theorem c417 : check 56 101 18 417 = true := by decide +kernel
theorem c418 : check 56 101 18 418 = true := by decide +kernel
theorem c419 : check 56 101 18 419 = true := by decide +kernel
theorem c420 : check 56 101 18 420 = true := by decide +kernel
theorem c421 : check 56 101 18 421 = true := by decide +kernel
theorem c422 : check 56 101 18 422 = true := by decide +kernel
theorem c423 : check 56 101 18 423 = true := by decide +kernel
theorem c424 : check 56 101 18 424 = true := by decide +kernel
theorem c425 : check 56 101 18 425 = true := by decide +kernel
theorem c426 : check 56 101 18 426 = true := by decide +kernel
theorem c427 : check 56 101 18 427 = true := by decide +kernel
theorem c428 : check 56 101 18 428 = true := by decide +kernel
theorem c429 : check 56 101 18 429 = true := by decide +kernel
theorem c430 : check 56 101 18 430 = true := by decide +kernel
theorem c431 : check 56 101 18 431 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 416 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c416) (chunksOK_one c417)) (chunksOK_append (chunksOK_one c418) (chunksOK_one c419))) (chunksOK_append (chunksOK_append (chunksOK_one c420) (chunksOK_one c421)) (chunksOK_append (chunksOK_one c422) (chunksOK_one c423)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c424) (chunksOK_one c425)) (chunksOK_append (chunksOK_one c426) (chunksOK_one c427))) (chunksOK_append (chunksOK_append (chunksOK_one c428) (chunksOK_one c429)) (chunksOK_append (chunksOK_one c430) (chunksOK_one c431)))))

end C26

/-! Kernel checks for `Q01` at width `56`: chunks `432` to `447` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C27

theorem c432 : check 56 101 18 432 = true := by decide +kernel
theorem c433 : check 56 101 18 433 = true := by decide +kernel
theorem c434 : check 56 101 18 434 = true := by decide +kernel
theorem c435 : check 56 101 18 435 = true := by decide +kernel
theorem c436 : check 56 101 18 436 = true := by decide +kernel
theorem c437 : check 56 101 18 437 = true := by decide +kernel
theorem c438 : check 56 101 18 438 = true := by decide +kernel
theorem c439 : check 56 101 18 439 = true := by decide +kernel
theorem c440 : check 56 101 18 440 = true := by decide +kernel
theorem c441 : check 56 101 18 441 = true := by decide +kernel
theorem c442 : check 56 101 18 442 = true := by decide +kernel
theorem c443 : check 56 101 18 443 = true := by decide +kernel
theorem c444 : check 56 101 18 444 = true := by decide +kernel
theorem c445 : check 56 101 18 445 = true := by decide +kernel
theorem c446 : check 56 101 18 446 = true := by decide +kernel
theorem c447 : check 56 101 18 447 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 432 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c432) (chunksOK_one c433)) (chunksOK_append (chunksOK_one c434) (chunksOK_one c435))) (chunksOK_append (chunksOK_append (chunksOK_one c436) (chunksOK_one c437)) (chunksOK_append (chunksOK_one c438) (chunksOK_one c439)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c440) (chunksOK_one c441)) (chunksOK_append (chunksOK_one c442) (chunksOK_one c443))) (chunksOK_append (chunksOK_append (chunksOK_one c444) (chunksOK_one c445)) (chunksOK_append (chunksOK_one c446) (chunksOK_one c447)))))

end C27

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

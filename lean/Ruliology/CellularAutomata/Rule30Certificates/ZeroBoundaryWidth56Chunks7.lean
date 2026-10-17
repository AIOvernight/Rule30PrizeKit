import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `56`: the chunk checks `448` to `511`

Data for `Rule30ZeroBoundaryWidth56`: the kernel checks `check 56 101 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 448, …, 511` of `1024`
(`2 ^ 18` lanes each, `101` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth56.C28` –
`C31`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 56 101 18 lo 16`.

Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,
round 2 (`kernel-certify-r2`, target 1); the `64` generated chunk files (`gen.py`)
are regrouped here, four to a module, with only the namespaces renamed; adversarially verified.
-/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `56`: chunks `448` to `463` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C28

theorem c448 : check 56 101 18 448 = true := by decide +kernel
theorem c449 : check 56 101 18 449 = true := by decide +kernel
theorem c450 : check 56 101 18 450 = true := by decide +kernel
theorem c451 : check 56 101 18 451 = true := by decide +kernel
theorem c452 : check 56 101 18 452 = true := by decide +kernel
theorem c453 : check 56 101 18 453 = true := by decide +kernel
theorem c454 : check 56 101 18 454 = true := by decide +kernel
theorem c455 : check 56 101 18 455 = true := by decide +kernel
theorem c456 : check 56 101 18 456 = true := by decide +kernel
theorem c457 : check 56 101 18 457 = true := by decide +kernel
theorem c458 : check 56 101 18 458 = true := by decide +kernel
theorem c459 : check 56 101 18 459 = true := by decide +kernel
theorem c460 : check 56 101 18 460 = true := by decide +kernel
theorem c461 : check 56 101 18 461 = true := by decide +kernel
theorem c462 : check 56 101 18 462 = true := by decide +kernel
theorem c463 : check 56 101 18 463 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 448 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c448) (chunksOK_one c449)) (chunksOK_append (chunksOK_one c450) (chunksOK_one c451))) (chunksOK_append (chunksOK_append (chunksOK_one c452) (chunksOK_one c453)) (chunksOK_append (chunksOK_one c454) (chunksOK_one c455)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c456) (chunksOK_one c457)) (chunksOK_append (chunksOK_one c458) (chunksOK_one c459))) (chunksOK_append (chunksOK_append (chunksOK_one c460) (chunksOK_one c461)) (chunksOK_append (chunksOK_one c462) (chunksOK_one c463)))))

end C28

/-! Kernel checks for `Q01` at width `56`: chunks `464` to `479` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C29

theorem c464 : check 56 101 18 464 = true := by decide +kernel
theorem c465 : check 56 101 18 465 = true := by decide +kernel
theorem c466 : check 56 101 18 466 = true := by decide +kernel
theorem c467 : check 56 101 18 467 = true := by decide +kernel
theorem c468 : check 56 101 18 468 = true := by decide +kernel
theorem c469 : check 56 101 18 469 = true := by decide +kernel
theorem c470 : check 56 101 18 470 = true := by decide +kernel
theorem c471 : check 56 101 18 471 = true := by decide +kernel
theorem c472 : check 56 101 18 472 = true := by decide +kernel
theorem c473 : check 56 101 18 473 = true := by decide +kernel
theorem c474 : check 56 101 18 474 = true := by decide +kernel
theorem c475 : check 56 101 18 475 = true := by decide +kernel
theorem c476 : check 56 101 18 476 = true := by decide +kernel
theorem c477 : check 56 101 18 477 = true := by decide +kernel
theorem c478 : check 56 101 18 478 = true := by decide +kernel
theorem c479 : check 56 101 18 479 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 464 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c464) (chunksOK_one c465)) (chunksOK_append (chunksOK_one c466) (chunksOK_one c467))) (chunksOK_append (chunksOK_append (chunksOK_one c468) (chunksOK_one c469)) (chunksOK_append (chunksOK_one c470) (chunksOK_one c471)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c472) (chunksOK_one c473)) (chunksOK_append (chunksOK_one c474) (chunksOK_one c475))) (chunksOK_append (chunksOK_append (chunksOK_one c476) (chunksOK_one c477)) (chunksOK_append (chunksOK_one c478) (chunksOK_one c479)))))

end C29

/-! Kernel checks for `Q01` at width `56`: chunks `480` to `495` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C30

theorem c480 : check 56 101 18 480 = true := by decide +kernel
theorem c481 : check 56 101 18 481 = true := by decide +kernel
theorem c482 : check 56 101 18 482 = true := by decide +kernel
theorem c483 : check 56 101 18 483 = true := by decide +kernel
theorem c484 : check 56 101 18 484 = true := by decide +kernel
theorem c485 : check 56 101 18 485 = true := by decide +kernel
theorem c486 : check 56 101 18 486 = true := by decide +kernel
theorem c487 : check 56 101 18 487 = true := by decide +kernel
theorem c488 : check 56 101 18 488 = true := by decide +kernel
theorem c489 : check 56 101 18 489 = true := by decide +kernel
theorem c490 : check 56 101 18 490 = true := by decide +kernel
theorem c491 : check 56 101 18 491 = true := by decide +kernel
theorem c492 : check 56 101 18 492 = true := by decide +kernel
theorem c493 : check 56 101 18 493 = true := by decide +kernel
theorem c494 : check 56 101 18 494 = true := by decide +kernel
theorem c495 : check 56 101 18 495 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 480 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c480) (chunksOK_one c481)) (chunksOK_append (chunksOK_one c482) (chunksOK_one c483))) (chunksOK_append (chunksOK_append (chunksOK_one c484) (chunksOK_one c485)) (chunksOK_append (chunksOK_one c486) (chunksOK_one c487)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c488) (chunksOK_one c489)) (chunksOK_append (chunksOK_one c490) (chunksOK_one c491))) (chunksOK_append (chunksOK_append (chunksOK_one c492) (chunksOK_one c493)) (chunksOK_append (chunksOK_one c494) (chunksOK_one c495)))))

end C30

/-! Kernel checks for `Q01` at width `56`: chunks `496` to `511` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace C31

theorem c496 : check 56 101 18 496 = true := by decide +kernel
theorem c497 : check 56 101 18 497 = true := by decide +kernel
theorem c498 : check 56 101 18 498 = true := by decide +kernel
theorem c499 : check 56 101 18 499 = true := by decide +kernel
theorem c500 : check 56 101 18 500 = true := by decide +kernel
theorem c501 : check 56 101 18 501 = true := by decide +kernel
theorem c502 : check 56 101 18 502 = true := by decide +kernel
theorem c503 : check 56 101 18 503 = true := by decide +kernel
theorem c504 : check 56 101 18 504 = true := by decide +kernel
theorem c505 : check 56 101 18 505 = true := by decide +kernel
theorem c506 : check 56 101 18 506 = true := by decide +kernel
theorem c507 : check 56 101 18 507 = true := by decide +kernel
theorem c508 : check 56 101 18 508 = true := by decide +kernel
theorem c509 : check 56 101 18 509 = true := by decide +kernel
theorem c510 : check 56 101 18 510 = true := by decide +kernel
theorem c511 : check 56 101 18 511 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 496 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c496) (chunksOK_one c497)) (chunksOK_append (chunksOK_one c498) (chunksOK_one c499))) (chunksOK_append (chunksOK_append (chunksOK_one c500) (chunksOK_one c501)) (chunksOK_append (chunksOK_one c502) (chunksOK_one c503)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c504) (chunksOK_one c505)) (chunksOK_append (chunksOK_one c506) (chunksOK_one c507))) (chunksOK_append (chunksOK_append (chunksOK_one c508) (chunksOK_one c509)) (chunksOK_append (chunksOK_one c510) (chunksOK_one c511)))))

end C31

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth56

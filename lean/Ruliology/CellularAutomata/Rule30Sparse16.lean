module

public import Ruliology.CellularAutomata.Rule30Certificates.Sparse16

/-!
# Sparse16: 56 even black observations force 17 initial black cells

For the official zero-boundary evolution `Rule30ZeroBoundary.zrow`, every Boolean
half-line L with black observations at depth 1 and times 0,2,...,110 has at least
17 black cells among L(1),...,L(111). L(0) is ignored; all positions past 111 are
unrestricted. The four consequences give the corresponding InX weight bound,
a white even-time observation for a prefix of weight at most 16, exclusion of
globally 16-sparse starts from InX, and the necessary left-prefix weight for an
arbitrary whole-line configuration alternating at its center from time zero.

The proof reconstructs anti-diagonals from the boundary history, charges each
initial black cell once, and exhausts the budget-16 histories through depth 111.
The certificate module proves both the packed program's scalar semantics and
stable compaction, and the kernel checks all 111 transitions. This module carries
the backward exclusion induction and applies the official reconstruction bridge.

Research and formalization by OpenAI Codex for @AIOvernight. This is a finite quantitative theorem;
it does not prove Q01 for every finite start or exclude period two for the seed.
-/

@[expose] public section

set_option Elab.async false
namespace Ruliology.CellularAutomata.Rule30Sparse16
open CheckpointSoundness
open Ruliology.CellularAutomata.Rule30ZeroBoundary
theorem excluded111 : Excluded 111 0 16 SWARProbe.F111 :=
  excluded_empty 111 0 16 SWARProbe.F111 (by decide +kernel)
theorem excluded110 : Excluded 110 1 16 SWARProbe.F110 :=
  excluded_step step_correct 110 0 16 SWARProbe.F110 SWARProbe.F111
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step110 excluded111
theorem excluded109 : Excluded 109 2 16 SWARProbe.F109 :=
  excluded_step step_correct 109 1 16 SWARProbe.F109 SWARProbe.F110
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step109 excluded110
theorem excluded108 : Excluded 108 3 16 SWARProbe.F108 :=
  excluded_step step_correct 108 2 16 SWARProbe.F108 SWARProbe.F109
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step108 excluded109
theorem excluded107 : Excluded 107 4 16 SWARProbe.F107 :=
  excluded_step step_correct 107 3 16 SWARProbe.F107 SWARProbe.F108
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step107 excluded108
theorem excluded106 : Excluded 106 5 16 SWARProbe.F106 :=
  excluded_step step_correct 106 4 16 SWARProbe.F106 SWARProbe.F107
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step106 excluded107
theorem excluded105 : Excluded 105 6 16 SWARProbe.F105 :=
  excluded_step step_correct 105 5 16 SWARProbe.F105 SWARProbe.F106
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step105 excluded106
theorem excluded104 : Excluded 104 7 16 SWARProbe.F104 :=
  excluded_step step_correct 104 6 16 SWARProbe.F104 SWARProbe.F105
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step104 excluded105
theorem excluded103 : Excluded 103 8 16 SWARProbe.F103 :=
  excluded_step step_correct 103 7 16 SWARProbe.F103 SWARProbe.F104
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step103 excluded104
theorem excluded102 : Excluded 102 9 16 SWARProbe.F102 :=
  excluded_step step_correct 102 8 16 SWARProbe.F102 SWARProbe.F103
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step102 excluded103
theorem excluded101 : Excluded 101 10 16 SWARProbe.F101 :=
  excluded_step step_correct 101 9 16 SWARProbe.F101 SWARProbe.F102
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step101 excluded102
theorem excluded100 : Excluded 100 11 16 SWARProbe.F100 :=
  excluded_step step_correct 100 10 16 SWARProbe.F100 SWARProbe.F101
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step100 excluded101
theorem excluded99 : Excluded 99 12 16 SWARProbe.F99 :=
  excluded_step step_correct 99 11 16 SWARProbe.F99 SWARProbe.F100
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step99 excluded100
theorem excluded98 : Excluded 98 13 16 SWARProbe.F98 :=
  excluded_step step_correct 98 12 16 SWARProbe.F98 SWARProbe.F99
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step98 excluded99
theorem excluded97 : Excluded 97 14 16 SWARProbe.F97 :=
  excluded_step step_correct 97 13 16 SWARProbe.F97 SWARProbe.F98
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step97 excluded98
theorem excluded96 : Excluded 96 15 16 SWARProbe.F96 :=
  excluded_step step_correct 96 14 16 SWARProbe.F96 SWARProbe.F97
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step96 excluded97
theorem excluded95 : Excluded 95 16 16 SWARProbe.F95 :=
  excluded_step step_correct 95 15 16 SWARProbe.F95 SWARProbe.F96
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step95 excluded96
theorem excluded94 : Excluded 94 17 16 SWARProbe.F94 :=
  excluded_step step_correct 94 16 16 SWARProbe.F94 SWARProbe.F95
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step94 excluded95
theorem excluded93 : Excluded 93 18 16 SWARProbe.F93 :=
  excluded_step step_correct 93 17 16 SWARProbe.F93 SWARProbe.F94
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step93 excluded94
theorem excluded92 : Excluded 92 19 16 SWARProbe.F92 :=
  excluded_step step_correct 92 18 16 SWARProbe.F92 SWARProbe.F93
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step92 excluded93
theorem excluded91 : Excluded 91 20 16 SWARProbe.F91 :=
  excluded_step step_correct 91 19 16 SWARProbe.F91 SWARProbe.F92
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step91 excluded92
theorem excluded90 : Excluded 90 21 16 SWARProbe.F90 :=
  excluded_step step_correct 90 20 16 SWARProbe.F90 SWARProbe.F91
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step90 excluded91
theorem excluded89 : Excluded 89 22 16 SWARProbe.F89 :=
  excluded_step step_correct 89 21 16 SWARProbe.F89 SWARProbe.F90
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step89 excluded90
theorem excluded88 : Excluded 88 23 16 SWARProbe.F88 :=
  excluded_step step_correct 88 22 16 SWARProbe.F88 SWARProbe.F89
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step88 excluded89
theorem excluded87 : Excluded 87 24 16 SWARProbe.F87 :=
  excluded_step step_correct 87 23 16 SWARProbe.F87 SWARProbe.F88
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step87 excluded88
theorem excluded86 : Excluded 86 25 16 SWARProbe.F86 :=
  excluded_step step_correct 86 24 16 SWARProbe.F86 SWARProbe.F87
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step86 excluded87
theorem excluded85 : Excluded 85 26 16 SWARProbe.F85 :=
  excluded_step step_correct 85 25 16 SWARProbe.F85 SWARProbe.F86
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step85 excluded86
theorem excluded84 : Excluded 84 27 16 SWARProbe.F84 :=
  excluded_step step_correct 84 26 16 SWARProbe.F84 SWARProbe.F85
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step84 excluded85
theorem excluded83 : Excluded 83 28 16 SWARProbe.F83 :=
  excluded_step step_correct 83 27 16 SWARProbe.F83 SWARProbe.F84
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step83 excluded84
theorem excluded82 : Excluded 82 29 16 SWARProbe.F82 :=
  excluded_step step_correct 82 28 16 SWARProbe.F82 SWARProbe.F83
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step82 excluded83
theorem excluded81 : Excluded 81 30 16 SWARProbe.F81 :=
  excluded_step step_correct 81 29 16 SWARProbe.F81 SWARProbe.F82
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step81 excluded82
theorem excluded80 : Excluded 80 31 16 SWARProbe.F80 :=
  excluded_step step_correct 80 30 16 SWARProbe.F80 SWARProbe.F81
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step80 excluded81
theorem excluded79 : Excluded 79 32 16 SWARProbe.F79 :=
  excluded_step step_correct 79 31 16 SWARProbe.F79 SWARProbe.F80
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step79 excluded80
theorem excluded78 : Excluded 78 33 16 SWARProbe.F78 :=
  excluded_step step_correct 78 32 16 SWARProbe.F78 SWARProbe.F79
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step78 excluded79
theorem excluded77 : Excluded 77 34 16 SWARProbe.F77 :=
  excluded_step step_correct 77 33 16 SWARProbe.F77 SWARProbe.F78
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step77 excluded78
theorem excluded76 : Excluded 76 35 16 SWARProbe.F76 :=
  excluded_step step_correct 76 34 16 SWARProbe.F76 SWARProbe.F77
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step76 excluded77
theorem excluded75 : Excluded 75 36 16 SWARProbe.F75 :=
  excluded_step step_correct 75 35 16 SWARProbe.F75 SWARProbe.F76
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step75 excluded76
theorem excluded74 : Excluded 74 37 16 SWARProbe.F74 :=
  excluded_step step_correct 74 36 16 SWARProbe.F74 SWARProbe.F75
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step74 excluded75
theorem excluded73 : Excluded 73 38 16 SWARProbe.F73 :=
  excluded_step step_correct 73 37 16 SWARProbe.F73 SWARProbe.F74
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step73 excluded74
theorem excluded72 : Excluded 72 39 16 SWARProbe.F72 :=
  excluded_step step_correct 72 38 16 SWARProbe.F72 SWARProbe.F73
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step72 excluded73
theorem excluded71 : Excluded 71 40 16 SWARProbe.F71 :=
  excluded_step step_correct 71 39 16 SWARProbe.F71 SWARProbe.F72
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step71 excluded72
theorem excluded70 : Excluded 70 41 16 SWARProbe.F70 :=
  excluded_step step_correct 70 40 16 SWARProbe.F70 SWARProbe.F71
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step70 excluded71
theorem excluded69 : Excluded 69 42 16 SWARProbe.F69 :=
  excluded_step step_correct 69 41 16 SWARProbe.F69 SWARProbe.F70
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step69 excluded70
theorem excluded68 : Excluded 68 43 16 SWARProbe.F68 :=
  excluded_step step_correct 68 42 16 SWARProbe.F68 SWARProbe.F69
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step68 excluded69
theorem excluded67 : Excluded 67 44 16 SWARProbe.F67 :=
  excluded_step step_correct 67 43 16 SWARProbe.F67 SWARProbe.F68
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step67 excluded68
theorem excluded66 : Excluded 66 45 16 SWARProbe.F66 :=
  excluded_step step_correct 66 44 16 SWARProbe.F66 SWARProbe.F67
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step66 excluded67
theorem excluded65 : Excluded 65 46 16 SWARProbe.F65 :=
  excluded_step step_correct 65 45 16 SWARProbe.F65 SWARProbe.F66
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step65 excluded66
theorem excluded64 : Excluded 64 47 16 SWARProbe.F64 :=
  excluded_step step_correct 64 46 16 SWARProbe.F64 SWARProbe.F65
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step64 excluded65
theorem excluded63 : Excluded 63 48 16 SWARProbe.F63 :=
  excluded_step step_correct 63 47 16 SWARProbe.F63 SWARProbe.F64
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step63 excluded64
theorem excluded62 : Excluded 62 49 16 SWARProbe.F62 :=
  excluded_step step_correct 62 48 16 SWARProbe.F62 SWARProbe.F63
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step62 excluded63
theorem excluded61 : Excluded 61 50 16 SWARProbe.F61 :=
  excluded_step step_correct 61 49 16 SWARProbe.F61 SWARProbe.F62
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step61 excluded62
theorem excluded60 : Excluded 60 51 16 SWARProbe.F60 :=
  excluded_step step_correct 60 50 16 SWARProbe.F60 SWARProbe.F61
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step60 excluded61
theorem excluded59 : Excluded 59 52 16 SWARProbe.F59 :=
  excluded_step step_correct 59 51 16 SWARProbe.F59 SWARProbe.F60
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step59 excluded60
theorem excluded58 : Excluded 58 53 16 SWARProbe.F58 :=
  excluded_step step_correct 58 52 16 SWARProbe.F58 SWARProbe.F59
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step58 excluded59
theorem excluded57 : Excluded 57 54 16 SWARProbe.F57 :=
  excluded_step step_correct 57 53 16 SWARProbe.F57 SWARProbe.F58
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step57 excluded58
theorem excluded56 : Excluded 56 55 16 SWARProbe.F56 :=
  excluded_step step_correct 56 54 16 SWARProbe.F56 SWARProbe.F57
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step56 excluded57
theorem excluded55 : Excluded 55 56 16 SWARProbe.F55 :=
  excluded_step step_correct 55 55 16 SWARProbe.F55 SWARProbe.F56
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step55 excluded56
theorem excluded54 : Excluded 54 57 16 SWARProbe.F54 :=
  excluded_step step_correct 54 56 16 SWARProbe.F54 SWARProbe.F55
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step54 excluded55
theorem excluded53 : Excluded 53 58 16 SWARProbe.F53 :=
  excluded_step step_correct 53 57 16 SWARProbe.F53 SWARProbe.F54
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step53 excluded54
theorem excluded52 : Excluded 52 59 16 SWARProbe.F52 :=
  excluded_step step_correct 52 58 16 SWARProbe.F52 SWARProbe.F53
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step52 excluded53
theorem excluded51 : Excluded 51 60 16 SWARProbe.F51 :=
  excluded_step step_correct 51 59 16 SWARProbe.F51 SWARProbe.F52
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step51 excluded52
theorem excluded50 : Excluded 50 61 16 SWARProbe.F50 :=
  excluded_step step_correct 50 60 16 SWARProbe.F50 SWARProbe.F51
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step50 excluded51
theorem excluded49 : Excluded 49 62 16 SWARProbe.F49 :=
  excluded_step step_correct 49 61 16 SWARProbe.F49 SWARProbe.F50
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step49 excluded50
theorem excluded48 : Excluded 48 63 16 SWARProbe.F48 :=
  excluded_step step_correct 48 62 16 SWARProbe.F48 SWARProbe.F49
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step48 excluded49
theorem excluded47 : Excluded 47 64 16 SWARProbe.F47 :=
  excluded_step step_correct 47 63 16 SWARProbe.F47 SWARProbe.F48
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step47 excluded48
theorem excluded46 : Excluded 46 65 16 SWARProbe.F46 :=
  excluded_step step_correct 46 64 16 SWARProbe.F46 SWARProbe.F47
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step46 excluded47
theorem excluded45 : Excluded 45 66 16 SWARProbe.F45 :=
  excluded_step step_correct 45 65 16 SWARProbe.F45 SWARProbe.F46
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step45 excluded46
theorem excluded44 : Excluded 44 67 16 SWARProbe.F44 :=
  excluded_step step_correct 44 66 16 SWARProbe.F44 SWARProbe.F45
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step44 excluded45
theorem excluded43 : Excluded 43 68 16 SWARProbe.F43 :=
  excluded_step step_correct 43 67 16 SWARProbe.F43 SWARProbe.F44
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step43 excluded44
theorem excluded42 : Excluded 42 69 16 SWARProbe.F42 :=
  excluded_step step_correct 42 68 16 SWARProbe.F42 SWARProbe.F43
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step42 excluded43
theorem excluded41 : Excluded 41 70 16 SWARProbe.F41 :=
  excluded_step step_correct 41 69 16 SWARProbe.F41 SWARProbe.F42
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step41 excluded42
theorem excluded40 : Excluded 40 71 16 SWARProbe.F40 :=
  excluded_step step_correct 40 70 16 SWARProbe.F40 SWARProbe.F41
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step40 excluded41
theorem excluded39 : Excluded 39 72 16 SWARProbe.F39 :=
  excluded_step step_correct 39 71 16 SWARProbe.F39 SWARProbe.F40
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step39 excluded40
theorem excluded38 : Excluded 38 73 16 SWARProbe.F38 :=
  excluded_step step_correct 38 72 16 SWARProbe.F38 SWARProbe.F39
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step38 excluded39
theorem excluded37 : Excluded 37 74 16 SWARProbe.F37 :=
  excluded_step step_correct 37 73 16 SWARProbe.F37 SWARProbe.F38
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step37 excluded38
theorem excluded36 : Excluded 36 75 16 SWARProbe.F36 :=
  excluded_step step_correct 36 74 16 SWARProbe.F36 SWARProbe.F37
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step36 excluded37
theorem excluded35 : Excluded 35 76 16 SWARProbe.F35 :=
  excluded_step step_correct 35 75 16 SWARProbe.F35 SWARProbe.F36
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step35 excluded36
theorem excluded34 : Excluded 34 77 16 SWARProbe.F34 :=
  excluded_step step_correct 34 76 16 SWARProbe.F34 SWARProbe.F35
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step34 excluded35
theorem excluded33 : Excluded 33 78 16 SWARProbe.F33 :=
  excluded_step step_correct 33 77 16 SWARProbe.F33 SWARProbe.F34
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step33 excluded34
theorem excluded32 : Excluded 32 79 16 SWARProbe.F32 :=
  excluded_step step_correct 32 78 16 SWARProbe.F32 SWARProbe.F33
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step32 excluded33
theorem excluded31 : Excluded 31 80 16 SWARProbe.F31 :=
  excluded_step step_correct 31 79 16 SWARProbe.F31 SWARProbe.F32
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step31 excluded32
theorem excluded30 : Excluded 30 81 16 SWARProbe.F30 :=
  excluded_step step_correct 30 80 16 SWARProbe.F30 SWARProbe.F31
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step30 excluded31
theorem excluded29 : Excluded 29 82 16 SWARProbe.F29 :=
  excluded_step step_correct 29 81 16 SWARProbe.F29 SWARProbe.F30
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step29 excluded30
theorem excluded28 : Excluded 28 83 16 SWARProbe.F28 :=
  excluded_step step_correct 28 82 16 SWARProbe.F28 SWARProbe.F29
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step28 excluded29
theorem excluded27 : Excluded 27 84 16 SWARProbe.F27 :=
  excluded_step step_correct 27 83 16 SWARProbe.F27 SWARProbe.F28
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step27 excluded28
theorem excluded26 : Excluded 26 85 16 SWARProbe.F26 :=
  excluded_step step_correct 26 84 16 SWARProbe.F26 SWARProbe.F27
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step26 excluded27
theorem excluded25 : Excluded 25 86 16 SWARProbe.F25 :=
  excluded_step step_correct 25 85 16 SWARProbe.F25 SWARProbe.F26
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step25 excluded26
theorem excluded24 : Excluded 24 87 16 SWARProbe.F24 :=
  excluded_step step_correct 24 86 16 SWARProbe.F24 SWARProbe.F25
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step24 excluded25
theorem excluded23 : Excluded 23 88 16 SWARProbe.F23 :=
  excluded_step step_correct 23 87 16 SWARProbe.F23 SWARProbe.F24
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step23 excluded24
theorem excluded22 : Excluded 22 89 16 SWARProbe.F22 :=
  excluded_step step_correct 22 88 16 SWARProbe.F22 SWARProbe.F23
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step22 excluded23
theorem excluded21 : Excluded 21 90 16 SWARProbe.F21 :=
  excluded_step step_correct 21 89 16 SWARProbe.F21 SWARProbe.F22
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step21 excluded22
theorem excluded20 : Excluded 20 91 16 SWARProbe.F20 :=
  excluded_step step_correct 20 90 16 SWARProbe.F20 SWARProbe.F21
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step20 excluded21
theorem excluded19 : Excluded 19 92 16 SWARProbe.F19 :=
  excluded_step step_correct 19 91 16 SWARProbe.F19 SWARProbe.F20
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step19 excluded20
theorem excluded18 : Excluded 18 93 16 SWARProbe.F18 :=
  excluded_step step_correct 18 92 16 SWARProbe.F18 SWARProbe.F19
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step18 excluded19
theorem excluded17 : Excluded 17 94 16 SWARProbe.F17 :=
  excluded_step step_correct 17 93 16 SWARProbe.F17 SWARProbe.F18
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step17 excluded18
theorem excluded16 : Excluded 16 95 16 SWARProbe.F16 :=
  excluded_step step_correct 16 94 16 SWARProbe.F16 SWARProbe.F17
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step16 excluded17
theorem excluded15 : Excluded 15 96 16 SWARProbe.F15 :=
  excluded_step step_correct 15 95 16 SWARProbe.F15 SWARProbe.F16
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step15 excluded16
theorem excluded14 : Excluded 14 97 16 SWARProbe.F14 :=
  excluded_step step_correct 14 96 16 SWARProbe.F14 SWARProbe.F15
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step14 excluded15
theorem excluded13 : Excluded 13 98 16 SWARProbe.F13 :=
  excluded_step step_correct 13 97 16 SWARProbe.F13 SWARProbe.F14
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step13 excluded14
theorem excluded12 : Excluded 12 99 16 SWARProbe.F12 :=
  excluded_step step_correct 12 98 16 SWARProbe.F12 SWARProbe.F13
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step12 excluded13
theorem excluded11 : Excluded 11 100 16 SWARProbe.F11 :=
  excluded_step step_correct 11 99 16 SWARProbe.F11 SWARProbe.F12
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step11 excluded12
theorem excluded10 : Excluded 10 101 16 SWARProbe.F10 :=
  excluded_step step_correct 10 100 16 SWARProbe.F10 SWARProbe.F11
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step10 excluded11
theorem excluded9 : Excluded 9 102 16 SWARProbe.F9 :=
  excluded_step step_correct 9 101 16 SWARProbe.F9 SWARProbe.F10
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step9 excluded10
theorem excluded8 : Excluded 8 103 16 SWARProbe.F8 :=
  excluded_step step_correct 8 102 16 SWARProbe.F8 SWARProbe.F9
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step8 excluded9
theorem excluded7 : Excluded 7 104 16 SWARProbe.F7 :=
  excluded_step step_correct 7 103 16 SWARProbe.F7 SWARProbe.F8
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step7 excluded8
theorem excluded6 : Excluded 6 105 16 SWARProbe.F6 :=
  excluded_step step_correct 6 104 16 SWARProbe.F6 SWARProbe.F7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step6 excluded7
theorem excluded5 : Excluded 5 106 16 SWARProbe.F5 :=
  excluded_step step_correct 5 105 16 SWARProbe.F5 SWARProbe.F6
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step5 excluded6
theorem excluded4 : Excluded 4 107 16 SWARProbe.F4 :=
  excluded_step step_correct 4 106 16 SWARProbe.F4 SWARProbe.F5
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step4 excluded5
theorem excluded3 : Excluded 3 108 16 SWARProbe.F3 :=
  excluded_step step_correct 3 107 16 SWARProbe.F3 SWARProbe.F4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step3 excluded4
theorem excluded2 : Excluded 2 109 16 SWARProbe.F2 :=
  excluded_step step_correct 2 108 16 SWARProbe.F2 SWARProbe.F3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step2 excluded3
theorem excluded1 : Excluded 1 110 16 SWARProbe.F1 :=
  excluded_step step_correct 1 109 16 SWARProbe.F1 SWARProbe.F2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step1 excluded2
theorem excluded0 : Excluded 0 111 16 SWARProbe.F0 :=
  excluded_step step_correct 0 110 16 SWARProbe.F0 SWARProbe.F1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    SWARProbe.step0 excluded1

/-- Fifty-six finite even observations force seventeen initial black cells.
The initial tail is unrestricted. -/
theorem fifty_six_even_black_forces_seventeen (L : Nat → Bool)
    (h : ∀ t, t < 56 → zrow L (2*t) 1 = true) :
    17 ≤ Rule30Submission.blackWeight L 0 111 := by
  have he : ∀ t, t < 111 → t%2=0 → zrow L t 1=true := by
    intro t ht hp
    have ht' : t = 2*(t/2) := by omega
    rw [ht']
    exact h (t/2) (by omega)
  have hh := excluded_root_weight 111 16 excluded0 L he
  omega

theorem constrained_weight_ge_seventeen (L : Nat → Bool) (h : InX L) :
    17 ≤ Rule30Submission.blackWeight L 0 111 :=
  fifty_six_even_black_forces_seventeen L (fun t _ => h t)

theorem sparse_even_white (L : Nat → Bool)
    (hw : Rule30Submission.blackWeight L 0 111 ≤ 16) :
    ∃ t, t < 56 ∧ zrow L (2*t) 1 = false := by
  apply Classical.byContradiction
  intro hn
  have he : ∀ t, t < 56 → zrow L (2*t) 1 = true := by
    intro t ht
    cases hb : zrow L (2*t) 1 with
    | false => exact False.elim (hn ⟨t,ht,hb⟩)
    | true => rfl
  have hh := fifty_six_even_black_forces_seventeen L he
  omega

theorem not_inX_of_sparse (L : Nat → Bool)
    (hw : ∀ n, Rule30Submission.blackWeight L 0 n ≤ 16) : ¬ InX L := by
  intro h
  have hh := constrained_weight_ge_seventeen L h
  have hl := hw 111
  omega

theorem alternating_left_weight_ge_seventeen (x : Int → Bool)
    (h : ∀ t, Ruliology.CellularAutomata.Rule30Realization.evol x t 0 =
      Ruliology.CellularAutomata.Rule30PeriodTwoCoupled.altCol t) :
    17 ≤ Rule30Submission.blackWeight (fun k => x (-(k : Int))) 0 111 :=
  constrained_weight_ge_seventeen _
    (Ruliology.CellularAutomata.Rule30PeriodTwoSideways.left_inX x h)


end Ruliology.CellularAutomata.Rule30Sparse16

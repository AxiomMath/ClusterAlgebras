/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the `E8` certificate at the seeds `[23826, 25080)`

This file checks by kernel evaluation that `raw.transOK` holds at every seed in
`[23826, 25080)` and every direction `k < 8`. The range is split into pieces of `8` seeds,
`transOK_19_0` to `transOK_19_156`, assembled by `CertificateCheck.allFrom_add`.

## Main results

* `transOK_19`: `raw.transOK` holds at every seed in `[23826, 25080)` and every direction.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- `raw.transOK` holds at every seed in `[23826, 23834)` and every direction `k < 8`. -/
theorem transOK_19_0 :
    allFrom 23826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23834, 23842)` and every direction `k < 8`. -/
theorem transOK_19_1 :
    allFrom 23834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23842, 23850)` and every direction `k < 8`. -/
theorem transOK_19_2 :
    allFrom 23842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23850, 23858)` and every direction `k < 8`. -/
theorem transOK_19_3 :
    allFrom 23850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23858, 23866)` and every direction `k < 8`. -/
theorem transOK_19_4 :
    allFrom 23858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23866, 23874)` and every direction `k < 8`. -/
theorem transOK_19_5 :
    allFrom 23866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23874, 23882)` and every direction `k < 8`. -/
theorem transOK_19_6 :
    allFrom 23874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23882, 23890)` and every direction `k < 8`. -/
theorem transOK_19_7 :
    allFrom 23882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23890, 23898)` and every direction `k < 8`. -/
theorem transOK_19_8 :
    allFrom 23890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23898, 23906)` and every direction `k < 8`. -/
theorem transOK_19_9 :
    allFrom 23898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23906, 23914)` and every direction `k < 8`. -/
theorem transOK_19_10 :
    allFrom 23906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23914, 23922)` and every direction `k < 8`. -/
theorem transOK_19_11 :
    allFrom 23914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23922, 23930)` and every direction `k < 8`. -/
theorem transOK_19_12 :
    allFrom 23922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23930, 23938)` and every direction `k < 8`. -/
theorem transOK_19_13 :
    allFrom 23930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23938, 23946)` and every direction `k < 8`. -/
theorem transOK_19_14 :
    allFrom 23938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23946, 23954)` and every direction `k < 8`. -/
theorem transOK_19_15 :
    allFrom 23946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23954, 23962)` and every direction `k < 8`. -/
theorem transOK_19_16 :
    allFrom 23954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23962, 23970)` and every direction `k < 8`. -/
theorem transOK_19_17 :
    allFrom 23962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23970, 23978)` and every direction `k < 8`. -/
theorem transOK_19_18 :
    allFrom 23970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23978, 23986)` and every direction `k < 8`. -/
theorem transOK_19_19 :
    allFrom 23978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23986, 23994)` and every direction `k < 8`. -/
theorem transOK_19_20 :
    allFrom 23986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23994, 24002)` and every direction `k < 8`. -/
theorem transOK_19_21 :
    allFrom 23994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24002, 24010)` and every direction `k < 8`. -/
theorem transOK_19_22 :
    allFrom 24002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24010, 24018)` and every direction `k < 8`. -/
theorem transOK_19_23 :
    allFrom 24010 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24018, 24026)` and every direction `k < 8`. -/
theorem transOK_19_24 :
    allFrom 24018 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24026, 24034)` and every direction `k < 8`. -/
theorem transOK_19_25 :
    allFrom 24026 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24034, 24042)` and every direction `k < 8`. -/
theorem transOK_19_26 :
    allFrom 24034 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24042, 24050)` and every direction `k < 8`. -/
theorem transOK_19_27 :
    allFrom 24042 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24050, 24058)` and every direction `k < 8`. -/
theorem transOK_19_28 :
    allFrom 24050 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24058, 24066)` and every direction `k < 8`. -/
theorem transOK_19_29 :
    allFrom 24058 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24066, 24074)` and every direction `k < 8`. -/
theorem transOK_19_30 :
    allFrom 24066 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24074, 24082)` and every direction `k < 8`. -/
theorem transOK_19_31 :
    allFrom 24074 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24082, 24090)` and every direction `k < 8`. -/
theorem transOK_19_32 :
    allFrom 24082 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24090, 24098)` and every direction `k < 8`. -/
theorem transOK_19_33 :
    allFrom 24090 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24098, 24106)` and every direction `k < 8`. -/
theorem transOK_19_34 :
    allFrom 24098 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24106, 24114)` and every direction `k < 8`. -/
theorem transOK_19_35 :
    allFrom 24106 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24114, 24122)` and every direction `k < 8`. -/
theorem transOK_19_36 :
    allFrom 24114 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24122, 24130)` and every direction `k < 8`. -/
theorem transOK_19_37 :
    allFrom 24122 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24130, 24138)` and every direction `k < 8`. -/
theorem transOK_19_38 :
    allFrom 24130 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24138, 24146)` and every direction `k < 8`. -/
theorem transOK_19_39 :
    allFrom 24138 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24146, 24154)` and every direction `k < 8`. -/
theorem transOK_19_40 :
    allFrom 24146 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24154, 24162)` and every direction `k < 8`. -/
theorem transOK_19_41 :
    allFrom 24154 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24162, 24170)` and every direction `k < 8`. -/
theorem transOK_19_42 :
    allFrom 24162 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24170, 24178)` and every direction `k < 8`. -/
theorem transOK_19_43 :
    allFrom 24170 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24178, 24186)` and every direction `k < 8`. -/
theorem transOK_19_44 :
    allFrom 24178 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24186, 24194)` and every direction `k < 8`. -/
theorem transOK_19_45 :
    allFrom 24186 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24194, 24202)` and every direction `k < 8`. -/
theorem transOK_19_46 :
    allFrom 24194 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24202, 24210)` and every direction `k < 8`. -/
theorem transOK_19_47 :
    allFrom 24202 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24210, 24218)` and every direction `k < 8`. -/
theorem transOK_19_48 :
    allFrom 24210 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24218, 24226)` and every direction `k < 8`. -/
theorem transOK_19_49 :
    allFrom 24218 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24226, 24234)` and every direction `k < 8`. -/
theorem transOK_19_50 :
    allFrom 24226 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24234, 24242)` and every direction `k < 8`. -/
theorem transOK_19_51 :
    allFrom 24234 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24242, 24250)` and every direction `k < 8`. -/
theorem transOK_19_52 :
    allFrom 24242 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24250, 24258)` and every direction `k < 8`. -/
theorem transOK_19_53 :
    allFrom 24250 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24258, 24266)` and every direction `k < 8`. -/
theorem transOK_19_54 :
    allFrom 24258 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24266, 24274)` and every direction `k < 8`. -/
theorem transOK_19_55 :
    allFrom 24266 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24274, 24282)` and every direction `k < 8`. -/
theorem transOK_19_56 :
    allFrom 24274 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24282, 24290)` and every direction `k < 8`. -/
theorem transOK_19_57 :
    allFrom 24282 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24290, 24298)` and every direction `k < 8`. -/
theorem transOK_19_58 :
    allFrom 24290 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24298, 24306)` and every direction `k < 8`. -/
theorem transOK_19_59 :
    allFrom 24298 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24306, 24314)` and every direction `k < 8`. -/
theorem transOK_19_60 :
    allFrom 24306 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24314, 24322)` and every direction `k < 8`. -/
theorem transOK_19_61 :
    allFrom 24314 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24322, 24330)` and every direction `k < 8`. -/
theorem transOK_19_62 :
    allFrom 24322 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24330, 24338)` and every direction `k < 8`. -/
theorem transOK_19_63 :
    allFrom 24330 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24338, 24346)` and every direction `k < 8`. -/
theorem transOK_19_64 :
    allFrom 24338 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24346, 24354)` and every direction `k < 8`. -/
theorem transOK_19_65 :
    allFrom 24346 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24354, 24362)` and every direction `k < 8`. -/
theorem transOK_19_66 :
    allFrom 24354 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24362, 24370)` and every direction `k < 8`. -/
theorem transOK_19_67 :
    allFrom 24362 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24370, 24378)` and every direction `k < 8`. -/
theorem transOK_19_68 :
    allFrom 24370 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24378, 24386)` and every direction `k < 8`. -/
theorem transOK_19_69 :
    allFrom 24378 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24386, 24394)` and every direction `k < 8`. -/
theorem transOK_19_70 :
    allFrom 24386 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24394, 24402)` and every direction `k < 8`. -/
theorem transOK_19_71 :
    allFrom 24394 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24402, 24410)` and every direction `k < 8`. -/
theorem transOK_19_72 :
    allFrom 24402 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24410, 24418)` and every direction `k < 8`. -/
theorem transOK_19_73 :
    allFrom 24410 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24418, 24426)` and every direction `k < 8`. -/
theorem transOK_19_74 :
    allFrom 24418 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24426, 24434)` and every direction `k < 8`. -/
theorem transOK_19_75 :
    allFrom 24426 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24434, 24442)` and every direction `k < 8`. -/
theorem transOK_19_76 :
    allFrom 24434 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24442, 24450)` and every direction `k < 8`. -/
theorem transOK_19_77 :
    allFrom 24442 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24450, 24458)` and every direction `k < 8`. -/
theorem transOK_19_78 :
    allFrom 24450 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24458, 24466)` and every direction `k < 8`. -/
theorem transOK_19_79 :
    allFrom 24458 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24466, 24474)` and every direction `k < 8`. -/
theorem transOK_19_80 :
    allFrom 24466 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24474, 24482)` and every direction `k < 8`. -/
theorem transOK_19_81 :
    allFrom 24474 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24482, 24490)` and every direction `k < 8`. -/
theorem transOK_19_82 :
    allFrom 24482 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24490, 24498)` and every direction `k < 8`. -/
theorem transOK_19_83 :
    allFrom 24490 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24498, 24506)` and every direction `k < 8`. -/
theorem transOK_19_84 :
    allFrom 24498 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24506, 24514)` and every direction `k < 8`. -/
theorem transOK_19_85 :
    allFrom 24506 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24514, 24522)` and every direction `k < 8`. -/
theorem transOK_19_86 :
    allFrom 24514 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24522, 24530)` and every direction `k < 8`. -/
theorem transOK_19_87 :
    allFrom 24522 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24530, 24538)` and every direction `k < 8`. -/
theorem transOK_19_88 :
    allFrom 24530 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24538, 24546)` and every direction `k < 8`. -/
theorem transOK_19_89 :
    allFrom 24538 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24546, 24554)` and every direction `k < 8`. -/
theorem transOK_19_90 :
    allFrom 24546 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24554, 24562)` and every direction `k < 8`. -/
theorem transOK_19_91 :
    allFrom 24554 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24562, 24570)` and every direction `k < 8`. -/
theorem transOK_19_92 :
    allFrom 24562 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24570, 24578)` and every direction `k < 8`. -/
theorem transOK_19_93 :
    allFrom 24570 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24578, 24586)` and every direction `k < 8`. -/
theorem transOK_19_94 :
    allFrom 24578 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24586, 24594)` and every direction `k < 8`. -/
theorem transOK_19_95 :
    allFrom 24586 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24594, 24602)` and every direction `k < 8`. -/
theorem transOK_19_96 :
    allFrom 24594 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24602, 24610)` and every direction `k < 8`. -/
theorem transOK_19_97 :
    allFrom 24602 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24610, 24618)` and every direction `k < 8`. -/
theorem transOK_19_98 :
    allFrom 24610 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24618, 24626)` and every direction `k < 8`. -/
theorem transOK_19_99 :
    allFrom 24618 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24626, 24634)` and every direction `k < 8`. -/
theorem transOK_19_100 :
    allFrom 24626 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24634, 24642)` and every direction `k < 8`. -/
theorem transOK_19_101 :
    allFrom 24634 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24642, 24650)` and every direction `k < 8`. -/
theorem transOK_19_102 :
    allFrom 24642 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24650, 24658)` and every direction `k < 8`. -/
theorem transOK_19_103 :
    allFrom 24650 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24658, 24666)` and every direction `k < 8`. -/
theorem transOK_19_104 :
    allFrom 24658 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24666, 24674)` and every direction `k < 8`. -/
theorem transOK_19_105 :
    allFrom 24666 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24674, 24682)` and every direction `k < 8`. -/
theorem transOK_19_106 :
    allFrom 24674 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24682, 24690)` and every direction `k < 8`. -/
theorem transOK_19_107 :
    allFrom 24682 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24690, 24698)` and every direction `k < 8`. -/
theorem transOK_19_108 :
    allFrom 24690 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24698, 24706)` and every direction `k < 8`. -/
theorem transOK_19_109 :
    allFrom 24698 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24706, 24714)` and every direction `k < 8`. -/
theorem transOK_19_110 :
    allFrom 24706 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24714, 24722)` and every direction `k < 8`. -/
theorem transOK_19_111 :
    allFrom 24714 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24722, 24730)` and every direction `k < 8`. -/
theorem transOK_19_112 :
    allFrom 24722 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24730, 24738)` and every direction `k < 8`. -/
theorem transOK_19_113 :
    allFrom 24730 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24738, 24746)` and every direction `k < 8`. -/
theorem transOK_19_114 :
    allFrom 24738 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24746, 24754)` and every direction `k < 8`. -/
theorem transOK_19_115 :
    allFrom 24746 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24754, 24762)` and every direction `k < 8`. -/
theorem transOK_19_116 :
    allFrom 24754 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24762, 24770)` and every direction `k < 8`. -/
theorem transOK_19_117 :
    allFrom 24762 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24770, 24778)` and every direction `k < 8`. -/
theorem transOK_19_118 :
    allFrom 24770 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24778, 24786)` and every direction `k < 8`. -/
theorem transOK_19_119 :
    allFrom 24778 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24786, 24794)` and every direction `k < 8`. -/
theorem transOK_19_120 :
    allFrom 24786 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24794, 24802)` and every direction `k < 8`. -/
theorem transOK_19_121 :
    allFrom 24794 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24802, 24810)` and every direction `k < 8`. -/
theorem transOK_19_122 :
    allFrom 24802 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24810, 24818)` and every direction `k < 8`. -/
theorem transOK_19_123 :
    allFrom 24810 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24818, 24826)` and every direction `k < 8`. -/
theorem transOK_19_124 :
    allFrom 24818 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24826, 24834)` and every direction `k < 8`. -/
theorem transOK_19_125 :
    allFrom 24826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24834, 24842)` and every direction `k < 8`. -/
theorem transOK_19_126 :
    allFrom 24834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24842, 24850)` and every direction `k < 8`. -/
theorem transOK_19_127 :
    allFrom 24842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24850, 24858)` and every direction `k < 8`. -/
theorem transOK_19_128 :
    allFrom 24850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24858, 24866)` and every direction `k < 8`. -/
theorem transOK_19_129 :
    allFrom 24858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24866, 24874)` and every direction `k < 8`. -/
theorem transOK_19_130 :
    allFrom 24866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24874, 24882)` and every direction `k < 8`. -/
theorem transOK_19_131 :
    allFrom 24874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24882, 24890)` and every direction `k < 8`. -/
theorem transOK_19_132 :
    allFrom 24882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24890, 24898)` and every direction `k < 8`. -/
theorem transOK_19_133 :
    allFrom 24890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24898, 24906)` and every direction `k < 8`. -/
theorem transOK_19_134 :
    allFrom 24898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24906, 24914)` and every direction `k < 8`. -/
theorem transOK_19_135 :
    allFrom 24906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24914, 24922)` and every direction `k < 8`. -/
theorem transOK_19_136 :
    allFrom 24914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24922, 24930)` and every direction `k < 8`. -/
theorem transOK_19_137 :
    allFrom 24922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24930, 24938)` and every direction `k < 8`. -/
theorem transOK_19_138 :
    allFrom 24930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24938, 24946)` and every direction `k < 8`. -/
theorem transOK_19_139 :
    allFrom 24938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24946, 24954)` and every direction `k < 8`. -/
theorem transOK_19_140 :
    allFrom 24946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24954, 24962)` and every direction `k < 8`. -/
theorem transOK_19_141 :
    allFrom 24954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24962, 24970)` and every direction `k < 8`. -/
theorem transOK_19_142 :
    allFrom 24962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24970, 24978)` and every direction `k < 8`. -/
theorem transOK_19_143 :
    allFrom 24970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24978, 24986)` and every direction `k < 8`. -/
theorem transOK_19_144 :
    allFrom 24978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24986, 24994)` and every direction `k < 8`. -/
theorem transOK_19_145 :
    allFrom 24986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[24994, 25002)` and every direction `k < 8`. -/
theorem transOK_19_146 :
    allFrom 24994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25002, 25010)` and every direction `k < 8`. -/
theorem transOK_19_147 :
    allFrom 25002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25010, 25018)` and every direction `k < 8`. -/
theorem transOK_19_148 :
    allFrom 25010 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25018, 25026)` and every direction `k < 8`. -/
theorem transOK_19_149 :
    allFrom 25018 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25026, 25034)` and every direction `k < 8`. -/
theorem transOK_19_150 :
    allFrom 25026 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25034, 25042)` and every direction `k < 8`. -/
theorem transOK_19_151 :
    allFrom 25034 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25042, 25050)` and every direction `k < 8`. -/
theorem transOK_19_152 :
    allFrom 25042 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25050, 25058)` and every direction `k < 8`. -/
theorem transOK_19_153 :
    allFrom 25050 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25058, 25066)` and every direction `k < 8`. -/
theorem transOK_19_154 :
    allFrom 25058 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25066, 25074)` and every direction `k < 8`. -/
theorem transOK_19_155 :
    allFrom 25066 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[25074, 25080)` and every direction `k < 8`. -/
theorem transOK_19_156 :
    allFrom 25074 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed in `[23826, 25080)` and every direction `k < 8`. -/
theorem transOK_19 :
    allFrom 23826 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_0
                              transOK_19_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_2
                              transOK_19_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_4
                              transOK_19_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_7
                                  transOK_19_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_9
                              transOK_19_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_12
                                  transOK_19_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_14
                              transOK_19_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_17
                                  transOK_19_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_19
                              transOK_19_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_22
                                  transOK_19_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_24
                              transOK_19_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_27
                                  transOK_19_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_29
                              transOK_19_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_32
                                  transOK_19_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_34
                              transOK_19_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_37
                                  transOK_19_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_39
                              transOK_19_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_41
                              transOK_19_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_43
                              transOK_19_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_46
                                  transOK_19_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_48
                              transOK_19_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_51
                                  transOK_19_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_53
                              transOK_19_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_56
                                  transOK_19_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_58
                              transOK_19_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_61
                                  transOK_19_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_63
                              transOK_19_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_66
                                  transOK_19_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_68
                              transOK_19_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_71
                                  transOK_19_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_73
                              transOK_19_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_76
                                  transOK_19_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_78
                              transOK_19_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_80
                              transOK_19_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_82
                              transOK_19_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_85
                                  transOK_19_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_87
                              transOK_19_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_90
                                  transOK_19_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_92
                              transOK_19_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_95
                                  transOK_19_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_97
                              transOK_19_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_100
                                  transOK_19_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_102
                              transOK_19_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_105
                                  transOK_19_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_107
                              transOK_19_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_110
                                  transOK_19_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_112
                              transOK_19_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_115
                                  transOK_19_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_117
                              transOK_19_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_120
                                  transOK_19_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_122
                              transOK_19_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_125
                                  transOK_19_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_127
                              transOK_19_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_130
                                  transOK_19_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_132
                              transOK_19_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_135
                                  transOK_19_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_137
                              transOK_19_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_140
                                  transOK_19_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_142
                              transOK_19_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_145
                                  transOK_19_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_147
                              transOK_19_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_19_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_19_150
                                  transOK_19_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_19_152
                              transOK_19_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_19_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_19_155
                                  transOK_19_156)))))))

end ClusterAlgebras.CertificateData.E8

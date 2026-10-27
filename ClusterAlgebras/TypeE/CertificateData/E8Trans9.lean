/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-! # Kernel check of the transitions of seeds `[11286, 12540)` of the `E8` certificate,
in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- `transOK` holds at every seed in `[11286, 11294)` and every direction `k < 8`. -/
theorem transOK_9_0 :
    allFrom 11286 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11294, 11302)` and every direction `k < 8`. -/
theorem transOK_9_1 :
    allFrom 11294 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11302, 11310)` and every direction `k < 8`. -/
theorem transOK_9_2 :
    allFrom 11302 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11310, 11318)` and every direction `k < 8`. -/
theorem transOK_9_3 :
    allFrom 11310 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11318, 11326)` and every direction `k < 8`. -/
theorem transOK_9_4 :
    allFrom 11318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11326, 11334)` and every direction `k < 8`. -/
theorem transOK_9_5 :
    allFrom 11326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11334, 11342)` and every direction `k < 8`. -/
theorem transOK_9_6 :
    allFrom 11334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11342, 11350)` and every direction `k < 8`. -/
theorem transOK_9_7 :
    allFrom 11342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11350, 11358)` and every direction `k < 8`. -/
theorem transOK_9_8 :
    allFrom 11350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11358, 11366)` and every direction `k < 8`. -/
theorem transOK_9_9 :
    allFrom 11358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11366, 11374)` and every direction `k < 8`. -/
theorem transOK_9_10 :
    allFrom 11366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11374, 11382)` and every direction `k < 8`. -/
theorem transOK_9_11 :
    allFrom 11374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11382, 11390)` and every direction `k < 8`. -/
theorem transOK_9_12 :
    allFrom 11382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11390, 11398)` and every direction `k < 8`. -/
theorem transOK_9_13 :
    allFrom 11390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11398, 11406)` and every direction `k < 8`. -/
theorem transOK_9_14 :
    allFrom 11398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11406, 11414)` and every direction `k < 8`. -/
theorem transOK_9_15 :
    allFrom 11406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11414, 11422)` and every direction `k < 8`. -/
theorem transOK_9_16 :
    allFrom 11414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11422, 11430)` and every direction `k < 8`. -/
theorem transOK_9_17 :
    allFrom 11422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11430, 11438)` and every direction `k < 8`. -/
theorem transOK_9_18 :
    allFrom 11430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11438, 11446)` and every direction `k < 8`. -/
theorem transOK_9_19 :
    allFrom 11438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11446, 11454)` and every direction `k < 8`. -/
theorem transOK_9_20 :
    allFrom 11446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11454, 11462)` and every direction `k < 8`. -/
theorem transOK_9_21 :
    allFrom 11454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11462, 11470)` and every direction `k < 8`. -/
theorem transOK_9_22 :
    allFrom 11462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11470, 11478)` and every direction `k < 8`. -/
theorem transOK_9_23 :
    allFrom 11470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11478, 11486)` and every direction `k < 8`. -/
theorem transOK_9_24 :
    allFrom 11478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11486, 11494)` and every direction `k < 8`. -/
theorem transOK_9_25 :
    allFrom 11486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11494, 11502)` and every direction `k < 8`. -/
theorem transOK_9_26 :
    allFrom 11494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11502, 11510)` and every direction `k < 8`. -/
theorem transOK_9_27 :
    allFrom 11502 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11510, 11518)` and every direction `k < 8`. -/
theorem transOK_9_28 :
    allFrom 11510 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11518, 11526)` and every direction `k < 8`. -/
theorem transOK_9_29 :
    allFrom 11518 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11526, 11534)` and every direction `k < 8`. -/
theorem transOK_9_30 :
    allFrom 11526 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11534, 11542)` and every direction `k < 8`. -/
theorem transOK_9_31 :
    allFrom 11534 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11542, 11550)` and every direction `k < 8`. -/
theorem transOK_9_32 :
    allFrom 11542 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11550, 11558)` and every direction `k < 8`. -/
theorem transOK_9_33 :
    allFrom 11550 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11558, 11566)` and every direction `k < 8`. -/
theorem transOK_9_34 :
    allFrom 11558 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11566, 11574)` and every direction `k < 8`. -/
theorem transOK_9_35 :
    allFrom 11566 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11574, 11582)` and every direction `k < 8`. -/
theorem transOK_9_36 :
    allFrom 11574 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11582, 11590)` and every direction `k < 8`. -/
theorem transOK_9_37 :
    allFrom 11582 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11590, 11598)` and every direction `k < 8`. -/
theorem transOK_9_38 :
    allFrom 11590 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11598, 11606)` and every direction `k < 8`. -/
theorem transOK_9_39 :
    allFrom 11598 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11606, 11614)` and every direction `k < 8`. -/
theorem transOK_9_40 :
    allFrom 11606 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11614, 11622)` and every direction `k < 8`. -/
theorem transOK_9_41 :
    allFrom 11614 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11622, 11630)` and every direction `k < 8`. -/
theorem transOK_9_42 :
    allFrom 11622 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11630, 11638)` and every direction `k < 8`. -/
theorem transOK_9_43 :
    allFrom 11630 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11638, 11646)` and every direction `k < 8`. -/
theorem transOK_9_44 :
    allFrom 11638 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11646, 11654)` and every direction `k < 8`. -/
theorem transOK_9_45 :
    allFrom 11646 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11654, 11662)` and every direction `k < 8`. -/
theorem transOK_9_46 :
    allFrom 11654 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11662, 11670)` and every direction `k < 8`. -/
theorem transOK_9_47 :
    allFrom 11662 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11670, 11678)` and every direction `k < 8`. -/
theorem transOK_9_48 :
    allFrom 11670 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11678, 11686)` and every direction `k < 8`. -/
theorem transOK_9_49 :
    allFrom 11678 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11686, 11694)` and every direction `k < 8`. -/
theorem transOK_9_50 :
    allFrom 11686 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11694, 11702)` and every direction `k < 8`. -/
theorem transOK_9_51 :
    allFrom 11694 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11702, 11710)` and every direction `k < 8`. -/
theorem transOK_9_52 :
    allFrom 11702 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11710, 11718)` and every direction `k < 8`. -/
theorem transOK_9_53 :
    allFrom 11710 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11718, 11726)` and every direction `k < 8`. -/
theorem transOK_9_54 :
    allFrom 11718 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11726, 11734)` and every direction `k < 8`. -/
theorem transOK_9_55 :
    allFrom 11726 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11734, 11742)` and every direction `k < 8`. -/
theorem transOK_9_56 :
    allFrom 11734 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11742, 11750)` and every direction `k < 8`. -/
theorem transOK_9_57 :
    allFrom 11742 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11750, 11758)` and every direction `k < 8`. -/
theorem transOK_9_58 :
    allFrom 11750 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11758, 11766)` and every direction `k < 8`. -/
theorem transOK_9_59 :
    allFrom 11758 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11766, 11774)` and every direction `k < 8`. -/
theorem transOK_9_60 :
    allFrom 11766 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11774, 11782)` and every direction `k < 8`. -/
theorem transOK_9_61 :
    allFrom 11774 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11782, 11790)` and every direction `k < 8`. -/
theorem transOK_9_62 :
    allFrom 11782 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11790, 11798)` and every direction `k < 8`. -/
theorem transOK_9_63 :
    allFrom 11790 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11798, 11806)` and every direction `k < 8`. -/
theorem transOK_9_64 :
    allFrom 11798 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11806, 11814)` and every direction `k < 8`. -/
theorem transOK_9_65 :
    allFrom 11806 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11814, 11822)` and every direction `k < 8`. -/
theorem transOK_9_66 :
    allFrom 11814 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11822, 11830)` and every direction `k < 8`. -/
theorem transOK_9_67 :
    allFrom 11822 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11830, 11838)` and every direction `k < 8`. -/
theorem transOK_9_68 :
    allFrom 11830 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11838, 11846)` and every direction `k < 8`. -/
theorem transOK_9_69 :
    allFrom 11838 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11846, 11854)` and every direction `k < 8`. -/
theorem transOK_9_70 :
    allFrom 11846 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11854, 11862)` and every direction `k < 8`. -/
theorem transOK_9_71 :
    allFrom 11854 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11862, 11870)` and every direction `k < 8`. -/
theorem transOK_9_72 :
    allFrom 11862 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11870, 11878)` and every direction `k < 8`. -/
theorem transOK_9_73 :
    allFrom 11870 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11878, 11886)` and every direction `k < 8`. -/
theorem transOK_9_74 :
    allFrom 11878 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11886, 11894)` and every direction `k < 8`. -/
theorem transOK_9_75 :
    allFrom 11886 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11894, 11902)` and every direction `k < 8`. -/
theorem transOK_9_76 :
    allFrom 11894 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11902, 11910)` and every direction `k < 8`. -/
theorem transOK_9_77 :
    allFrom 11902 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11910, 11918)` and every direction `k < 8`. -/
theorem transOK_9_78 :
    allFrom 11910 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11918, 11926)` and every direction `k < 8`. -/
theorem transOK_9_79 :
    allFrom 11918 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11926, 11934)` and every direction `k < 8`. -/
theorem transOK_9_80 :
    allFrom 11926 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11934, 11942)` and every direction `k < 8`. -/
theorem transOK_9_81 :
    allFrom 11934 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11942, 11950)` and every direction `k < 8`. -/
theorem transOK_9_82 :
    allFrom 11942 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11950, 11958)` and every direction `k < 8`. -/
theorem transOK_9_83 :
    allFrom 11950 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11958, 11966)` and every direction `k < 8`. -/
theorem transOK_9_84 :
    allFrom 11958 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11966, 11974)` and every direction `k < 8`. -/
theorem transOK_9_85 :
    allFrom 11966 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11974, 11982)` and every direction `k < 8`. -/
theorem transOK_9_86 :
    allFrom 11974 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11982, 11990)` and every direction `k < 8`. -/
theorem transOK_9_87 :
    allFrom 11982 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11990, 11998)` and every direction `k < 8`. -/
theorem transOK_9_88 :
    allFrom 11990 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11998, 12006)` and every direction `k < 8`. -/
theorem transOK_9_89 :
    allFrom 11998 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12006, 12014)` and every direction `k < 8`. -/
theorem transOK_9_90 :
    allFrom 12006 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12014, 12022)` and every direction `k < 8`. -/
theorem transOK_9_91 :
    allFrom 12014 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12022, 12030)` and every direction `k < 8`. -/
theorem transOK_9_92 :
    allFrom 12022 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12030, 12038)` and every direction `k < 8`. -/
theorem transOK_9_93 :
    allFrom 12030 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12038, 12046)` and every direction `k < 8`. -/
theorem transOK_9_94 :
    allFrom 12038 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12046, 12054)` and every direction `k < 8`. -/
theorem transOK_9_95 :
    allFrom 12046 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12054, 12062)` and every direction `k < 8`. -/
theorem transOK_9_96 :
    allFrom 12054 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12062, 12070)` and every direction `k < 8`. -/
theorem transOK_9_97 :
    allFrom 12062 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12070, 12078)` and every direction `k < 8`. -/
theorem transOK_9_98 :
    allFrom 12070 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12078, 12086)` and every direction `k < 8`. -/
theorem transOK_9_99 :
    allFrom 12078 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12086, 12094)` and every direction `k < 8`. -/
theorem transOK_9_100 :
    allFrom 12086 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12094, 12102)` and every direction `k < 8`. -/
theorem transOK_9_101 :
    allFrom 12094 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12102, 12110)` and every direction `k < 8`. -/
theorem transOK_9_102 :
    allFrom 12102 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12110, 12118)` and every direction `k < 8`. -/
theorem transOK_9_103 :
    allFrom 12110 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12118, 12126)` and every direction `k < 8`. -/
theorem transOK_9_104 :
    allFrom 12118 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12126, 12134)` and every direction `k < 8`. -/
theorem transOK_9_105 :
    allFrom 12126 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12134, 12142)` and every direction `k < 8`. -/
theorem transOK_9_106 :
    allFrom 12134 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12142, 12150)` and every direction `k < 8`. -/
theorem transOK_9_107 :
    allFrom 12142 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12150, 12158)` and every direction `k < 8`. -/
theorem transOK_9_108 :
    allFrom 12150 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12158, 12166)` and every direction `k < 8`. -/
theorem transOK_9_109 :
    allFrom 12158 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12166, 12174)` and every direction `k < 8`. -/
theorem transOK_9_110 :
    allFrom 12166 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12174, 12182)` and every direction `k < 8`. -/
theorem transOK_9_111 :
    allFrom 12174 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12182, 12190)` and every direction `k < 8`. -/
theorem transOK_9_112 :
    allFrom 12182 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12190, 12198)` and every direction `k < 8`. -/
theorem transOK_9_113 :
    allFrom 12190 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12198, 12206)` and every direction `k < 8`. -/
theorem transOK_9_114 :
    allFrom 12198 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12206, 12214)` and every direction `k < 8`. -/
theorem transOK_9_115 :
    allFrom 12206 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12214, 12222)` and every direction `k < 8`. -/
theorem transOK_9_116 :
    allFrom 12214 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12222, 12230)` and every direction `k < 8`. -/
theorem transOK_9_117 :
    allFrom 12222 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12230, 12238)` and every direction `k < 8`. -/
theorem transOK_9_118 :
    allFrom 12230 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12238, 12246)` and every direction `k < 8`. -/
theorem transOK_9_119 :
    allFrom 12238 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12246, 12254)` and every direction `k < 8`. -/
theorem transOK_9_120 :
    allFrom 12246 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12254, 12262)` and every direction `k < 8`. -/
theorem transOK_9_121 :
    allFrom 12254 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12262, 12270)` and every direction `k < 8`. -/
theorem transOK_9_122 :
    allFrom 12262 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12270, 12278)` and every direction `k < 8`. -/
theorem transOK_9_123 :
    allFrom 12270 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12278, 12286)` and every direction `k < 8`. -/
theorem transOK_9_124 :
    allFrom 12278 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12286, 12294)` and every direction `k < 8`. -/
theorem transOK_9_125 :
    allFrom 12286 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12294, 12302)` and every direction `k < 8`. -/
theorem transOK_9_126 :
    allFrom 12294 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12302, 12310)` and every direction `k < 8`. -/
theorem transOK_9_127 :
    allFrom 12302 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12310, 12318)` and every direction `k < 8`. -/
theorem transOK_9_128 :
    allFrom 12310 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12318, 12326)` and every direction `k < 8`. -/
theorem transOK_9_129 :
    allFrom 12318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12326, 12334)` and every direction `k < 8`. -/
theorem transOK_9_130 :
    allFrom 12326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12334, 12342)` and every direction `k < 8`. -/
theorem transOK_9_131 :
    allFrom 12334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12342, 12350)` and every direction `k < 8`. -/
theorem transOK_9_132 :
    allFrom 12342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12350, 12358)` and every direction `k < 8`. -/
theorem transOK_9_133 :
    allFrom 12350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12358, 12366)` and every direction `k < 8`. -/
theorem transOK_9_134 :
    allFrom 12358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12366, 12374)` and every direction `k < 8`. -/
theorem transOK_9_135 :
    allFrom 12366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12374, 12382)` and every direction `k < 8`. -/
theorem transOK_9_136 :
    allFrom 12374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12382, 12390)` and every direction `k < 8`. -/
theorem transOK_9_137 :
    allFrom 12382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12390, 12398)` and every direction `k < 8`. -/
theorem transOK_9_138 :
    allFrom 12390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12398, 12406)` and every direction `k < 8`. -/
theorem transOK_9_139 :
    allFrom 12398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12406, 12414)` and every direction `k < 8`. -/
theorem transOK_9_140 :
    allFrom 12406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12414, 12422)` and every direction `k < 8`. -/
theorem transOK_9_141 :
    allFrom 12414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12422, 12430)` and every direction `k < 8`. -/
theorem transOK_9_142 :
    allFrom 12422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12430, 12438)` and every direction `k < 8`. -/
theorem transOK_9_143 :
    allFrom 12430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12438, 12446)` and every direction `k < 8`. -/
theorem transOK_9_144 :
    allFrom 12438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12446, 12454)` and every direction `k < 8`. -/
theorem transOK_9_145 :
    allFrom 12446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12454, 12462)` and every direction `k < 8`. -/
theorem transOK_9_146 :
    allFrom 12454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12462, 12470)` and every direction `k < 8`. -/
theorem transOK_9_147 :
    allFrom 12462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12470, 12478)` and every direction `k < 8`. -/
theorem transOK_9_148 :
    allFrom 12470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12478, 12486)` and every direction `k < 8`. -/
theorem transOK_9_149 :
    allFrom 12478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12486, 12494)` and every direction `k < 8`. -/
theorem transOK_9_150 :
    allFrom 12486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12494, 12502)` and every direction `k < 8`. -/
theorem transOK_9_151 :
    allFrom 12494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12502, 12510)` and every direction `k < 8`. -/
theorem transOK_9_152 :
    allFrom 12502 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12510, 12518)` and every direction `k < 8`. -/
theorem transOK_9_153 :
    allFrom 12510 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12518, 12526)` and every direction `k < 8`. -/
theorem transOK_9_154 :
    allFrom 12518 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12526, 12534)` and every direction `k < 8`. -/
theorem transOK_9_155 :
    allFrom 12526 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[12534, 12540)` and every direction `k < 8`. -/
theorem transOK_9_156 :
    allFrom 12534 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every seed in `[11286, 12540)` and every direction `k < 8`. -/
theorem transOK_9 :
    allFrom 11286 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_0
                              transOK_9_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_2
                              transOK_9_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_4
                              transOK_9_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_7
                                  transOK_9_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_9
                              transOK_9_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_12
                                  transOK_9_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_14
                              transOK_9_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_17
                                  transOK_9_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_19
                              transOK_9_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_22
                                  transOK_9_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_24
                              transOK_9_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_27
                                  transOK_9_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_29
                              transOK_9_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_32
                                  transOK_9_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_34
                              transOK_9_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_37
                                  transOK_9_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_39
                              transOK_9_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_41
                              transOK_9_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_43
                              transOK_9_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_46
                                  transOK_9_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_48
                              transOK_9_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_51
                                  transOK_9_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_53
                              transOK_9_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_56
                                  transOK_9_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_58
                              transOK_9_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_61
                                  transOK_9_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_63
                              transOK_9_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_66
                                  transOK_9_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_68
                              transOK_9_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_71
                                  transOK_9_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_73
                              transOK_9_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_76
                                  transOK_9_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_78
                              transOK_9_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_80
                              transOK_9_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_82
                              transOK_9_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_85
                                  transOK_9_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_87
                              transOK_9_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_90
                                  transOK_9_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_92
                              transOK_9_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_95
                                  transOK_9_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_97
                              transOK_9_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_100
                                  transOK_9_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_102
                              transOK_9_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_105
                                  transOK_9_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_107
                              transOK_9_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_110
                                  transOK_9_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_112
                              transOK_9_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_115
                                  transOK_9_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_117
                              transOK_9_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_120
                                  transOK_9_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_122
                              transOK_9_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_125
                                  transOK_9_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_127
                              transOK_9_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_130
                                  transOK_9_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_132
                              transOK_9_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_135
                                  transOK_9_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_137
                              transOK_9_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_140
                                  transOK_9_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_142
                              transOK_9_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_145
                                  transOK_9_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_147
                              transOK_9_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_9_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_9_150
                                  transOK_9_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_9_152
                              transOK_9_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_9_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_9_155
                                  transOK_9_156)))))))

end ClusterAlgebras.CertificateData.E8

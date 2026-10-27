/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-! # Kernel check of the transitions of seeds `[21318, 22572)` of the `E8` certificate,
in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Every transition of the `E8` certificate out of a seed in `[21318, 21326)` checks. -/
theorem transOK_17_0 :
    allFrom 21318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21326, 21334)` checks. -/
theorem transOK_17_1 :
    allFrom 21326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21334, 21342)` checks. -/
theorem transOK_17_2 :
    allFrom 21334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21342, 21350)` checks. -/
theorem transOK_17_3 :
    allFrom 21342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21350, 21358)` checks. -/
theorem transOK_17_4 :
    allFrom 21350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21358, 21366)` checks. -/
theorem transOK_17_5 :
    allFrom 21358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21366, 21374)` checks. -/
theorem transOK_17_6 :
    allFrom 21366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21374, 21382)` checks. -/
theorem transOK_17_7 :
    allFrom 21374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21382, 21390)` checks. -/
theorem transOK_17_8 :
    allFrom 21382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21390, 21398)` checks. -/
theorem transOK_17_9 :
    allFrom 21390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21398, 21406)` checks. -/
theorem transOK_17_10 :
    allFrom 21398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21406, 21414)` checks. -/
theorem transOK_17_11 :
    allFrom 21406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21414, 21422)` checks. -/
theorem transOK_17_12 :
    allFrom 21414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21422, 21430)` checks. -/
theorem transOK_17_13 :
    allFrom 21422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21430, 21438)` checks. -/
theorem transOK_17_14 :
    allFrom 21430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21438, 21446)` checks. -/
theorem transOK_17_15 :
    allFrom 21438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21446, 21454)` checks. -/
theorem transOK_17_16 :
    allFrom 21446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21454, 21462)` checks. -/
theorem transOK_17_17 :
    allFrom 21454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21462, 21470)` checks. -/
theorem transOK_17_18 :
    allFrom 21462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21470, 21478)` checks. -/
theorem transOK_17_19 :
    allFrom 21470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21478, 21486)` checks. -/
theorem transOK_17_20 :
    allFrom 21478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21486, 21494)` checks. -/
theorem transOK_17_21 :
    allFrom 21486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21494, 21502)` checks. -/
theorem transOK_17_22 :
    allFrom 21494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21502, 21510)` checks. -/
theorem transOK_17_23 :
    allFrom 21502 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21510, 21518)` checks. -/
theorem transOK_17_24 :
    allFrom 21510 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21518, 21526)` checks. -/
theorem transOK_17_25 :
    allFrom 21518 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21526, 21534)` checks. -/
theorem transOK_17_26 :
    allFrom 21526 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21534, 21542)` checks. -/
theorem transOK_17_27 :
    allFrom 21534 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21542, 21550)` checks. -/
theorem transOK_17_28 :
    allFrom 21542 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21550, 21558)` checks. -/
theorem transOK_17_29 :
    allFrom 21550 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21558, 21566)` checks. -/
theorem transOK_17_30 :
    allFrom 21558 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21566, 21574)` checks. -/
theorem transOK_17_31 :
    allFrom 21566 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21574, 21582)` checks. -/
theorem transOK_17_32 :
    allFrom 21574 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21582, 21590)` checks. -/
theorem transOK_17_33 :
    allFrom 21582 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21590, 21598)` checks. -/
theorem transOK_17_34 :
    allFrom 21590 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21598, 21606)` checks. -/
theorem transOK_17_35 :
    allFrom 21598 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21606, 21614)` checks. -/
theorem transOK_17_36 :
    allFrom 21606 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21614, 21622)` checks. -/
theorem transOK_17_37 :
    allFrom 21614 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21622, 21630)` checks. -/
theorem transOK_17_38 :
    allFrom 21622 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21630, 21638)` checks. -/
theorem transOK_17_39 :
    allFrom 21630 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21638, 21646)` checks. -/
theorem transOK_17_40 :
    allFrom 21638 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21646, 21654)` checks. -/
theorem transOK_17_41 :
    allFrom 21646 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21654, 21662)` checks. -/
theorem transOK_17_42 :
    allFrom 21654 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21662, 21670)` checks. -/
theorem transOK_17_43 :
    allFrom 21662 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21670, 21678)` checks. -/
theorem transOK_17_44 :
    allFrom 21670 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21678, 21686)` checks. -/
theorem transOK_17_45 :
    allFrom 21678 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21686, 21694)` checks. -/
theorem transOK_17_46 :
    allFrom 21686 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21694, 21702)` checks. -/
theorem transOK_17_47 :
    allFrom 21694 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21702, 21710)` checks. -/
theorem transOK_17_48 :
    allFrom 21702 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21710, 21718)` checks. -/
theorem transOK_17_49 :
    allFrom 21710 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21718, 21726)` checks. -/
theorem transOK_17_50 :
    allFrom 21718 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21726, 21734)` checks. -/
theorem transOK_17_51 :
    allFrom 21726 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21734, 21742)` checks. -/
theorem transOK_17_52 :
    allFrom 21734 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21742, 21750)` checks. -/
theorem transOK_17_53 :
    allFrom 21742 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21750, 21758)` checks. -/
theorem transOK_17_54 :
    allFrom 21750 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21758, 21766)` checks. -/
theorem transOK_17_55 :
    allFrom 21758 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21766, 21774)` checks. -/
theorem transOK_17_56 :
    allFrom 21766 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21774, 21782)` checks. -/
theorem transOK_17_57 :
    allFrom 21774 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21782, 21790)` checks. -/
theorem transOK_17_58 :
    allFrom 21782 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21790, 21798)` checks. -/
theorem transOK_17_59 :
    allFrom 21790 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21798, 21806)` checks. -/
theorem transOK_17_60 :
    allFrom 21798 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21806, 21814)` checks. -/
theorem transOK_17_61 :
    allFrom 21806 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21814, 21822)` checks. -/
theorem transOK_17_62 :
    allFrom 21814 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21822, 21830)` checks. -/
theorem transOK_17_63 :
    allFrom 21822 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21830, 21838)` checks. -/
theorem transOK_17_64 :
    allFrom 21830 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21838, 21846)` checks. -/
theorem transOK_17_65 :
    allFrom 21838 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21846, 21854)` checks. -/
theorem transOK_17_66 :
    allFrom 21846 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21854, 21862)` checks. -/
theorem transOK_17_67 :
    allFrom 21854 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21862, 21870)` checks. -/
theorem transOK_17_68 :
    allFrom 21862 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21870, 21878)` checks. -/
theorem transOK_17_69 :
    allFrom 21870 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21878, 21886)` checks. -/
theorem transOK_17_70 :
    allFrom 21878 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21886, 21894)` checks. -/
theorem transOK_17_71 :
    allFrom 21886 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21894, 21902)` checks. -/
theorem transOK_17_72 :
    allFrom 21894 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21902, 21910)` checks. -/
theorem transOK_17_73 :
    allFrom 21902 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21910, 21918)` checks. -/
theorem transOK_17_74 :
    allFrom 21910 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21918, 21926)` checks. -/
theorem transOK_17_75 :
    allFrom 21918 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21926, 21934)` checks. -/
theorem transOK_17_76 :
    allFrom 21926 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21934, 21942)` checks. -/
theorem transOK_17_77 :
    allFrom 21934 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21942, 21950)` checks. -/
theorem transOK_17_78 :
    allFrom 21942 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21950, 21958)` checks. -/
theorem transOK_17_79 :
    allFrom 21950 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21958, 21966)` checks. -/
theorem transOK_17_80 :
    allFrom 21958 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21966, 21974)` checks. -/
theorem transOK_17_81 :
    allFrom 21966 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21974, 21982)` checks. -/
theorem transOK_17_82 :
    allFrom 21974 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21982, 21990)` checks. -/
theorem transOK_17_83 :
    allFrom 21982 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21990, 21998)` checks. -/
theorem transOK_17_84 :
    allFrom 21990 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21998, 22006)` checks. -/
theorem transOK_17_85 :
    allFrom 21998 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22006, 22014)` checks. -/
theorem transOK_17_86 :
    allFrom 22006 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22014, 22022)` checks. -/
theorem transOK_17_87 :
    allFrom 22014 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22022, 22030)` checks. -/
theorem transOK_17_88 :
    allFrom 22022 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22030, 22038)` checks. -/
theorem transOK_17_89 :
    allFrom 22030 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22038, 22046)` checks. -/
theorem transOK_17_90 :
    allFrom 22038 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22046, 22054)` checks. -/
theorem transOK_17_91 :
    allFrom 22046 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22054, 22062)` checks. -/
theorem transOK_17_92 :
    allFrom 22054 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22062, 22070)` checks. -/
theorem transOK_17_93 :
    allFrom 22062 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22070, 22078)` checks. -/
theorem transOK_17_94 :
    allFrom 22070 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22078, 22086)` checks. -/
theorem transOK_17_95 :
    allFrom 22078 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22086, 22094)` checks. -/
theorem transOK_17_96 :
    allFrom 22086 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22094, 22102)` checks. -/
theorem transOK_17_97 :
    allFrom 22094 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22102, 22110)` checks. -/
theorem transOK_17_98 :
    allFrom 22102 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22110, 22118)` checks. -/
theorem transOK_17_99 :
    allFrom 22110 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22118, 22126)` checks. -/
theorem transOK_17_100 :
    allFrom 22118 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22126, 22134)` checks. -/
theorem transOK_17_101 :
    allFrom 22126 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22134, 22142)` checks. -/
theorem transOK_17_102 :
    allFrom 22134 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22142, 22150)` checks. -/
theorem transOK_17_103 :
    allFrom 22142 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22150, 22158)` checks. -/
theorem transOK_17_104 :
    allFrom 22150 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22158, 22166)` checks. -/
theorem transOK_17_105 :
    allFrom 22158 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22166, 22174)` checks. -/
theorem transOK_17_106 :
    allFrom 22166 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22174, 22182)` checks. -/
theorem transOK_17_107 :
    allFrom 22174 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22182, 22190)` checks. -/
theorem transOK_17_108 :
    allFrom 22182 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22190, 22198)` checks. -/
theorem transOK_17_109 :
    allFrom 22190 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22198, 22206)` checks. -/
theorem transOK_17_110 :
    allFrom 22198 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22206, 22214)` checks. -/
theorem transOK_17_111 :
    allFrom 22206 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22214, 22222)` checks. -/
theorem transOK_17_112 :
    allFrom 22214 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22222, 22230)` checks. -/
theorem transOK_17_113 :
    allFrom 22222 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22230, 22238)` checks. -/
theorem transOK_17_114 :
    allFrom 22230 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22238, 22246)` checks. -/
theorem transOK_17_115 :
    allFrom 22238 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22246, 22254)` checks. -/
theorem transOK_17_116 :
    allFrom 22246 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22254, 22262)` checks. -/
theorem transOK_17_117 :
    allFrom 22254 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22262, 22270)` checks. -/
theorem transOK_17_118 :
    allFrom 22262 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22270, 22278)` checks. -/
theorem transOK_17_119 :
    allFrom 22270 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22278, 22286)` checks. -/
theorem transOK_17_120 :
    allFrom 22278 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22286, 22294)` checks. -/
theorem transOK_17_121 :
    allFrom 22286 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22294, 22302)` checks. -/
theorem transOK_17_122 :
    allFrom 22294 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22302, 22310)` checks. -/
theorem transOK_17_123 :
    allFrom 22302 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22310, 22318)` checks. -/
theorem transOK_17_124 :
    allFrom 22310 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22318, 22326)` checks. -/
theorem transOK_17_125 :
    allFrom 22318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22326, 22334)` checks. -/
theorem transOK_17_126 :
    allFrom 22326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22334, 22342)` checks. -/
theorem transOK_17_127 :
    allFrom 22334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22342, 22350)` checks. -/
theorem transOK_17_128 :
    allFrom 22342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22350, 22358)` checks. -/
theorem transOK_17_129 :
    allFrom 22350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22358, 22366)` checks. -/
theorem transOK_17_130 :
    allFrom 22358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22366, 22374)` checks. -/
theorem transOK_17_131 :
    allFrom 22366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22374, 22382)` checks. -/
theorem transOK_17_132 :
    allFrom 22374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22382, 22390)` checks. -/
theorem transOK_17_133 :
    allFrom 22382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22390, 22398)` checks. -/
theorem transOK_17_134 :
    allFrom 22390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22398, 22406)` checks. -/
theorem transOK_17_135 :
    allFrom 22398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22406, 22414)` checks. -/
theorem transOK_17_136 :
    allFrom 22406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22414, 22422)` checks. -/
theorem transOK_17_137 :
    allFrom 22414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22422, 22430)` checks. -/
theorem transOK_17_138 :
    allFrom 22422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22430, 22438)` checks. -/
theorem transOK_17_139 :
    allFrom 22430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22438, 22446)` checks. -/
theorem transOK_17_140 :
    allFrom 22438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22446, 22454)` checks. -/
theorem transOK_17_141 :
    allFrom 22446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22454, 22462)` checks. -/
theorem transOK_17_142 :
    allFrom 22454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22462, 22470)` checks. -/
theorem transOK_17_143 :
    allFrom 22462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22470, 22478)` checks. -/
theorem transOK_17_144 :
    allFrom 22470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22478, 22486)` checks. -/
theorem transOK_17_145 :
    allFrom 22478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22486, 22494)` checks. -/
theorem transOK_17_146 :
    allFrom 22486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22494, 22502)` checks. -/
theorem transOK_17_147 :
    allFrom 22494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22502, 22510)` checks. -/
theorem transOK_17_148 :
    allFrom 22502 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22510, 22518)` checks. -/
theorem transOK_17_149 :
    allFrom 22510 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22518, 22526)` checks. -/
theorem transOK_17_150 :
    allFrom 22518 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22526, 22534)` checks. -/
theorem transOK_17_151 :
    allFrom 22526 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22534, 22542)` checks. -/
theorem transOK_17_152 :
    allFrom 22534 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22542, 22550)` checks. -/
theorem transOK_17_153 :
    allFrom 22542 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22550, 22558)` checks. -/
theorem transOK_17_154 :
    allFrom 22550 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22558, 22566)` checks. -/
theorem transOK_17_155 :
    allFrom 22558 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[22566, 22572)` checks. -/
theorem transOK_17_156 :
    allFrom 22566 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[21318, 22572)` checks. -/
theorem transOK_17 :
    allFrom 21318 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_0
                              transOK_17_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_2
                              transOK_17_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_4
                              transOK_17_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_7
                                  transOK_17_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_9
                              transOK_17_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_12
                                  transOK_17_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_14
                              transOK_17_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_17
                                  transOK_17_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_19
                              transOK_17_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_22
                                  transOK_17_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_24
                              transOK_17_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_27
                                  transOK_17_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_29
                              transOK_17_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_32
                                  transOK_17_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_34
                              transOK_17_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_37
                                  transOK_17_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_39
                              transOK_17_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_41
                              transOK_17_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_43
                              transOK_17_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_46
                                  transOK_17_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_48
                              transOK_17_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_51
                                  transOK_17_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_53
                              transOK_17_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_56
                                  transOK_17_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_58
                              transOK_17_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_61
                                  transOK_17_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_63
                              transOK_17_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_66
                                  transOK_17_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_68
                              transOK_17_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_71
                                  transOK_17_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_73
                              transOK_17_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_76
                                  transOK_17_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_78
                              transOK_17_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_80
                              transOK_17_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_82
                              transOK_17_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_85
                                  transOK_17_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_87
                              transOK_17_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_90
                                  transOK_17_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_92
                              transOK_17_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_95
                                  transOK_17_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_97
                              transOK_17_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_100
                                  transOK_17_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_102
                              transOK_17_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_105
                                  transOK_17_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_107
                              transOK_17_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_110
                                  transOK_17_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_112
                              transOK_17_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_115
                                  transOK_17_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_117
                              transOK_17_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_120
                                  transOK_17_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_122
                              transOK_17_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_125
                                  transOK_17_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_127
                              transOK_17_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_130
                                  transOK_17_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_132
                              transOK_17_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_135
                                  transOK_17_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_137
                              transOK_17_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_140
                                  transOK_17_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_142
                              transOK_17_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_145
                                  transOK_17_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_147
                              transOK_17_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_17_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_17_150
                                  transOK_17_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_17_152
                              transOK_17_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_17_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_17_155
                                  transOK_17_156)))))))

end ClusterAlgebras.CertificateData.E8

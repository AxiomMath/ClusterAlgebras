/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the seeds `[6270, 7524)` of the `E8` certificate

Every transition out of the seeds `[6270, 7524)` of the `E8` certificate passes
`CertificateCheck.Raw.transOK`, checked by the kernel in pieces of `8` seeds and assembled by
`CertificateCheck.allFrom_add`.

## Main results

* `transOK_5`: every transition out of the seeds `[6270, 7524)` passes `transOK`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Every transition out of the seeds `[6270, 6278)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_0 :
    allFrom 6270 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6278, 6286)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_1 :
    allFrom 6278 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6286, 6294)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_2 :
    allFrom 6286 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6294, 6302)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_3 :
    allFrom 6294 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6302, 6310)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_4 :
    allFrom 6302 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6310, 6318)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_5 :
    allFrom 6310 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6318, 6326)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_6 :
    allFrom 6318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6326, 6334)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_7 :
    allFrom 6326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6334, 6342)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_8 :
    allFrom 6334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6342, 6350)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_9 :
    allFrom 6342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6350, 6358)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_10 :
    allFrom 6350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6358, 6366)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_11 :
    allFrom 6358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6366, 6374)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_12 :
    allFrom 6366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6374, 6382)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_13 :
    allFrom 6374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6382, 6390)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_14 :
    allFrom 6382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6390, 6398)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_15 :
    allFrom 6390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6398, 6406)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_16 :
    allFrom 6398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6406, 6414)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_17 :
    allFrom 6406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6414, 6422)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_18 :
    allFrom 6414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6422, 6430)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_19 :
    allFrom 6422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6430, 6438)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_20 :
    allFrom 6430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6438, 6446)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_21 :
    allFrom 6438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6446, 6454)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_22 :
    allFrom 6446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6454, 6462)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_23 :
    allFrom 6454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6462, 6470)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_24 :
    allFrom 6462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6470, 6478)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_25 :
    allFrom 6470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6478, 6486)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_26 :
    allFrom 6478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6486, 6494)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_27 :
    allFrom 6486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6494, 6502)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_28 :
    allFrom 6494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6502, 6510)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_29 :
    allFrom 6502 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6510, 6518)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_30 :
    allFrom 6510 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6518, 6526)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_31 :
    allFrom 6518 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6526, 6534)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_32 :
    allFrom 6526 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6534, 6542)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_33 :
    allFrom 6534 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6542, 6550)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_34 :
    allFrom 6542 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6550, 6558)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_35 :
    allFrom 6550 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6558, 6566)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_36 :
    allFrom 6558 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6566, 6574)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_37 :
    allFrom 6566 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6574, 6582)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_38 :
    allFrom 6574 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6582, 6590)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_39 :
    allFrom 6582 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6590, 6598)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_40 :
    allFrom 6590 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6598, 6606)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_41 :
    allFrom 6598 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6606, 6614)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_42 :
    allFrom 6606 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6614, 6622)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_43 :
    allFrom 6614 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6622, 6630)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_44 :
    allFrom 6622 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6630, 6638)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_45 :
    allFrom 6630 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6638, 6646)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_46 :
    allFrom 6638 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6646, 6654)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_47 :
    allFrom 6646 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6654, 6662)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_48 :
    allFrom 6654 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6662, 6670)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_49 :
    allFrom 6662 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6670, 6678)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_50 :
    allFrom 6670 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6678, 6686)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_51 :
    allFrom 6678 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6686, 6694)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_52 :
    allFrom 6686 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6694, 6702)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_53 :
    allFrom 6694 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6702, 6710)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_54 :
    allFrom 6702 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6710, 6718)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_55 :
    allFrom 6710 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6718, 6726)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_56 :
    allFrom 6718 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6726, 6734)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_57 :
    allFrom 6726 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6734, 6742)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_58 :
    allFrom 6734 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6742, 6750)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_59 :
    allFrom 6742 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6750, 6758)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_60 :
    allFrom 6750 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6758, 6766)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_61 :
    allFrom 6758 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6766, 6774)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_62 :
    allFrom 6766 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6774, 6782)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_63 :
    allFrom 6774 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6782, 6790)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_64 :
    allFrom 6782 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6790, 6798)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_65 :
    allFrom 6790 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6798, 6806)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_66 :
    allFrom 6798 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6806, 6814)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_67 :
    allFrom 6806 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6814, 6822)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_68 :
    allFrom 6814 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6822, 6830)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_69 :
    allFrom 6822 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6830, 6838)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_70 :
    allFrom 6830 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6838, 6846)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_71 :
    allFrom 6838 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6846, 6854)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_72 :
    allFrom 6846 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6854, 6862)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_73 :
    allFrom 6854 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6862, 6870)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_74 :
    allFrom 6862 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6870, 6878)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_75 :
    allFrom 6870 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6878, 6886)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_76 :
    allFrom 6878 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6886, 6894)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_77 :
    allFrom 6886 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6894, 6902)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_78 :
    allFrom 6894 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6902, 6910)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_79 :
    allFrom 6902 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6910, 6918)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_80 :
    allFrom 6910 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6918, 6926)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_81 :
    allFrom 6918 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6926, 6934)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_82 :
    allFrom 6926 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6934, 6942)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_83 :
    allFrom 6934 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6942, 6950)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_84 :
    allFrom 6942 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6950, 6958)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_85 :
    allFrom 6950 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6958, 6966)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_86 :
    allFrom 6958 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6966, 6974)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_87 :
    allFrom 6966 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6974, 6982)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_88 :
    allFrom 6974 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6982, 6990)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_89 :
    allFrom 6982 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6990, 6998)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_90 :
    allFrom 6990 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6998, 7006)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_91 :
    allFrom 6998 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7006, 7014)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_92 :
    allFrom 7006 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7014, 7022)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_93 :
    allFrom 7014 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7022, 7030)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_94 :
    allFrom 7022 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7030, 7038)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_95 :
    allFrom 7030 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7038, 7046)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_96 :
    allFrom 7038 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7046, 7054)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_97 :
    allFrom 7046 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7054, 7062)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_98 :
    allFrom 7054 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7062, 7070)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_99 :
    allFrom 7062 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7070, 7078)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_100 :
    allFrom 7070 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7078, 7086)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_101 :
    allFrom 7078 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7086, 7094)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_102 :
    allFrom 7086 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7094, 7102)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_103 :
    allFrom 7094 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7102, 7110)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_104 :
    allFrom 7102 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7110, 7118)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_105 :
    allFrom 7110 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7118, 7126)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_106 :
    allFrom 7118 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7126, 7134)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_107 :
    allFrom 7126 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7134, 7142)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_108 :
    allFrom 7134 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7142, 7150)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_109 :
    allFrom 7142 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7150, 7158)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_110 :
    allFrom 7150 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7158, 7166)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_111 :
    allFrom 7158 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7166, 7174)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_112 :
    allFrom 7166 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7174, 7182)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_113 :
    allFrom 7174 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7182, 7190)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_114 :
    allFrom 7182 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7190, 7198)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_115 :
    allFrom 7190 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7198, 7206)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_116 :
    allFrom 7198 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7206, 7214)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_117 :
    allFrom 7206 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7214, 7222)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_118 :
    allFrom 7214 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7222, 7230)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_119 :
    allFrom 7222 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7230, 7238)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_120 :
    allFrom 7230 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7238, 7246)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_121 :
    allFrom 7238 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7246, 7254)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_122 :
    allFrom 7246 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7254, 7262)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_123 :
    allFrom 7254 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7262, 7270)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_124 :
    allFrom 7262 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7270, 7278)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_125 :
    allFrom 7270 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7278, 7286)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_126 :
    allFrom 7278 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7286, 7294)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_127 :
    allFrom 7286 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7294, 7302)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_128 :
    allFrom 7294 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7302, 7310)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_129 :
    allFrom 7302 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7310, 7318)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_130 :
    allFrom 7310 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7318, 7326)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_131 :
    allFrom 7318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7326, 7334)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_132 :
    allFrom 7326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7334, 7342)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_133 :
    allFrom 7334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7342, 7350)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_134 :
    allFrom 7342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7350, 7358)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_135 :
    allFrom 7350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7358, 7366)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_136 :
    allFrom 7358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7366, 7374)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_137 :
    allFrom 7366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7374, 7382)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_138 :
    allFrom 7374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7382, 7390)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_139 :
    allFrom 7382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7390, 7398)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_140 :
    allFrom 7390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7398, 7406)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_141 :
    allFrom 7398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7406, 7414)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_142 :
    allFrom 7406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7414, 7422)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_143 :
    allFrom 7414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7422, 7430)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_144 :
    allFrom 7422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7430, 7438)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_145 :
    allFrom 7430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7438, 7446)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_146 :
    allFrom 7438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7446, 7454)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_147 :
    allFrom 7446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7454, 7462)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_148 :
    allFrom 7454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7462, 7470)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_149 :
    allFrom 7462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7470, 7478)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_150 :
    allFrom 7470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7478, 7486)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_151 :
    allFrom 7478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7486, 7494)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_152 :
    allFrom 7486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7494, 7502)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_153 :
    allFrom 7494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7502, 7510)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_154 :
    allFrom 7502 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7510, 7518)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_155 :
    allFrom 7510 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[7518, 7524)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5_156 :
    allFrom 7518 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `[6270, 7524)` of the `E8` certificate passes `transOK`. -/
theorem transOK_5 :
    allFrom 6270 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_0
                              transOK_5_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_2
                              transOK_5_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_4
                              transOK_5_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_7
                                  transOK_5_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_9
                              transOK_5_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_12
                                  transOK_5_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_14
                              transOK_5_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_17
                                  transOK_5_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_19
                              transOK_5_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_22
                                  transOK_5_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_24
                              transOK_5_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_27
                                  transOK_5_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_29
                              transOK_5_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_32
                                  transOK_5_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_34
                              transOK_5_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_37
                                  transOK_5_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_39
                              transOK_5_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_41
                              transOK_5_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_43
                              transOK_5_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_46
                                  transOK_5_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_48
                              transOK_5_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_51
                                  transOK_5_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_53
                              transOK_5_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_56
                                  transOK_5_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_58
                              transOK_5_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_61
                                  transOK_5_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_63
                              transOK_5_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_66
                                  transOK_5_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_68
                              transOK_5_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_71
                                  transOK_5_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_73
                              transOK_5_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_76
                                  transOK_5_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_78
                              transOK_5_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_80
                              transOK_5_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_82
                              transOK_5_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_85
                                  transOK_5_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_87
                              transOK_5_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_90
                                  transOK_5_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_92
                              transOK_5_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_95
                                  transOK_5_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_97
                              transOK_5_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_100
                                  transOK_5_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_102
                              transOK_5_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_105
                                  transOK_5_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_107
                              transOK_5_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_110
                                  transOK_5_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_112
                              transOK_5_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_115
                                  transOK_5_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_117
                              transOK_5_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_120
                                  transOK_5_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_122
                              transOK_5_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_125
                                  transOK_5_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_127
                              transOK_5_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_130
                                  transOK_5_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_132
                              transOK_5_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_135
                                  transOK_5_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_137
                              transOK_5_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_140
                                  transOK_5_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_142
                              transOK_5_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_145
                                  transOK_5_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_147
                              transOK_5_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_5_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_5_150
                                  transOK_5_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_5_152
                              transOK_5_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_5_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_5_155
                                  transOK_5_156)))))))

end ClusterAlgebras.CertificateData.E8

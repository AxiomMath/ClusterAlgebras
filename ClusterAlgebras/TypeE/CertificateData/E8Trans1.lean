/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of seeds `[1254, 2508)` of the `E8` certificate

Every seed of `raw` with index in `[1254, 2508)` passes `transOK` in each direction, checked by
kernel evaluation in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add`.

## Main results

* `transOK_1`: every seed of `raw` with index in `[1254, 2508)` passes `transOK` in each
  direction `k < 8`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Every seed of `raw` in `[1254, 1262)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_0 :
    allFrom 1254 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1262, 1270)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_1 :
    allFrom 1262 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1270, 1278)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_2 :
    allFrom 1270 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1278, 1286)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_3 :
    allFrom 1278 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1286, 1294)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_4 :
    allFrom 1286 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1294, 1302)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_5 :
    allFrom 1294 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1302, 1310)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_6 :
    allFrom 1302 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1310, 1318)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_7 :
    allFrom 1310 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1318, 1326)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_8 :
    allFrom 1318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1326, 1334)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_9 :
    allFrom 1326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1334, 1342)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_10 :
    allFrom 1334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1342, 1350)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_11 :
    allFrom 1342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1350, 1358)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_12 :
    allFrom 1350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1358, 1366)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_13 :
    allFrom 1358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1366, 1374)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_14 :
    allFrom 1366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1374, 1382)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_15 :
    allFrom 1374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1382, 1390)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_16 :
    allFrom 1382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1390, 1398)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_17 :
    allFrom 1390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1398, 1406)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_18 :
    allFrom 1398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1406, 1414)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_19 :
    allFrom 1406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1414, 1422)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_20 :
    allFrom 1414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1422, 1430)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_21 :
    allFrom 1422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1430, 1438)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_22 :
    allFrom 1430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1438, 1446)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_23 :
    allFrom 1438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1446, 1454)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_24 :
    allFrom 1446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1454, 1462)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_25 :
    allFrom 1454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1462, 1470)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_26 :
    allFrom 1462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1470, 1478)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_27 :
    allFrom 1470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1478, 1486)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_28 :
    allFrom 1478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1486, 1494)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_29 :
    allFrom 1486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1494, 1502)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_30 :
    allFrom 1494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1502, 1510)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_31 :
    allFrom 1502 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1510, 1518)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_32 :
    allFrom 1510 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1518, 1526)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_33 :
    allFrom 1518 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1526, 1534)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_34 :
    allFrom 1526 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1534, 1542)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_35 :
    allFrom 1534 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1542, 1550)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_36 :
    allFrom 1542 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1550, 1558)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_37 :
    allFrom 1550 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1558, 1566)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_38 :
    allFrom 1558 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1566, 1574)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_39 :
    allFrom 1566 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1574, 1582)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_40 :
    allFrom 1574 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1582, 1590)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_41 :
    allFrom 1582 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1590, 1598)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_42 :
    allFrom 1590 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1598, 1606)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_43 :
    allFrom 1598 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1606, 1614)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_44 :
    allFrom 1606 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1614, 1622)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_45 :
    allFrom 1614 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1622, 1630)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_46 :
    allFrom 1622 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1630, 1638)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_47 :
    allFrom 1630 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1638, 1646)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_48 :
    allFrom 1638 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1646, 1654)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_49 :
    allFrom 1646 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1654, 1662)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_50 :
    allFrom 1654 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1662, 1670)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_51 :
    allFrom 1662 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1670, 1678)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_52 :
    allFrom 1670 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1678, 1686)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_53 :
    allFrom 1678 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1686, 1694)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_54 :
    allFrom 1686 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1694, 1702)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_55 :
    allFrom 1694 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1702, 1710)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_56 :
    allFrom 1702 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1710, 1718)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_57 :
    allFrom 1710 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1718, 1726)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_58 :
    allFrom 1718 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1726, 1734)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_59 :
    allFrom 1726 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1734, 1742)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_60 :
    allFrom 1734 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1742, 1750)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_61 :
    allFrom 1742 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1750, 1758)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_62 :
    allFrom 1750 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1758, 1766)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_63 :
    allFrom 1758 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1766, 1774)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_64 :
    allFrom 1766 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1774, 1782)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_65 :
    allFrom 1774 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1782, 1790)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_66 :
    allFrom 1782 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1790, 1798)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_67 :
    allFrom 1790 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1798, 1806)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_68 :
    allFrom 1798 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1806, 1814)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_69 :
    allFrom 1806 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1814, 1822)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_70 :
    allFrom 1814 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1822, 1830)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_71 :
    allFrom 1822 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1830, 1838)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_72 :
    allFrom 1830 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1838, 1846)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_73 :
    allFrom 1838 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1846, 1854)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_74 :
    allFrom 1846 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1854, 1862)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_75 :
    allFrom 1854 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1862, 1870)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_76 :
    allFrom 1862 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1870, 1878)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_77 :
    allFrom 1870 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1878, 1886)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_78 :
    allFrom 1878 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1886, 1894)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_79 :
    allFrom 1886 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1894, 1902)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_80 :
    allFrom 1894 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1902, 1910)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_81 :
    allFrom 1902 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1910, 1918)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_82 :
    allFrom 1910 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1918, 1926)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_83 :
    allFrom 1918 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1926, 1934)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_84 :
    allFrom 1926 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1934, 1942)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_85 :
    allFrom 1934 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1942, 1950)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_86 :
    allFrom 1942 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1950, 1958)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_87 :
    allFrom 1950 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1958, 1966)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_88 :
    allFrom 1958 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1966, 1974)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_89 :
    allFrom 1966 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1974, 1982)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_90 :
    allFrom 1974 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1982, 1990)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_91 :
    allFrom 1982 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1990, 1998)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_92 :
    allFrom 1990 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1998, 2006)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_93 :
    allFrom 1998 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2006, 2014)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_94 :
    allFrom 2006 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2014, 2022)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_95 :
    allFrom 2014 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2022, 2030)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_96 :
    allFrom 2022 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2030, 2038)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_97 :
    allFrom 2030 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2038, 2046)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_98 :
    allFrom 2038 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2046, 2054)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_99 :
    allFrom 2046 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2054, 2062)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_100 :
    allFrom 2054 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2062, 2070)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_101 :
    allFrom 2062 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2070, 2078)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_102 :
    allFrom 2070 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2078, 2086)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_103 :
    allFrom 2078 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2086, 2094)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_104 :
    allFrom 2086 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2094, 2102)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_105 :
    allFrom 2094 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2102, 2110)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_106 :
    allFrom 2102 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2110, 2118)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_107 :
    allFrom 2110 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2118, 2126)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_108 :
    allFrom 2118 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2126, 2134)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_109 :
    allFrom 2126 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2134, 2142)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_110 :
    allFrom 2134 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2142, 2150)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_111 :
    allFrom 2142 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2150, 2158)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_112 :
    allFrom 2150 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2158, 2166)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_113 :
    allFrom 2158 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2166, 2174)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_114 :
    allFrom 2166 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2174, 2182)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_115 :
    allFrom 2174 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2182, 2190)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_116 :
    allFrom 2182 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2190, 2198)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_117 :
    allFrom 2190 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2198, 2206)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_118 :
    allFrom 2198 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2206, 2214)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_119 :
    allFrom 2206 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2214, 2222)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_120 :
    allFrom 2214 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2222, 2230)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_121 :
    allFrom 2222 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2230, 2238)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_122 :
    allFrom 2230 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2238, 2246)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_123 :
    allFrom 2238 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2246, 2254)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_124 :
    allFrom 2246 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2254, 2262)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_125 :
    allFrom 2254 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2262, 2270)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_126 :
    allFrom 2262 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2270, 2278)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_127 :
    allFrom 2270 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2278, 2286)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_128 :
    allFrom 2278 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2286, 2294)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_129 :
    allFrom 2286 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2294, 2302)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_130 :
    allFrom 2294 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2302, 2310)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_131 :
    allFrom 2302 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2310, 2318)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_132 :
    allFrom 2310 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2318, 2326)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_133 :
    allFrom 2318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2326, 2334)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_134 :
    allFrom 2326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2334, 2342)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_135 :
    allFrom 2334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2342, 2350)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_136 :
    allFrom 2342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2350, 2358)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_137 :
    allFrom 2350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2358, 2366)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_138 :
    allFrom 2358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2366, 2374)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_139 :
    allFrom 2366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2374, 2382)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_140 :
    allFrom 2374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2382, 2390)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_141 :
    allFrom 2382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2390, 2398)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_142 :
    allFrom 2390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2398, 2406)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_143 :
    allFrom 2398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2406, 2414)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_144 :
    allFrom 2406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2414, 2422)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_145 :
    allFrom 2414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2422, 2430)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_146 :
    allFrom 2422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2430, 2438)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_147 :
    allFrom 2430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2438, 2446)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_148 :
    allFrom 2438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2446, 2454)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_149 :
    allFrom 2446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2454, 2462)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_150 :
    allFrom 2454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2462, 2470)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_151 :
    allFrom 2462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2470, 2478)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_152 :
    allFrom 2470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2478, 2486)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_153 :
    allFrom 2478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2486, 2494)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_154 :
    allFrom 2486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2494, 2502)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_155 :
    allFrom 2494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[2502, 2508)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1_156 :
    allFrom 2502 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of `raw` in `[1254, 2508)` passes `transOK` in each direction `k < 8`. -/
theorem transOK_1 :
    allFrom 1254 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_0
                              transOK_1_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_2
                              transOK_1_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_4
                              transOK_1_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_7
                                  transOK_1_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_9
                              transOK_1_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_12
                                  transOK_1_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_14
                              transOK_1_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_17
                                  transOK_1_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_19
                              transOK_1_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_22
                                  transOK_1_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_24
                              transOK_1_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_27
                                  transOK_1_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_29
                              transOK_1_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_32
                                  transOK_1_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_34
                              transOK_1_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_37
                                  transOK_1_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_39
                              transOK_1_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_41
                              transOK_1_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_43
                              transOK_1_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_46
                                  transOK_1_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_48
                              transOK_1_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_51
                                  transOK_1_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_53
                              transOK_1_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_56
                                  transOK_1_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_58
                              transOK_1_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_61
                                  transOK_1_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_63
                              transOK_1_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_66
                                  transOK_1_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_68
                              transOK_1_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_71
                                  transOK_1_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_73
                              transOK_1_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_76
                                  transOK_1_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_78
                              transOK_1_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_80
                              transOK_1_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_82
                              transOK_1_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_85
                                  transOK_1_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_87
                              transOK_1_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_90
                                  transOK_1_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_92
                              transOK_1_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_95
                                  transOK_1_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_97
                              transOK_1_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_100
                                  transOK_1_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_102
                              transOK_1_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_105
                                  transOK_1_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_107
                              transOK_1_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_110
                                  transOK_1_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_112
                              transOK_1_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_115
                                  transOK_1_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_117
                              transOK_1_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_120
                                  transOK_1_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_122
                              transOK_1_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_125
                                  transOK_1_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_127
                              transOK_1_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_130
                                  transOK_1_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_132
                              transOK_1_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_135
                                  transOK_1_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_137
                              transOK_1_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_140
                                  transOK_1_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_142
                              transOK_1_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_145
                                  transOK_1_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_147
                              transOK_1_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_1_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_150
                                  transOK_1_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_1_152
                              transOK_1_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_1_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_1_155
                                  transOK_1_156)))))))

end ClusterAlgebras.CertificateData.E8

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Exchange relations `[1047, 1884)` of the `E8` certificate

The exchange relations of `raw` with indices in `[1047, 1884)` are checked by kernel evaluation
of `relOKD`, in pieces of `16` relations assembled by `CertificateCheck.allFrom_add`.

## Main results

* `relOK_1`: the exchange relations of `raw` with indices in `[1047, 1884)` hold.

## Implementation notes

Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the cost
of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel checks of the
pieces would hold their memory until the end of the file, so it is disabled.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

set_option Elab.async false

/-- The exchange relations of `raw` with indices in `[1047, 1063)` hold, as checked by `relOKD`. -/
theorem relOK_1_0 :
    allFrom 1047 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1063, 1079)` hold, as checked by `relOKD`. -/
theorem relOK_1_1 :
    allFrom 1063 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1079, 1095)` hold, as checked by `relOKD`. -/
theorem relOK_1_2 :
    allFrom 1079 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1095, 1111)` hold, as checked by `relOKD`. -/
theorem relOK_1_3 :
    allFrom 1095 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1111, 1127)` hold, as checked by `relOKD`. -/
theorem relOK_1_4 :
    allFrom 1111 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1127, 1143)` hold, as checked by `relOKD`. -/
theorem relOK_1_5 :
    allFrom 1127 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1143, 1159)` hold, as checked by `relOKD`. -/
theorem relOK_1_6 :
    allFrom 1143 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1159, 1175)` hold, as checked by `relOKD`. -/
theorem relOK_1_7 :
    allFrom 1159 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1175, 1191)` hold, as checked by `relOKD`. -/
theorem relOK_1_8 :
    allFrom 1175 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1191, 1207)` hold, as checked by `relOKD`. -/
theorem relOK_1_9 :
    allFrom 1191 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1207, 1223)` hold, as checked by `relOKD`. -/
theorem relOK_1_10 :
    allFrom 1207 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1223, 1239)` hold, as checked by `relOKD`. -/
theorem relOK_1_11 :
    allFrom 1223 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1239, 1255)` hold, as checked by `relOKD`. -/
theorem relOK_1_12 :
    allFrom 1239 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1255, 1271)` hold, as checked by `relOKD`. -/
theorem relOK_1_13 :
    allFrom 1255 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1271, 1287)` hold, as checked by `relOKD`. -/
theorem relOK_1_14 :
    allFrom 1271 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1287, 1303)` hold, as checked by `relOKD`. -/
theorem relOK_1_15 :
    allFrom 1287 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1303, 1319)` hold, as checked by `relOKD`. -/
theorem relOK_1_16 :
    allFrom 1303 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1319, 1335)` hold, as checked by `relOKD`. -/
theorem relOK_1_17 :
    allFrom 1319 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1335, 1351)` hold, as checked by `relOKD`. -/
theorem relOK_1_18 :
    allFrom 1335 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1351, 1367)` hold, as checked by `relOKD`. -/
theorem relOK_1_19 :
    allFrom 1351 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1367, 1383)` hold, as checked by `relOKD`. -/
theorem relOK_1_20 :
    allFrom 1367 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1383, 1399)` hold, as checked by `relOKD`. -/
theorem relOK_1_21 :
    allFrom 1383 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1399, 1415)` hold, as checked by `relOKD`. -/
theorem relOK_1_22 :
    allFrom 1399 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1415, 1431)` hold, as checked by `relOKD`. -/
theorem relOK_1_23 :
    allFrom 1415 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1431, 1447)` hold, as checked by `relOKD`. -/
theorem relOK_1_24 :
    allFrom 1431 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1447, 1463)` hold, as checked by `relOKD`. -/
theorem relOK_1_25 :
    allFrom 1447 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1463, 1479)` hold, as checked by `relOKD`. -/
theorem relOK_1_26 :
    allFrom 1463 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1479, 1495)` hold, as checked by `relOKD`. -/
theorem relOK_1_27 :
    allFrom 1479 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1495, 1511)` hold, as checked by `relOKD`. -/
theorem relOK_1_28 :
    allFrom 1495 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1511, 1527)` hold, as checked by `relOKD`. -/
theorem relOK_1_29 :
    allFrom 1511 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1527, 1543)` hold, as checked by `relOKD`. -/
theorem relOK_1_30 :
    allFrom 1527 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1543, 1559)` hold, as checked by `relOKD`. -/
theorem relOK_1_31 :
    allFrom 1543 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1559, 1575)` hold, as checked by `relOKD`. -/
theorem relOK_1_32 :
    allFrom 1559 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1575, 1591)` hold, as checked by `relOKD`. -/
theorem relOK_1_33 :
    allFrom 1575 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1591, 1607)` hold, as checked by `relOKD`. -/
theorem relOK_1_34 :
    allFrom 1591 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1607, 1623)` hold, as checked by `relOKD`. -/
theorem relOK_1_35 :
    allFrom 1607 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1623, 1639)` hold, as checked by `relOKD`. -/
theorem relOK_1_36 :
    allFrom 1623 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1639, 1655)` hold, as checked by `relOKD`. -/
theorem relOK_1_37 :
    allFrom 1639 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1655, 1671)` hold, as checked by `relOKD`. -/
theorem relOK_1_38 :
    allFrom 1655 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1671, 1687)` hold, as checked by `relOKD`. -/
theorem relOK_1_39 :
    allFrom 1671 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1687, 1703)` hold, as checked by `relOKD`. -/
theorem relOK_1_40 :
    allFrom 1687 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1703, 1719)` hold, as checked by `relOKD`. -/
theorem relOK_1_41 :
    allFrom 1703 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1719, 1735)` hold, as checked by `relOKD`. -/
theorem relOK_1_42 :
    allFrom 1719 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1735, 1751)` hold, as checked by `relOKD`. -/
theorem relOK_1_43 :
    allFrom 1735 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1751, 1767)` hold, as checked by `relOKD`. -/
theorem relOK_1_44 :
    allFrom 1751 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1767, 1783)` hold, as checked by `relOKD`. -/
theorem relOK_1_45 :
    allFrom 1767 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1783, 1799)` hold, as checked by `relOKD`. -/
theorem relOK_1_46 :
    allFrom 1783 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1799, 1815)` hold, as checked by `relOKD`. -/
theorem relOK_1_47 :
    allFrom 1799 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1815, 1831)` hold, as checked by `relOKD`. -/
theorem relOK_1_48 :
    allFrom 1815 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1831, 1847)` hold, as checked by `relOKD`. -/
theorem relOK_1_49 :
    allFrom 1831 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1847, 1863)` hold, as checked by `relOKD`. -/
theorem relOK_1_50 :
    allFrom 1847 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1863, 1879)` hold, as checked by `relOKD`. -/
theorem relOK_1_51 :
    allFrom 1863 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1879, 1884)` hold, as checked by `relOKD`. -/
theorem relOK_1_52 :
    allFrom 1879 5
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1047, 1884)` hold, as checked by `relOKD`. -/
theorem relOK_1 :
    allFrom 1047 837
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true :=
  allFrom_add (a := 416) (b := 421)
      (allFrom_add (a := 208) (b := 208)
          (allFrom_add (a := 96) (b := 112)
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_0
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_1
                          relOK_1_2))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_3
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_4
                          relOK_1_5)))
              (allFrom_add (a := 48) (b := 64)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_6
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_7
                          relOK_1_8))
                  (allFrom_add (a := 32) (b := 32)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_9
                          relOK_1_10)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_11
                          relOK_1_12))))
          (allFrom_add (a := 96) (b := 112)
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_13
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_14
                          relOK_1_15))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_16
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_17
                          relOK_1_18)))
              (allFrom_add (a := 48) (b := 64)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_19
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_20
                          relOK_1_21))
                  (allFrom_add (a := 32) (b := 32)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_22
                          relOK_1_23)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_24
                          relOK_1_25)))))
      (allFrom_add (a := 208) (b := 213)
          (allFrom_add (a := 96) (b := 112)
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_26
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_27
                          relOK_1_28))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_29
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_30
                          relOK_1_31)))
              (allFrom_add (a := 48) (b := 64)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_32
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_33
                          relOK_1_34))
                  (allFrom_add (a := 32) (b := 32)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_35
                          relOK_1_36)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_37
                          relOK_1_38))))
          (allFrom_add (a := 112) (b := 101)
              (allFrom_add (a := 48) (b := 64)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_39
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_40
                          relOK_1_41))
                  (allFrom_add (a := 32) (b := 32)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_42
                          relOK_1_43)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_44
                          relOK_1_45)))
              (allFrom_add (a := 48) (b := 53)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_1_46
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_47
                          relOK_1_48))
                  (allFrom_add (a := 32) (b := 21)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_1_49
                          relOK_1_50)
                      (allFrom_add (a := 16) (b := 5)
                          relOK_1_51
                          relOK_1_52)))))

end ClusterAlgebras.CertificateData.E8

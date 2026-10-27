/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7

/-!
# Exchange relations `1005` to `1022` of the `E7` certificate

The exchange relations with indices in `[1005, 1023)` of the `E7` certificate `raw` pass the check
`CertificateCheck.Raw.relOKD`, verified by kernel evaluation.

## Main results

* `relOK_5`: every exchange relation with index in `[1005, 1023)` passes `relOKD`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relation `1005` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_0 :
    allFrom 1005 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1006` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_1 :
    allFrom 1006 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1007` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_2 :
    allFrom 1007 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1008` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_3 :
    allFrom 1008 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1009` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_4 :
    allFrom 1009 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1010` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_5 :
    allFrom 1010 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1011` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_6 :
    allFrom 1011 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1012` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_7 :
    allFrom 1012 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1013` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_8 :
    allFrom 1013 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1014` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_9 :
    allFrom 1014 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1015` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_10 :
    allFrom 1015 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1016` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_11 :
    allFrom 1016 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1017` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_12 :
    allFrom 1017 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1018` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_13 :
    allFrom 1018 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1019` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_14 :
    allFrom 1019 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1020` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_15 :
    allFrom 1020 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1021` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_16 :
    allFrom 1021 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1022` of the `E7` certificate passes `relOKD`. -/
theorem relOK_5_17 :
    allFrom 1022 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations `1005` to `1022` of the `E7` certificate pass `relOKD`. -/
theorem relOK_5 :
    allFrom 1005 18
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true :=
  allFrom_add (a := 9) (b := 9)
      (allFrom_add (a := 4) (b := 5)
          (allFrom_add (a := 2) (b := 2)
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_0
                  relOK_5_1)
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_2
                  relOK_5_3))
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_4
                  relOK_5_5)
              (allFrom_add (a := 1) (b := 2)
                  relOK_5_6
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_7
                      relOK_5_8))))
      (allFrom_add (a := 4) (b := 5)
          (allFrom_add (a := 2) (b := 2)
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_9
                  relOK_5_10)
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_11
                  relOK_5_12))
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_13
                  relOK_5_14)
              (allFrom_add (a := 1) (b := 2)
                  relOK_5_15
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_16
                      relOK_5_17))))

end ClusterAlgebras.CertificateData.E7

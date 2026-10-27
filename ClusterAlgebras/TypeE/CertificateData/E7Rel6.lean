/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7

/-!
# Exchange relations `[1023, 1043)` of the `E7` certificate

The exchange relations with indices in `[1023, 1043)` of the `E7` certificate `raw` hold, as
checked by `relOKD` with the term codes `varList`, in rank `7` with `70` cluster variables.

## Main results

* `relOK_6`: every relation with index in `[1023, 1043)` is accepted by `relOKD`.

## Implementation notes

Each relation is checked by the kernel in its own theorem, `relOK_6_i` for the relation
`1023 + i`, and these are assembled by `CertificateCheck.allFrom_add`. The cost of a kernel
evaluation grows faster than its length, and separate theorems let the kernel drop its caches
between pieces; `Elab.async` is disabled so that the kernel checks do not hold their memory until
the end of the file.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7

open CertificateCheck

set_option Elab.async false

/-- The exchange relation `1023` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_0 :
    allFrom 1023 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1024` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_1 :
    allFrom 1024 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1025` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_2 :
    allFrom 1025 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1026` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_3 :
    allFrom 1026 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1027` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_4 :
    allFrom 1027 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1028` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_5 :
    allFrom 1028 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1029` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_6 :
    allFrom 1029 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1030` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_7 :
    allFrom 1030 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1031` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_8 :
    allFrom 1031 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1032` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_9 :
    allFrom 1032 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1033` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_10 :
    allFrom 1033 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1034` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_11 :
    allFrom 1034 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1035` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_12 :
    allFrom 1035 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1036` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_13 :
    allFrom 1036 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1037` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_14 :
    allFrom 1037 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1038` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_15 :
    allFrom 1038 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1039` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_16 :
    allFrom 1039 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1040` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_17 :
    allFrom 1040 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1041` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_18 :
    allFrom 1041 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1042` of the `E7` certificate is accepted by `relOKD`. -/
theorem relOK_6_19 :
    allFrom 1042 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- Every exchange relation of the `E7` certificate with index in `[1023, 1043)` is accepted by
`relOKD`. -/
theorem relOK_6 :
    allFrom 1023 20
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true :=
  allFrom_add (a := 10) (b := 10)
      (allFrom_add (a := 5) (b := 5)
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_6_0
                  relOK_6_1)
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_2
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_3
                      relOK_6_4)))
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_6_5
                  relOK_6_6)
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_7
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_8
                      relOK_6_9))))
      (allFrom_add (a := 5) (b := 5)
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_6_10
                  relOK_6_11)
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_12
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_13
                      relOK_6_14)))
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_6_15
                  relOK_6_16)
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_17
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_18
                      relOK_6_19))))

end ClusterAlgebras.CertificateData.E7

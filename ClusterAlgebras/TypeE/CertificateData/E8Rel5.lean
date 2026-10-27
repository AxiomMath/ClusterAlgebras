/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Exchange relations `3089` to `3119` of the `E8` certificate

The exchange relations of indices `3089` to `3119` of the `E8` certificate pass the check
`relOKD`.

## Main results

* `relOK_5`: the relations of indices `3089` to `3119` pass `relOKD`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relation of index `3089` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_0 :
    allFrom 3089 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3090` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_1 :
    allFrom 3090 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3091` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_2 :
    allFrom 3091 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3092` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_3 :
    allFrom 3092 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3093` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_4 :
    allFrom 3093 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3094` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_5 :
    allFrom 3094 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3095` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_6 :
    allFrom 3095 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3096` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_7 :
    allFrom 3096 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3097` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_8 :
    allFrom 3097 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3098` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_9 :
    allFrom 3098 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3099` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_10 :
    allFrom 3099 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3100` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_11 :
    allFrom 3100 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3101` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_12 :
    allFrom 3101 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3102` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_13 :
    allFrom 3102 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3103` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_14 :
    allFrom 3103 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3104` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_15 :
    allFrom 3104 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3105` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_16 :
    allFrom 3105 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3106` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_17 :
    allFrom 3106 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3107` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_18 :
    allFrom 3107 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3108` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_19 :
    allFrom 3108 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3109` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_20 :
    allFrom 3109 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3110` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_21 :
    allFrom 3110 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3111` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_22 :
    allFrom 3111 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3112` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_23 :
    allFrom 3112 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3113` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_24 :
    allFrom 3113 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3114` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_25 :
    allFrom 3114 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3115` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_26 :
    allFrom 3115 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3116` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_27 :
    allFrom 3116 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3117` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_28 :
    allFrom 3117 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3118` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_29 :
    allFrom 3118 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of index `3119` of the `E8` certificate passes `relOKD`. -/
theorem relOK_5_30 :
    allFrom 3119 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of indices `3089` to `3119` of the `E8` certificate pass
`relOKD`. -/
theorem relOK_5 :
    allFrom 3089 31
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true :=
  allFrom_add (a := 15) (b := 16)
      (allFrom_add (a := 7) (b := 8)
          (allFrom_add (a := 3) (b := 4)
              (allFrom_add (a := 1) (b := 2)
                  relOK_5_0
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_1
                      relOK_5_2))
              (allFrom_add (a := 2) (b := 2)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_3
                      relOK_5_4)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_5
                      relOK_5_6)))
          (allFrom_add (a := 4) (b := 4)
              (allFrom_add (a := 2) (b := 2)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_7
                      relOK_5_8)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_9
                      relOK_5_10))
              (allFrom_add (a := 2) (b := 2)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_11
                      relOK_5_12)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_13
                      relOK_5_14))))
      (allFrom_add (a := 8) (b := 8)
          (allFrom_add (a := 4) (b := 4)
              (allFrom_add (a := 2) (b := 2)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_15
                      relOK_5_16)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_17
                      relOK_5_18))
              (allFrom_add (a := 2) (b := 2)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_19
                      relOK_5_20)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_21
                      relOK_5_22)))
          (allFrom_add (a := 4) (b := 4)
              (allFrom_add (a := 2) (b := 2)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_23
                      relOK_5_24)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_25
                      relOK_5_26))
              (allFrom_add (a := 2) (b := 2)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_27
                      relOK_5_28)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_5_29
                      relOK_5_30))))

end ClusterAlgebras.CertificateData.E8

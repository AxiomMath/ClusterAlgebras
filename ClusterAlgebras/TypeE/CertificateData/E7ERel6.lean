/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7E

/-! # Kernel check of the exchange relations `[1017, 1042)` of the `E7E` certificate,
one relation per theorem, assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7E

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The `E7E` certificate's exchange relation `1017` holds. -/
theorem relOK_6_0 :
    allFrom 1017 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1018` holds. -/
theorem relOK_6_1 :
    allFrom 1018 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1019` holds. -/
theorem relOK_6_2 :
    allFrom 1019 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1020` holds. -/
theorem relOK_6_3 :
    allFrom 1020 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1021` holds. -/
theorem relOK_6_4 :
    allFrom 1021 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1022` holds. -/
theorem relOK_6_5 :
    allFrom 1022 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1023` holds. -/
theorem relOK_6_6 :
    allFrom 1023 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1024` holds. -/
theorem relOK_6_7 :
    allFrom 1024 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1025` holds. -/
theorem relOK_6_8 :
    allFrom 1025 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1026` holds. -/
theorem relOK_6_9 :
    allFrom 1026 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1027` holds. -/
theorem relOK_6_10 :
    allFrom 1027 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1028` holds. -/
theorem relOK_6_11 :
    allFrom 1028 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1029` holds. -/
theorem relOK_6_12 :
    allFrom 1029 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1030` holds. -/
theorem relOK_6_13 :
    allFrom 1030 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1031` holds. -/
theorem relOK_6_14 :
    allFrom 1031 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1032` holds. -/
theorem relOK_6_15 :
    allFrom 1032 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1033` holds. -/
theorem relOK_6_16 :
    allFrom 1033 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1034` holds. -/
theorem relOK_6_17 :
    allFrom 1034 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1035` holds. -/
theorem relOK_6_18 :
    allFrom 1035 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1036` holds. -/
theorem relOK_6_19 :
    allFrom 1036 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1037` holds. -/
theorem relOK_6_20 :
    allFrom 1037 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1038` holds. -/
theorem relOK_6_21 :
    allFrom 1038 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1039` holds. -/
theorem relOK_6_22 :
    allFrom 1039 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1040` holds. -/
theorem relOK_6_23 :
    allFrom 1040 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relation `1041` holds. -/
theorem relOK_6_24 :
    allFrom 1041 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The `E7E` certificate's exchange relations `[1017, 1042)` hold. -/
theorem relOK_6 :
    allFrom 1017 25
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true :=
  allFrom_add (a := 12) (b := 13)
      (allFrom_add (a := 6) (b := 6)
          (allFrom_add (a := 3) (b := 3)
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_0
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_1
                      relOK_6_2))
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_3
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_4
                      relOK_6_5)))
          (allFrom_add (a := 3) (b := 3)
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_6
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_7
                      relOK_6_8))
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_9
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_10
                      relOK_6_11))))
      (allFrom_add (a := 6) (b := 7)
          (allFrom_add (a := 3) (b := 3)
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_12
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_13
                      relOK_6_14))
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_15
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_16
                      relOK_6_17)))
          (allFrom_add (a := 3) (b := 4)
              (allFrom_add (a := 1) (b := 2)
                  relOK_6_18
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_19
                      relOK_6_20))
              (allFrom_add (a := 2) (b := 2)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_21
                      relOK_6_22)
                  (allFrom_add (a := 1) (b := 1)
                      relOK_6_23
                      relOK_6_24))))

end ClusterAlgebras.CertificateData.E7E

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7E

/-! # Kernel check of the exchange relations `[975, 995)` of the `E7E` certificate,
one relation per theorem, assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7E

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relation `975` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_0 :
    allFrom 975 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `976` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_1 :
    allFrom 976 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `977` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_2 :
    allFrom 977 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `978` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_3 :
    allFrom 978 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `979` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_4 :
    allFrom 979 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `980` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_5 :
    allFrom 980 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `981` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_6 :
    allFrom 981 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `982` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_7 :
    allFrom 982 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `983` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_8 :
    allFrom 983 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `984` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_9 :
    allFrom 984 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `985` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_10 :
    allFrom 985 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `986` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_11 :
    allFrom 986 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `987` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_12 :
    allFrom 987 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `988` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_13 :
    allFrom 988 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `989` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_14 :
    allFrom 989 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `990` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_15 :
    allFrom 990 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `991` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_16 :
    allFrom 991 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `992` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_17 :
    allFrom 992 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `993` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_18 :
    allFrom 993 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `994` of the `E7E` certificate holds, as checked by `relOKD`. -/
theorem relOK_3_19 :
    allFrom 994 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relations `[975, 995)` of the `E7E` certificate hold, as checked by `relOKD`. -/
theorem relOK_3 :
    allFrom 975 20
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true :=
  allFrom_add (a := 10) (b := 10)
      (allFrom_add (a := 5) (b := 5)
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_3_0
                  relOK_3_1)
              (allFrom_add (a := 1) (b := 2)
                  relOK_3_2
                  (allFrom_add (a := 1) (b := 1)
                      relOK_3_3
                      relOK_3_4)))
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_3_5
                  relOK_3_6)
              (allFrom_add (a := 1) (b := 2)
                  relOK_3_7
                  (allFrom_add (a := 1) (b := 1)
                      relOK_3_8
                      relOK_3_9))))
      (allFrom_add (a := 5) (b := 5)
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_3_10
                  relOK_3_11)
              (allFrom_add (a := 1) (b := 2)
                  relOK_3_12
                  (allFrom_add (a := 1) (b := 1)
                      relOK_3_13
                      relOK_3_14)))
          (allFrom_add (a := 2) (b := 3)
              (allFrom_add (a := 1) (b := 1)
                  relOK_3_15
                  relOK_3_16)
              (allFrom_add (a := 1) (b := 2)
                  relOK_3_17
                  (allFrom_add (a := 1) (b := 1)
                      relOK_3_18
                      relOK_3_19))))

end ClusterAlgebras.CertificateData.E7E

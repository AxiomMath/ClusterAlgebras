/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7E

/-! # Kernel check of the exchange relations `[1042, 1050)` of the `E7E` certificate,
one relation per theorem, assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7E

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Exchange relation `1042` of the `E7E` certificate satisfies `relOKD`. -/
theorem relOK_7_0 :
    allFrom 1042 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Exchange relation `1043` of the `E7E` certificate satisfies `relOKD`. -/
theorem relOK_7_1 :
    allFrom 1043 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Exchange relation `1044` of the `E7E` certificate satisfies `relOKD`. -/
theorem relOK_7_2 :
    allFrom 1044 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Exchange relation `1045` of the `E7E` certificate satisfies `relOKD`. -/
theorem relOK_7_3 :
    allFrom 1045 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Exchange relation `1046` of the `E7E` certificate satisfies `relOKD`. -/
theorem relOK_7_4 :
    allFrom 1046 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Exchange relation `1047` of the `E7E` certificate satisfies `relOKD`. -/
theorem relOK_7_5 :
    allFrom 1047 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Exchange relation `1048` of the `E7E` certificate satisfies `relOKD`. -/
theorem relOK_7_6 :
    allFrom 1048 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Exchange relation `1049` of the `E7E` certificate satisfies `relOKD`. -/
theorem relOK_7_7 :
    allFrom 1049 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation in `[1042, 1050)` of the `E7E` certificate satisfies `relOKD`. -/
theorem relOK_7 :
    allFrom 1042 8
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true :=
  allFrom_add (a := 4) (b := 4)
      (allFrom_add (a := 2) (b := 2)
          (allFrom_add (a := 1) (b := 1)
              relOK_7_0
              relOK_7_1)
          (allFrom_add (a := 1) (b := 1)
              relOK_7_2
              relOK_7_3))
      (allFrom_add (a := 2) (b := 2)
          (allFrom_add (a := 1) (b := 1)
              relOK_7_4
              relOK_7_5)
          (allFrom_add (a := 1) (b := 1)
              relOK_7_6
              relOK_7_7))

end ClusterAlgebras.CertificateData.E7E

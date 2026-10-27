/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7

/-! # Kernel check of the exchange relations `[995, 1005)` of the `E7` certificate,
one relation per theorem, assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relation `995` of the `E7` certificate holds. -/
theorem relOK_4_0 :
    allFrom 995 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `996` of the `E7` certificate holds. -/
theorem relOK_4_1 :
    allFrom 996 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `997` of the `E7` certificate holds. -/
theorem relOK_4_2 :
    allFrom 997 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `998` of the `E7` certificate holds. -/
theorem relOK_4_3 :
    allFrom 998 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `999` of the `E7` certificate holds. -/
theorem relOK_4_4 :
    allFrom 999 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1000` of the `E7` certificate holds. -/
theorem relOK_4_5 :
    allFrom 1000 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1001` of the `E7` certificate holds. -/
theorem relOK_4_6 :
    allFrom 1001 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1002` of the `E7` certificate holds. -/
theorem relOK_4_7 :
    allFrom 1002 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1003` of the `E7` certificate holds. -/
theorem relOK_4_8 :
    allFrom 1003 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `1004` of the `E7` certificate holds. -/
theorem relOK_4_9 :
    allFrom 1004 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations `[995, 1005)` of the `E7` certificate hold. -/
theorem relOK_4 :
    allFrom 995 10
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true :=
  allFrom_add (a := 5) (b := 5)
      (allFrom_add (a := 2) (b := 3)
          (allFrom_add (a := 1) (b := 1)
              relOK_4_0
              relOK_4_1)
          (allFrom_add (a := 1) (b := 2)
              relOK_4_2
              (allFrom_add (a := 1) (b := 1)
                  relOK_4_3
                  relOK_4_4)))
      (allFrom_add (a := 2) (b := 3)
          (allFrom_add (a := 1) (b := 1)
              relOK_4_5
              relOK_4_6)
          (allFrom_add (a := 1) (b := 2)
              relOK_4_7
              (allFrom_add (a := 1) (b := 1)
                  relOK_4_8
                  relOK_4_9)))

end ClusterAlgebras.CertificateData.E7

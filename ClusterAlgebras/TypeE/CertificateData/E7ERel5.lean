/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7E

/-!
# Exchange relations `[1005, 1017)` of the `E7E` certificate

The exchange relations with indices in `[1005, 1017)` of the `E7E` certificate hold, checked by
the kernel one relation per theorem and combined with `CertificateCheck.allFrom_add`.

## Main results

* `relOK_5`: the exchange relations with indices in `[1005, 1017)` of the certificate hold.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7E

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relation with index `1005` of the `E7E` certificate holds. -/
theorem relOK_5_0 :
    allFrom 1005 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1006` of the `E7E` certificate holds. -/
theorem relOK_5_1 :
    allFrom 1006 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1007` of the `E7E` certificate holds. -/
theorem relOK_5_2 :
    allFrom 1007 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1008` of the `E7E` certificate holds. -/
theorem relOK_5_3 :
    allFrom 1008 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1009` of the `E7E` certificate holds. -/
theorem relOK_5_4 :
    allFrom 1009 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1010` of the `E7E` certificate holds. -/
theorem relOK_5_5 :
    allFrom 1010 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1011` of the `E7E` certificate holds. -/
theorem relOK_5_6 :
    allFrom 1011 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1012` of the `E7E` certificate holds. -/
theorem relOK_5_7 :
    allFrom 1012 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1013` of the `E7E` certificate holds. -/
theorem relOK_5_8 :
    allFrom 1013 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1014` of the `E7E` certificate holds. -/
theorem relOK_5_9 :
    allFrom 1014 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1015` of the `E7E` certificate holds. -/
theorem relOK_5_10 :
    allFrom 1015 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1016` of the `E7E` certificate holds. -/
theorem relOK_5_11 :
    allFrom 1016 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[1005, 1017)` of the `E7E` certificate hold. -/
theorem relOK_5 :
    allFrom 1005 12
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true :=
  allFrom_add (a := 6) (b := 6)
      (allFrom_add (a := 3) (b := 3)
          (allFrom_add (a := 1) (b := 2)
              relOK_5_0
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_1
                  relOK_5_2))
          (allFrom_add (a := 1) (b := 2)
              relOK_5_3
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_4
                  relOK_5_5)))
      (allFrom_add (a := 3) (b := 3)
          (allFrom_add (a := 1) (b := 2)
              relOK_5_6
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_7
                  relOK_5_8))
          (allFrom_add (a := 1) (b := 2)
              relOK_5_9
              (allFrom_add (a := 1) (b := 1)
                  relOK_5_10
                  relOK_5_11)))

end ClusterAlgebras.CertificateData.E7E

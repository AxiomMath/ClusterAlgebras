/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7

/-!
# Exchange relations `[1043, 1050)` of the `E7` certificate

The exchange relations with indices in `[1043, 1050)` of the `E7` certificate hold, checked by
the kernel one relation at a time and assembled by `CertificateCheck.allFrom_add`.

## Main results

* `relOK_7`: every exchange relation with index in `[1043, 1050)` passes `relOKD`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relation with index `1043` of the `E7` certificate passes `relOKD`. -/
theorem relOK_7_0 :
    allFrom 1043 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1044` of the `E7` certificate passes `relOKD`. -/
theorem relOK_7_1 :
    allFrom 1044 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1045` of the `E7` certificate passes `relOKD`. -/
theorem relOK_7_2 :
    allFrom 1045 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1046` of the `E7` certificate passes `relOKD`. -/
theorem relOK_7_3 :
    allFrom 1046 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1047` of the `E7` certificate passes `relOKD`. -/
theorem relOK_7_4 :
    allFrom 1047 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1048` of the `E7` certificate passes `relOKD`. -/
theorem relOK_7_5 :
    allFrom 1048 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `1049` of the `E7` certificate passes `relOKD`. -/
theorem relOK_7_6 :
    allFrom 1049 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- Every exchange relation with index in `[1043, 1050)` of the `E7` certificate passes
`relOKD`. -/
theorem relOK_7 :
    allFrom 1043 7
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true :=
  allFrom_add (a := 3) (b := 4)
      (allFrom_add (a := 1) (b := 2)
          relOK_7_0
          (allFrom_add (a := 1) (b := 1)
              relOK_7_1
              relOK_7_2))
      (allFrom_add (a := 2) (b := 2)
          (allFrom_add (a := 1) (b := 1)
              relOK_7_3
              relOK_7_4)
          (allFrom_add (a := 1) (b := 1)
              relOK_7_5
              relOK_7_6))

end ClusterAlgebras.CertificateData.E7

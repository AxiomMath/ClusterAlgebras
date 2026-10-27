/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7

/-! # Kernel check of the exchange relations `[982, 995)` of the `E7` certificate,
one relation per theorem, assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relation with index `982` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_0 :
    allFrom 982 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `983` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_1 :
    allFrom 983 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `984` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_2 :
    allFrom 984 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `985` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_3 :
    allFrom 985 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `986` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_4 :
    allFrom 986 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `987` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_5 :
    allFrom 987 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `988` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_6 :
    allFrom 988 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `989` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_7 :
    allFrom 989 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `990` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_8 :
    allFrom 990 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `991` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_9 :
    allFrom 991 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `992` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_10 :
    allFrom 992 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `993` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_11 :
    allFrom 993 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation with index `994` of the `E7` certificate `raw` passes the check
`relOKD`. -/
theorem relOK_3_12 :
    allFrom 994 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[982, 995)` of the `E7` certificate `raw` pass the
check `relOKD`. -/
theorem relOK_3 :
    allFrom 982 13
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true :=
  allFrom_add (a := 6) (b := 7)
      (allFrom_add (a := 3) (b := 3)
          (allFrom_add (a := 1) (b := 2)
              relOK_3_0
              (allFrom_add (a := 1) (b := 1)
                  relOK_3_1
                  relOK_3_2))
          (allFrom_add (a := 1) (b := 2)
              relOK_3_3
              (allFrom_add (a := 1) (b := 1)
                  relOK_3_4
                  relOK_3_5)))
      (allFrom_add (a := 3) (b := 4)
          (allFrom_add (a := 1) (b := 2)
              relOK_3_6
              (allFrom_add (a := 1) (b := 1)
                  relOK_3_7
                  relOK_3_8))
          (allFrom_add (a := 2) (b := 2)
              (allFrom_add (a := 1) (b := 1)
                  relOK_3_9
                  relOK_3_10)
              (allFrom_add (a := 1) (b := 1)
                  relOK_3_11
                  relOK_3_12)))

end ClusterAlgebras.CertificateData.E7

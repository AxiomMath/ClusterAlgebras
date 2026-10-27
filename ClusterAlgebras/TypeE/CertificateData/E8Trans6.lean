/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-! # Kernel check of the transitions of seeds `[7524, 8778)` of the `E8` certificate,
in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Every transition `(a, k)` of the `E8` certificate with `7524 ≤ a < 7532` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_0 :
    allFrom 7524 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7532 ≤ a < 7540` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_1 :
    allFrom 7532 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7540 ≤ a < 7548` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_2 :
    allFrom 7540 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7548 ≤ a < 7556` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_3 :
    allFrom 7548 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7556 ≤ a < 7564` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_4 :
    allFrom 7556 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7564 ≤ a < 7572` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_5 :
    allFrom 7564 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7572 ≤ a < 7580` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_6 :
    allFrom 7572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7580 ≤ a < 7588` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_7 :
    allFrom 7580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7588 ≤ a < 7596` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_8 :
    allFrom 7588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7596 ≤ a < 7604` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_9 :
    allFrom 7596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7604 ≤ a < 7612` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_10 :
    allFrom 7604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7612 ≤ a < 7620` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_11 :
    allFrom 7612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7620 ≤ a < 7628` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_12 :
    allFrom 7620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7628 ≤ a < 7636` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_13 :
    allFrom 7628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7636 ≤ a < 7644` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_14 :
    allFrom 7636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7644 ≤ a < 7652` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_15 :
    allFrom 7644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7652 ≤ a < 7660` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_16 :
    allFrom 7652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7660 ≤ a < 7668` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_17 :
    allFrom 7660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7668 ≤ a < 7676` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_18 :
    allFrom 7668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7676 ≤ a < 7684` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_19 :
    allFrom 7676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7684 ≤ a < 7692` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_20 :
    allFrom 7684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7692 ≤ a < 7700` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_21 :
    allFrom 7692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7700 ≤ a < 7708` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_22 :
    allFrom 7700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7708 ≤ a < 7716` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_23 :
    allFrom 7708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7716 ≤ a < 7724` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_24 :
    allFrom 7716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7724 ≤ a < 7732` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_25 :
    allFrom 7724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7732 ≤ a < 7740` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_26 :
    allFrom 7732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7740 ≤ a < 7748` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_27 :
    allFrom 7740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7748 ≤ a < 7756` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_28 :
    allFrom 7748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7756 ≤ a < 7764` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_29 :
    allFrom 7756 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7764 ≤ a < 7772` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_30 :
    allFrom 7764 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7772 ≤ a < 7780` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_31 :
    allFrom 7772 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7780 ≤ a < 7788` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_32 :
    allFrom 7780 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7788 ≤ a < 7796` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_33 :
    allFrom 7788 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7796 ≤ a < 7804` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_34 :
    allFrom 7796 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7804 ≤ a < 7812` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_35 :
    allFrom 7804 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7812 ≤ a < 7820` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_36 :
    allFrom 7812 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7820 ≤ a < 7828` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_37 :
    allFrom 7820 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7828 ≤ a < 7836` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_38 :
    allFrom 7828 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7836 ≤ a < 7844` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_39 :
    allFrom 7836 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7844 ≤ a < 7852` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_40 :
    allFrom 7844 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7852 ≤ a < 7860` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_41 :
    allFrom 7852 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7860 ≤ a < 7868` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_42 :
    allFrom 7860 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7868 ≤ a < 7876` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_43 :
    allFrom 7868 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7876 ≤ a < 7884` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_44 :
    allFrom 7876 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7884 ≤ a < 7892` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_45 :
    allFrom 7884 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7892 ≤ a < 7900` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_46 :
    allFrom 7892 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7900 ≤ a < 7908` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_47 :
    allFrom 7900 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7908 ≤ a < 7916` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_48 :
    allFrom 7908 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7916 ≤ a < 7924` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_49 :
    allFrom 7916 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7924 ≤ a < 7932` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_50 :
    allFrom 7924 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7932 ≤ a < 7940` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_51 :
    allFrom 7932 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7940 ≤ a < 7948` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_52 :
    allFrom 7940 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7948 ≤ a < 7956` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_53 :
    allFrom 7948 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7956 ≤ a < 7964` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_54 :
    allFrom 7956 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7964 ≤ a < 7972` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_55 :
    allFrom 7964 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7972 ≤ a < 7980` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_56 :
    allFrom 7972 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7980 ≤ a < 7988` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_57 :
    allFrom 7980 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7988 ≤ a < 7996` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_58 :
    allFrom 7988 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7996 ≤ a < 8004` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_59 :
    allFrom 7996 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8004 ≤ a < 8012` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_60 :
    allFrom 8004 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8012 ≤ a < 8020` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_61 :
    allFrom 8012 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8020 ≤ a < 8028` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_62 :
    allFrom 8020 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8028 ≤ a < 8036` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_63 :
    allFrom 8028 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8036 ≤ a < 8044` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_64 :
    allFrom 8036 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8044 ≤ a < 8052` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_65 :
    allFrom 8044 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8052 ≤ a < 8060` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_66 :
    allFrom 8052 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8060 ≤ a < 8068` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_67 :
    allFrom 8060 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8068 ≤ a < 8076` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_68 :
    allFrom 8068 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8076 ≤ a < 8084` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_69 :
    allFrom 8076 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8084 ≤ a < 8092` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_70 :
    allFrom 8084 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8092 ≤ a < 8100` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_71 :
    allFrom 8092 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8100 ≤ a < 8108` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_72 :
    allFrom 8100 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8108 ≤ a < 8116` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_73 :
    allFrom 8108 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8116 ≤ a < 8124` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_74 :
    allFrom 8116 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8124 ≤ a < 8132` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_75 :
    allFrom 8124 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8132 ≤ a < 8140` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_76 :
    allFrom 8132 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8140 ≤ a < 8148` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_77 :
    allFrom 8140 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8148 ≤ a < 8156` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_78 :
    allFrom 8148 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8156 ≤ a < 8164` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_79 :
    allFrom 8156 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8164 ≤ a < 8172` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_80 :
    allFrom 8164 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8172 ≤ a < 8180` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_81 :
    allFrom 8172 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8180 ≤ a < 8188` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_82 :
    allFrom 8180 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8188 ≤ a < 8196` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_83 :
    allFrom 8188 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8196 ≤ a < 8204` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_84 :
    allFrom 8196 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8204 ≤ a < 8212` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_85 :
    allFrom 8204 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8212 ≤ a < 8220` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_86 :
    allFrom 8212 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8220 ≤ a < 8228` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_87 :
    allFrom 8220 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8228 ≤ a < 8236` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_88 :
    allFrom 8228 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8236 ≤ a < 8244` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_89 :
    allFrom 8236 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8244 ≤ a < 8252` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_90 :
    allFrom 8244 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8252 ≤ a < 8260` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_91 :
    allFrom 8252 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8260 ≤ a < 8268` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_92 :
    allFrom 8260 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8268 ≤ a < 8276` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_93 :
    allFrom 8268 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8276 ≤ a < 8284` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_94 :
    allFrom 8276 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8284 ≤ a < 8292` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_95 :
    allFrom 8284 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8292 ≤ a < 8300` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_96 :
    allFrom 8292 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8300 ≤ a < 8308` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_97 :
    allFrom 8300 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8308 ≤ a < 8316` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_98 :
    allFrom 8308 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8316 ≤ a < 8324` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_99 :
    allFrom 8316 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8324 ≤ a < 8332` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_100 :
    allFrom 8324 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8332 ≤ a < 8340` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_101 :
    allFrom 8332 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8340 ≤ a < 8348` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_102 :
    allFrom 8340 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8348 ≤ a < 8356` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_103 :
    allFrom 8348 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8356 ≤ a < 8364` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_104 :
    allFrom 8356 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8364 ≤ a < 8372` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_105 :
    allFrom 8364 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8372 ≤ a < 8380` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_106 :
    allFrom 8372 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8380 ≤ a < 8388` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_107 :
    allFrom 8380 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8388 ≤ a < 8396` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_108 :
    allFrom 8388 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8396 ≤ a < 8404` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_109 :
    allFrom 8396 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8404 ≤ a < 8412` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_110 :
    allFrom 8404 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8412 ≤ a < 8420` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_111 :
    allFrom 8412 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8420 ≤ a < 8428` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_112 :
    allFrom 8420 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8428 ≤ a < 8436` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_113 :
    allFrom 8428 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8436 ≤ a < 8444` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_114 :
    allFrom 8436 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8444 ≤ a < 8452` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_115 :
    allFrom 8444 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8452 ≤ a < 8460` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_116 :
    allFrom 8452 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8460 ≤ a < 8468` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_117 :
    allFrom 8460 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8468 ≤ a < 8476` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_118 :
    allFrom 8468 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8476 ≤ a < 8484` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_119 :
    allFrom 8476 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8484 ≤ a < 8492` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_120 :
    allFrom 8484 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8492 ≤ a < 8500` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_121 :
    allFrom 8492 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8500 ≤ a < 8508` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_122 :
    allFrom 8500 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8508 ≤ a < 8516` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_123 :
    allFrom 8508 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8516 ≤ a < 8524` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_124 :
    allFrom 8516 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8524 ≤ a < 8532` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_125 :
    allFrom 8524 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8532 ≤ a < 8540` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_126 :
    allFrom 8532 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8540 ≤ a < 8548` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_127 :
    allFrom 8540 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8548 ≤ a < 8556` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_128 :
    allFrom 8548 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8556 ≤ a < 8564` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_129 :
    allFrom 8556 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8564 ≤ a < 8572` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_130 :
    allFrom 8564 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8572 ≤ a < 8580` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_131 :
    allFrom 8572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8580 ≤ a < 8588` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_132 :
    allFrom 8580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8588 ≤ a < 8596` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_133 :
    allFrom 8588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8596 ≤ a < 8604` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_134 :
    allFrom 8596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8604 ≤ a < 8612` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_135 :
    allFrom 8604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8612 ≤ a < 8620` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_136 :
    allFrom 8612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8620 ≤ a < 8628` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_137 :
    allFrom 8620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8628 ≤ a < 8636` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_138 :
    allFrom 8628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8636 ≤ a < 8644` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_139 :
    allFrom 8636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8644 ≤ a < 8652` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_140 :
    allFrom 8644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8652 ≤ a < 8660` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_141 :
    allFrom 8652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8660 ≤ a < 8668` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_142 :
    allFrom 8660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8668 ≤ a < 8676` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_143 :
    allFrom 8668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8676 ≤ a < 8684` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_144 :
    allFrom 8676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8684 ≤ a < 8692` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_145 :
    allFrom 8684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8692 ≤ a < 8700` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_146 :
    allFrom 8692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8700 ≤ a < 8708` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_147 :
    allFrom 8700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8708 ≤ a < 8716` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_148 :
    allFrom 8708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8716 ≤ a < 8724` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_149 :
    allFrom 8716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8724 ≤ a < 8732` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_150 :
    allFrom 8724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8732 ≤ a < 8740` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_151 :
    allFrom 8732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8740 ≤ a < 8748` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_152 :
    allFrom 8740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8748 ≤ a < 8756` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_153 :
    allFrom 8748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8756 ≤ a < 8764` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_154 :
    allFrom 8756 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8764 ≤ a < 8772` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_155 :
    allFrom 8764 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `8772 ≤ a < 8778` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6_156 :
    allFrom 8772 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `7524 ≤ a < 8778` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_6 :
    allFrom 7524 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_0
                              transOK_6_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_2
                              transOK_6_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_4
                              transOK_6_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_7
                                  transOK_6_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_9
                              transOK_6_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_12
                                  transOK_6_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_14
                              transOK_6_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_17
                                  transOK_6_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_19
                              transOK_6_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_22
                                  transOK_6_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_24
                              transOK_6_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_27
                                  transOK_6_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_29
                              transOK_6_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_32
                                  transOK_6_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_34
                              transOK_6_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_37
                                  transOK_6_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_39
                              transOK_6_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_41
                              transOK_6_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_43
                              transOK_6_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_46
                                  transOK_6_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_48
                              transOK_6_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_51
                                  transOK_6_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_53
                              transOK_6_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_56
                                  transOK_6_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_58
                              transOK_6_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_61
                                  transOK_6_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_63
                              transOK_6_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_66
                                  transOK_6_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_68
                              transOK_6_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_71
                                  transOK_6_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_73
                              transOK_6_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_76
                                  transOK_6_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_78
                              transOK_6_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_80
                              transOK_6_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_82
                              transOK_6_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_85
                                  transOK_6_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_87
                              transOK_6_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_90
                                  transOK_6_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_92
                              transOK_6_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_95
                                  transOK_6_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_97
                              transOK_6_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_100
                                  transOK_6_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_102
                              transOK_6_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_105
                                  transOK_6_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_107
                              transOK_6_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_110
                                  transOK_6_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_112
                              transOK_6_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_115
                                  transOK_6_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_117
                              transOK_6_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_120
                                  transOK_6_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_122
                              transOK_6_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_125
                                  transOK_6_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_127
                              transOK_6_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_130
                                  transOK_6_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_132
                              transOK_6_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_135
                                  transOK_6_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_137
                              transOK_6_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_140
                                  transOK_6_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_142
                              transOK_6_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_145
                                  transOK_6_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_147
                              transOK_6_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_6_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_6_150
                                  transOK_6_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_6_152
                              transOK_6_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_6_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_6_155
                                  transOK_6_156)))))))

end ClusterAlgebras.CertificateData.E8

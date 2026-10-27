/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the seeds `[12540, 13794)` of the `E8` certificate

Every transition `(a, k)` with `12540 ≤ a < 13794` and `k < 8` passes `raw.transOK`, checked by
the kernel in pieces of `8` seeds and assembled by `CertificateCheck.allFrom_add`.

## Main results

* `transOK_10`: every transition out of the seeds `[12540, 13794)` passes `raw.transOK`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_0 :
    allFrom 12540 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_1 :
    allFrom 12548 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_2 :
    allFrom 12556 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_3 :
    allFrom 12564 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_4 :
    allFrom 12572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_5 :
    allFrom 12580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_6 :
    allFrom 12588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_7 :
    allFrom 12596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_8 :
    allFrom 12604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_9 :
    allFrom 12612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_10 :
    allFrom 12620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_11 :
    allFrom 12628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_12 :
    allFrom 12636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_13 :
    allFrom 12644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_14 :
    allFrom 12652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_15 :
    allFrom 12660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_16 :
    allFrom 12668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_17 :
    allFrom 12676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_18 :
    allFrom 12684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_19 :
    allFrom 12692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_20 :
    allFrom 12700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_21 :
    allFrom 12708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_22 :
    allFrom 12716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_23 :
    allFrom 12724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_24 :
    allFrom 12732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_25 :
    allFrom 12740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_26 :
    allFrom 12748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_27 :
    allFrom 12756 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_28 :
    allFrom 12764 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_29 :
    allFrom 12772 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_30 :
    allFrom 12780 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_31 :
    allFrom 12788 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_32 :
    allFrom 12796 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_33 :
    allFrom 12804 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_34 :
    allFrom 12812 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_35 :
    allFrom 12820 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_36 :
    allFrom 12828 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_37 :
    allFrom 12836 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_38 :
    allFrom 12844 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_39 :
    allFrom 12852 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_40 :
    allFrom 12860 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_41 :
    allFrom 12868 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_42 :
    allFrom 12876 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_43 :
    allFrom 12884 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_44 :
    allFrom 12892 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_45 :
    allFrom 12900 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_46 :
    allFrom 12908 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_47 :
    allFrom 12916 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_48 :
    allFrom 12924 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_49 :
    allFrom 12932 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_50 :
    allFrom 12940 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_51 :
    allFrom 12948 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_52 :
    allFrom 12956 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_53 :
    allFrom 12964 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_54 :
    allFrom 12972 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_55 :
    allFrom 12980 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_56 :
    allFrom 12988 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_57 :
    allFrom 12996 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_58 :
    allFrom 13004 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_59 :
    allFrom 13012 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_60 :
    allFrom 13020 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_61 :
    allFrom 13028 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_62 :
    allFrom 13036 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_63 :
    allFrom 13044 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_64 :
    allFrom 13052 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_65 :
    allFrom 13060 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_66 :
    allFrom 13068 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_67 :
    allFrom 13076 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_68 :
    allFrom 13084 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_69 :
    allFrom 13092 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_70 :
    allFrom 13100 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_71 :
    allFrom 13108 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_72 :
    allFrom 13116 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_73 :
    allFrom 13124 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_74 :
    allFrom 13132 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_75 :
    allFrom 13140 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_76 :
    allFrom 13148 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_77 :
    allFrom 13156 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_78 :
    allFrom 13164 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_79 :
    allFrom 13172 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_80 :
    allFrom 13180 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_81 :
    allFrom 13188 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_82 :
    allFrom 13196 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_83 :
    allFrom 13204 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_84 :
    allFrom 13212 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_85 :
    allFrom 13220 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_86 :
    allFrom 13228 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_87 :
    allFrom 13236 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_88 :
    allFrom 13244 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_89 :
    allFrom 13252 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_90 :
    allFrom 13260 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_91 :
    allFrom 13268 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_92 :
    allFrom 13276 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_93 :
    allFrom 13284 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_94 :
    allFrom 13292 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_95 :
    allFrom 13300 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_96 :
    allFrom 13308 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_97 :
    allFrom 13316 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_98 :
    allFrom 13324 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_99 :
    allFrom 13332 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_100 :
    allFrom 13340 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_101 :
    allFrom 13348 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_102 :
    allFrom 13356 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_103 :
    allFrom 13364 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_104 :
    allFrom 13372 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_105 :
    allFrom 13380 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_106 :
    allFrom 13388 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_107 :
    allFrom 13396 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_108 :
    allFrom 13404 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_109 :
    allFrom 13412 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_110 :
    allFrom 13420 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_111 :
    allFrom 13428 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_112 :
    allFrom 13436 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_113 :
    allFrom 13444 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_114 :
    allFrom 13452 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_115 :
    allFrom 13460 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_116 :
    allFrom 13468 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_117 :
    allFrom 13476 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_118 :
    allFrom 13484 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_119 :
    allFrom 13492 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_120 :
    allFrom 13500 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_121 :
    allFrom 13508 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_122 :
    allFrom 13516 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_123 :
    allFrom 13524 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_124 :
    allFrom 13532 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_125 :
    allFrom 13540 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_126 :
    allFrom 13548 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_127 :
    allFrom 13556 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_128 :
    allFrom 13564 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_129 :
    allFrom 13572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_130 :
    allFrom 13580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_131 :
    allFrom 13588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_132 :
    allFrom 13596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_133 :
    allFrom 13604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_134 :
    allFrom 13612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_135 :
    allFrom 13620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_136 :
    allFrom 13628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_137 :
    allFrom 13636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_138 :
    allFrom 13644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_139 :
    allFrom 13652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_140 :
    allFrom 13660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_141 :
    allFrom 13668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_142 :
    allFrom 13676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_143 :
    allFrom 13684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_144 :
    allFrom 13692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_145 :
    allFrom 13700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_146 :
    allFrom 13708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_147 :
    allFrom 13716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_148 :
    allFrom 13724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_149 :
    allFrom 13732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_150 :
    allFrom 13740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_151 :
    allFrom 13748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_152 :
    allFrom 13756 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_153 :
    allFrom 13764 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_154 :
    allFrom 13772 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_155 :
    allFrom 13780 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `a` in the stated range of seeds and
`k < 8` passes `raw.transOK`. -/
theorem transOK_10_156 :
    allFrom 13788 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` of the `E8` certificate with `12540 ≤ a < 13794` and `k < 8` passes
`raw.transOK`. -/
theorem transOK_10 :
    allFrom 12540 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_0
                              transOK_10_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_2
                              transOK_10_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_4
                              transOK_10_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_7
                                  transOK_10_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_9
                              transOK_10_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_12
                                  transOK_10_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_14
                              transOK_10_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_17
                                  transOK_10_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_19
                              transOK_10_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_22
                                  transOK_10_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_24
                              transOK_10_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_27
                                  transOK_10_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_29
                              transOK_10_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_32
                                  transOK_10_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_34
                              transOK_10_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_37
                                  transOK_10_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_39
                              transOK_10_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_41
                              transOK_10_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_43
                              transOK_10_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_46
                                  transOK_10_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_48
                              transOK_10_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_51
                                  transOK_10_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_53
                              transOK_10_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_56
                                  transOK_10_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_58
                              transOK_10_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_61
                                  transOK_10_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_63
                              transOK_10_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_66
                                  transOK_10_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_68
                              transOK_10_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_71
                                  transOK_10_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_73
                              transOK_10_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_76
                                  transOK_10_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_78
                              transOK_10_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_80
                              transOK_10_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_82
                              transOK_10_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_85
                                  transOK_10_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_87
                              transOK_10_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_90
                                  transOK_10_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_92
                              transOK_10_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_95
                                  transOK_10_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_97
                              transOK_10_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_100
                                  transOK_10_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_102
                              transOK_10_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_105
                                  transOK_10_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_107
                              transOK_10_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_110
                                  transOK_10_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_112
                              transOK_10_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_115
                                  transOK_10_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_117
                              transOK_10_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_120
                                  transOK_10_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_122
                              transOK_10_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_125
                                  transOK_10_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_127
                              transOK_10_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_130
                                  transOK_10_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_132
                              transOK_10_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_135
                                  transOK_10_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_137
                              transOK_10_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_140
                                  transOK_10_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_142
                              transOK_10_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_145
                                  transOK_10_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_147
                              transOK_10_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_10_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_10_150
                                  transOK_10_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_10_152
                              transOK_10_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_10_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_10_155
                                  transOK_10_156)))))))

end ClusterAlgebras.CertificateData.E8

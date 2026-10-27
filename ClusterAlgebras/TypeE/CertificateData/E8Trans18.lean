/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the seeds `22572` to `23825` of the `E8` certificate

Every transition out of the seeds `22572` to `23825` of the `E8` certificate passes
`raw.transOK`, checked by the kernel in pieces of `8` seeds assembled by
`CertificateCheck.allFrom_add`.

## Main results

* `transOK_18`: every transition out of the seeds `22572` to `23825` passes `raw.transOK`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_0 :
    allFrom 22572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_1 :
    allFrom 22580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_2 :
    allFrom 22588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_3 :
    allFrom 22596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_4 :
    allFrom 22604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_5 :
    allFrom 22612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_6 :
    allFrom 22620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_7 :
    allFrom 22628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_8 :
    allFrom 22636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_9 :
    allFrom 22644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_10 :
    allFrom 22652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_11 :
    allFrom 22660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_12 :
    allFrom 22668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_13 :
    allFrom 22676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_14 :
    allFrom 22684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_15 :
    allFrom 22692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_16 :
    allFrom 22700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_17 :
    allFrom 22708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_18 :
    allFrom 22716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_19 :
    allFrom 22724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_20 :
    allFrom 22732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_21 :
    allFrom 22740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_22 :
    allFrom 22748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_23 :
    allFrom 22756 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_24 :
    allFrom 22764 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_25 :
    allFrom 22772 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_26 :
    allFrom 22780 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_27 :
    allFrom 22788 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_28 :
    allFrom 22796 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_29 :
    allFrom 22804 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_30 :
    allFrom 22812 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_31 :
    allFrom 22820 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_32 :
    allFrom 22828 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_33 :
    allFrom 22836 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_34 :
    allFrom 22844 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_35 :
    allFrom 22852 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_36 :
    allFrom 22860 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_37 :
    allFrom 22868 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_38 :
    allFrom 22876 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_39 :
    allFrom 22884 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_40 :
    allFrom 22892 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_41 :
    allFrom 22900 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_42 :
    allFrom 22908 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_43 :
    allFrom 22916 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_44 :
    allFrom 22924 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_45 :
    allFrom 22932 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_46 :
    allFrom 22940 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_47 :
    allFrom 22948 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_48 :
    allFrom 22956 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_49 :
    allFrom 22964 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_50 :
    allFrom 22972 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_51 :
    allFrom 22980 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_52 :
    allFrom 22988 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_53 :
    allFrom 22996 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_54 :
    allFrom 23004 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_55 :
    allFrom 23012 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_56 :
    allFrom 23020 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_57 :
    allFrom 23028 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_58 :
    allFrom 23036 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_59 :
    allFrom 23044 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_60 :
    allFrom 23052 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_61 :
    allFrom 23060 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_62 :
    allFrom 23068 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_63 :
    allFrom 23076 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_64 :
    allFrom 23084 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_65 :
    allFrom 23092 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_66 :
    allFrom 23100 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_67 :
    allFrom 23108 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_68 :
    allFrom 23116 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_69 :
    allFrom 23124 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_70 :
    allFrom 23132 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_71 :
    allFrom 23140 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_72 :
    allFrom 23148 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_73 :
    allFrom 23156 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_74 :
    allFrom 23164 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_75 :
    allFrom 23172 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_76 :
    allFrom 23180 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_77 :
    allFrom 23188 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_78 :
    allFrom 23196 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_79 :
    allFrom 23204 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_80 :
    allFrom 23212 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_81 :
    allFrom 23220 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_82 :
    allFrom 23228 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_83 :
    allFrom 23236 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_84 :
    allFrom 23244 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_85 :
    allFrom 23252 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_86 :
    allFrom 23260 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_87 :
    allFrom 23268 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_88 :
    allFrom 23276 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_89 :
    allFrom 23284 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_90 :
    allFrom 23292 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_91 :
    allFrom 23300 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_92 :
    allFrom 23308 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_93 :
    allFrom 23316 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_94 :
    allFrom 23324 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_95 :
    allFrom 23332 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_96 :
    allFrom 23340 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_97 :
    allFrom 23348 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_98 :
    allFrom 23356 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_99 :
    allFrom 23364 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_100 :
    allFrom 23372 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_101 :
    allFrom 23380 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_102 :
    allFrom 23388 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_103 :
    allFrom 23396 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_104 :
    allFrom 23404 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_105 :
    allFrom 23412 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_106 :
    allFrom 23420 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_107 :
    allFrom 23428 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_108 :
    allFrom 23436 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_109 :
    allFrom 23444 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_110 :
    allFrom 23452 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_111 :
    allFrom 23460 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_112 :
    allFrom 23468 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_113 :
    allFrom 23476 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_114 :
    allFrom 23484 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_115 :
    allFrom 23492 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_116 :
    allFrom 23500 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_117 :
    allFrom 23508 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_118 :
    allFrom 23516 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_119 :
    allFrom 23524 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_120 :
    allFrom 23532 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_121 :
    allFrom 23540 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_122 :
    allFrom 23548 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_123 :
    allFrom 23556 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_124 :
    allFrom 23564 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_125 :
    allFrom 23572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_126 :
    allFrom 23580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_127 :
    allFrom 23588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_128 :
    allFrom 23596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_129 :
    allFrom 23604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_130 :
    allFrom 23612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_131 :
    allFrom 23620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_132 :
    allFrom 23628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_133 :
    allFrom 23636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_134 :
    allFrom 23644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_135 :
    allFrom 23652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_136 :
    allFrom 23660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_137 :
    allFrom 23668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_138 :
    allFrom 23676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_139 :
    allFrom 23684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_140 :
    allFrom 23692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_141 :
    allFrom 23700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_142 :
    allFrom 23708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_143 :
    allFrom 23716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_144 :
    allFrom 23724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_145 :
    allFrom 23732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_146 :
    allFrom 23740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_147 :
    allFrom 23748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_148 :
    allFrom 23756 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_149 :
    allFrom 23764 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_150 :
    allFrom 23772 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_151 :
    allFrom 23780 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_152 :
    allFrom 23788 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_153 :
    allFrom 23796 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_154 :
    allFrom 23804 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_155 :
    allFrom 23812 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds in the range of this `allFrom` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18_156 :
    allFrom 23820 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition out of the seeds `22572` to `23825` of the `E8` certificate passes
`raw.transOK`. -/
theorem transOK_18 :
    allFrom 22572 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_0
                              transOK_18_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_2
                              transOK_18_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_4
                              transOK_18_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_7
                                  transOK_18_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_9
                              transOK_18_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_12
                                  transOK_18_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_14
                              transOK_18_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_17
                                  transOK_18_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_19
                              transOK_18_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_22
                                  transOK_18_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_24
                              transOK_18_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_27
                                  transOK_18_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_29
                              transOK_18_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_32
                                  transOK_18_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_34
                              transOK_18_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_37
                                  transOK_18_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_39
                              transOK_18_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_41
                              transOK_18_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_43
                              transOK_18_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_46
                                  transOK_18_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_48
                              transOK_18_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_51
                                  transOK_18_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_53
                              transOK_18_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_56
                                  transOK_18_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_58
                              transOK_18_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_61
                                  transOK_18_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_63
                              transOK_18_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_66
                                  transOK_18_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_68
                              transOK_18_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_71
                                  transOK_18_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_73
                              transOK_18_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_76
                                  transOK_18_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_78
                              transOK_18_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_80
                              transOK_18_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_82
                              transOK_18_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_85
                                  transOK_18_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_87
                              transOK_18_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_90
                                  transOK_18_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_92
                              transOK_18_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_95
                                  transOK_18_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_97
                              transOK_18_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_100
                                  transOK_18_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_102
                              transOK_18_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_105
                                  transOK_18_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_107
                              transOK_18_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_110
                                  transOK_18_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_112
                              transOK_18_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_115
                                  transOK_18_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_117
                              transOK_18_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_120
                                  transOK_18_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_122
                              transOK_18_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_125
                                  transOK_18_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_127
                              transOK_18_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_130
                                  transOK_18_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_132
                              transOK_18_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_135
                                  transOK_18_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_137
                              transOK_18_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_140
                                  transOK_18_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_142
                              transOK_18_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_145
                                  transOK_18_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_147
                              transOK_18_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_18_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_18_150
                                  transOK_18_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_18_152
                              transOK_18_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_18_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_18_155
                                  transOK_18_156)))))))

end ClusterAlgebras.CertificateData.E8

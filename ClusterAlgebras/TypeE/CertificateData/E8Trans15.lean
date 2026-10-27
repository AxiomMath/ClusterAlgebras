/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the `E8` certificate, seeds `[18810, 20064)`

The transition check `transOK` of the `E8` certificate holds at every seed in `[18810, 20064)`.

## Main results

* `transOK_15`: every transition out of a seed in `[18810, 20064)` passes `transOK`.

## Implementation notes

The range is checked by `decide +kernel` in pieces of `8` seeds, `transOK_15_0` to
`transOK_15_156`, assembled by `CertificateCheck.allFrom_add`. Each piece is its own theorem, so
that the kernel's caches are dropped between pieces: the cost of a kernel evaluation grows faster
than its length. `Elab.async` is off, since with it the kernel checks of the pieces would hold
their memory until the end of the file.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

set_option Elab.async false

/-- Every transition of the `E8` certificate out of a seed in `[18810, 18818)` passes `transOK`. -/
theorem transOK_15_0 :
    allFrom 18810 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18818, 18826)` passes `transOK`. -/
theorem transOK_15_1 :
    allFrom 18818 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18826, 18834)` passes `transOK`. -/
theorem transOK_15_2 :
    allFrom 18826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18834, 18842)` passes `transOK`. -/
theorem transOK_15_3 :
    allFrom 18834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18842, 18850)` passes `transOK`. -/
theorem transOK_15_4 :
    allFrom 18842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18850, 18858)` passes `transOK`. -/
theorem transOK_15_5 :
    allFrom 18850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18858, 18866)` passes `transOK`. -/
theorem transOK_15_6 :
    allFrom 18858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18866, 18874)` passes `transOK`. -/
theorem transOK_15_7 :
    allFrom 18866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18874, 18882)` passes `transOK`. -/
theorem transOK_15_8 :
    allFrom 18874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18882, 18890)` passes `transOK`. -/
theorem transOK_15_9 :
    allFrom 18882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18890, 18898)` passes `transOK`. -/
theorem transOK_15_10 :
    allFrom 18890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18898, 18906)` passes `transOK`. -/
theorem transOK_15_11 :
    allFrom 18898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18906, 18914)` passes `transOK`. -/
theorem transOK_15_12 :
    allFrom 18906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18914, 18922)` passes `transOK`. -/
theorem transOK_15_13 :
    allFrom 18914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18922, 18930)` passes `transOK`. -/
theorem transOK_15_14 :
    allFrom 18922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18930, 18938)` passes `transOK`. -/
theorem transOK_15_15 :
    allFrom 18930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18938, 18946)` passes `transOK`. -/
theorem transOK_15_16 :
    allFrom 18938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18946, 18954)` passes `transOK`. -/
theorem transOK_15_17 :
    allFrom 18946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18954, 18962)` passes `transOK`. -/
theorem transOK_15_18 :
    allFrom 18954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18962, 18970)` passes `transOK`. -/
theorem transOK_15_19 :
    allFrom 18962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18970, 18978)` passes `transOK`. -/
theorem transOK_15_20 :
    allFrom 18970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18978, 18986)` passes `transOK`. -/
theorem transOK_15_21 :
    allFrom 18978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18986, 18994)` passes `transOK`. -/
theorem transOK_15_22 :
    allFrom 18986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18994, 19002)` passes `transOK`. -/
theorem transOK_15_23 :
    allFrom 18994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19002, 19010)` passes `transOK`. -/
theorem transOK_15_24 :
    allFrom 19002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19010, 19018)` passes `transOK`. -/
theorem transOK_15_25 :
    allFrom 19010 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19018, 19026)` passes `transOK`. -/
theorem transOK_15_26 :
    allFrom 19018 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19026, 19034)` passes `transOK`. -/
theorem transOK_15_27 :
    allFrom 19026 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19034, 19042)` passes `transOK`. -/
theorem transOK_15_28 :
    allFrom 19034 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19042, 19050)` passes `transOK`. -/
theorem transOK_15_29 :
    allFrom 19042 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19050, 19058)` passes `transOK`. -/
theorem transOK_15_30 :
    allFrom 19050 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19058, 19066)` passes `transOK`. -/
theorem transOK_15_31 :
    allFrom 19058 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19066, 19074)` passes `transOK`. -/
theorem transOK_15_32 :
    allFrom 19066 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19074, 19082)` passes `transOK`. -/
theorem transOK_15_33 :
    allFrom 19074 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19082, 19090)` passes `transOK`. -/
theorem transOK_15_34 :
    allFrom 19082 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19090, 19098)` passes `transOK`. -/
theorem transOK_15_35 :
    allFrom 19090 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19098, 19106)` passes `transOK`. -/
theorem transOK_15_36 :
    allFrom 19098 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19106, 19114)` passes `transOK`. -/
theorem transOK_15_37 :
    allFrom 19106 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19114, 19122)` passes `transOK`. -/
theorem transOK_15_38 :
    allFrom 19114 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19122, 19130)` passes `transOK`. -/
theorem transOK_15_39 :
    allFrom 19122 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19130, 19138)` passes `transOK`. -/
theorem transOK_15_40 :
    allFrom 19130 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19138, 19146)` passes `transOK`. -/
theorem transOK_15_41 :
    allFrom 19138 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19146, 19154)` passes `transOK`. -/
theorem transOK_15_42 :
    allFrom 19146 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19154, 19162)` passes `transOK`. -/
theorem transOK_15_43 :
    allFrom 19154 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19162, 19170)` passes `transOK`. -/
theorem transOK_15_44 :
    allFrom 19162 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19170, 19178)` passes `transOK`. -/
theorem transOK_15_45 :
    allFrom 19170 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19178, 19186)` passes `transOK`. -/
theorem transOK_15_46 :
    allFrom 19178 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19186, 19194)` passes `transOK`. -/
theorem transOK_15_47 :
    allFrom 19186 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19194, 19202)` passes `transOK`. -/
theorem transOK_15_48 :
    allFrom 19194 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19202, 19210)` passes `transOK`. -/
theorem transOK_15_49 :
    allFrom 19202 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19210, 19218)` passes `transOK`. -/
theorem transOK_15_50 :
    allFrom 19210 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19218, 19226)` passes `transOK`. -/
theorem transOK_15_51 :
    allFrom 19218 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19226, 19234)` passes `transOK`. -/
theorem transOK_15_52 :
    allFrom 19226 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19234, 19242)` passes `transOK`. -/
theorem transOK_15_53 :
    allFrom 19234 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19242, 19250)` passes `transOK`. -/
theorem transOK_15_54 :
    allFrom 19242 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19250, 19258)` passes `transOK`. -/
theorem transOK_15_55 :
    allFrom 19250 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19258, 19266)` passes `transOK`. -/
theorem transOK_15_56 :
    allFrom 19258 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19266, 19274)` passes `transOK`. -/
theorem transOK_15_57 :
    allFrom 19266 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19274, 19282)` passes `transOK`. -/
theorem transOK_15_58 :
    allFrom 19274 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19282, 19290)` passes `transOK`. -/
theorem transOK_15_59 :
    allFrom 19282 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19290, 19298)` passes `transOK`. -/
theorem transOK_15_60 :
    allFrom 19290 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19298, 19306)` passes `transOK`. -/
theorem transOK_15_61 :
    allFrom 19298 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19306, 19314)` passes `transOK`. -/
theorem transOK_15_62 :
    allFrom 19306 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19314, 19322)` passes `transOK`. -/
theorem transOK_15_63 :
    allFrom 19314 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19322, 19330)` passes `transOK`. -/
theorem transOK_15_64 :
    allFrom 19322 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19330, 19338)` passes `transOK`. -/
theorem transOK_15_65 :
    allFrom 19330 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19338, 19346)` passes `transOK`. -/
theorem transOK_15_66 :
    allFrom 19338 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19346, 19354)` passes `transOK`. -/
theorem transOK_15_67 :
    allFrom 19346 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19354, 19362)` passes `transOK`. -/
theorem transOK_15_68 :
    allFrom 19354 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19362, 19370)` passes `transOK`. -/
theorem transOK_15_69 :
    allFrom 19362 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19370, 19378)` passes `transOK`. -/
theorem transOK_15_70 :
    allFrom 19370 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19378, 19386)` passes `transOK`. -/
theorem transOK_15_71 :
    allFrom 19378 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19386, 19394)` passes `transOK`. -/
theorem transOK_15_72 :
    allFrom 19386 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19394, 19402)` passes `transOK`. -/
theorem transOK_15_73 :
    allFrom 19394 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19402, 19410)` passes `transOK`. -/
theorem transOK_15_74 :
    allFrom 19402 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19410, 19418)` passes `transOK`. -/
theorem transOK_15_75 :
    allFrom 19410 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19418, 19426)` passes `transOK`. -/
theorem transOK_15_76 :
    allFrom 19418 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19426, 19434)` passes `transOK`. -/
theorem transOK_15_77 :
    allFrom 19426 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19434, 19442)` passes `transOK`. -/
theorem transOK_15_78 :
    allFrom 19434 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19442, 19450)` passes `transOK`. -/
theorem transOK_15_79 :
    allFrom 19442 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19450, 19458)` passes `transOK`. -/
theorem transOK_15_80 :
    allFrom 19450 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19458, 19466)` passes `transOK`. -/
theorem transOK_15_81 :
    allFrom 19458 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19466, 19474)` passes `transOK`. -/
theorem transOK_15_82 :
    allFrom 19466 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19474, 19482)` passes `transOK`. -/
theorem transOK_15_83 :
    allFrom 19474 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19482, 19490)` passes `transOK`. -/
theorem transOK_15_84 :
    allFrom 19482 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19490, 19498)` passes `transOK`. -/
theorem transOK_15_85 :
    allFrom 19490 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19498, 19506)` passes `transOK`. -/
theorem transOK_15_86 :
    allFrom 19498 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19506, 19514)` passes `transOK`. -/
theorem transOK_15_87 :
    allFrom 19506 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19514, 19522)` passes `transOK`. -/
theorem transOK_15_88 :
    allFrom 19514 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19522, 19530)` passes `transOK`. -/
theorem transOK_15_89 :
    allFrom 19522 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19530, 19538)` passes `transOK`. -/
theorem transOK_15_90 :
    allFrom 19530 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19538, 19546)` passes `transOK`. -/
theorem transOK_15_91 :
    allFrom 19538 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19546, 19554)` passes `transOK`. -/
theorem transOK_15_92 :
    allFrom 19546 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19554, 19562)` passes `transOK`. -/
theorem transOK_15_93 :
    allFrom 19554 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19562, 19570)` passes `transOK`. -/
theorem transOK_15_94 :
    allFrom 19562 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19570, 19578)` passes `transOK`. -/
theorem transOK_15_95 :
    allFrom 19570 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19578, 19586)` passes `transOK`. -/
theorem transOK_15_96 :
    allFrom 19578 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19586, 19594)` passes `transOK`. -/
theorem transOK_15_97 :
    allFrom 19586 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19594, 19602)` passes `transOK`. -/
theorem transOK_15_98 :
    allFrom 19594 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19602, 19610)` passes `transOK`. -/
theorem transOK_15_99 :
    allFrom 19602 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19610, 19618)` passes `transOK`. -/
theorem transOK_15_100 :
    allFrom 19610 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19618, 19626)` passes `transOK`. -/
theorem transOK_15_101 :
    allFrom 19618 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19626, 19634)` passes `transOK`. -/
theorem transOK_15_102 :
    allFrom 19626 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19634, 19642)` passes `transOK`. -/
theorem transOK_15_103 :
    allFrom 19634 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19642, 19650)` passes `transOK`. -/
theorem transOK_15_104 :
    allFrom 19642 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19650, 19658)` passes `transOK`. -/
theorem transOK_15_105 :
    allFrom 19650 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19658, 19666)` passes `transOK`. -/
theorem transOK_15_106 :
    allFrom 19658 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19666, 19674)` passes `transOK`. -/
theorem transOK_15_107 :
    allFrom 19666 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19674, 19682)` passes `transOK`. -/
theorem transOK_15_108 :
    allFrom 19674 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19682, 19690)` passes `transOK`. -/
theorem transOK_15_109 :
    allFrom 19682 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19690, 19698)` passes `transOK`. -/
theorem transOK_15_110 :
    allFrom 19690 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19698, 19706)` passes `transOK`. -/
theorem transOK_15_111 :
    allFrom 19698 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19706, 19714)` passes `transOK`. -/
theorem transOK_15_112 :
    allFrom 19706 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19714, 19722)` passes `transOK`. -/
theorem transOK_15_113 :
    allFrom 19714 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19722, 19730)` passes `transOK`. -/
theorem transOK_15_114 :
    allFrom 19722 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19730, 19738)` passes `transOK`. -/
theorem transOK_15_115 :
    allFrom 19730 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19738, 19746)` passes `transOK`. -/
theorem transOK_15_116 :
    allFrom 19738 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19746, 19754)` passes `transOK`. -/
theorem transOK_15_117 :
    allFrom 19746 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19754, 19762)` passes `transOK`. -/
theorem transOK_15_118 :
    allFrom 19754 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19762, 19770)` passes `transOK`. -/
theorem transOK_15_119 :
    allFrom 19762 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19770, 19778)` passes `transOK`. -/
theorem transOK_15_120 :
    allFrom 19770 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19778, 19786)` passes `transOK`. -/
theorem transOK_15_121 :
    allFrom 19778 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19786, 19794)` passes `transOK`. -/
theorem transOK_15_122 :
    allFrom 19786 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19794, 19802)` passes `transOK`. -/
theorem transOK_15_123 :
    allFrom 19794 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19802, 19810)` passes `transOK`. -/
theorem transOK_15_124 :
    allFrom 19802 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19810, 19818)` passes `transOK`. -/
theorem transOK_15_125 :
    allFrom 19810 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19818, 19826)` passes `transOK`. -/
theorem transOK_15_126 :
    allFrom 19818 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19826, 19834)` passes `transOK`. -/
theorem transOK_15_127 :
    allFrom 19826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19834, 19842)` passes `transOK`. -/
theorem transOK_15_128 :
    allFrom 19834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19842, 19850)` passes `transOK`. -/
theorem transOK_15_129 :
    allFrom 19842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19850, 19858)` passes `transOK`. -/
theorem transOK_15_130 :
    allFrom 19850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19858, 19866)` passes `transOK`. -/
theorem transOK_15_131 :
    allFrom 19858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19866, 19874)` passes `transOK`. -/
theorem transOK_15_132 :
    allFrom 19866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19874, 19882)` passes `transOK`. -/
theorem transOK_15_133 :
    allFrom 19874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19882, 19890)` passes `transOK`. -/
theorem transOK_15_134 :
    allFrom 19882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19890, 19898)` passes `transOK`. -/
theorem transOK_15_135 :
    allFrom 19890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19898, 19906)` passes `transOK`. -/
theorem transOK_15_136 :
    allFrom 19898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19906, 19914)` passes `transOK`. -/
theorem transOK_15_137 :
    allFrom 19906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19914, 19922)` passes `transOK`. -/
theorem transOK_15_138 :
    allFrom 19914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19922, 19930)` passes `transOK`. -/
theorem transOK_15_139 :
    allFrom 19922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19930, 19938)` passes `transOK`. -/
theorem transOK_15_140 :
    allFrom 19930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19938, 19946)` passes `transOK`. -/
theorem transOK_15_141 :
    allFrom 19938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19946, 19954)` passes `transOK`. -/
theorem transOK_15_142 :
    allFrom 19946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19954, 19962)` passes `transOK`. -/
theorem transOK_15_143 :
    allFrom 19954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19962, 19970)` passes `transOK`. -/
theorem transOK_15_144 :
    allFrom 19962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19970, 19978)` passes `transOK`. -/
theorem transOK_15_145 :
    allFrom 19970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19978, 19986)` passes `transOK`. -/
theorem transOK_15_146 :
    allFrom 19978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19986, 19994)` passes `transOK`. -/
theorem transOK_15_147 :
    allFrom 19986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[19994, 20002)` passes `transOK`. -/
theorem transOK_15_148 :
    allFrom 19994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[20002, 20010)` passes `transOK`. -/
theorem transOK_15_149 :
    allFrom 20002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[20010, 20018)` passes `transOK`. -/
theorem transOK_15_150 :
    allFrom 20010 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[20018, 20026)` passes `transOK`. -/
theorem transOK_15_151 :
    allFrom 20018 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[20026, 20034)` passes `transOK`. -/
theorem transOK_15_152 :
    allFrom 20026 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[20034, 20042)` passes `transOK`. -/
theorem transOK_15_153 :
    allFrom 20034 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[20042, 20050)` passes `transOK`. -/
theorem transOK_15_154 :
    allFrom 20042 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[20050, 20058)` passes `transOK`. -/
theorem transOK_15_155 :
    allFrom 20050 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[20058, 20064)` passes `transOK`. -/
theorem transOK_15_156 :
    allFrom 20058 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition of the `E8` certificate out of a seed in `[18810, 20064)` passes `transOK`. -/
theorem transOK_15 :
    allFrom 18810 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_0
                              transOK_15_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_2
                              transOK_15_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_4
                              transOK_15_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_7
                                  transOK_15_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_9
                              transOK_15_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_12
                                  transOK_15_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_14
                              transOK_15_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_17
                                  transOK_15_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_19
                              transOK_15_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_22
                                  transOK_15_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_24
                              transOK_15_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_27
                                  transOK_15_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_29
                              transOK_15_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_32
                                  transOK_15_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_34
                              transOK_15_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_37
                                  transOK_15_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_39
                              transOK_15_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_41
                              transOK_15_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_43
                              transOK_15_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_46
                                  transOK_15_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_48
                              transOK_15_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_51
                                  transOK_15_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_53
                              transOK_15_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_56
                                  transOK_15_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_58
                              transOK_15_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_61
                                  transOK_15_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_63
                              transOK_15_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_66
                                  transOK_15_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_68
                              transOK_15_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_71
                                  transOK_15_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_73
                              transOK_15_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_76
                                  transOK_15_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_78
                              transOK_15_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_80
                              transOK_15_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_82
                              transOK_15_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_85
                                  transOK_15_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_87
                              transOK_15_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_90
                                  transOK_15_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_92
                              transOK_15_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_95
                                  transOK_15_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_97
                              transOK_15_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_100
                                  transOK_15_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_102
                              transOK_15_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_105
                                  transOK_15_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_107
                              transOK_15_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_110
                                  transOK_15_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_112
                              transOK_15_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_115
                                  transOK_15_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_117
                              transOK_15_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_120
                                  transOK_15_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_122
                              transOK_15_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_125
                                  transOK_15_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_127
                              transOK_15_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_130
                                  transOK_15_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_132
                              transOK_15_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_135
                                  transOK_15_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_137
                              transOK_15_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_140
                                  transOK_15_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_142
                              transOK_15_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_145
                                  transOK_15_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_147
                              transOK_15_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_15_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_15_150
                                  transOK_15_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_15_152
                              transOK_15_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_15_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_15_155
                                  transOK_15_156)))))))

end ClusterAlgebras.CertificateData.E8

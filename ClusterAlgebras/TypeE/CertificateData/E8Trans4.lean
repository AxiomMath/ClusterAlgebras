/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the `E8` certificate, seeds `5016` to `6269`

The transition check `raw.transOK` of the `E8` certificate holds for every seed in `[5016, 6270)`
and every direction `k < 8`, checked by the kernel in pieces of `8` seeds.

## Main results

* `transOK_4`: every seed in `[5016, 6270)` passes `raw.transOK` in every direction `k < 8`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_0 :
    allFrom 5016 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_1 :
    allFrom 5024 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_2 :
    allFrom 5032 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_3 :
    allFrom 5040 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_4 :
    allFrom 5048 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_5 :
    allFrom 5056 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_6 :
    allFrom 5064 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_7 :
    allFrom 5072 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_8 :
    allFrom 5080 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_9 :
    allFrom 5088 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_10 :
    allFrom 5096 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_11 :
    allFrom 5104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_12 :
    allFrom 5112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_13 :
    allFrom 5120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_14 :
    allFrom 5128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_15 :
    allFrom 5136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_16 :
    allFrom 5144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_17 :
    allFrom 5152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_18 :
    allFrom 5160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_19 :
    allFrom 5168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_20 :
    allFrom 5176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_21 :
    allFrom 5184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_22 :
    allFrom 5192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_23 :
    allFrom 5200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_24 :
    allFrom 5208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_25 :
    allFrom 5216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_26 :
    allFrom 5224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_27 :
    allFrom 5232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_28 :
    allFrom 5240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_29 :
    allFrom 5248 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_30 :
    allFrom 5256 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_31 :
    allFrom 5264 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_32 :
    allFrom 5272 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_33 :
    allFrom 5280 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_34 :
    allFrom 5288 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_35 :
    allFrom 5296 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_36 :
    allFrom 5304 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_37 :
    allFrom 5312 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_38 :
    allFrom 5320 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_39 :
    allFrom 5328 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_40 :
    allFrom 5336 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_41 :
    allFrom 5344 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_42 :
    allFrom 5352 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_43 :
    allFrom 5360 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_44 :
    allFrom 5368 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_45 :
    allFrom 5376 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_46 :
    allFrom 5384 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_47 :
    allFrom 5392 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_48 :
    allFrom 5400 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_49 :
    allFrom 5408 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_50 :
    allFrom 5416 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_51 :
    allFrom 5424 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_52 :
    allFrom 5432 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_53 :
    allFrom 5440 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_54 :
    allFrom 5448 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_55 :
    allFrom 5456 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_56 :
    allFrom 5464 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_57 :
    allFrom 5472 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_58 :
    allFrom 5480 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_59 :
    allFrom 5488 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_60 :
    allFrom 5496 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_61 :
    allFrom 5504 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_62 :
    allFrom 5512 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_63 :
    allFrom 5520 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_64 :
    allFrom 5528 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_65 :
    allFrom 5536 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_66 :
    allFrom 5544 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_67 :
    allFrom 5552 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_68 :
    allFrom 5560 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_69 :
    allFrom 5568 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_70 :
    allFrom 5576 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_71 :
    allFrom 5584 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_72 :
    allFrom 5592 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_73 :
    allFrom 5600 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_74 :
    allFrom 5608 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_75 :
    allFrom 5616 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_76 :
    allFrom 5624 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_77 :
    allFrom 5632 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_78 :
    allFrom 5640 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_79 :
    allFrom 5648 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_80 :
    allFrom 5656 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_81 :
    allFrom 5664 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_82 :
    allFrom 5672 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_83 :
    allFrom 5680 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_84 :
    allFrom 5688 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_85 :
    allFrom 5696 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_86 :
    allFrom 5704 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_87 :
    allFrom 5712 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_88 :
    allFrom 5720 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_89 :
    allFrom 5728 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_90 :
    allFrom 5736 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_91 :
    allFrom 5744 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_92 :
    allFrom 5752 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_93 :
    allFrom 5760 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_94 :
    allFrom 5768 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_95 :
    allFrom 5776 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_96 :
    allFrom 5784 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_97 :
    allFrom 5792 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_98 :
    allFrom 5800 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_99 :
    allFrom 5808 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_100 :
    allFrom 5816 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_101 :
    allFrom 5824 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_102 :
    allFrom 5832 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_103 :
    allFrom 5840 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_104 :
    allFrom 5848 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_105 :
    allFrom 5856 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_106 :
    allFrom 5864 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_107 :
    allFrom 5872 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_108 :
    allFrom 5880 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_109 :
    allFrom 5888 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_110 :
    allFrom 5896 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_111 :
    allFrom 5904 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_112 :
    allFrom 5912 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_113 :
    allFrom 5920 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_114 :
    allFrom 5928 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_115 :
    allFrom 5936 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_116 :
    allFrom 5944 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_117 :
    allFrom 5952 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_118 :
    allFrom 5960 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_119 :
    allFrom 5968 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_120 :
    allFrom 5976 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_121 :
    allFrom 5984 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_122 :
    allFrom 5992 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_123 :
    allFrom 6000 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_124 :
    allFrom 6008 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_125 :
    allFrom 6016 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_126 :
    allFrom 6024 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_127 :
    allFrom 6032 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_128 :
    allFrom 6040 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_129 :
    allFrom 6048 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_130 :
    allFrom 6056 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_131 :
    allFrom 6064 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_132 :
    allFrom 6072 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_133 :
    allFrom 6080 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_134 :
    allFrom 6088 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_135 :
    allFrom 6096 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_136 :
    allFrom 6104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_137 :
    allFrom 6112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_138 :
    allFrom 6120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_139 :
    allFrom 6128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_140 :
    allFrom 6136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_141 :
    allFrom 6144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_142 :
    allFrom 6152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_143 :
    allFrom 6160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_144 :
    allFrom 6168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_145 :
    allFrom 6176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_146 :
    allFrom 6184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_147 :
    allFrom 6192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_148 :
    allFrom 6200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_149 :
    allFrom 6208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_150 :
    allFrom 6216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_151 :
    allFrom 6224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_152 :
    allFrom 6232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_153 :
    allFrom 6240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_154 :
    allFrom 6248 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_155 :
    allFrom 6256 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed of the range given to `allFrom` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4_156 :
    allFrom 6264 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every seed in `[5016, 6270)` passes `raw.transOK` in every direction `k < 8`. -/
theorem transOK_4 :
    allFrom 5016 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_0
                              transOK_4_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_2
                              transOK_4_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_4
                              transOK_4_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_7
                                  transOK_4_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_9
                              transOK_4_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_12
                                  transOK_4_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_14
                              transOK_4_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_17
                                  transOK_4_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_19
                              transOK_4_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_22
                                  transOK_4_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_24
                              transOK_4_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_27
                                  transOK_4_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_29
                              transOK_4_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_32
                                  transOK_4_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_34
                              transOK_4_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_37
                                  transOK_4_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_39
                              transOK_4_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_41
                              transOK_4_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_43
                              transOK_4_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_46
                                  transOK_4_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_48
                              transOK_4_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_51
                                  transOK_4_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_53
                              transOK_4_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_56
                                  transOK_4_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_58
                              transOK_4_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_61
                                  transOK_4_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_63
                              transOK_4_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_66
                                  transOK_4_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_68
                              transOK_4_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_71
                                  transOK_4_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_73
                              transOK_4_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_76
                                  transOK_4_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_78
                              transOK_4_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_80
                              transOK_4_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_82
                              transOK_4_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_85
                                  transOK_4_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_87
                              transOK_4_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_90
                                  transOK_4_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_92
                              transOK_4_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_95
                                  transOK_4_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_97
                              transOK_4_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_100
                                  transOK_4_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_102
                              transOK_4_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_105
                                  transOK_4_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_107
                              transOK_4_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_110
                                  transOK_4_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_112
                              transOK_4_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_115
                                  transOK_4_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_117
                              transOK_4_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_120
                                  transOK_4_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_122
                              transOK_4_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_125
                                  transOK_4_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_127
                              transOK_4_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_130
                                  transOK_4_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_132
                              transOK_4_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_135
                                  transOK_4_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_137
                              transOK_4_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_140
                                  transOK_4_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_142
                              transOK_4_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_145
                                  transOK_4_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_147
                              transOK_4_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_4_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_4_150
                                  transOK_4_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_4_152
                              transOK_4_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_4_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_4_155
                                  transOK_4_156)))))))

end ClusterAlgebras.CertificateData.E8

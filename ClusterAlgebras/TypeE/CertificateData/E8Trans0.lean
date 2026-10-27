/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of seeds `[0, 1254)` of the `E8` certificate

The transitions `(a, k)` of `raw` with `a ∈ [0, 1254)` and `k < 8` are checked by kernel
evaluation of `transOK`, in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add`.

## Main results

* `transOK_0`: the transitions `(a, k)` of `raw` with `a ∈ [0, 1254)` and `k < 8` pass `transOK`.

## Implementation notes

Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the cost
of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel checks of the
pieces would hold their memory until the end of the file, so it is disabled.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

set_option Elab.async false

/-- The transitions `(a, k)` of `raw` with `a ∈ [0, 8)` and `k < 8` pass `transOK`. -/
theorem transOK_0_0 :
    allFrom 0 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [8, 16)` and `k < 8` pass `transOK`. -/
theorem transOK_0_1 :
    allFrom 8 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [16, 24)` and `k < 8` pass `transOK`. -/
theorem transOK_0_2 :
    allFrom 16 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [24, 32)` and `k < 8` pass `transOK`. -/
theorem transOK_0_3 :
    allFrom 24 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [32, 40)` and `k < 8` pass `transOK`. -/
theorem transOK_0_4 :
    allFrom 32 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [40, 48)` and `k < 8` pass `transOK`. -/
theorem transOK_0_5 :
    allFrom 40 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [48, 56)` and `k < 8` pass `transOK`. -/
theorem transOK_0_6 :
    allFrom 48 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [56, 64)` and `k < 8` pass `transOK`. -/
theorem transOK_0_7 :
    allFrom 56 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [64, 72)` and `k < 8` pass `transOK`. -/
theorem transOK_0_8 :
    allFrom 64 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [72, 80)` and `k < 8` pass `transOK`. -/
theorem transOK_0_9 :
    allFrom 72 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [80, 88)` and `k < 8` pass `transOK`. -/
theorem transOK_0_10 :
    allFrom 80 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [88, 96)` and `k < 8` pass `transOK`. -/
theorem transOK_0_11 :
    allFrom 88 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [96, 104)` and `k < 8` pass `transOK`. -/
theorem transOK_0_12 :
    allFrom 96 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [104, 112)` and `k < 8` pass `transOK`. -/
theorem transOK_0_13 :
    allFrom 104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [112, 120)` and `k < 8` pass `transOK`. -/
theorem transOK_0_14 :
    allFrom 112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [120, 128)` and `k < 8` pass `transOK`. -/
theorem transOK_0_15 :
    allFrom 120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [128, 136)` and `k < 8` pass `transOK`. -/
theorem transOK_0_16 :
    allFrom 128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [136, 144)` and `k < 8` pass `transOK`. -/
theorem transOK_0_17 :
    allFrom 136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [144, 152)` and `k < 8` pass `transOK`. -/
theorem transOK_0_18 :
    allFrom 144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [152, 160)` and `k < 8` pass `transOK`. -/
theorem transOK_0_19 :
    allFrom 152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [160, 168)` and `k < 8` pass `transOK`. -/
theorem transOK_0_20 :
    allFrom 160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [168, 176)` and `k < 8` pass `transOK`. -/
theorem transOK_0_21 :
    allFrom 168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [176, 184)` and `k < 8` pass `transOK`. -/
theorem transOK_0_22 :
    allFrom 176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [184, 192)` and `k < 8` pass `transOK`. -/
theorem transOK_0_23 :
    allFrom 184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [192, 200)` and `k < 8` pass `transOK`. -/
theorem transOK_0_24 :
    allFrom 192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [200, 208)` and `k < 8` pass `transOK`. -/
theorem transOK_0_25 :
    allFrom 200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [208, 216)` and `k < 8` pass `transOK`. -/
theorem transOK_0_26 :
    allFrom 208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [216, 224)` and `k < 8` pass `transOK`. -/
theorem transOK_0_27 :
    allFrom 216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [224, 232)` and `k < 8` pass `transOK`. -/
theorem transOK_0_28 :
    allFrom 224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [232, 240)` and `k < 8` pass `transOK`. -/
theorem transOK_0_29 :
    allFrom 232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [240, 248)` and `k < 8` pass `transOK`. -/
theorem transOK_0_30 :
    allFrom 240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [248, 256)` and `k < 8` pass `transOK`. -/
theorem transOK_0_31 :
    allFrom 248 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [256, 264)` and `k < 8` pass `transOK`. -/
theorem transOK_0_32 :
    allFrom 256 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [264, 272)` and `k < 8` pass `transOK`. -/
theorem transOK_0_33 :
    allFrom 264 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [272, 280)` and `k < 8` pass `transOK`. -/
theorem transOK_0_34 :
    allFrom 272 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [280, 288)` and `k < 8` pass `transOK`. -/
theorem transOK_0_35 :
    allFrom 280 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [288, 296)` and `k < 8` pass `transOK`. -/
theorem transOK_0_36 :
    allFrom 288 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [296, 304)` and `k < 8` pass `transOK`. -/
theorem transOK_0_37 :
    allFrom 296 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [304, 312)` and `k < 8` pass `transOK`. -/
theorem transOK_0_38 :
    allFrom 304 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [312, 320)` and `k < 8` pass `transOK`. -/
theorem transOK_0_39 :
    allFrom 312 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [320, 328)` and `k < 8` pass `transOK`. -/
theorem transOK_0_40 :
    allFrom 320 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [328, 336)` and `k < 8` pass `transOK`. -/
theorem transOK_0_41 :
    allFrom 328 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [336, 344)` and `k < 8` pass `transOK`. -/
theorem transOK_0_42 :
    allFrom 336 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [344, 352)` and `k < 8` pass `transOK`. -/
theorem transOK_0_43 :
    allFrom 344 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [352, 360)` and `k < 8` pass `transOK`. -/
theorem transOK_0_44 :
    allFrom 352 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [360, 368)` and `k < 8` pass `transOK`. -/
theorem transOK_0_45 :
    allFrom 360 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [368, 376)` and `k < 8` pass `transOK`. -/
theorem transOK_0_46 :
    allFrom 368 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [376, 384)` and `k < 8` pass `transOK`. -/
theorem transOK_0_47 :
    allFrom 376 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [384, 392)` and `k < 8` pass `transOK`. -/
theorem transOK_0_48 :
    allFrom 384 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [392, 400)` and `k < 8` pass `transOK`. -/
theorem transOK_0_49 :
    allFrom 392 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [400, 408)` and `k < 8` pass `transOK`. -/
theorem transOK_0_50 :
    allFrom 400 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [408, 416)` and `k < 8` pass `transOK`. -/
theorem transOK_0_51 :
    allFrom 408 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [416, 424)` and `k < 8` pass `transOK`. -/
theorem transOK_0_52 :
    allFrom 416 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [424, 432)` and `k < 8` pass `transOK`. -/
theorem transOK_0_53 :
    allFrom 424 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [432, 440)` and `k < 8` pass `transOK`. -/
theorem transOK_0_54 :
    allFrom 432 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [440, 448)` and `k < 8` pass `transOK`. -/
theorem transOK_0_55 :
    allFrom 440 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [448, 456)` and `k < 8` pass `transOK`. -/
theorem transOK_0_56 :
    allFrom 448 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [456, 464)` and `k < 8` pass `transOK`. -/
theorem transOK_0_57 :
    allFrom 456 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [464, 472)` and `k < 8` pass `transOK`. -/
theorem transOK_0_58 :
    allFrom 464 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [472, 480)` and `k < 8` pass `transOK`. -/
theorem transOK_0_59 :
    allFrom 472 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [480, 488)` and `k < 8` pass `transOK`. -/
theorem transOK_0_60 :
    allFrom 480 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [488, 496)` and `k < 8` pass `transOK`. -/
theorem transOK_0_61 :
    allFrom 488 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [496, 504)` and `k < 8` pass `transOK`. -/
theorem transOK_0_62 :
    allFrom 496 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [504, 512)` and `k < 8` pass `transOK`. -/
theorem transOK_0_63 :
    allFrom 504 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [512, 520)` and `k < 8` pass `transOK`. -/
theorem transOK_0_64 :
    allFrom 512 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [520, 528)` and `k < 8` pass `transOK`. -/
theorem transOK_0_65 :
    allFrom 520 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [528, 536)` and `k < 8` pass `transOK`. -/
theorem transOK_0_66 :
    allFrom 528 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [536, 544)` and `k < 8` pass `transOK`. -/
theorem transOK_0_67 :
    allFrom 536 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [544, 552)` and `k < 8` pass `transOK`. -/
theorem transOK_0_68 :
    allFrom 544 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [552, 560)` and `k < 8` pass `transOK`. -/
theorem transOK_0_69 :
    allFrom 552 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [560, 568)` and `k < 8` pass `transOK`. -/
theorem transOK_0_70 :
    allFrom 560 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [568, 576)` and `k < 8` pass `transOK`. -/
theorem transOK_0_71 :
    allFrom 568 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [576, 584)` and `k < 8` pass `transOK`. -/
theorem transOK_0_72 :
    allFrom 576 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [584, 592)` and `k < 8` pass `transOK`. -/
theorem transOK_0_73 :
    allFrom 584 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [592, 600)` and `k < 8` pass `transOK`. -/
theorem transOK_0_74 :
    allFrom 592 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [600, 608)` and `k < 8` pass `transOK`. -/
theorem transOK_0_75 :
    allFrom 600 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [608, 616)` and `k < 8` pass `transOK`. -/
theorem transOK_0_76 :
    allFrom 608 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [616, 624)` and `k < 8` pass `transOK`. -/
theorem transOK_0_77 :
    allFrom 616 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [624, 632)` and `k < 8` pass `transOK`. -/
theorem transOK_0_78 :
    allFrom 624 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [632, 640)` and `k < 8` pass `transOK`. -/
theorem transOK_0_79 :
    allFrom 632 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [640, 648)` and `k < 8` pass `transOK`. -/
theorem transOK_0_80 :
    allFrom 640 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [648, 656)` and `k < 8` pass `transOK`. -/
theorem transOK_0_81 :
    allFrom 648 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [656, 664)` and `k < 8` pass `transOK`. -/
theorem transOK_0_82 :
    allFrom 656 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [664, 672)` and `k < 8` pass `transOK`. -/
theorem transOK_0_83 :
    allFrom 664 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [672, 680)` and `k < 8` pass `transOK`. -/
theorem transOK_0_84 :
    allFrom 672 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [680, 688)` and `k < 8` pass `transOK`. -/
theorem transOK_0_85 :
    allFrom 680 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [688, 696)` and `k < 8` pass `transOK`. -/
theorem transOK_0_86 :
    allFrom 688 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [696, 704)` and `k < 8` pass `transOK`. -/
theorem transOK_0_87 :
    allFrom 696 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [704, 712)` and `k < 8` pass `transOK`. -/
theorem transOK_0_88 :
    allFrom 704 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [712, 720)` and `k < 8` pass `transOK`. -/
theorem transOK_0_89 :
    allFrom 712 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [720, 728)` and `k < 8` pass `transOK`. -/
theorem transOK_0_90 :
    allFrom 720 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [728, 736)` and `k < 8` pass `transOK`. -/
theorem transOK_0_91 :
    allFrom 728 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [736, 744)` and `k < 8` pass `transOK`. -/
theorem transOK_0_92 :
    allFrom 736 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [744, 752)` and `k < 8` pass `transOK`. -/
theorem transOK_0_93 :
    allFrom 744 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [752, 760)` and `k < 8` pass `transOK`. -/
theorem transOK_0_94 :
    allFrom 752 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [760, 768)` and `k < 8` pass `transOK`. -/
theorem transOK_0_95 :
    allFrom 760 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [768, 776)` and `k < 8` pass `transOK`. -/
theorem transOK_0_96 :
    allFrom 768 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [776, 784)` and `k < 8` pass `transOK`. -/
theorem transOK_0_97 :
    allFrom 776 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [784, 792)` and `k < 8` pass `transOK`. -/
theorem transOK_0_98 :
    allFrom 784 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [792, 800)` and `k < 8` pass `transOK`. -/
theorem transOK_0_99 :
    allFrom 792 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [800, 808)` and `k < 8` pass `transOK`. -/
theorem transOK_0_100 :
    allFrom 800 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [808, 816)` and `k < 8` pass `transOK`. -/
theorem transOK_0_101 :
    allFrom 808 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [816, 824)` and `k < 8` pass `transOK`. -/
theorem transOK_0_102 :
    allFrom 816 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [824, 832)` and `k < 8` pass `transOK`. -/
theorem transOK_0_103 :
    allFrom 824 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [832, 840)` and `k < 8` pass `transOK`. -/
theorem transOK_0_104 :
    allFrom 832 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [840, 848)` and `k < 8` pass `transOK`. -/
theorem transOK_0_105 :
    allFrom 840 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [848, 856)` and `k < 8` pass `transOK`. -/
theorem transOK_0_106 :
    allFrom 848 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [856, 864)` and `k < 8` pass `transOK`. -/
theorem transOK_0_107 :
    allFrom 856 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [864, 872)` and `k < 8` pass `transOK`. -/
theorem transOK_0_108 :
    allFrom 864 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [872, 880)` and `k < 8` pass `transOK`. -/
theorem transOK_0_109 :
    allFrom 872 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [880, 888)` and `k < 8` pass `transOK`. -/
theorem transOK_0_110 :
    allFrom 880 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [888, 896)` and `k < 8` pass `transOK`. -/
theorem transOK_0_111 :
    allFrom 888 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [896, 904)` and `k < 8` pass `transOK`. -/
theorem transOK_0_112 :
    allFrom 896 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [904, 912)` and `k < 8` pass `transOK`. -/
theorem transOK_0_113 :
    allFrom 904 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [912, 920)` and `k < 8` pass `transOK`. -/
theorem transOK_0_114 :
    allFrom 912 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [920, 928)` and `k < 8` pass `transOK`. -/
theorem transOK_0_115 :
    allFrom 920 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [928, 936)` and `k < 8` pass `transOK`. -/
theorem transOK_0_116 :
    allFrom 928 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [936, 944)` and `k < 8` pass `transOK`. -/
theorem transOK_0_117 :
    allFrom 936 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [944, 952)` and `k < 8` pass `transOK`. -/
theorem transOK_0_118 :
    allFrom 944 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [952, 960)` and `k < 8` pass `transOK`. -/
theorem transOK_0_119 :
    allFrom 952 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [960, 968)` and `k < 8` pass `transOK`. -/
theorem transOK_0_120 :
    allFrom 960 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [968, 976)` and `k < 8` pass `transOK`. -/
theorem transOK_0_121 :
    allFrom 968 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [976, 984)` and `k < 8` pass `transOK`. -/
theorem transOK_0_122 :
    allFrom 976 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [984, 992)` and `k < 8` pass `transOK`. -/
theorem transOK_0_123 :
    allFrom 984 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [992, 1000)` and `k < 8` pass `transOK`. -/
theorem transOK_0_124 :
    allFrom 992 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1000, 1008)` and `k < 8` pass `transOK`. -/
theorem transOK_0_125 :
    allFrom 1000 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1008, 1016)` and `k < 8` pass `transOK`. -/
theorem transOK_0_126 :
    allFrom 1008 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1016, 1024)` and `k < 8` pass `transOK`. -/
theorem transOK_0_127 :
    allFrom 1016 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1024, 1032)` and `k < 8` pass `transOK`. -/
theorem transOK_0_128 :
    allFrom 1024 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1032, 1040)` and `k < 8` pass `transOK`. -/
theorem transOK_0_129 :
    allFrom 1032 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1040, 1048)` and `k < 8` pass `transOK`. -/
theorem transOK_0_130 :
    allFrom 1040 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1048, 1056)` and `k < 8` pass `transOK`. -/
theorem transOK_0_131 :
    allFrom 1048 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1056, 1064)` and `k < 8` pass `transOK`. -/
theorem transOK_0_132 :
    allFrom 1056 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1064, 1072)` and `k < 8` pass `transOK`. -/
theorem transOK_0_133 :
    allFrom 1064 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1072, 1080)` and `k < 8` pass `transOK`. -/
theorem transOK_0_134 :
    allFrom 1072 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1080, 1088)` and `k < 8` pass `transOK`. -/
theorem transOK_0_135 :
    allFrom 1080 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1088, 1096)` and `k < 8` pass `transOK`. -/
theorem transOK_0_136 :
    allFrom 1088 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1096, 1104)` and `k < 8` pass `transOK`. -/
theorem transOK_0_137 :
    allFrom 1096 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1104, 1112)` and `k < 8` pass `transOK`. -/
theorem transOK_0_138 :
    allFrom 1104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1112, 1120)` and `k < 8` pass `transOK`. -/
theorem transOK_0_139 :
    allFrom 1112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1120, 1128)` and `k < 8` pass `transOK`. -/
theorem transOK_0_140 :
    allFrom 1120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1128, 1136)` and `k < 8` pass `transOK`. -/
theorem transOK_0_141 :
    allFrom 1128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1136, 1144)` and `k < 8` pass `transOK`. -/
theorem transOK_0_142 :
    allFrom 1136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1144, 1152)` and `k < 8` pass `transOK`. -/
theorem transOK_0_143 :
    allFrom 1144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1152, 1160)` and `k < 8` pass `transOK`. -/
theorem transOK_0_144 :
    allFrom 1152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1160, 1168)` and `k < 8` pass `transOK`. -/
theorem transOK_0_145 :
    allFrom 1160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1168, 1176)` and `k < 8` pass `transOK`. -/
theorem transOK_0_146 :
    allFrom 1168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1176, 1184)` and `k < 8` pass `transOK`. -/
theorem transOK_0_147 :
    allFrom 1176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1184, 1192)` and `k < 8` pass `transOK`. -/
theorem transOK_0_148 :
    allFrom 1184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1192, 1200)` and `k < 8` pass `transOK`. -/
theorem transOK_0_149 :
    allFrom 1192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1200, 1208)` and `k < 8` pass `transOK`. -/
theorem transOK_0_150 :
    allFrom 1200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1208, 1216)` and `k < 8` pass `transOK`. -/
theorem transOK_0_151 :
    allFrom 1208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1216, 1224)` and `k < 8` pass `transOK`. -/
theorem transOK_0_152 :
    allFrom 1216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1224, 1232)` and `k < 8` pass `transOK`. -/
theorem transOK_0_153 :
    allFrom 1224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1232, 1240)` and `k < 8` pass `transOK`. -/
theorem transOK_0_154 :
    allFrom 1232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1240, 1248)` and `k < 8` pass `transOK`. -/
theorem transOK_0_155 :
    allFrom 1240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [1248, 1254)` and `k < 8` pass `transOK`. -/
theorem transOK_0_156 :
    allFrom 1248 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `a ∈ [0, 1254)` and `k < 8` pass `transOK`. -/
theorem transOK_0 :
    allFrom 0 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_0
                              transOK_0_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_2
                              transOK_0_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_4
                              transOK_0_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_7
                                  transOK_0_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_9
                              transOK_0_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_12
                                  transOK_0_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_14
                              transOK_0_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_17
                                  transOK_0_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_19
                              transOK_0_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_22
                                  transOK_0_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_24
                              transOK_0_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_27
                                  transOK_0_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_29
                              transOK_0_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_32
                                  transOK_0_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_34
                              transOK_0_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_37
                                  transOK_0_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_39
                              transOK_0_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_41
                              transOK_0_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_43
                              transOK_0_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_46
                                  transOK_0_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_48
                              transOK_0_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_51
                                  transOK_0_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_53
                              transOK_0_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_56
                                  transOK_0_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_58
                              transOK_0_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_61
                                  transOK_0_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_63
                              transOK_0_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_66
                                  transOK_0_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_68
                              transOK_0_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_71
                                  transOK_0_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_73
                              transOK_0_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_76
                                  transOK_0_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_78
                              transOK_0_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_80
                              transOK_0_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_82
                              transOK_0_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_85
                                  transOK_0_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_87
                              transOK_0_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_90
                                  transOK_0_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_92
                              transOK_0_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_95
                                  transOK_0_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_97
                              transOK_0_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_100
                                  transOK_0_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_102
                              transOK_0_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_105
                                  transOK_0_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_107
                              transOK_0_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_110
                                  transOK_0_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_112
                              transOK_0_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_115
                                  transOK_0_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_117
                              transOK_0_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_120
                                  transOK_0_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_122
                              transOK_0_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_125
                                  transOK_0_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_127
                              transOK_0_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_130
                                  transOK_0_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_132
                              transOK_0_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_135
                                  transOK_0_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_137
                              transOK_0_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_140
                                  transOK_0_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_142
                              transOK_0_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_145
                                  transOK_0_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_147
                              transOK_0_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_0_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_150
                                  transOK_0_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_152
                              transOK_0_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_0_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_0_155
                                  transOK_0_156)))))))

end ClusterAlgebras.CertificateData.E8

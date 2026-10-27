/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E6

/-!
# Transitions of seeds `[0, 833)` of the `E6` certificate

The transitions of `raw` at the seeds with indices in `[0, 833)` are checked by kernel evaluation
of `transOK`, in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add`.

## Main results

* `transOK_0`: the transitions of `raw` at the seeds with indices in `[0, 833)` are valid.

## Implementation notes

Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the cost
of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel checks of the
pieces would hold their memory until the end of the file, so it is disabled.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E6

open CertificateCheck

set_option Elab.async false

/-- The transitions of `raw` at the seeds with indices in `[0, 8)` are valid. -/
theorem transOK_0_0 :
    allFrom 0 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[8, 16)` are valid. -/
theorem transOK_0_1 :
    allFrom 8 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[16, 24)` are valid. -/
theorem transOK_0_2 :
    allFrom 16 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[24, 32)` are valid. -/
theorem transOK_0_3 :
    allFrom 24 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[32, 40)` are valid. -/
theorem transOK_0_4 :
    allFrom 32 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[40, 48)` are valid. -/
theorem transOK_0_5 :
    allFrom 40 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[48, 56)` are valid. -/
theorem transOK_0_6 :
    allFrom 48 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[56, 64)` are valid. -/
theorem transOK_0_7 :
    allFrom 56 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[64, 72)` are valid. -/
theorem transOK_0_8 :
    allFrom 64 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[72, 80)` are valid. -/
theorem transOK_0_9 :
    allFrom 72 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[80, 88)` are valid. -/
theorem transOK_0_10 :
    allFrom 80 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[88, 96)` are valid. -/
theorem transOK_0_11 :
    allFrom 88 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[96, 104)` are valid. -/
theorem transOK_0_12 :
    allFrom 96 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[104, 112)` are valid. -/
theorem transOK_0_13 :
    allFrom 104 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[112, 120)` are valid. -/
theorem transOK_0_14 :
    allFrom 112 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[120, 128)` are valid. -/
theorem transOK_0_15 :
    allFrom 120 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[128, 136)` are valid. -/
theorem transOK_0_16 :
    allFrom 128 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[136, 144)` are valid. -/
theorem transOK_0_17 :
    allFrom 136 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[144, 152)` are valid. -/
theorem transOK_0_18 :
    allFrom 144 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[152, 160)` are valid. -/
theorem transOK_0_19 :
    allFrom 152 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[160, 168)` are valid. -/
theorem transOK_0_20 :
    allFrom 160 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[168, 176)` are valid. -/
theorem transOK_0_21 :
    allFrom 168 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[176, 184)` are valid. -/
theorem transOK_0_22 :
    allFrom 176 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[184, 192)` are valid. -/
theorem transOK_0_23 :
    allFrom 184 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[192, 200)` are valid. -/
theorem transOK_0_24 :
    allFrom 192 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[200, 208)` are valid. -/
theorem transOK_0_25 :
    allFrom 200 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[208, 216)` are valid. -/
theorem transOK_0_26 :
    allFrom 208 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[216, 224)` are valid. -/
theorem transOK_0_27 :
    allFrom 216 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[224, 232)` are valid. -/
theorem transOK_0_28 :
    allFrom 224 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[232, 240)` are valid. -/
theorem transOK_0_29 :
    allFrom 232 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[240, 248)` are valid. -/
theorem transOK_0_30 :
    allFrom 240 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[248, 256)` are valid. -/
theorem transOK_0_31 :
    allFrom 248 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[256, 264)` are valid. -/
theorem transOK_0_32 :
    allFrom 256 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[264, 272)` are valid. -/
theorem transOK_0_33 :
    allFrom 264 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[272, 280)` are valid. -/
theorem transOK_0_34 :
    allFrom 272 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[280, 288)` are valid. -/
theorem transOK_0_35 :
    allFrom 280 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[288, 296)` are valid. -/
theorem transOK_0_36 :
    allFrom 288 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[296, 304)` are valid. -/
theorem transOK_0_37 :
    allFrom 296 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[304, 312)` are valid. -/
theorem transOK_0_38 :
    allFrom 304 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[312, 320)` are valid. -/
theorem transOK_0_39 :
    allFrom 312 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[320, 328)` are valid. -/
theorem transOK_0_40 :
    allFrom 320 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[328, 336)` are valid. -/
theorem transOK_0_41 :
    allFrom 328 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[336, 344)` are valid. -/
theorem transOK_0_42 :
    allFrom 336 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[344, 352)` are valid. -/
theorem transOK_0_43 :
    allFrom 344 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[352, 360)` are valid. -/
theorem transOK_0_44 :
    allFrom 352 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[360, 368)` are valid. -/
theorem transOK_0_45 :
    allFrom 360 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[368, 376)` are valid. -/
theorem transOK_0_46 :
    allFrom 368 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[376, 384)` are valid. -/
theorem transOK_0_47 :
    allFrom 376 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[384, 392)` are valid. -/
theorem transOK_0_48 :
    allFrom 384 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[392, 400)` are valid. -/
theorem transOK_0_49 :
    allFrom 392 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[400, 408)` are valid. -/
theorem transOK_0_50 :
    allFrom 400 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[408, 416)` are valid. -/
theorem transOK_0_51 :
    allFrom 408 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[416, 424)` are valid. -/
theorem transOK_0_52 :
    allFrom 416 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[424, 432)` are valid. -/
theorem transOK_0_53 :
    allFrom 424 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[432, 440)` are valid. -/
theorem transOK_0_54 :
    allFrom 432 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[440, 448)` are valid. -/
theorem transOK_0_55 :
    allFrom 440 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[448, 456)` are valid. -/
theorem transOK_0_56 :
    allFrom 448 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[456, 464)` are valid. -/
theorem transOK_0_57 :
    allFrom 456 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[464, 472)` are valid. -/
theorem transOK_0_58 :
    allFrom 464 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[472, 480)` are valid. -/
theorem transOK_0_59 :
    allFrom 472 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[480, 488)` are valid. -/
theorem transOK_0_60 :
    allFrom 480 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[488, 496)` are valid. -/
theorem transOK_0_61 :
    allFrom 488 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[496, 504)` are valid. -/
theorem transOK_0_62 :
    allFrom 496 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[504, 512)` are valid. -/
theorem transOK_0_63 :
    allFrom 504 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[512, 520)` are valid. -/
theorem transOK_0_64 :
    allFrom 512 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[520, 528)` are valid. -/
theorem transOK_0_65 :
    allFrom 520 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[528, 536)` are valid. -/
theorem transOK_0_66 :
    allFrom 528 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[536, 544)` are valid. -/
theorem transOK_0_67 :
    allFrom 536 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[544, 552)` are valid. -/
theorem transOK_0_68 :
    allFrom 544 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[552, 560)` are valid. -/
theorem transOK_0_69 :
    allFrom 552 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[560, 568)` are valid. -/
theorem transOK_0_70 :
    allFrom 560 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[568, 576)` are valid. -/
theorem transOK_0_71 :
    allFrom 568 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[576, 584)` are valid. -/
theorem transOK_0_72 :
    allFrom 576 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[584, 592)` are valid. -/
theorem transOK_0_73 :
    allFrom 584 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[592, 600)` are valid. -/
theorem transOK_0_74 :
    allFrom 592 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[600, 608)` are valid. -/
theorem transOK_0_75 :
    allFrom 600 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[608, 616)` are valid. -/
theorem transOK_0_76 :
    allFrom 608 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[616, 624)` are valid. -/
theorem transOK_0_77 :
    allFrom 616 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[624, 632)` are valid. -/
theorem transOK_0_78 :
    allFrom 624 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[632, 640)` are valid. -/
theorem transOK_0_79 :
    allFrom 632 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[640, 648)` are valid. -/
theorem transOK_0_80 :
    allFrom 640 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[648, 656)` are valid. -/
theorem transOK_0_81 :
    allFrom 648 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[656, 664)` are valid. -/
theorem transOK_0_82 :
    allFrom 656 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[664, 672)` are valid. -/
theorem transOK_0_83 :
    allFrom 664 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[672, 680)` are valid. -/
theorem transOK_0_84 :
    allFrom 672 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[680, 688)` are valid. -/
theorem transOK_0_85 :
    allFrom 680 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[688, 696)` are valid. -/
theorem transOK_0_86 :
    allFrom 688 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[696, 704)` are valid. -/
theorem transOK_0_87 :
    allFrom 696 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[704, 712)` are valid. -/
theorem transOK_0_88 :
    allFrom 704 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[712, 720)` are valid. -/
theorem transOK_0_89 :
    allFrom 712 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[720, 728)` are valid. -/
theorem transOK_0_90 :
    allFrom 720 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[728, 736)` are valid. -/
theorem transOK_0_91 :
    allFrom 728 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[736, 744)` are valid. -/
theorem transOK_0_92 :
    allFrom 736 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[744, 752)` are valid. -/
theorem transOK_0_93 :
    allFrom 744 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[752, 760)` are valid. -/
theorem transOK_0_94 :
    allFrom 752 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[760, 768)` are valid. -/
theorem transOK_0_95 :
    allFrom 760 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[768, 776)` are valid. -/
theorem transOK_0_96 :
    allFrom 768 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[776, 784)` are valid. -/
theorem transOK_0_97 :
    allFrom 776 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[784, 792)` are valid. -/
theorem transOK_0_98 :
    allFrom 784 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[792, 800)` are valid. -/
theorem transOK_0_99 :
    allFrom 792 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[800, 808)` are valid. -/
theorem transOK_0_100 :
    allFrom 800 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[808, 816)` are valid. -/
theorem transOK_0_101 :
    allFrom 808 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[816, 824)` are valid. -/
theorem transOK_0_102 :
    allFrom 816 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[824, 832)` are valid. -/
theorem transOK_0_103 :
    allFrom 824 8 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[832, 833)` are valid. -/
theorem transOK_0_104 :
    allFrom 832 1 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true := by
  decide +kernel

/-- The transitions of `raw` at the seeds with indices in `[0, 833)` are valid. -/
theorem transOK_0 :
    allFrom 0 833 (fun a => allBelow 6 fun k => raw.transOK 6 6 42 833 385 a k) = true :=
  allFrom_add (a := 416) (b := 417)
      (allFrom_add (a := 208) (b := 208)
          (allFrom_add (a := 104) (b := 104)
              (allFrom_add (a := 48) (b := 56)
                  (allFrom_add (a := 24) (b := 24)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_0
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_1
                              transOK_0_2))
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_3
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_4
                              transOK_0_5)))
                  (allFrom_add (a := 24) (b := 32)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_6
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_7
                              transOK_0_8))
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_9
                              transOK_0_10)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_11
                              transOK_0_12))))
              (allFrom_add (a := 48) (b := 56)
                  (allFrom_add (a := 24) (b := 24)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_13
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_14
                              transOK_0_15))
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_16
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_17
                              transOK_0_18)))
                  (allFrom_add (a := 24) (b := 32)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_19
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_20
                              transOK_0_21))
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_22
                              transOK_0_23)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_24
                              transOK_0_25)))))
          (allFrom_add (a := 104) (b := 104)
              (allFrom_add (a := 48) (b := 56)
                  (allFrom_add (a := 24) (b := 24)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_26
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_27
                              transOK_0_28))
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_29
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_30
                              transOK_0_31)))
                  (allFrom_add (a := 24) (b := 32)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_32
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_33
                              transOK_0_34))
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_35
                              transOK_0_36)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_37
                              transOK_0_38))))
              (allFrom_add (a := 48) (b := 56)
                  (allFrom_add (a := 24) (b := 24)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_39
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_40
                              transOK_0_41))
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_42
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_43
                              transOK_0_44)))
                  (allFrom_add (a := 24) (b := 32)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_45
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_46
                              transOK_0_47))
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_48
                              transOK_0_49)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_50
                              transOK_0_51))))))
      (allFrom_add (a := 208) (b := 209)
          (allFrom_add (a := 104) (b := 104)
              (allFrom_add (a := 48) (b := 56)
                  (allFrom_add (a := 24) (b := 24)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_52
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_53
                              transOK_0_54))
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_55
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_56
                              transOK_0_57)))
                  (allFrom_add (a := 24) (b := 32)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_58
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_59
                              transOK_0_60))
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_61
                              transOK_0_62)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_63
                              transOK_0_64))))
              (allFrom_add (a := 48) (b := 56)
                  (allFrom_add (a := 24) (b := 24)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_65
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_66
                              transOK_0_67))
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_68
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_69
                              transOK_0_70)))
                  (allFrom_add (a := 24) (b := 32)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_71
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_72
                              transOK_0_73))
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_74
                              transOK_0_75)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_76
                              transOK_0_77)))))
          (allFrom_add (a := 104) (b := 105)
              (allFrom_add (a := 48) (b := 56)
                  (allFrom_add (a := 24) (b := 24)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_78
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_79
                              transOK_0_80))
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_81
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_82
                              transOK_0_83)))
                  (allFrom_add (a := 24) (b := 32)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_84
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_85
                              transOK_0_86))
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_87
                              transOK_0_88)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_89
                              transOK_0_90))))
              (allFrom_add (a := 56) (b := 49)
                  (allFrom_add (a := 24) (b := 32)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_91
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_92
                              transOK_0_93))
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_94
                              transOK_0_95)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_96
                              transOK_0_97)))
                  (allFrom_add (a := 24) (b := 25)
                      (allFrom_add (a := 8) (b := 16)
                          transOK_0_98
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_99
                              transOK_0_100))
                      (allFrom_add (a := 16) (b := 9)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_0_101
                              transOK_0_102)
                          (allFrom_add (a := 8) (b := 1)
                              transOK_0_103
                              transOK_0_104))))))

end ClusterAlgebras.CertificateData.E6

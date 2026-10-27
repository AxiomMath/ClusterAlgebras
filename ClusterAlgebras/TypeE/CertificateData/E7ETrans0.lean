/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E7E

/-!
# Transitions of the seeds `[0, 2080)` of the `E7E` certificate

The check `transOK` holds at every direction `k < 7` for every seed `a < 2080` of the `E7E`
certificate. It is checked by the kernel in pieces of `8` seeds, which are assembled by
`CertificateCheck.allFrom_add`.

## Main results

* `transOK_0`: `transOK` holds at every direction `k < 7` for every seed `a < 2080`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7E

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_0 :
    allFrom 0 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_1 :
    allFrom 8 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_2 :
    allFrom 16 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_3 :
    allFrom 24 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_4 :
    allFrom 32 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_5 :
    allFrom 40 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_6 :
    allFrom 48 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_7 :
    allFrom 56 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_8 :
    allFrom 64 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_9 :
    allFrom 72 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_10 :
    allFrom 80 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_11 :
    allFrom 88 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_12 :
    allFrom 96 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_13 :
    allFrom 104 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_14 :
    allFrom 112 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_15 :
    allFrom 120 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_16 :
    allFrom 128 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_17 :
    allFrom 136 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_18 :
    allFrom 144 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_19 :
    allFrom 152 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_20 :
    allFrom 160 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_21 :
    allFrom 168 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_22 :
    allFrom 176 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_23 :
    allFrom 184 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_24 :
    allFrom 192 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_25 :
    allFrom 200 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_26 :
    allFrom 208 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_27 :
    allFrom 216 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_28 :
    allFrom 224 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_29 :
    allFrom 232 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_30 :
    allFrom 240 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_31 :
    allFrom 248 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_32 :
    allFrom 256 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_33 :
    allFrom 264 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_34 :
    allFrom 272 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_35 :
    allFrom 280 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_36 :
    allFrom 288 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_37 :
    allFrom 296 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_38 :
    allFrom 304 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_39 :
    allFrom 312 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_40 :
    allFrom 320 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_41 :
    allFrom 328 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_42 :
    allFrom 336 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_43 :
    allFrom 344 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_44 :
    allFrom 352 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_45 :
    allFrom 360 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_46 :
    allFrom 368 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_47 :
    allFrom 376 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_48 :
    allFrom 384 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_49 :
    allFrom 392 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_50 :
    allFrom 400 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_51 :
    allFrom 408 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_52 :
    allFrom 416 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_53 :
    allFrom 424 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_54 :
    allFrom 432 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_55 :
    allFrom 440 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_56 :
    allFrom 448 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_57 :
    allFrom 456 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_58 :
    allFrom 464 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_59 :
    allFrom 472 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_60 :
    allFrom 480 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_61 :
    allFrom 488 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_62 :
    allFrom 496 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_63 :
    allFrom 504 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_64 :
    allFrom 512 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_65 :
    allFrom 520 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_66 :
    allFrom 528 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_67 :
    allFrom 536 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_68 :
    allFrom 544 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_69 :
    allFrom 552 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_70 :
    allFrom 560 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_71 :
    allFrom 568 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_72 :
    allFrom 576 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_73 :
    allFrom 584 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_74 :
    allFrom 592 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_75 :
    allFrom 600 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_76 :
    allFrom 608 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_77 :
    allFrom 616 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_78 :
    allFrom 624 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_79 :
    allFrom 632 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_80 :
    allFrom 640 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_81 :
    allFrom 648 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_82 :
    allFrom 656 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_83 :
    allFrom 664 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_84 :
    allFrom 672 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_85 :
    allFrom 680 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_86 :
    allFrom 688 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_87 :
    allFrom 696 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_88 :
    allFrom 704 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_89 :
    allFrom 712 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_90 :
    allFrom 720 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_91 :
    allFrom 728 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_92 :
    allFrom 736 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_93 :
    allFrom 744 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_94 :
    allFrom 752 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_95 :
    allFrom 760 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_96 :
    allFrom 768 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_97 :
    allFrom 776 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_98 :
    allFrom 784 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_99 :
    allFrom 792 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_100 :
    allFrom 800 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_101 :
    allFrom 808 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_102 :
    allFrom 816 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_103 :
    allFrom 824 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_104 :
    allFrom 832 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_105 :
    allFrom 840 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_106 :
    allFrom 848 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_107 :
    allFrom 856 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_108 :
    allFrom 864 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_109 :
    allFrom 872 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_110 :
    allFrom 880 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_111 :
    allFrom 888 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_112 :
    allFrom 896 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_113 :
    allFrom 904 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_114 :
    allFrom 912 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_115 :
    allFrom 920 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_116 :
    allFrom 928 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_117 :
    allFrom 936 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_118 :
    allFrom 944 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_119 :
    allFrom 952 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_120 :
    allFrom 960 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_121 :
    allFrom 968 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_122 :
    allFrom 976 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_123 :
    allFrom 984 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_124 :
    allFrom 992 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_125 :
    allFrom 1000 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_126 :
    allFrom 1008 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_127 :
    allFrom 1016 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_128 :
    allFrom 1024 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_129 :
    allFrom 1032 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_130 :
    allFrom 1040 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_131 :
    allFrom 1048 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_132 :
    allFrom 1056 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_133 :
    allFrom 1064 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_134 :
    allFrom 1072 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_135 :
    allFrom 1080 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_136 :
    allFrom 1088 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_137 :
    allFrom 1096 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_138 :
    allFrom 1104 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_139 :
    allFrom 1112 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_140 :
    allFrom 1120 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_141 :
    allFrom 1128 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_142 :
    allFrom 1136 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_143 :
    allFrom 1144 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_144 :
    allFrom 1152 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_145 :
    allFrom 1160 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_146 :
    allFrom 1168 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_147 :
    allFrom 1176 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_148 :
    allFrom 1184 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_149 :
    allFrom 1192 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_150 :
    allFrom 1200 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_151 :
    allFrom 1208 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_152 :
    allFrom 1216 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_153 :
    allFrom 1224 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_154 :
    allFrom 1232 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_155 :
    allFrom 1240 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_156 :
    allFrom 1248 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_157 :
    allFrom 1256 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_158 :
    allFrom 1264 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_159 :
    allFrom 1272 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_160 :
    allFrom 1280 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_161 :
    allFrom 1288 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_162 :
    allFrom 1296 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_163 :
    allFrom 1304 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_164 :
    allFrom 1312 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_165 :
    allFrom 1320 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_166 :
    allFrom 1328 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_167 :
    allFrom 1336 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_168 :
    allFrom 1344 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_169 :
    allFrom 1352 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_170 :
    allFrom 1360 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_171 :
    allFrom 1368 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_172 :
    allFrom 1376 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_173 :
    allFrom 1384 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_174 :
    allFrom 1392 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_175 :
    allFrom 1400 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_176 :
    allFrom 1408 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_177 :
    allFrom 1416 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_178 :
    allFrom 1424 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_179 :
    allFrom 1432 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_180 :
    allFrom 1440 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_181 :
    allFrom 1448 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_182 :
    allFrom 1456 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_183 :
    allFrom 1464 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_184 :
    allFrom 1472 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_185 :
    allFrom 1480 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_186 :
    allFrom 1488 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_187 :
    allFrom 1496 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_188 :
    allFrom 1504 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_189 :
    allFrom 1512 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_190 :
    allFrom 1520 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_191 :
    allFrom 1528 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_192 :
    allFrom 1536 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_193 :
    allFrom 1544 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_194 :
    allFrom 1552 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_195 :
    allFrom 1560 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_196 :
    allFrom 1568 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_197 :
    allFrom 1576 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_198 :
    allFrom 1584 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_199 :
    allFrom 1592 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_200 :
    allFrom 1600 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_201 :
    allFrom 1608 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_202 :
    allFrom 1616 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_203 :
    allFrom 1624 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_204 :
    allFrom 1632 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_205 :
    allFrom 1640 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_206 :
    allFrom 1648 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_207 :
    allFrom 1656 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_208 :
    allFrom 1664 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_209 :
    allFrom 1672 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_210 :
    allFrom 1680 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_211 :
    allFrom 1688 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_212 :
    allFrom 1696 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_213 :
    allFrom 1704 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_214 :
    allFrom 1712 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_215 :
    allFrom 1720 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_216 :
    allFrom 1728 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_217 :
    allFrom 1736 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_218 :
    allFrom 1744 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_219 :
    allFrom 1752 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_220 :
    allFrom 1760 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_221 :
    allFrom 1768 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_222 :
    allFrom 1776 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_223 :
    allFrom 1784 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_224 :
    allFrom 1792 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_225 :
    allFrom 1800 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_226 :
    allFrom 1808 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_227 :
    allFrom 1816 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_228 :
    allFrom 1824 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_229 :
    allFrom 1832 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_230 :
    allFrom 1840 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_231 :
    allFrom 1848 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_232 :
    allFrom 1856 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_233 :
    allFrom 1864 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_234 :
    allFrom 1872 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_235 :
    allFrom 1880 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_236 :
    allFrom 1888 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_237 :
    allFrom 1896 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_238 :
    allFrom 1904 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_239 :
    allFrom 1912 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_240 :
    allFrom 1920 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_241 :
    allFrom 1928 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_242 :
    allFrom 1936 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_243 :
    allFrom 1944 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_244 :
    allFrom 1952 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_245 :
    allFrom 1960 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_246 :
    allFrom 1968 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_247 :
    allFrom 1976 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_248 :
    allFrom 1984 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_249 :
    allFrom 1992 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_250 :
    allFrom 2000 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_251 :
    allFrom 2008 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_252 :
    allFrom 2016 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_253 :
    allFrom 2024 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_254 :
    allFrom 2032 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_255 :
    allFrom 2040 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_256 :
    allFrom 2048 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_257 :
    allFrom 2056 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_258 :
    allFrom 2064 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for each of the `8` seeds of this piece of the
`E7E` certificate. -/
theorem transOK_0_259 :
    allFrom 2072 8 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- `transOK` holds at every direction `k < 7` for every seed `a < 2080` of the `E7E`
certificate. -/
theorem transOK_0 :
    allFrom 0 2080 (fun a => allBelow 7 fun k => raw.transOK 8 7 70 4160 1050 a k) = true :=
  allFrom_add (a := 1040) (b := 1040)
      (allFrom_add (a := 520) (b := 520)
          (allFrom_add (a := 256) (b := 264)
              (allFrom_add (a := 128) (b := 128)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_0
                                  transOK_0_1)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_2
                                  transOK_0_3))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_4
                                  transOK_0_5)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_6
                                  transOK_0_7)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_8
                                  transOK_0_9)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_10
                                  transOK_0_11))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_12
                                  transOK_0_13)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_14
                                  transOK_0_15))))
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_16
                                  transOK_0_17)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_18
                                  transOK_0_19))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_20
                                  transOK_0_21)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_22
                                  transOK_0_23)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_24
                                  transOK_0_25)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_26
                                  transOK_0_27))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_28
                                  transOK_0_29)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_30
                                  transOK_0_31)))))
              (allFrom_add (a := 128) (b := 136)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_32
                                  transOK_0_33)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_34
                                  transOK_0_35))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_36
                                  transOK_0_37)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_38
                                  transOK_0_39)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_40
                                  transOK_0_41)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_42
                                  transOK_0_43))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_44
                                  transOK_0_45)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_46
                                  transOK_0_47))))
                  (allFrom_add (a := 64) (b := 72)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_48
                                  transOK_0_49)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_50
                                  transOK_0_51))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_52
                                  transOK_0_53)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_54
                                  transOK_0_55)))
                      (allFrom_add (a := 32) (b := 40)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_56
                                  transOK_0_57)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_58
                                  transOK_0_59))
                          (allFrom_add (a := 16) (b := 24)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_60
                                  transOK_0_61)
                              (allFrom_add (a := 8) (b := 16)
                                  transOK_0_62
                                  (allFrom_add (a := 8) (b := 8)
                                      transOK_0_63
                                      transOK_0_64)))))))
          (allFrom_add (a := 256) (b := 264)
              (allFrom_add (a := 128) (b := 128)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_65
                                  transOK_0_66)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_67
                                  transOK_0_68))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_69
                                  transOK_0_70)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_71
                                  transOK_0_72)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_73
                                  transOK_0_74)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_75
                                  transOK_0_76))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_77
                                  transOK_0_78)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_79
                                  transOK_0_80))))
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_81
                                  transOK_0_82)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_83
                                  transOK_0_84))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_85
                                  transOK_0_86)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_87
                                  transOK_0_88)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_89
                                  transOK_0_90)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_91
                                  transOK_0_92))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_93
                                  transOK_0_94)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_95
                                  transOK_0_96)))))
              (allFrom_add (a := 128) (b := 136)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_97
                                  transOK_0_98)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_99
                                  transOK_0_100))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_101
                                  transOK_0_102)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_103
                                  transOK_0_104)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_105
                                  transOK_0_106)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_107
                                  transOK_0_108))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_109
                                  transOK_0_110)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_111
                                  transOK_0_112))))
                  (allFrom_add (a := 64) (b := 72)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_113
                                  transOK_0_114)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_115
                                  transOK_0_116))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_117
                                  transOK_0_118)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_119
                                  transOK_0_120)))
                      (allFrom_add (a := 32) (b := 40)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_121
                                  transOK_0_122)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_123
                                  transOK_0_124))
                          (allFrom_add (a := 16) (b := 24)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_125
                                  transOK_0_126)
                              (allFrom_add (a := 8) (b := 16)
                                  transOK_0_127
                                  (allFrom_add (a := 8) (b := 8)
                                      transOK_0_128
                                      transOK_0_129))))))))
      (allFrom_add (a := 520) (b := 520)
          (allFrom_add (a := 256) (b := 264)
              (allFrom_add (a := 128) (b := 128)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_130
                                  transOK_0_131)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_132
                                  transOK_0_133))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_134
                                  transOK_0_135)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_136
                                  transOK_0_137)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_138
                                  transOK_0_139)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_140
                                  transOK_0_141))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_142
                                  transOK_0_143)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_144
                                  transOK_0_145))))
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_146
                                  transOK_0_147)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_148
                                  transOK_0_149))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_150
                                  transOK_0_151)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_152
                                  transOK_0_153)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_154
                                  transOK_0_155)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_156
                                  transOK_0_157))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_158
                                  transOK_0_159)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_160
                                  transOK_0_161)))))
              (allFrom_add (a := 128) (b := 136)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_162
                                  transOK_0_163)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_164
                                  transOK_0_165))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_166
                                  transOK_0_167)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_168
                                  transOK_0_169)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_170
                                  transOK_0_171)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_172
                                  transOK_0_173))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_174
                                  transOK_0_175)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_176
                                  transOK_0_177))))
                  (allFrom_add (a := 64) (b := 72)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_178
                                  transOK_0_179)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_180
                                  transOK_0_181))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_182
                                  transOK_0_183)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_184
                                  transOK_0_185)))
                      (allFrom_add (a := 32) (b := 40)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_186
                                  transOK_0_187)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_188
                                  transOK_0_189))
                          (allFrom_add (a := 16) (b := 24)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_190
                                  transOK_0_191)
                              (allFrom_add (a := 8) (b := 16)
                                  transOK_0_192
                                  (allFrom_add (a := 8) (b := 8)
                                      transOK_0_193
                                      transOK_0_194)))))))
          (allFrom_add (a := 256) (b := 264)
              (allFrom_add (a := 128) (b := 128)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_195
                                  transOK_0_196)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_197
                                  transOK_0_198))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_199
                                  transOK_0_200)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_201
                                  transOK_0_202)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_203
                                  transOK_0_204)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_205
                                  transOK_0_206))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_207
                                  transOK_0_208)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_209
                                  transOK_0_210))))
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_211
                                  transOK_0_212)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_213
                                  transOK_0_214))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_215
                                  transOK_0_216)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_217
                                  transOK_0_218)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_219
                                  transOK_0_220)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_221
                                  transOK_0_222))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_223
                                  transOK_0_224)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_225
                                  transOK_0_226)))))
              (allFrom_add (a := 128) (b := 136)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_227
                                  transOK_0_228)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_229
                                  transOK_0_230))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_231
                                  transOK_0_232)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_233
                                  transOK_0_234)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_235
                                  transOK_0_236)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_237
                                  transOK_0_238))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_239
                                  transOK_0_240)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_241
                                  transOK_0_242))))
                  (allFrom_add (a := 64) (b := 72)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_243
                                  transOK_0_244)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_245
                                  transOK_0_246))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_247
                                  transOK_0_248)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_249
                                  transOK_0_250)))
                      (allFrom_add (a := 32) (b := 40)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_251
                                  transOK_0_252)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_253
                                  transOK_0_254))
                          (allFrom_add (a := 16) (b := 24)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_0_255
                                  transOK_0_256)
                              (allFrom_add (a := 8) (b := 16)
                                  transOK_0_257
                                  (allFrom_add (a := 8) (b := 8)
                                      transOK_0_258
                                      transOK_0_259))))))))

end ClusterAlgebras.CertificateData.E7E

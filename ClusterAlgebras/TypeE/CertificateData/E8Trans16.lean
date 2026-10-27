/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of seeds `[20064, 21318)` of the `E8` certificate

This file checks in the kernel that `raw.transOK` holds for every seed in `[20064, 21318)` and
every direction, in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add`.

## Main results

* `transOK_16`: `raw.transOK` holds for every seed in `[20064, 21318)` and direction `k < 8`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_0 :
    allFrom 20064 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_1 :
    allFrom 20072 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_2 :
    allFrom 20080 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_3 :
    allFrom 20088 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_4 :
    allFrom 20096 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_5 :
    allFrom 20104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_6 :
    allFrom 20112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_7 :
    allFrom 20120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_8 :
    allFrom 20128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_9 :
    allFrom 20136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_10 :
    allFrom 20144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_11 :
    allFrom 20152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_12 :
    allFrom 20160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_13 :
    allFrom 20168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_14 :
    allFrom 20176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_15 :
    allFrom 20184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_16 :
    allFrom 20192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_17 :
    allFrom 20200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_18 :
    allFrom 20208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_19 :
    allFrom 20216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_20 :
    allFrom 20224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_21 :
    allFrom 20232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_22 :
    allFrom 20240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_23 :
    allFrom 20248 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_24 :
    allFrom 20256 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_25 :
    allFrom 20264 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_26 :
    allFrom 20272 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_27 :
    allFrom 20280 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_28 :
    allFrom 20288 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_29 :
    allFrom 20296 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_30 :
    allFrom 20304 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_31 :
    allFrom 20312 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_32 :
    allFrom 20320 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_33 :
    allFrom 20328 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_34 :
    allFrom 20336 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_35 :
    allFrom 20344 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_36 :
    allFrom 20352 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_37 :
    allFrom 20360 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_38 :
    allFrom 20368 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_39 :
    allFrom 20376 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_40 :
    allFrom 20384 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_41 :
    allFrom 20392 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_42 :
    allFrom 20400 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_43 :
    allFrom 20408 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_44 :
    allFrom 20416 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_45 :
    allFrom 20424 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_46 :
    allFrom 20432 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_47 :
    allFrom 20440 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_48 :
    allFrom 20448 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_49 :
    allFrom 20456 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_50 :
    allFrom 20464 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_51 :
    allFrom 20472 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_52 :
    allFrom 20480 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_53 :
    allFrom 20488 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_54 :
    allFrom 20496 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_55 :
    allFrom 20504 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_56 :
    allFrom 20512 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_57 :
    allFrom 20520 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_58 :
    allFrom 20528 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_59 :
    allFrom 20536 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_60 :
    allFrom 20544 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_61 :
    allFrom 20552 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_62 :
    allFrom 20560 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_63 :
    allFrom 20568 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_64 :
    allFrom 20576 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_65 :
    allFrom 20584 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_66 :
    allFrom 20592 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_67 :
    allFrom 20600 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_68 :
    allFrom 20608 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_69 :
    allFrom 20616 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_70 :
    allFrom 20624 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_71 :
    allFrom 20632 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_72 :
    allFrom 20640 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_73 :
    allFrom 20648 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_74 :
    allFrom 20656 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_75 :
    allFrom 20664 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_76 :
    allFrom 20672 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_77 :
    allFrom 20680 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_78 :
    allFrom 20688 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_79 :
    allFrom 20696 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_80 :
    allFrom 20704 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_81 :
    allFrom 20712 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_82 :
    allFrom 20720 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_83 :
    allFrom 20728 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_84 :
    allFrom 20736 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_85 :
    allFrom 20744 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_86 :
    allFrom 20752 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_87 :
    allFrom 20760 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_88 :
    allFrom 20768 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_89 :
    allFrom 20776 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_90 :
    allFrom 20784 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_91 :
    allFrom 20792 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_92 :
    allFrom 20800 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_93 :
    allFrom 20808 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_94 :
    allFrom 20816 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_95 :
    allFrom 20824 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_96 :
    allFrom 20832 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_97 :
    allFrom 20840 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_98 :
    allFrom 20848 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_99 :
    allFrom 20856 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_100 :
    allFrom 20864 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_101 :
    allFrom 20872 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_102 :
    allFrom 20880 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_103 :
    allFrom 20888 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_104 :
    allFrom 20896 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_105 :
    allFrom 20904 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_106 :
    allFrom 20912 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_107 :
    allFrom 20920 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_108 :
    allFrom 20928 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_109 :
    allFrom 20936 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_110 :
    allFrom 20944 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_111 :
    allFrom 20952 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_112 :
    allFrom 20960 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_113 :
    allFrom 20968 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_114 :
    allFrom 20976 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_115 :
    allFrom 20984 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_116 :
    allFrom 20992 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_117 :
    allFrom 21000 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_118 :
    allFrom 21008 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_119 :
    allFrom 21016 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_120 :
    allFrom 21024 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_121 :
    allFrom 21032 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_122 :
    allFrom 21040 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_123 :
    allFrom 21048 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_124 :
    allFrom 21056 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_125 :
    allFrom 21064 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_126 :
    allFrom 21072 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_127 :
    allFrom 21080 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_128 :
    allFrom 21088 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_129 :
    allFrom 21096 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_130 :
    allFrom 21104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_131 :
    allFrom 21112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_132 :
    allFrom 21120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_133 :
    allFrom 21128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_134 :
    allFrom 21136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_135 :
    allFrom 21144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_136 :
    allFrom 21152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_137 :
    allFrom 21160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_138 :
    allFrom 21168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_139 :
    allFrom 21176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_140 :
    allFrom 21184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_141 :
    allFrom 21192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_142 :
    allFrom 21200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_143 :
    allFrom 21208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_144 :
    allFrom 21216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_145 :
    allFrom 21224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_146 :
    allFrom 21232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_147 :
    allFrom 21240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_148 :
    allFrom 21248 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_149 :
    allFrom 21256 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_150 :
    allFrom 21264 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_151 :
    allFrom 21272 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_152 :
    allFrom 21280 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_153 :
    allFrom 21288 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_154 :
    allFrom 21296 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_155 :
    allFrom 21304 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in the `allFrom` range and every direction `k < 8`. -/
theorem transOK_16_156 :
    allFrom 21312 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed `a` in `[20064, 21318)` and every direction `k < 8`. -/
theorem transOK_16 :
    allFrom 20064 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_0
                              transOK_16_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_2
                              transOK_16_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_4
                              transOK_16_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_7
                                  transOK_16_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_9
                              transOK_16_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_12
                                  transOK_16_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_14
                              transOK_16_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_17
                                  transOK_16_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_19
                              transOK_16_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_22
                                  transOK_16_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_24
                              transOK_16_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_27
                                  transOK_16_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_29
                              transOK_16_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_32
                                  transOK_16_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_34
                              transOK_16_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_37
                                  transOK_16_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_39
                              transOK_16_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_41
                              transOK_16_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_43
                              transOK_16_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_46
                                  transOK_16_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_48
                              transOK_16_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_51
                                  transOK_16_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_53
                              transOK_16_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_56
                                  transOK_16_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_58
                              transOK_16_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_61
                                  transOK_16_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_63
                              transOK_16_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_66
                                  transOK_16_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_68
                              transOK_16_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_71
                                  transOK_16_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_73
                              transOK_16_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_76
                                  transOK_16_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_78
                              transOK_16_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_80
                              transOK_16_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_82
                              transOK_16_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_85
                                  transOK_16_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_87
                              transOK_16_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_90
                                  transOK_16_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_92
                              transOK_16_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_95
                                  transOK_16_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_97
                              transOK_16_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_100
                                  transOK_16_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_102
                              transOK_16_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_105
                                  transOK_16_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_107
                              transOK_16_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_110
                                  transOK_16_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_112
                              transOK_16_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_115
                                  transOK_16_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_117
                              transOK_16_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_120
                                  transOK_16_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_122
                              transOK_16_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_125
                                  transOK_16_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_127
                              transOK_16_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_130
                                  transOK_16_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_132
                              transOK_16_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_135
                                  transOK_16_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_137
                              transOK_16_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_140
                                  transOK_16_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_142
                              transOK_16_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_145
                                  transOK_16_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_147
                              transOK_16_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_16_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_16_150
                                  transOK_16_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_16_152
                              transOK_16_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_16_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_16_155
                                  transOK_16_156)))))))

end ClusterAlgebras.CertificateData.E8

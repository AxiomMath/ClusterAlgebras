/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the `E8` certificate, seeds `[10032, 11286)`

The transition check `raw.transOK` of the `E8` certificate holds at every seed in `[10032, 11286)`
and every direction `k < 8`. It is checked by the kernel in pieces of `8` seeds, assembled by
`CertificateCheck.allFrom_add`.

## Main results

* `transOK_8`: the transition check holds at every seed in `[10032, 11286)` and every direction
  `k < 8`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the cost
-- of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel checks of the
-- pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The transition check `raw.transOK` holds at every seed in `[10032, 10040)` and every direction
`k < 8`. -/
theorem transOK_8_0 :
    allFrom 10032 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10040, 10048)` and every direction
`k < 8`. -/
theorem transOK_8_1 :
    allFrom 10040 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10048, 10056)` and every direction
`k < 8`. -/
theorem transOK_8_2 :
    allFrom 10048 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10056, 10064)` and every direction
`k < 8`. -/
theorem transOK_8_3 :
    allFrom 10056 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10064, 10072)` and every direction
`k < 8`. -/
theorem transOK_8_4 :
    allFrom 10064 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10072, 10080)` and every direction
`k < 8`. -/
theorem transOK_8_5 :
    allFrom 10072 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10080, 10088)` and every direction
`k < 8`. -/
theorem transOK_8_6 :
    allFrom 10080 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10088, 10096)` and every direction
`k < 8`. -/
theorem transOK_8_7 :
    allFrom 10088 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10096, 10104)` and every direction
`k < 8`. -/
theorem transOK_8_8 :
    allFrom 10096 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10104, 10112)` and every direction
`k < 8`. -/
theorem transOK_8_9 :
    allFrom 10104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10112, 10120)` and every direction
`k < 8`. -/
theorem transOK_8_10 :
    allFrom 10112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10120, 10128)` and every direction
`k < 8`. -/
theorem transOK_8_11 :
    allFrom 10120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10128, 10136)` and every direction
`k < 8`. -/
theorem transOK_8_12 :
    allFrom 10128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10136, 10144)` and every direction
`k < 8`. -/
theorem transOK_8_13 :
    allFrom 10136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10144, 10152)` and every direction
`k < 8`. -/
theorem transOK_8_14 :
    allFrom 10144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10152, 10160)` and every direction
`k < 8`. -/
theorem transOK_8_15 :
    allFrom 10152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10160, 10168)` and every direction
`k < 8`. -/
theorem transOK_8_16 :
    allFrom 10160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10168, 10176)` and every direction
`k < 8`. -/
theorem transOK_8_17 :
    allFrom 10168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10176, 10184)` and every direction
`k < 8`. -/
theorem transOK_8_18 :
    allFrom 10176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10184, 10192)` and every direction
`k < 8`. -/
theorem transOK_8_19 :
    allFrom 10184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10192, 10200)` and every direction
`k < 8`. -/
theorem transOK_8_20 :
    allFrom 10192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10200, 10208)` and every direction
`k < 8`. -/
theorem transOK_8_21 :
    allFrom 10200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10208, 10216)` and every direction
`k < 8`. -/
theorem transOK_8_22 :
    allFrom 10208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10216, 10224)` and every direction
`k < 8`. -/
theorem transOK_8_23 :
    allFrom 10216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10224, 10232)` and every direction
`k < 8`. -/
theorem transOK_8_24 :
    allFrom 10224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10232, 10240)` and every direction
`k < 8`. -/
theorem transOK_8_25 :
    allFrom 10232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10240, 10248)` and every direction
`k < 8`. -/
theorem transOK_8_26 :
    allFrom 10240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10248, 10256)` and every direction
`k < 8`. -/
theorem transOK_8_27 :
    allFrom 10248 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10256, 10264)` and every direction
`k < 8`. -/
theorem transOK_8_28 :
    allFrom 10256 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10264, 10272)` and every direction
`k < 8`. -/
theorem transOK_8_29 :
    allFrom 10264 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10272, 10280)` and every direction
`k < 8`. -/
theorem transOK_8_30 :
    allFrom 10272 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10280, 10288)` and every direction
`k < 8`. -/
theorem transOK_8_31 :
    allFrom 10280 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10288, 10296)` and every direction
`k < 8`. -/
theorem transOK_8_32 :
    allFrom 10288 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10296, 10304)` and every direction
`k < 8`. -/
theorem transOK_8_33 :
    allFrom 10296 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10304, 10312)` and every direction
`k < 8`. -/
theorem transOK_8_34 :
    allFrom 10304 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10312, 10320)` and every direction
`k < 8`. -/
theorem transOK_8_35 :
    allFrom 10312 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10320, 10328)` and every direction
`k < 8`. -/
theorem transOK_8_36 :
    allFrom 10320 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10328, 10336)` and every direction
`k < 8`. -/
theorem transOK_8_37 :
    allFrom 10328 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10336, 10344)` and every direction
`k < 8`. -/
theorem transOK_8_38 :
    allFrom 10336 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10344, 10352)` and every direction
`k < 8`. -/
theorem transOK_8_39 :
    allFrom 10344 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10352, 10360)` and every direction
`k < 8`. -/
theorem transOK_8_40 :
    allFrom 10352 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10360, 10368)` and every direction
`k < 8`. -/
theorem transOK_8_41 :
    allFrom 10360 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10368, 10376)` and every direction
`k < 8`. -/
theorem transOK_8_42 :
    allFrom 10368 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10376, 10384)` and every direction
`k < 8`. -/
theorem transOK_8_43 :
    allFrom 10376 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10384, 10392)` and every direction
`k < 8`. -/
theorem transOK_8_44 :
    allFrom 10384 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10392, 10400)` and every direction
`k < 8`. -/
theorem transOK_8_45 :
    allFrom 10392 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10400, 10408)` and every direction
`k < 8`. -/
theorem transOK_8_46 :
    allFrom 10400 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10408, 10416)` and every direction
`k < 8`. -/
theorem transOK_8_47 :
    allFrom 10408 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10416, 10424)` and every direction
`k < 8`. -/
theorem transOK_8_48 :
    allFrom 10416 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10424, 10432)` and every direction
`k < 8`. -/
theorem transOK_8_49 :
    allFrom 10424 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10432, 10440)` and every direction
`k < 8`. -/
theorem transOK_8_50 :
    allFrom 10432 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10440, 10448)` and every direction
`k < 8`. -/
theorem transOK_8_51 :
    allFrom 10440 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10448, 10456)` and every direction
`k < 8`. -/
theorem transOK_8_52 :
    allFrom 10448 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10456, 10464)` and every direction
`k < 8`. -/
theorem transOK_8_53 :
    allFrom 10456 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10464, 10472)` and every direction
`k < 8`. -/
theorem transOK_8_54 :
    allFrom 10464 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10472, 10480)` and every direction
`k < 8`. -/
theorem transOK_8_55 :
    allFrom 10472 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10480, 10488)` and every direction
`k < 8`. -/
theorem transOK_8_56 :
    allFrom 10480 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10488, 10496)` and every direction
`k < 8`. -/
theorem transOK_8_57 :
    allFrom 10488 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10496, 10504)` and every direction
`k < 8`. -/
theorem transOK_8_58 :
    allFrom 10496 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10504, 10512)` and every direction
`k < 8`. -/
theorem transOK_8_59 :
    allFrom 10504 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10512, 10520)` and every direction
`k < 8`. -/
theorem transOK_8_60 :
    allFrom 10512 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10520, 10528)` and every direction
`k < 8`. -/
theorem transOK_8_61 :
    allFrom 10520 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10528, 10536)` and every direction
`k < 8`. -/
theorem transOK_8_62 :
    allFrom 10528 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10536, 10544)` and every direction
`k < 8`. -/
theorem transOK_8_63 :
    allFrom 10536 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10544, 10552)` and every direction
`k < 8`. -/
theorem transOK_8_64 :
    allFrom 10544 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10552, 10560)` and every direction
`k < 8`. -/
theorem transOK_8_65 :
    allFrom 10552 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10560, 10568)` and every direction
`k < 8`. -/
theorem transOK_8_66 :
    allFrom 10560 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10568, 10576)` and every direction
`k < 8`. -/
theorem transOK_8_67 :
    allFrom 10568 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10576, 10584)` and every direction
`k < 8`. -/
theorem transOK_8_68 :
    allFrom 10576 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10584, 10592)` and every direction
`k < 8`. -/
theorem transOK_8_69 :
    allFrom 10584 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10592, 10600)` and every direction
`k < 8`. -/
theorem transOK_8_70 :
    allFrom 10592 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10600, 10608)` and every direction
`k < 8`. -/
theorem transOK_8_71 :
    allFrom 10600 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10608, 10616)` and every direction
`k < 8`. -/
theorem transOK_8_72 :
    allFrom 10608 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10616, 10624)` and every direction
`k < 8`. -/
theorem transOK_8_73 :
    allFrom 10616 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10624, 10632)` and every direction
`k < 8`. -/
theorem transOK_8_74 :
    allFrom 10624 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10632, 10640)` and every direction
`k < 8`. -/
theorem transOK_8_75 :
    allFrom 10632 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10640, 10648)` and every direction
`k < 8`. -/
theorem transOK_8_76 :
    allFrom 10640 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10648, 10656)` and every direction
`k < 8`. -/
theorem transOK_8_77 :
    allFrom 10648 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10656, 10664)` and every direction
`k < 8`. -/
theorem transOK_8_78 :
    allFrom 10656 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10664, 10672)` and every direction
`k < 8`. -/
theorem transOK_8_79 :
    allFrom 10664 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10672, 10680)` and every direction
`k < 8`. -/
theorem transOK_8_80 :
    allFrom 10672 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10680, 10688)` and every direction
`k < 8`. -/
theorem transOK_8_81 :
    allFrom 10680 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10688, 10696)` and every direction
`k < 8`. -/
theorem transOK_8_82 :
    allFrom 10688 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10696, 10704)` and every direction
`k < 8`. -/
theorem transOK_8_83 :
    allFrom 10696 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10704, 10712)` and every direction
`k < 8`. -/
theorem transOK_8_84 :
    allFrom 10704 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10712, 10720)` and every direction
`k < 8`. -/
theorem transOK_8_85 :
    allFrom 10712 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10720, 10728)` and every direction
`k < 8`. -/
theorem transOK_8_86 :
    allFrom 10720 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10728, 10736)` and every direction
`k < 8`. -/
theorem transOK_8_87 :
    allFrom 10728 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10736, 10744)` and every direction
`k < 8`. -/
theorem transOK_8_88 :
    allFrom 10736 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10744, 10752)` and every direction
`k < 8`. -/
theorem transOK_8_89 :
    allFrom 10744 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10752, 10760)` and every direction
`k < 8`. -/
theorem transOK_8_90 :
    allFrom 10752 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10760, 10768)` and every direction
`k < 8`. -/
theorem transOK_8_91 :
    allFrom 10760 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10768, 10776)` and every direction
`k < 8`. -/
theorem transOK_8_92 :
    allFrom 10768 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10776, 10784)` and every direction
`k < 8`. -/
theorem transOK_8_93 :
    allFrom 10776 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10784, 10792)` and every direction
`k < 8`. -/
theorem transOK_8_94 :
    allFrom 10784 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10792, 10800)` and every direction
`k < 8`. -/
theorem transOK_8_95 :
    allFrom 10792 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10800, 10808)` and every direction
`k < 8`. -/
theorem transOK_8_96 :
    allFrom 10800 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10808, 10816)` and every direction
`k < 8`. -/
theorem transOK_8_97 :
    allFrom 10808 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10816, 10824)` and every direction
`k < 8`. -/
theorem transOK_8_98 :
    allFrom 10816 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10824, 10832)` and every direction
`k < 8`. -/
theorem transOK_8_99 :
    allFrom 10824 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10832, 10840)` and every direction
`k < 8`. -/
theorem transOK_8_100 :
    allFrom 10832 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10840, 10848)` and every direction
`k < 8`. -/
theorem transOK_8_101 :
    allFrom 10840 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10848, 10856)` and every direction
`k < 8`. -/
theorem transOK_8_102 :
    allFrom 10848 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10856, 10864)` and every direction
`k < 8`. -/
theorem transOK_8_103 :
    allFrom 10856 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10864, 10872)` and every direction
`k < 8`. -/
theorem transOK_8_104 :
    allFrom 10864 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10872, 10880)` and every direction
`k < 8`. -/
theorem transOK_8_105 :
    allFrom 10872 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10880, 10888)` and every direction
`k < 8`. -/
theorem transOK_8_106 :
    allFrom 10880 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10888, 10896)` and every direction
`k < 8`. -/
theorem transOK_8_107 :
    allFrom 10888 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10896, 10904)` and every direction
`k < 8`. -/
theorem transOK_8_108 :
    allFrom 10896 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10904, 10912)` and every direction
`k < 8`. -/
theorem transOK_8_109 :
    allFrom 10904 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10912, 10920)` and every direction
`k < 8`. -/
theorem transOK_8_110 :
    allFrom 10912 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10920, 10928)` and every direction
`k < 8`. -/
theorem transOK_8_111 :
    allFrom 10920 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10928, 10936)` and every direction
`k < 8`. -/
theorem transOK_8_112 :
    allFrom 10928 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10936, 10944)` and every direction
`k < 8`. -/
theorem transOK_8_113 :
    allFrom 10936 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10944, 10952)` and every direction
`k < 8`. -/
theorem transOK_8_114 :
    allFrom 10944 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10952, 10960)` and every direction
`k < 8`. -/
theorem transOK_8_115 :
    allFrom 10952 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10960, 10968)` and every direction
`k < 8`. -/
theorem transOK_8_116 :
    allFrom 10960 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10968, 10976)` and every direction
`k < 8`. -/
theorem transOK_8_117 :
    allFrom 10968 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10976, 10984)` and every direction
`k < 8`. -/
theorem transOK_8_118 :
    allFrom 10976 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10984, 10992)` and every direction
`k < 8`. -/
theorem transOK_8_119 :
    allFrom 10984 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10992, 11000)` and every direction
`k < 8`. -/
theorem transOK_8_120 :
    allFrom 10992 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11000, 11008)` and every direction
`k < 8`. -/
theorem transOK_8_121 :
    allFrom 11000 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11008, 11016)` and every direction
`k < 8`. -/
theorem transOK_8_122 :
    allFrom 11008 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11016, 11024)` and every direction
`k < 8`. -/
theorem transOK_8_123 :
    allFrom 11016 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11024, 11032)` and every direction
`k < 8`. -/
theorem transOK_8_124 :
    allFrom 11024 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11032, 11040)` and every direction
`k < 8`. -/
theorem transOK_8_125 :
    allFrom 11032 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11040, 11048)` and every direction
`k < 8`. -/
theorem transOK_8_126 :
    allFrom 11040 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11048, 11056)` and every direction
`k < 8`. -/
theorem transOK_8_127 :
    allFrom 11048 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11056, 11064)` and every direction
`k < 8`. -/
theorem transOK_8_128 :
    allFrom 11056 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11064, 11072)` and every direction
`k < 8`. -/
theorem transOK_8_129 :
    allFrom 11064 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11072, 11080)` and every direction
`k < 8`. -/
theorem transOK_8_130 :
    allFrom 11072 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11080, 11088)` and every direction
`k < 8`. -/
theorem transOK_8_131 :
    allFrom 11080 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11088, 11096)` and every direction
`k < 8`. -/
theorem transOK_8_132 :
    allFrom 11088 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11096, 11104)` and every direction
`k < 8`. -/
theorem transOK_8_133 :
    allFrom 11096 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11104, 11112)` and every direction
`k < 8`. -/
theorem transOK_8_134 :
    allFrom 11104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11112, 11120)` and every direction
`k < 8`. -/
theorem transOK_8_135 :
    allFrom 11112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11120, 11128)` and every direction
`k < 8`. -/
theorem transOK_8_136 :
    allFrom 11120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11128, 11136)` and every direction
`k < 8`. -/
theorem transOK_8_137 :
    allFrom 11128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11136, 11144)` and every direction
`k < 8`. -/
theorem transOK_8_138 :
    allFrom 11136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11144, 11152)` and every direction
`k < 8`. -/
theorem transOK_8_139 :
    allFrom 11144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11152, 11160)` and every direction
`k < 8`. -/
theorem transOK_8_140 :
    allFrom 11152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11160, 11168)` and every direction
`k < 8`. -/
theorem transOK_8_141 :
    allFrom 11160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11168, 11176)` and every direction
`k < 8`. -/
theorem transOK_8_142 :
    allFrom 11168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11176, 11184)` and every direction
`k < 8`. -/
theorem transOK_8_143 :
    allFrom 11176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11184, 11192)` and every direction
`k < 8`. -/
theorem transOK_8_144 :
    allFrom 11184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11192, 11200)` and every direction
`k < 8`. -/
theorem transOK_8_145 :
    allFrom 11192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11200, 11208)` and every direction
`k < 8`. -/
theorem transOK_8_146 :
    allFrom 11200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11208, 11216)` and every direction
`k < 8`. -/
theorem transOK_8_147 :
    allFrom 11208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11216, 11224)` and every direction
`k < 8`. -/
theorem transOK_8_148 :
    allFrom 11216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11224, 11232)` and every direction
`k < 8`. -/
theorem transOK_8_149 :
    allFrom 11224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11232, 11240)` and every direction
`k < 8`. -/
theorem transOK_8_150 :
    allFrom 11232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11240, 11248)` and every direction
`k < 8`. -/
theorem transOK_8_151 :
    allFrom 11240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11248, 11256)` and every direction
`k < 8`. -/
theorem transOK_8_152 :
    allFrom 11248 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11256, 11264)` and every direction
`k < 8`. -/
theorem transOK_8_153 :
    allFrom 11256 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11264, 11272)` and every direction
`k < 8`. -/
theorem transOK_8_154 :
    allFrom 11264 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11272, 11280)` and every direction
`k < 8`. -/
theorem transOK_8_155 :
    allFrom 11272 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[11280, 11286)` and every direction
`k < 8`. -/
theorem transOK_8_156 :
    allFrom 11280 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed in `[10032, 11286)` and every direction
`k < 8`. -/
theorem transOK_8 :
    allFrom 10032 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_0
                              transOK_8_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_2
                              transOK_8_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_4
                              transOK_8_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_7
                                  transOK_8_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_9
                              transOK_8_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_12
                                  transOK_8_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_14
                              transOK_8_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_17
                                  transOK_8_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_19
                              transOK_8_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_22
                                  transOK_8_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_24
                              transOK_8_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_27
                                  transOK_8_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_29
                              transOK_8_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_32
                                  transOK_8_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_34
                              transOK_8_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_37
                                  transOK_8_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_39
                              transOK_8_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_41
                              transOK_8_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_43
                              transOK_8_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_46
                                  transOK_8_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_48
                              transOK_8_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_51
                                  transOK_8_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_53
                              transOK_8_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_56
                                  transOK_8_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_58
                              transOK_8_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_61
                                  transOK_8_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_63
                              transOK_8_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_66
                                  transOK_8_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_68
                              transOK_8_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_71
                                  transOK_8_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_73
                              transOK_8_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_76
                                  transOK_8_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_78
                              transOK_8_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_80
                              transOK_8_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_82
                              transOK_8_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_85
                                  transOK_8_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_87
                              transOK_8_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_90
                                  transOK_8_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_92
                              transOK_8_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_95
                                  transOK_8_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_97
                              transOK_8_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_100
                                  transOK_8_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_102
                              transOK_8_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_105
                                  transOK_8_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_107
                              transOK_8_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_110
                                  transOK_8_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_112
                              transOK_8_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_115
                                  transOK_8_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_117
                              transOK_8_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_120
                                  transOK_8_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_122
                              transOK_8_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_125
                                  transOK_8_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_127
                              transOK_8_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_130
                                  transOK_8_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_132
                              transOK_8_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_135
                                  transOK_8_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_137
                              transOK_8_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_140
                                  transOK_8_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_142
                              transOK_8_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_145
                                  transOK_8_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_147
                              transOK_8_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_8_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_8_150
                                  transOK_8_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_8_152
                              transOK_8_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_8_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_8_155
                                  transOK_8_156)))))))

end ClusterAlgebras.CertificateData.E8

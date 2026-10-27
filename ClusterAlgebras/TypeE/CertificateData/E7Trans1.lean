/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E7

/-!
# Transitions of the seeds `[2080, 4160)` of the `E7` certificate

The transition check `raw.transOK` of the `E7` certificate holds at every seed with index in
`[2080, 4160)` and in every direction `k < 7`. It is evaluated by the kernel in pieces of `8`
seeds, which are assembled by `CertificateCheck.allFrom_add`.

## Main results

* `transOK_1`: the transition check holds at every seed of `[2080, 4160)`.

## Implementation notes

Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the cost
of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel checks of the
pieces would hold their memory until the end of the file, so it is disabled.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7

open CertificateCheck

set_option Elab.async false

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_0 :
    allFrom 2080 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_1 :
    allFrom 2088 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_2 :
    allFrom 2096 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_3 :
    allFrom 2104 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_4 :
    allFrom 2112 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_5 :
    allFrom 2120 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_6 :
    allFrom 2128 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_7 :
    allFrom 2136 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_8 :
    allFrom 2144 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_9 :
    allFrom 2152 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_10 :
    allFrom 2160 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_11 :
    allFrom 2168 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_12 :
    allFrom 2176 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_13 :
    allFrom 2184 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_14 :
    allFrom 2192 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_15 :
    allFrom 2200 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_16 :
    allFrom 2208 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_17 :
    allFrom 2216 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_18 :
    allFrom 2224 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_19 :
    allFrom 2232 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_20 :
    allFrom 2240 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_21 :
    allFrom 2248 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_22 :
    allFrom 2256 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_23 :
    allFrom 2264 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_24 :
    allFrom 2272 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_25 :
    allFrom 2280 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_26 :
    allFrom 2288 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_27 :
    allFrom 2296 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_28 :
    allFrom 2304 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_29 :
    allFrom 2312 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_30 :
    allFrom 2320 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_31 :
    allFrom 2328 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_32 :
    allFrom 2336 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_33 :
    allFrom 2344 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_34 :
    allFrom 2352 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_35 :
    allFrom 2360 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_36 :
    allFrom 2368 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_37 :
    allFrom 2376 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_38 :
    allFrom 2384 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_39 :
    allFrom 2392 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_40 :
    allFrom 2400 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_41 :
    allFrom 2408 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_42 :
    allFrom 2416 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_43 :
    allFrom 2424 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_44 :
    allFrom 2432 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_45 :
    allFrom 2440 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_46 :
    allFrom 2448 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_47 :
    allFrom 2456 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_48 :
    allFrom 2464 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_49 :
    allFrom 2472 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_50 :
    allFrom 2480 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_51 :
    allFrom 2488 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_52 :
    allFrom 2496 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_53 :
    allFrom 2504 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_54 :
    allFrom 2512 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_55 :
    allFrom 2520 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_56 :
    allFrom 2528 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_57 :
    allFrom 2536 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_58 :
    allFrom 2544 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_59 :
    allFrom 2552 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_60 :
    allFrom 2560 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_61 :
    allFrom 2568 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_62 :
    allFrom 2576 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_63 :
    allFrom 2584 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_64 :
    allFrom 2592 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_65 :
    allFrom 2600 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_66 :
    allFrom 2608 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_67 :
    allFrom 2616 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_68 :
    allFrom 2624 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_69 :
    allFrom 2632 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_70 :
    allFrom 2640 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_71 :
    allFrom 2648 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_72 :
    allFrom 2656 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_73 :
    allFrom 2664 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_74 :
    allFrom 2672 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_75 :
    allFrom 2680 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_76 :
    allFrom 2688 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_77 :
    allFrom 2696 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_78 :
    allFrom 2704 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_79 :
    allFrom 2712 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_80 :
    allFrom 2720 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_81 :
    allFrom 2728 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_82 :
    allFrom 2736 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_83 :
    allFrom 2744 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_84 :
    allFrom 2752 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_85 :
    allFrom 2760 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_86 :
    allFrom 2768 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_87 :
    allFrom 2776 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_88 :
    allFrom 2784 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_89 :
    allFrom 2792 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_90 :
    allFrom 2800 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_91 :
    allFrom 2808 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_92 :
    allFrom 2816 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_93 :
    allFrom 2824 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_94 :
    allFrom 2832 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_95 :
    allFrom 2840 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_96 :
    allFrom 2848 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_97 :
    allFrom 2856 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_98 :
    allFrom 2864 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_99 :
    allFrom 2872 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_100 :
    allFrom 2880 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_101 :
    allFrom 2888 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_102 :
    allFrom 2896 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_103 :
    allFrom 2904 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_104 :
    allFrom 2912 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_105 :
    allFrom 2920 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_106 :
    allFrom 2928 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_107 :
    allFrom 2936 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_108 :
    allFrom 2944 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_109 :
    allFrom 2952 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_110 :
    allFrom 2960 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_111 :
    allFrom 2968 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_112 :
    allFrom 2976 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_113 :
    allFrom 2984 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_114 :
    allFrom 2992 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_115 :
    allFrom 3000 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_116 :
    allFrom 3008 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_117 :
    allFrom 3016 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_118 :
    allFrom 3024 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_119 :
    allFrom 3032 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_120 :
    allFrom 3040 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_121 :
    allFrom 3048 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_122 :
    allFrom 3056 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_123 :
    allFrom 3064 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_124 :
    allFrom 3072 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_125 :
    allFrom 3080 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_126 :
    allFrom 3088 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_127 :
    allFrom 3096 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_128 :
    allFrom 3104 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_129 :
    allFrom 3112 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_130 :
    allFrom 3120 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_131 :
    allFrom 3128 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_132 :
    allFrom 3136 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_133 :
    allFrom 3144 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_134 :
    allFrom 3152 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_135 :
    allFrom 3160 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_136 :
    allFrom 3168 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_137 :
    allFrom 3176 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_138 :
    allFrom 3184 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_139 :
    allFrom 3192 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_140 :
    allFrom 3200 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_141 :
    allFrom 3208 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_142 :
    allFrom 3216 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_143 :
    allFrom 3224 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_144 :
    allFrom 3232 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_145 :
    allFrom 3240 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_146 :
    allFrom 3248 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_147 :
    allFrom 3256 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_148 :
    allFrom 3264 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_149 :
    allFrom 3272 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_150 :
    allFrom 3280 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_151 :
    allFrom 3288 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_152 :
    allFrom 3296 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_153 :
    allFrom 3304 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_154 :
    allFrom 3312 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_155 :
    allFrom 3320 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_156 :
    allFrom 3328 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_157 :
    allFrom 3336 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_158 :
    allFrom 3344 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_159 :
    allFrom 3352 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_160 :
    allFrom 3360 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_161 :
    allFrom 3368 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_162 :
    allFrom 3376 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_163 :
    allFrom 3384 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_164 :
    allFrom 3392 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_165 :
    allFrom 3400 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_166 :
    allFrom 3408 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_167 :
    allFrom 3416 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_168 :
    allFrom 3424 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_169 :
    allFrom 3432 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_170 :
    allFrom 3440 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_171 :
    allFrom 3448 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_172 :
    allFrom 3456 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_173 :
    allFrom 3464 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_174 :
    allFrom 3472 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_175 :
    allFrom 3480 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_176 :
    allFrom 3488 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_177 :
    allFrom 3496 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_178 :
    allFrom 3504 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_179 :
    allFrom 3512 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_180 :
    allFrom 3520 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_181 :
    allFrom 3528 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_182 :
    allFrom 3536 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_183 :
    allFrom 3544 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_184 :
    allFrom 3552 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_185 :
    allFrom 3560 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_186 :
    allFrom 3568 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_187 :
    allFrom 3576 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_188 :
    allFrom 3584 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_189 :
    allFrom 3592 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_190 :
    allFrom 3600 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_191 :
    allFrom 3608 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_192 :
    allFrom 3616 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_193 :
    allFrom 3624 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_194 :
    allFrom 3632 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_195 :
    allFrom 3640 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_196 :
    allFrom 3648 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_197 :
    allFrom 3656 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_198 :
    allFrom 3664 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_199 :
    allFrom 3672 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_200 :
    allFrom 3680 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_201 :
    allFrom 3688 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_202 :
    allFrom 3696 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_203 :
    allFrom 3704 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_204 :
    allFrom 3712 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_205 :
    allFrom 3720 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_206 :
    allFrom 3728 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_207 :
    allFrom 3736 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_208 :
    allFrom 3744 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_209 :
    allFrom 3752 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_210 :
    allFrom 3760 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_211 :
    allFrom 3768 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_212 :
    allFrom 3776 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_213 :
    allFrom 3784 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_214 :
    allFrom 3792 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_215 :
    allFrom 3800 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_216 :
    allFrom 3808 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_217 :
    allFrom 3816 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_218 :
    allFrom 3824 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_219 :
    allFrom 3832 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_220 :
    allFrom 3840 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_221 :
    allFrom 3848 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_222 :
    allFrom 3856 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_223 :
    allFrom 3864 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_224 :
    allFrom 3872 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_225 :
    allFrom 3880 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_226 :
    allFrom 3888 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_227 :
    allFrom 3896 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_228 :
    allFrom 3904 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_229 :
    allFrom 3912 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_230 :
    allFrom 3920 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_231 :
    allFrom 3928 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_232 :
    allFrom 3936 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_233 :
    allFrom 3944 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_234 :
    allFrom 3952 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_235 :
    allFrom 3960 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_236 :
    allFrom 3968 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_237 :
    allFrom 3976 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_238 :
    allFrom 3984 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_239 :
    allFrom 3992 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_240 :
    allFrom 4000 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_241 :
    allFrom 4008 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_242 :
    allFrom 4016 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_243 :
    allFrom 4024 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_244 :
    allFrom 4032 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_245 :
    allFrom 4040 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_246 :
    allFrom 4048 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_247 :
    allFrom 4056 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_248 :
    allFrom 4064 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_249 :
    allFrom 4072 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_250 :
    allFrom 4080 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_251 :
    allFrom 4088 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_252 :
    allFrom 4096 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_253 :
    allFrom 4104 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_254 :
    allFrom 4112 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_255 :
    allFrom 4120 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_256 :
    allFrom 4128 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_257 :
    allFrom 4136 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_258 :
    allFrom 4144 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at each of the eight seeds starting from the given index. -/
theorem transOK_1_259 :
    allFrom 4152 8 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` of the `E7` certificate holds in every direction `k < 7`
at every seed with index in `[2080, 4160)`. -/
theorem transOK_1 :
    allFrom 2080 2080 (fun a => allBelow 7 fun k => raw.transOK 7 7 70 4160 1050 a k) = true :=
  allFrom_add (a := 1040) (b := 1040)
      (allFrom_add (a := 520) (b := 520)
          (allFrom_add (a := 256) (b := 264)
              (allFrom_add (a := 128) (b := 128)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_0
                                  transOK_1_1)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_2
                                  transOK_1_3))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_4
                                  transOK_1_5)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_6
                                  transOK_1_7)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_8
                                  transOK_1_9)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_10
                                  transOK_1_11))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_12
                                  transOK_1_13)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_14
                                  transOK_1_15))))
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_16
                                  transOK_1_17)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_18
                                  transOK_1_19))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_20
                                  transOK_1_21)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_22
                                  transOK_1_23)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_24
                                  transOK_1_25)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_26
                                  transOK_1_27))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_28
                                  transOK_1_29)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_30
                                  transOK_1_31)))))
              (allFrom_add (a := 128) (b := 136)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_32
                                  transOK_1_33)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_34
                                  transOK_1_35))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_36
                                  transOK_1_37)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_38
                                  transOK_1_39)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_40
                                  transOK_1_41)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_42
                                  transOK_1_43))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_44
                                  transOK_1_45)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_46
                                  transOK_1_47))))
                  (allFrom_add (a := 64) (b := 72)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_48
                                  transOK_1_49)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_50
                                  transOK_1_51))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_52
                                  transOK_1_53)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_54
                                  transOK_1_55)))
                      (allFrom_add (a := 32) (b := 40)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_56
                                  transOK_1_57)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_58
                                  transOK_1_59))
                          (allFrom_add (a := 16) (b := 24)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_60
                                  transOK_1_61)
                              (allFrom_add (a := 8) (b := 16)
                                  transOK_1_62
                                  (allFrom_add (a := 8) (b := 8)
                                      transOK_1_63
                                      transOK_1_64)))))))
          (allFrom_add (a := 256) (b := 264)
              (allFrom_add (a := 128) (b := 128)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_65
                                  transOK_1_66)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_67
                                  transOK_1_68))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_69
                                  transOK_1_70)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_71
                                  transOK_1_72)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_73
                                  transOK_1_74)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_75
                                  transOK_1_76))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_77
                                  transOK_1_78)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_79
                                  transOK_1_80))))
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_81
                                  transOK_1_82)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_83
                                  transOK_1_84))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_85
                                  transOK_1_86)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_87
                                  transOK_1_88)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_89
                                  transOK_1_90)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_91
                                  transOK_1_92))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_93
                                  transOK_1_94)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_95
                                  transOK_1_96)))))
              (allFrom_add (a := 128) (b := 136)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_97
                                  transOK_1_98)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_99
                                  transOK_1_100))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_101
                                  transOK_1_102)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_103
                                  transOK_1_104)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_105
                                  transOK_1_106)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_107
                                  transOK_1_108))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_109
                                  transOK_1_110)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_111
                                  transOK_1_112))))
                  (allFrom_add (a := 64) (b := 72)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_113
                                  transOK_1_114)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_115
                                  transOK_1_116))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_117
                                  transOK_1_118)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_119
                                  transOK_1_120)))
                      (allFrom_add (a := 32) (b := 40)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_121
                                  transOK_1_122)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_123
                                  transOK_1_124))
                          (allFrom_add (a := 16) (b := 24)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_125
                                  transOK_1_126)
                              (allFrom_add (a := 8) (b := 16)
                                  transOK_1_127
                                  (allFrom_add (a := 8) (b := 8)
                                      transOK_1_128
                                      transOK_1_129))))))))
      (allFrom_add (a := 520) (b := 520)
          (allFrom_add (a := 256) (b := 264)
              (allFrom_add (a := 128) (b := 128)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_130
                                  transOK_1_131)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_132
                                  transOK_1_133))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_134
                                  transOK_1_135)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_136
                                  transOK_1_137)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_138
                                  transOK_1_139)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_140
                                  transOK_1_141))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_142
                                  transOK_1_143)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_144
                                  transOK_1_145))))
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_146
                                  transOK_1_147)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_148
                                  transOK_1_149))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_150
                                  transOK_1_151)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_152
                                  transOK_1_153)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_154
                                  transOK_1_155)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_156
                                  transOK_1_157))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_158
                                  transOK_1_159)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_160
                                  transOK_1_161)))))
              (allFrom_add (a := 128) (b := 136)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_162
                                  transOK_1_163)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_164
                                  transOK_1_165))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_166
                                  transOK_1_167)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_168
                                  transOK_1_169)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_170
                                  transOK_1_171)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_172
                                  transOK_1_173))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_174
                                  transOK_1_175)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_176
                                  transOK_1_177))))
                  (allFrom_add (a := 64) (b := 72)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_178
                                  transOK_1_179)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_180
                                  transOK_1_181))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_182
                                  transOK_1_183)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_184
                                  transOK_1_185)))
                      (allFrom_add (a := 32) (b := 40)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_186
                                  transOK_1_187)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_188
                                  transOK_1_189))
                          (allFrom_add (a := 16) (b := 24)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_190
                                  transOK_1_191)
                              (allFrom_add (a := 8) (b := 16)
                                  transOK_1_192
                                  (allFrom_add (a := 8) (b := 8)
                                      transOK_1_193
                                      transOK_1_194)))))))
          (allFrom_add (a := 256) (b := 264)
              (allFrom_add (a := 128) (b := 128)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_195
                                  transOK_1_196)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_197
                                  transOK_1_198))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_199
                                  transOK_1_200)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_201
                                  transOK_1_202)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_203
                                  transOK_1_204)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_205
                                  transOK_1_206))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_207
                                  transOK_1_208)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_209
                                  transOK_1_210))))
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_211
                                  transOK_1_212)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_213
                                  transOK_1_214))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_215
                                  transOK_1_216)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_217
                                  transOK_1_218)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_219
                                  transOK_1_220)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_221
                                  transOK_1_222))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_223
                                  transOK_1_224)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_225
                                  transOK_1_226)))))
              (allFrom_add (a := 128) (b := 136)
                  (allFrom_add (a := 64) (b := 64)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_227
                                  transOK_1_228)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_229
                                  transOK_1_230))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_231
                                  transOK_1_232)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_233
                                  transOK_1_234)))
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_235
                                  transOK_1_236)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_237
                                  transOK_1_238))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_239
                                  transOK_1_240)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_241
                                  transOK_1_242))))
                  (allFrom_add (a := 64) (b := 72)
                      (allFrom_add (a := 32) (b := 32)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_243
                                  transOK_1_244)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_245
                                  transOK_1_246))
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_247
                                  transOK_1_248)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_249
                                  transOK_1_250)))
                      (allFrom_add (a := 32) (b := 40)
                          (allFrom_add (a := 16) (b := 16)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_251
                                  transOK_1_252)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_253
                                  transOK_1_254))
                          (allFrom_add (a := 16) (b := 24)
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_1_255
                                  transOK_1_256)
                              (allFrom_add (a := 8) (b := 16)
                                  transOK_1_257
                                  (allFrom_add (a := 8) (b := 8)
                                      transOK_1_258
                                      transOK_1_259))))))))

end ClusterAlgebras.CertificateData.E7

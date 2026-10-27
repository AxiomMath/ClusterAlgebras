/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the `E8` certificate from the seeds `[2508, 3762)`

The kernel checks that the transitions `(a, k)` of the `E8` certificate pass
`CertificateCheck.transOK` for the seeds `2508 ≤ a < 3762` and all `k < 8`, in pieces of `8` seeds
assembled by `CertificateCheck.allFrom_add`.

## Main results

* `transOK_2`: every transition `(a, k)` with `2508 ≤ a < 3762` and `k < 8` passes `transOK`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2508 ≤ a < 2516` and all `k < 8`. -/
theorem transOK_2_0 :
    allFrom 2508 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2516 ≤ a < 2524` and all `k < 8`. -/
theorem transOK_2_1 :
    allFrom 2516 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2524 ≤ a < 2532` and all `k < 8`. -/
theorem transOK_2_2 :
    allFrom 2524 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2532 ≤ a < 2540` and all `k < 8`. -/
theorem transOK_2_3 :
    allFrom 2532 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2540 ≤ a < 2548` and all `k < 8`. -/
theorem transOK_2_4 :
    allFrom 2540 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2548 ≤ a < 2556` and all `k < 8`. -/
theorem transOK_2_5 :
    allFrom 2548 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2556 ≤ a < 2564` and all `k < 8`. -/
theorem transOK_2_6 :
    allFrom 2556 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2564 ≤ a < 2572` and all `k < 8`. -/
theorem transOK_2_7 :
    allFrom 2564 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2572 ≤ a < 2580` and all `k < 8`. -/
theorem transOK_2_8 :
    allFrom 2572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2580 ≤ a < 2588` and all `k < 8`. -/
theorem transOK_2_9 :
    allFrom 2580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2588 ≤ a < 2596` and all `k < 8`. -/
theorem transOK_2_10 :
    allFrom 2588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2596 ≤ a < 2604` and all `k < 8`. -/
theorem transOK_2_11 :
    allFrom 2596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2604 ≤ a < 2612` and all `k < 8`. -/
theorem transOK_2_12 :
    allFrom 2604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2612 ≤ a < 2620` and all `k < 8`. -/
theorem transOK_2_13 :
    allFrom 2612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2620 ≤ a < 2628` and all `k < 8`. -/
theorem transOK_2_14 :
    allFrom 2620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2628 ≤ a < 2636` and all `k < 8`. -/
theorem transOK_2_15 :
    allFrom 2628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2636 ≤ a < 2644` and all `k < 8`. -/
theorem transOK_2_16 :
    allFrom 2636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2644 ≤ a < 2652` and all `k < 8`. -/
theorem transOK_2_17 :
    allFrom 2644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2652 ≤ a < 2660` and all `k < 8`. -/
theorem transOK_2_18 :
    allFrom 2652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2660 ≤ a < 2668` and all `k < 8`. -/
theorem transOK_2_19 :
    allFrom 2660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2668 ≤ a < 2676` and all `k < 8`. -/
theorem transOK_2_20 :
    allFrom 2668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2676 ≤ a < 2684` and all `k < 8`. -/
theorem transOK_2_21 :
    allFrom 2676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2684 ≤ a < 2692` and all `k < 8`. -/
theorem transOK_2_22 :
    allFrom 2684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2692 ≤ a < 2700` and all `k < 8`. -/
theorem transOK_2_23 :
    allFrom 2692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2700 ≤ a < 2708` and all `k < 8`. -/
theorem transOK_2_24 :
    allFrom 2700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2708 ≤ a < 2716` and all `k < 8`. -/
theorem transOK_2_25 :
    allFrom 2708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2716 ≤ a < 2724` and all `k < 8`. -/
theorem transOK_2_26 :
    allFrom 2716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2724 ≤ a < 2732` and all `k < 8`. -/
theorem transOK_2_27 :
    allFrom 2724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2732 ≤ a < 2740` and all `k < 8`. -/
theorem transOK_2_28 :
    allFrom 2732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2740 ≤ a < 2748` and all `k < 8`. -/
theorem transOK_2_29 :
    allFrom 2740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2748 ≤ a < 2756` and all `k < 8`. -/
theorem transOK_2_30 :
    allFrom 2748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2756 ≤ a < 2764` and all `k < 8`. -/
theorem transOK_2_31 :
    allFrom 2756 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2764 ≤ a < 2772` and all `k < 8`. -/
theorem transOK_2_32 :
    allFrom 2764 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2772 ≤ a < 2780` and all `k < 8`. -/
theorem transOK_2_33 :
    allFrom 2772 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2780 ≤ a < 2788` and all `k < 8`. -/
theorem transOK_2_34 :
    allFrom 2780 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2788 ≤ a < 2796` and all `k < 8`. -/
theorem transOK_2_35 :
    allFrom 2788 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2796 ≤ a < 2804` and all `k < 8`. -/
theorem transOK_2_36 :
    allFrom 2796 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2804 ≤ a < 2812` and all `k < 8`. -/
theorem transOK_2_37 :
    allFrom 2804 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2812 ≤ a < 2820` and all `k < 8`. -/
theorem transOK_2_38 :
    allFrom 2812 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2820 ≤ a < 2828` and all `k < 8`. -/
theorem transOK_2_39 :
    allFrom 2820 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2828 ≤ a < 2836` and all `k < 8`. -/
theorem transOK_2_40 :
    allFrom 2828 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2836 ≤ a < 2844` and all `k < 8`. -/
theorem transOK_2_41 :
    allFrom 2836 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2844 ≤ a < 2852` and all `k < 8`. -/
theorem transOK_2_42 :
    allFrom 2844 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2852 ≤ a < 2860` and all `k < 8`. -/
theorem transOK_2_43 :
    allFrom 2852 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2860 ≤ a < 2868` and all `k < 8`. -/
theorem transOK_2_44 :
    allFrom 2860 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2868 ≤ a < 2876` and all `k < 8`. -/
theorem transOK_2_45 :
    allFrom 2868 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2876 ≤ a < 2884` and all `k < 8`. -/
theorem transOK_2_46 :
    allFrom 2876 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2884 ≤ a < 2892` and all `k < 8`. -/
theorem transOK_2_47 :
    allFrom 2884 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2892 ≤ a < 2900` and all `k < 8`. -/
theorem transOK_2_48 :
    allFrom 2892 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2900 ≤ a < 2908` and all `k < 8`. -/
theorem transOK_2_49 :
    allFrom 2900 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2908 ≤ a < 2916` and all `k < 8`. -/
theorem transOK_2_50 :
    allFrom 2908 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2916 ≤ a < 2924` and all `k < 8`. -/
theorem transOK_2_51 :
    allFrom 2916 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2924 ≤ a < 2932` and all `k < 8`. -/
theorem transOK_2_52 :
    allFrom 2924 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2932 ≤ a < 2940` and all `k < 8`. -/
theorem transOK_2_53 :
    allFrom 2932 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2940 ≤ a < 2948` and all `k < 8`. -/
theorem transOK_2_54 :
    allFrom 2940 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2948 ≤ a < 2956` and all `k < 8`. -/
theorem transOK_2_55 :
    allFrom 2948 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2956 ≤ a < 2964` and all `k < 8`. -/
theorem transOK_2_56 :
    allFrom 2956 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2964 ≤ a < 2972` and all `k < 8`. -/
theorem transOK_2_57 :
    allFrom 2964 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2972 ≤ a < 2980` and all `k < 8`. -/
theorem transOK_2_58 :
    allFrom 2972 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2980 ≤ a < 2988` and all `k < 8`. -/
theorem transOK_2_59 :
    allFrom 2980 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2988 ≤ a < 2996` and all `k < 8`. -/
theorem transOK_2_60 :
    allFrom 2988 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2996 ≤ a < 3004` and all `k < 8`. -/
theorem transOK_2_61 :
    allFrom 2996 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3004 ≤ a < 3012` and all `k < 8`. -/
theorem transOK_2_62 :
    allFrom 3004 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3012 ≤ a < 3020` and all `k < 8`. -/
theorem transOK_2_63 :
    allFrom 3012 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3020 ≤ a < 3028` and all `k < 8`. -/
theorem transOK_2_64 :
    allFrom 3020 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3028 ≤ a < 3036` and all `k < 8`. -/
theorem transOK_2_65 :
    allFrom 3028 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3036 ≤ a < 3044` and all `k < 8`. -/
theorem transOK_2_66 :
    allFrom 3036 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3044 ≤ a < 3052` and all `k < 8`. -/
theorem transOK_2_67 :
    allFrom 3044 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3052 ≤ a < 3060` and all `k < 8`. -/
theorem transOK_2_68 :
    allFrom 3052 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3060 ≤ a < 3068` and all `k < 8`. -/
theorem transOK_2_69 :
    allFrom 3060 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3068 ≤ a < 3076` and all `k < 8`. -/
theorem transOK_2_70 :
    allFrom 3068 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3076 ≤ a < 3084` and all `k < 8`. -/
theorem transOK_2_71 :
    allFrom 3076 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3084 ≤ a < 3092` and all `k < 8`. -/
theorem transOK_2_72 :
    allFrom 3084 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3092 ≤ a < 3100` and all `k < 8`. -/
theorem transOK_2_73 :
    allFrom 3092 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3100 ≤ a < 3108` and all `k < 8`. -/
theorem transOK_2_74 :
    allFrom 3100 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3108 ≤ a < 3116` and all `k < 8`. -/
theorem transOK_2_75 :
    allFrom 3108 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3116 ≤ a < 3124` and all `k < 8`. -/
theorem transOK_2_76 :
    allFrom 3116 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3124 ≤ a < 3132` and all `k < 8`. -/
theorem transOK_2_77 :
    allFrom 3124 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3132 ≤ a < 3140` and all `k < 8`. -/
theorem transOK_2_78 :
    allFrom 3132 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3140 ≤ a < 3148` and all `k < 8`. -/
theorem transOK_2_79 :
    allFrom 3140 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3148 ≤ a < 3156` and all `k < 8`. -/
theorem transOK_2_80 :
    allFrom 3148 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3156 ≤ a < 3164` and all `k < 8`. -/
theorem transOK_2_81 :
    allFrom 3156 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3164 ≤ a < 3172` and all `k < 8`. -/
theorem transOK_2_82 :
    allFrom 3164 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3172 ≤ a < 3180` and all `k < 8`. -/
theorem transOK_2_83 :
    allFrom 3172 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3180 ≤ a < 3188` and all `k < 8`. -/
theorem transOK_2_84 :
    allFrom 3180 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3188 ≤ a < 3196` and all `k < 8`. -/
theorem transOK_2_85 :
    allFrom 3188 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3196 ≤ a < 3204` and all `k < 8`. -/
theorem transOK_2_86 :
    allFrom 3196 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3204 ≤ a < 3212` and all `k < 8`. -/
theorem transOK_2_87 :
    allFrom 3204 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3212 ≤ a < 3220` and all `k < 8`. -/
theorem transOK_2_88 :
    allFrom 3212 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3220 ≤ a < 3228` and all `k < 8`. -/
theorem transOK_2_89 :
    allFrom 3220 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3228 ≤ a < 3236` and all `k < 8`. -/
theorem transOK_2_90 :
    allFrom 3228 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3236 ≤ a < 3244` and all `k < 8`. -/
theorem transOK_2_91 :
    allFrom 3236 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3244 ≤ a < 3252` and all `k < 8`. -/
theorem transOK_2_92 :
    allFrom 3244 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3252 ≤ a < 3260` and all `k < 8`. -/
theorem transOK_2_93 :
    allFrom 3252 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3260 ≤ a < 3268` and all `k < 8`. -/
theorem transOK_2_94 :
    allFrom 3260 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3268 ≤ a < 3276` and all `k < 8`. -/
theorem transOK_2_95 :
    allFrom 3268 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3276 ≤ a < 3284` and all `k < 8`. -/
theorem transOK_2_96 :
    allFrom 3276 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3284 ≤ a < 3292` and all `k < 8`. -/
theorem transOK_2_97 :
    allFrom 3284 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3292 ≤ a < 3300` and all `k < 8`. -/
theorem transOK_2_98 :
    allFrom 3292 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3300 ≤ a < 3308` and all `k < 8`. -/
theorem transOK_2_99 :
    allFrom 3300 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3308 ≤ a < 3316` and all `k < 8`. -/
theorem transOK_2_100 :
    allFrom 3308 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3316 ≤ a < 3324` and all `k < 8`. -/
theorem transOK_2_101 :
    allFrom 3316 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3324 ≤ a < 3332` and all `k < 8`. -/
theorem transOK_2_102 :
    allFrom 3324 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3332 ≤ a < 3340` and all `k < 8`. -/
theorem transOK_2_103 :
    allFrom 3332 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3340 ≤ a < 3348` and all `k < 8`. -/
theorem transOK_2_104 :
    allFrom 3340 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3348 ≤ a < 3356` and all `k < 8`. -/
theorem transOK_2_105 :
    allFrom 3348 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3356 ≤ a < 3364` and all `k < 8`. -/
theorem transOK_2_106 :
    allFrom 3356 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3364 ≤ a < 3372` and all `k < 8`. -/
theorem transOK_2_107 :
    allFrom 3364 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3372 ≤ a < 3380` and all `k < 8`. -/
theorem transOK_2_108 :
    allFrom 3372 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3380 ≤ a < 3388` and all `k < 8`. -/
theorem transOK_2_109 :
    allFrom 3380 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3388 ≤ a < 3396` and all `k < 8`. -/
theorem transOK_2_110 :
    allFrom 3388 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3396 ≤ a < 3404` and all `k < 8`. -/
theorem transOK_2_111 :
    allFrom 3396 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3404 ≤ a < 3412` and all `k < 8`. -/
theorem transOK_2_112 :
    allFrom 3404 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3412 ≤ a < 3420` and all `k < 8`. -/
theorem transOK_2_113 :
    allFrom 3412 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3420 ≤ a < 3428` and all `k < 8`. -/
theorem transOK_2_114 :
    allFrom 3420 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3428 ≤ a < 3436` and all `k < 8`. -/
theorem transOK_2_115 :
    allFrom 3428 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3436 ≤ a < 3444` and all `k < 8`. -/
theorem transOK_2_116 :
    allFrom 3436 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3444 ≤ a < 3452` and all `k < 8`. -/
theorem transOK_2_117 :
    allFrom 3444 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3452 ≤ a < 3460` and all `k < 8`. -/
theorem transOK_2_118 :
    allFrom 3452 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3460 ≤ a < 3468` and all `k < 8`. -/
theorem transOK_2_119 :
    allFrom 3460 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3468 ≤ a < 3476` and all `k < 8`. -/
theorem transOK_2_120 :
    allFrom 3468 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3476 ≤ a < 3484` and all `k < 8`. -/
theorem transOK_2_121 :
    allFrom 3476 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3484 ≤ a < 3492` and all `k < 8`. -/
theorem transOK_2_122 :
    allFrom 3484 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3492 ≤ a < 3500` and all `k < 8`. -/
theorem transOK_2_123 :
    allFrom 3492 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3500 ≤ a < 3508` and all `k < 8`. -/
theorem transOK_2_124 :
    allFrom 3500 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3508 ≤ a < 3516` and all `k < 8`. -/
theorem transOK_2_125 :
    allFrom 3508 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3516 ≤ a < 3524` and all `k < 8`. -/
theorem transOK_2_126 :
    allFrom 3516 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3524 ≤ a < 3532` and all `k < 8`. -/
theorem transOK_2_127 :
    allFrom 3524 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3532 ≤ a < 3540` and all `k < 8`. -/
theorem transOK_2_128 :
    allFrom 3532 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3540 ≤ a < 3548` and all `k < 8`. -/
theorem transOK_2_129 :
    allFrom 3540 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3548 ≤ a < 3556` and all `k < 8`. -/
theorem transOK_2_130 :
    allFrom 3548 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3556 ≤ a < 3564` and all `k < 8`. -/
theorem transOK_2_131 :
    allFrom 3556 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3564 ≤ a < 3572` and all `k < 8`. -/
theorem transOK_2_132 :
    allFrom 3564 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3572 ≤ a < 3580` and all `k < 8`. -/
theorem transOK_2_133 :
    allFrom 3572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3580 ≤ a < 3588` and all `k < 8`. -/
theorem transOK_2_134 :
    allFrom 3580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3588 ≤ a < 3596` and all `k < 8`. -/
theorem transOK_2_135 :
    allFrom 3588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3596 ≤ a < 3604` and all `k < 8`. -/
theorem transOK_2_136 :
    allFrom 3596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3604 ≤ a < 3612` and all `k < 8`. -/
theorem transOK_2_137 :
    allFrom 3604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3612 ≤ a < 3620` and all `k < 8`. -/
theorem transOK_2_138 :
    allFrom 3612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3620 ≤ a < 3628` and all `k < 8`. -/
theorem transOK_2_139 :
    allFrom 3620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3628 ≤ a < 3636` and all `k < 8`. -/
theorem transOK_2_140 :
    allFrom 3628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3636 ≤ a < 3644` and all `k < 8`. -/
theorem transOK_2_141 :
    allFrom 3636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3644 ≤ a < 3652` and all `k < 8`. -/
theorem transOK_2_142 :
    allFrom 3644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3652 ≤ a < 3660` and all `k < 8`. -/
theorem transOK_2_143 :
    allFrom 3652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3660 ≤ a < 3668` and all `k < 8`. -/
theorem transOK_2_144 :
    allFrom 3660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3668 ≤ a < 3676` and all `k < 8`. -/
theorem transOK_2_145 :
    allFrom 3668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3676 ≤ a < 3684` and all `k < 8`. -/
theorem transOK_2_146 :
    allFrom 3676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3684 ≤ a < 3692` and all `k < 8`. -/
theorem transOK_2_147 :
    allFrom 3684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3692 ≤ a < 3700` and all `k < 8`. -/
theorem transOK_2_148 :
    allFrom 3692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3700 ≤ a < 3708` and all `k < 8`. -/
theorem transOK_2_149 :
    allFrom 3700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3708 ≤ a < 3716` and all `k < 8`. -/
theorem transOK_2_150 :
    allFrom 3708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3716 ≤ a < 3724` and all `k < 8`. -/
theorem transOK_2_151 :
    allFrom 3716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3724 ≤ a < 3732` and all `k < 8`. -/
theorem transOK_2_152 :
    allFrom 3724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3732 ≤ a < 3740` and all `k < 8`. -/
theorem transOK_2_153 :
    allFrom 3732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3740 ≤ a < 3748` and all `k < 8`. -/
theorem transOK_2_154 :
    allFrom 3740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3748 ≤ a < 3756` and all `k < 8`. -/
theorem transOK_2_155 :
    allFrom 3748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`3756 ≤ a < 3762` and all `k < 8`. -/
theorem transOK_2_156 :
    allFrom 3756 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of the `E8` certificate pass `transOK` for the seeds
`2508 ≤ a < 3762` and all `k < 8`. -/
theorem transOK_2 :
    allFrom 2508 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_0
                              transOK_2_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_2
                              transOK_2_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_4
                              transOK_2_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_7
                                  transOK_2_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_9
                              transOK_2_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_12
                                  transOK_2_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_14
                              transOK_2_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_17
                                  transOK_2_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_19
                              transOK_2_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_22
                                  transOK_2_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_24
                              transOK_2_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_27
                                  transOK_2_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_29
                              transOK_2_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_32
                                  transOK_2_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_34
                              transOK_2_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_37
                                  transOK_2_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_39
                              transOK_2_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_41
                              transOK_2_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_43
                              transOK_2_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_46
                                  transOK_2_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_48
                              transOK_2_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_51
                                  transOK_2_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_53
                              transOK_2_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_56
                                  transOK_2_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_58
                              transOK_2_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_61
                                  transOK_2_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_63
                              transOK_2_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_66
                                  transOK_2_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_68
                              transOK_2_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_71
                                  transOK_2_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_73
                              transOK_2_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_76
                                  transOK_2_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_78
                              transOK_2_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_80
                              transOK_2_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_82
                              transOK_2_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_85
                                  transOK_2_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_87
                              transOK_2_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_90
                                  transOK_2_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_92
                              transOK_2_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_95
                                  transOK_2_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_97
                              transOK_2_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_100
                                  transOK_2_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_102
                              transOK_2_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_105
                                  transOK_2_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_107
                              transOK_2_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_110
                                  transOK_2_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_112
                              transOK_2_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_115
                                  transOK_2_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_117
                              transOK_2_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_120
                                  transOK_2_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_122
                              transOK_2_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_125
                                  transOK_2_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_127
                              transOK_2_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_130
                                  transOK_2_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_132
                              transOK_2_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_135
                                  transOK_2_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_137
                              transOK_2_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_140
                                  transOK_2_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_142
                              transOK_2_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_145
                                  transOK_2_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_147
                              transOK_2_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_2_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_2_150
                                  transOK_2_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_2_152
                              transOK_2_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_2_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_2_155
                                  transOK_2_156)))))))

end ClusterAlgebras.CertificateData.E8

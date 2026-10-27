/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the seeds `16302` to `17555` of the `E8` certificate

The transitions `(a, k)` of `raw` with `16302 ≤ a < 17556` and `k < 8` pass
`CertificateCheck.transOK`, checked by the kernel in pieces of `8` seeds.

## Main results

* `transOK_13`: the transitions of the seeds `16302 ≤ a < 17556` pass `transOK`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The transitions `(a, k)` of `raw` with `16302 ≤ a < 16310` and `k < 8` pass `transOK`. -/
theorem transOK_13_0 :
    allFrom 16302 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16310 ≤ a < 16318` and `k < 8` pass `transOK`. -/
theorem transOK_13_1 :
    allFrom 16310 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16318 ≤ a < 16326` and `k < 8` pass `transOK`. -/
theorem transOK_13_2 :
    allFrom 16318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16326 ≤ a < 16334` and `k < 8` pass `transOK`. -/
theorem transOK_13_3 :
    allFrom 16326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16334 ≤ a < 16342` and `k < 8` pass `transOK`. -/
theorem transOK_13_4 :
    allFrom 16334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16342 ≤ a < 16350` and `k < 8` pass `transOK`. -/
theorem transOK_13_5 :
    allFrom 16342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16350 ≤ a < 16358` and `k < 8` pass `transOK`. -/
theorem transOK_13_6 :
    allFrom 16350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16358 ≤ a < 16366` and `k < 8` pass `transOK`. -/
theorem transOK_13_7 :
    allFrom 16358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16366 ≤ a < 16374` and `k < 8` pass `transOK`. -/
theorem transOK_13_8 :
    allFrom 16366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16374 ≤ a < 16382` and `k < 8` pass `transOK`. -/
theorem transOK_13_9 :
    allFrom 16374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16382 ≤ a < 16390` and `k < 8` pass `transOK`. -/
theorem transOK_13_10 :
    allFrom 16382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16390 ≤ a < 16398` and `k < 8` pass `transOK`. -/
theorem transOK_13_11 :
    allFrom 16390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16398 ≤ a < 16406` and `k < 8` pass `transOK`. -/
theorem transOK_13_12 :
    allFrom 16398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16406 ≤ a < 16414` and `k < 8` pass `transOK`. -/
theorem transOK_13_13 :
    allFrom 16406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16414 ≤ a < 16422` and `k < 8` pass `transOK`. -/
theorem transOK_13_14 :
    allFrom 16414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16422 ≤ a < 16430` and `k < 8` pass `transOK`. -/
theorem transOK_13_15 :
    allFrom 16422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16430 ≤ a < 16438` and `k < 8` pass `transOK`. -/
theorem transOK_13_16 :
    allFrom 16430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16438 ≤ a < 16446` and `k < 8` pass `transOK`. -/
theorem transOK_13_17 :
    allFrom 16438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16446 ≤ a < 16454` and `k < 8` pass `transOK`. -/
theorem transOK_13_18 :
    allFrom 16446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16454 ≤ a < 16462` and `k < 8` pass `transOK`. -/
theorem transOK_13_19 :
    allFrom 16454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16462 ≤ a < 16470` and `k < 8` pass `transOK`. -/
theorem transOK_13_20 :
    allFrom 16462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16470 ≤ a < 16478` and `k < 8` pass `transOK`. -/
theorem transOK_13_21 :
    allFrom 16470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16478 ≤ a < 16486` and `k < 8` pass `transOK`. -/
theorem transOK_13_22 :
    allFrom 16478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16486 ≤ a < 16494` and `k < 8` pass `transOK`. -/
theorem transOK_13_23 :
    allFrom 16486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16494 ≤ a < 16502` and `k < 8` pass `transOK`. -/
theorem transOK_13_24 :
    allFrom 16494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16502 ≤ a < 16510` and `k < 8` pass `transOK`. -/
theorem transOK_13_25 :
    allFrom 16502 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16510 ≤ a < 16518` and `k < 8` pass `transOK`. -/
theorem transOK_13_26 :
    allFrom 16510 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16518 ≤ a < 16526` and `k < 8` pass `transOK`. -/
theorem transOK_13_27 :
    allFrom 16518 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16526 ≤ a < 16534` and `k < 8` pass `transOK`. -/
theorem transOK_13_28 :
    allFrom 16526 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16534 ≤ a < 16542` and `k < 8` pass `transOK`. -/
theorem transOK_13_29 :
    allFrom 16534 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16542 ≤ a < 16550` and `k < 8` pass `transOK`. -/
theorem transOK_13_30 :
    allFrom 16542 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16550 ≤ a < 16558` and `k < 8` pass `transOK`. -/
theorem transOK_13_31 :
    allFrom 16550 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16558 ≤ a < 16566` and `k < 8` pass `transOK`. -/
theorem transOK_13_32 :
    allFrom 16558 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16566 ≤ a < 16574` and `k < 8` pass `transOK`. -/
theorem transOK_13_33 :
    allFrom 16566 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16574 ≤ a < 16582` and `k < 8` pass `transOK`. -/
theorem transOK_13_34 :
    allFrom 16574 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16582 ≤ a < 16590` and `k < 8` pass `transOK`. -/
theorem transOK_13_35 :
    allFrom 16582 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16590 ≤ a < 16598` and `k < 8` pass `transOK`. -/
theorem transOK_13_36 :
    allFrom 16590 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16598 ≤ a < 16606` and `k < 8` pass `transOK`. -/
theorem transOK_13_37 :
    allFrom 16598 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16606 ≤ a < 16614` and `k < 8` pass `transOK`. -/
theorem transOK_13_38 :
    allFrom 16606 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16614 ≤ a < 16622` and `k < 8` pass `transOK`. -/
theorem transOK_13_39 :
    allFrom 16614 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16622 ≤ a < 16630` and `k < 8` pass `transOK`. -/
theorem transOK_13_40 :
    allFrom 16622 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16630 ≤ a < 16638` and `k < 8` pass `transOK`. -/
theorem transOK_13_41 :
    allFrom 16630 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16638 ≤ a < 16646` and `k < 8` pass `transOK`. -/
theorem transOK_13_42 :
    allFrom 16638 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16646 ≤ a < 16654` and `k < 8` pass `transOK`. -/
theorem transOK_13_43 :
    allFrom 16646 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16654 ≤ a < 16662` and `k < 8` pass `transOK`. -/
theorem transOK_13_44 :
    allFrom 16654 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16662 ≤ a < 16670` and `k < 8` pass `transOK`. -/
theorem transOK_13_45 :
    allFrom 16662 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16670 ≤ a < 16678` and `k < 8` pass `transOK`. -/
theorem transOK_13_46 :
    allFrom 16670 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16678 ≤ a < 16686` and `k < 8` pass `transOK`. -/
theorem transOK_13_47 :
    allFrom 16678 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16686 ≤ a < 16694` and `k < 8` pass `transOK`. -/
theorem transOK_13_48 :
    allFrom 16686 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16694 ≤ a < 16702` and `k < 8` pass `transOK`. -/
theorem transOK_13_49 :
    allFrom 16694 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16702 ≤ a < 16710` and `k < 8` pass `transOK`. -/
theorem transOK_13_50 :
    allFrom 16702 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16710 ≤ a < 16718` and `k < 8` pass `transOK`. -/
theorem transOK_13_51 :
    allFrom 16710 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16718 ≤ a < 16726` and `k < 8` pass `transOK`. -/
theorem transOK_13_52 :
    allFrom 16718 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16726 ≤ a < 16734` and `k < 8` pass `transOK`. -/
theorem transOK_13_53 :
    allFrom 16726 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16734 ≤ a < 16742` and `k < 8` pass `transOK`. -/
theorem transOK_13_54 :
    allFrom 16734 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16742 ≤ a < 16750` and `k < 8` pass `transOK`. -/
theorem transOK_13_55 :
    allFrom 16742 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16750 ≤ a < 16758` and `k < 8` pass `transOK`. -/
theorem transOK_13_56 :
    allFrom 16750 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16758 ≤ a < 16766` and `k < 8` pass `transOK`. -/
theorem transOK_13_57 :
    allFrom 16758 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16766 ≤ a < 16774` and `k < 8` pass `transOK`. -/
theorem transOK_13_58 :
    allFrom 16766 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16774 ≤ a < 16782` and `k < 8` pass `transOK`. -/
theorem transOK_13_59 :
    allFrom 16774 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16782 ≤ a < 16790` and `k < 8` pass `transOK`. -/
theorem transOK_13_60 :
    allFrom 16782 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16790 ≤ a < 16798` and `k < 8` pass `transOK`. -/
theorem transOK_13_61 :
    allFrom 16790 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16798 ≤ a < 16806` and `k < 8` pass `transOK`. -/
theorem transOK_13_62 :
    allFrom 16798 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16806 ≤ a < 16814` and `k < 8` pass `transOK`. -/
theorem transOK_13_63 :
    allFrom 16806 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16814 ≤ a < 16822` and `k < 8` pass `transOK`. -/
theorem transOK_13_64 :
    allFrom 16814 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16822 ≤ a < 16830` and `k < 8` pass `transOK`. -/
theorem transOK_13_65 :
    allFrom 16822 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16830 ≤ a < 16838` and `k < 8` pass `transOK`. -/
theorem transOK_13_66 :
    allFrom 16830 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16838 ≤ a < 16846` and `k < 8` pass `transOK`. -/
theorem transOK_13_67 :
    allFrom 16838 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16846 ≤ a < 16854` and `k < 8` pass `transOK`. -/
theorem transOK_13_68 :
    allFrom 16846 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16854 ≤ a < 16862` and `k < 8` pass `transOK`. -/
theorem transOK_13_69 :
    allFrom 16854 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16862 ≤ a < 16870` and `k < 8` pass `transOK`. -/
theorem transOK_13_70 :
    allFrom 16862 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16870 ≤ a < 16878` and `k < 8` pass `transOK`. -/
theorem transOK_13_71 :
    allFrom 16870 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16878 ≤ a < 16886` and `k < 8` pass `transOK`. -/
theorem transOK_13_72 :
    allFrom 16878 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16886 ≤ a < 16894` and `k < 8` pass `transOK`. -/
theorem transOK_13_73 :
    allFrom 16886 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16894 ≤ a < 16902` and `k < 8` pass `transOK`. -/
theorem transOK_13_74 :
    allFrom 16894 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16902 ≤ a < 16910` and `k < 8` pass `transOK`. -/
theorem transOK_13_75 :
    allFrom 16902 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16910 ≤ a < 16918` and `k < 8` pass `transOK`. -/
theorem transOK_13_76 :
    allFrom 16910 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16918 ≤ a < 16926` and `k < 8` pass `transOK`. -/
theorem transOK_13_77 :
    allFrom 16918 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16926 ≤ a < 16934` and `k < 8` pass `transOK`. -/
theorem transOK_13_78 :
    allFrom 16926 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16934 ≤ a < 16942` and `k < 8` pass `transOK`. -/
theorem transOK_13_79 :
    allFrom 16934 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16942 ≤ a < 16950` and `k < 8` pass `transOK`. -/
theorem transOK_13_80 :
    allFrom 16942 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16950 ≤ a < 16958` and `k < 8` pass `transOK`. -/
theorem transOK_13_81 :
    allFrom 16950 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16958 ≤ a < 16966` and `k < 8` pass `transOK`. -/
theorem transOK_13_82 :
    allFrom 16958 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16966 ≤ a < 16974` and `k < 8` pass `transOK`. -/
theorem transOK_13_83 :
    allFrom 16966 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16974 ≤ a < 16982` and `k < 8` pass `transOK`. -/
theorem transOK_13_84 :
    allFrom 16974 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16982 ≤ a < 16990` and `k < 8` pass `transOK`. -/
theorem transOK_13_85 :
    allFrom 16982 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16990 ≤ a < 16998` and `k < 8` pass `transOK`. -/
theorem transOK_13_86 :
    allFrom 16990 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16998 ≤ a < 17006` and `k < 8` pass `transOK`. -/
theorem transOK_13_87 :
    allFrom 16998 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17006 ≤ a < 17014` and `k < 8` pass `transOK`. -/
theorem transOK_13_88 :
    allFrom 17006 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17014 ≤ a < 17022` and `k < 8` pass `transOK`. -/
theorem transOK_13_89 :
    allFrom 17014 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17022 ≤ a < 17030` and `k < 8` pass `transOK`. -/
theorem transOK_13_90 :
    allFrom 17022 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17030 ≤ a < 17038` and `k < 8` pass `transOK`. -/
theorem transOK_13_91 :
    allFrom 17030 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17038 ≤ a < 17046` and `k < 8` pass `transOK`. -/
theorem transOK_13_92 :
    allFrom 17038 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17046 ≤ a < 17054` and `k < 8` pass `transOK`. -/
theorem transOK_13_93 :
    allFrom 17046 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17054 ≤ a < 17062` and `k < 8` pass `transOK`. -/
theorem transOK_13_94 :
    allFrom 17054 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17062 ≤ a < 17070` and `k < 8` pass `transOK`. -/
theorem transOK_13_95 :
    allFrom 17062 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17070 ≤ a < 17078` and `k < 8` pass `transOK`. -/
theorem transOK_13_96 :
    allFrom 17070 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17078 ≤ a < 17086` and `k < 8` pass `transOK`. -/
theorem transOK_13_97 :
    allFrom 17078 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17086 ≤ a < 17094` and `k < 8` pass `transOK`. -/
theorem transOK_13_98 :
    allFrom 17086 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17094 ≤ a < 17102` and `k < 8` pass `transOK`. -/
theorem transOK_13_99 :
    allFrom 17094 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17102 ≤ a < 17110` and `k < 8` pass `transOK`. -/
theorem transOK_13_100 :
    allFrom 17102 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17110 ≤ a < 17118` and `k < 8` pass `transOK`. -/
theorem transOK_13_101 :
    allFrom 17110 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17118 ≤ a < 17126` and `k < 8` pass `transOK`. -/
theorem transOK_13_102 :
    allFrom 17118 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17126 ≤ a < 17134` and `k < 8` pass `transOK`. -/
theorem transOK_13_103 :
    allFrom 17126 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17134 ≤ a < 17142` and `k < 8` pass `transOK`. -/
theorem transOK_13_104 :
    allFrom 17134 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17142 ≤ a < 17150` and `k < 8` pass `transOK`. -/
theorem transOK_13_105 :
    allFrom 17142 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17150 ≤ a < 17158` and `k < 8` pass `transOK`. -/
theorem transOK_13_106 :
    allFrom 17150 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17158 ≤ a < 17166` and `k < 8` pass `transOK`. -/
theorem transOK_13_107 :
    allFrom 17158 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17166 ≤ a < 17174` and `k < 8` pass `transOK`. -/
theorem transOK_13_108 :
    allFrom 17166 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17174 ≤ a < 17182` and `k < 8` pass `transOK`. -/
theorem transOK_13_109 :
    allFrom 17174 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17182 ≤ a < 17190` and `k < 8` pass `transOK`. -/
theorem transOK_13_110 :
    allFrom 17182 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17190 ≤ a < 17198` and `k < 8` pass `transOK`. -/
theorem transOK_13_111 :
    allFrom 17190 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17198 ≤ a < 17206` and `k < 8` pass `transOK`. -/
theorem transOK_13_112 :
    allFrom 17198 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17206 ≤ a < 17214` and `k < 8` pass `transOK`. -/
theorem transOK_13_113 :
    allFrom 17206 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17214 ≤ a < 17222` and `k < 8` pass `transOK`. -/
theorem transOK_13_114 :
    allFrom 17214 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17222 ≤ a < 17230` and `k < 8` pass `transOK`. -/
theorem transOK_13_115 :
    allFrom 17222 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17230 ≤ a < 17238` and `k < 8` pass `transOK`. -/
theorem transOK_13_116 :
    allFrom 17230 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17238 ≤ a < 17246` and `k < 8` pass `transOK`. -/
theorem transOK_13_117 :
    allFrom 17238 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17246 ≤ a < 17254` and `k < 8` pass `transOK`. -/
theorem transOK_13_118 :
    allFrom 17246 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17254 ≤ a < 17262` and `k < 8` pass `transOK`. -/
theorem transOK_13_119 :
    allFrom 17254 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17262 ≤ a < 17270` and `k < 8` pass `transOK`. -/
theorem transOK_13_120 :
    allFrom 17262 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17270 ≤ a < 17278` and `k < 8` pass `transOK`. -/
theorem transOK_13_121 :
    allFrom 17270 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17278 ≤ a < 17286` and `k < 8` pass `transOK`. -/
theorem transOK_13_122 :
    allFrom 17278 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17286 ≤ a < 17294` and `k < 8` pass `transOK`. -/
theorem transOK_13_123 :
    allFrom 17286 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17294 ≤ a < 17302` and `k < 8` pass `transOK`. -/
theorem transOK_13_124 :
    allFrom 17294 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17302 ≤ a < 17310` and `k < 8` pass `transOK`. -/
theorem transOK_13_125 :
    allFrom 17302 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17310 ≤ a < 17318` and `k < 8` pass `transOK`. -/
theorem transOK_13_126 :
    allFrom 17310 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17318 ≤ a < 17326` and `k < 8` pass `transOK`. -/
theorem transOK_13_127 :
    allFrom 17318 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17326 ≤ a < 17334` and `k < 8` pass `transOK`. -/
theorem transOK_13_128 :
    allFrom 17326 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17334 ≤ a < 17342` and `k < 8` pass `transOK`. -/
theorem transOK_13_129 :
    allFrom 17334 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17342 ≤ a < 17350` and `k < 8` pass `transOK`. -/
theorem transOK_13_130 :
    allFrom 17342 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17350 ≤ a < 17358` and `k < 8` pass `transOK`. -/
theorem transOK_13_131 :
    allFrom 17350 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17358 ≤ a < 17366` and `k < 8` pass `transOK`. -/
theorem transOK_13_132 :
    allFrom 17358 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17366 ≤ a < 17374` and `k < 8` pass `transOK`. -/
theorem transOK_13_133 :
    allFrom 17366 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17374 ≤ a < 17382` and `k < 8` pass `transOK`. -/
theorem transOK_13_134 :
    allFrom 17374 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17382 ≤ a < 17390` and `k < 8` pass `transOK`. -/
theorem transOK_13_135 :
    allFrom 17382 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17390 ≤ a < 17398` and `k < 8` pass `transOK`. -/
theorem transOK_13_136 :
    allFrom 17390 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17398 ≤ a < 17406` and `k < 8` pass `transOK`. -/
theorem transOK_13_137 :
    allFrom 17398 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17406 ≤ a < 17414` and `k < 8` pass `transOK`. -/
theorem transOK_13_138 :
    allFrom 17406 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17414 ≤ a < 17422` and `k < 8` pass `transOK`. -/
theorem transOK_13_139 :
    allFrom 17414 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17422 ≤ a < 17430` and `k < 8` pass `transOK`. -/
theorem transOK_13_140 :
    allFrom 17422 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17430 ≤ a < 17438` and `k < 8` pass `transOK`. -/
theorem transOK_13_141 :
    allFrom 17430 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17438 ≤ a < 17446` and `k < 8` pass `transOK`. -/
theorem transOK_13_142 :
    allFrom 17438 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17446 ≤ a < 17454` and `k < 8` pass `transOK`. -/
theorem transOK_13_143 :
    allFrom 17446 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17454 ≤ a < 17462` and `k < 8` pass `transOK`. -/
theorem transOK_13_144 :
    allFrom 17454 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17462 ≤ a < 17470` and `k < 8` pass `transOK`. -/
theorem transOK_13_145 :
    allFrom 17462 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17470 ≤ a < 17478` and `k < 8` pass `transOK`. -/
theorem transOK_13_146 :
    allFrom 17470 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17478 ≤ a < 17486` and `k < 8` pass `transOK`. -/
theorem transOK_13_147 :
    allFrom 17478 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17486 ≤ a < 17494` and `k < 8` pass `transOK`. -/
theorem transOK_13_148 :
    allFrom 17486 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17494 ≤ a < 17502` and `k < 8` pass `transOK`. -/
theorem transOK_13_149 :
    allFrom 17494 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17502 ≤ a < 17510` and `k < 8` pass `transOK`. -/
theorem transOK_13_150 :
    allFrom 17502 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17510 ≤ a < 17518` and `k < 8` pass `transOK`. -/
theorem transOK_13_151 :
    allFrom 17510 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17518 ≤ a < 17526` and `k < 8` pass `transOK`. -/
theorem transOK_13_152 :
    allFrom 17518 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17526 ≤ a < 17534` and `k < 8` pass `transOK`. -/
theorem transOK_13_153 :
    allFrom 17526 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17534 ≤ a < 17542` and `k < 8` pass `transOK`. -/
theorem transOK_13_154 :
    allFrom 17534 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17542 ≤ a < 17550` and `k < 8` pass `transOK`. -/
theorem transOK_13_155 :
    allFrom 17542 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `17550 ≤ a < 17556` and `k < 8` pass `transOK`. -/
theorem transOK_13_156 :
    allFrom 17550 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transitions `(a, k)` of `raw` with `16302 ≤ a < 17556` and `k < 8` pass `transOK`. -/
theorem transOK_13 :
    allFrom 16302 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_0
                              transOK_13_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_2
                              transOK_13_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_4
                              transOK_13_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_7
                                  transOK_13_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_9
                              transOK_13_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_12
                                  transOK_13_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_14
                              transOK_13_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_17
                                  transOK_13_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_19
                              transOK_13_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_22
                                  transOK_13_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_24
                              transOK_13_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_27
                                  transOK_13_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_29
                              transOK_13_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_32
                                  transOK_13_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_34
                              transOK_13_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_37
                                  transOK_13_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_39
                              transOK_13_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_41
                              transOK_13_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_43
                              transOK_13_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_46
                                  transOK_13_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_48
                              transOK_13_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_51
                                  transOK_13_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_53
                              transOK_13_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_56
                                  transOK_13_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_58
                              transOK_13_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_61
                                  transOK_13_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_63
                              transOK_13_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_66
                                  transOK_13_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_68
                              transOK_13_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_71
                                  transOK_13_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_73
                              transOK_13_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_76
                                  transOK_13_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_78
                              transOK_13_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_80
                              transOK_13_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_82
                              transOK_13_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_85
                                  transOK_13_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_87
                              transOK_13_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_90
                                  transOK_13_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_92
                              transOK_13_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_95
                                  transOK_13_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_97
                              transOK_13_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_100
                                  transOK_13_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_102
                              transOK_13_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_105
                                  transOK_13_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_107
                              transOK_13_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_110
                                  transOK_13_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_112
                              transOK_13_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_115
                                  transOK_13_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_117
                              transOK_13_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_120
                                  transOK_13_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_122
                              transOK_13_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_125
                                  transOK_13_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_127
                              transOK_13_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_130
                                  transOK_13_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_132
                              transOK_13_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_135
                                  transOK_13_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_137
                              transOK_13_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_140
                                  transOK_13_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_142
                              transOK_13_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_145
                                  transOK_13_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_147
                              transOK_13_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_13_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_13_150
                                  transOK_13_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_13_152
                              transOK_13_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_13_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_13_155
                                  transOK_13_156)))))))

end ClusterAlgebras.CertificateData.E8

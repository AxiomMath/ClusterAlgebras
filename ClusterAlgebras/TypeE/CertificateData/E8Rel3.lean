/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Exchange relations `[2562, 2864)` of the `E8` certificate

The exchange relations of `raw` with indices in `[2562, 2864)` are checked by kernel evaluation
of `relOKD`, one relation per theorem, assembled by `CertificateCheck.allFrom_add`.

## Main results

* `relOK_3`: the exchange relations of `raw` with indices in `[2562, 2864)` hold.

## Implementation notes

Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the cost
of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel checks of the
pieces would hold their memory until the end of the file, so it is disabled.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

set_option Elab.async false

/-- The exchange relation of `raw` with index `2562` holds, as checked by `relOKD`. -/
theorem relOK_3_0 :
    allFrom 2562 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2563` holds, as checked by `relOKD`. -/
theorem relOK_3_1 :
    allFrom 2563 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2564` holds, as checked by `relOKD`. -/
theorem relOK_3_2 :
    allFrom 2564 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2565` holds, as checked by `relOKD`. -/
theorem relOK_3_3 :
    allFrom 2565 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2566` holds, as checked by `relOKD`. -/
theorem relOK_3_4 :
    allFrom 2566 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2567` holds, as checked by `relOKD`. -/
theorem relOK_3_5 :
    allFrom 2567 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2568` holds, as checked by `relOKD`. -/
theorem relOK_3_6 :
    allFrom 2568 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2569` holds, as checked by `relOKD`. -/
theorem relOK_3_7 :
    allFrom 2569 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2570` holds, as checked by `relOKD`. -/
theorem relOK_3_8 :
    allFrom 2570 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2571` holds, as checked by `relOKD`. -/
theorem relOK_3_9 :
    allFrom 2571 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2572` holds, as checked by `relOKD`. -/
theorem relOK_3_10 :
    allFrom 2572 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2573` holds, as checked by `relOKD`. -/
theorem relOK_3_11 :
    allFrom 2573 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2574` holds, as checked by `relOKD`. -/
theorem relOK_3_12 :
    allFrom 2574 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2575` holds, as checked by `relOKD`. -/
theorem relOK_3_13 :
    allFrom 2575 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2576` holds, as checked by `relOKD`. -/
theorem relOK_3_14 :
    allFrom 2576 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2577` holds, as checked by `relOKD`. -/
theorem relOK_3_15 :
    allFrom 2577 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2578` holds, as checked by `relOKD`. -/
theorem relOK_3_16 :
    allFrom 2578 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2579` holds, as checked by `relOKD`. -/
theorem relOK_3_17 :
    allFrom 2579 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2580` holds, as checked by `relOKD`. -/
theorem relOK_3_18 :
    allFrom 2580 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2581` holds, as checked by `relOKD`. -/
theorem relOK_3_19 :
    allFrom 2581 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2582` holds, as checked by `relOKD`. -/
theorem relOK_3_20 :
    allFrom 2582 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2583` holds, as checked by `relOKD`. -/
theorem relOK_3_21 :
    allFrom 2583 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2584` holds, as checked by `relOKD`. -/
theorem relOK_3_22 :
    allFrom 2584 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2585` holds, as checked by `relOKD`. -/
theorem relOK_3_23 :
    allFrom 2585 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2586` holds, as checked by `relOKD`. -/
theorem relOK_3_24 :
    allFrom 2586 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2587` holds, as checked by `relOKD`. -/
theorem relOK_3_25 :
    allFrom 2587 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2588` holds, as checked by `relOKD`. -/
theorem relOK_3_26 :
    allFrom 2588 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2589` holds, as checked by `relOKD`. -/
theorem relOK_3_27 :
    allFrom 2589 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2590` holds, as checked by `relOKD`. -/
theorem relOK_3_28 :
    allFrom 2590 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2591` holds, as checked by `relOKD`. -/
theorem relOK_3_29 :
    allFrom 2591 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2592` holds, as checked by `relOKD`. -/
theorem relOK_3_30 :
    allFrom 2592 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2593` holds, as checked by `relOKD`. -/
theorem relOK_3_31 :
    allFrom 2593 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2594` holds, as checked by `relOKD`. -/
theorem relOK_3_32 :
    allFrom 2594 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2595` holds, as checked by `relOKD`. -/
theorem relOK_3_33 :
    allFrom 2595 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2596` holds, as checked by `relOKD`. -/
theorem relOK_3_34 :
    allFrom 2596 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2597` holds, as checked by `relOKD`. -/
theorem relOK_3_35 :
    allFrom 2597 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2598` holds, as checked by `relOKD`. -/
theorem relOK_3_36 :
    allFrom 2598 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2599` holds, as checked by `relOKD`. -/
theorem relOK_3_37 :
    allFrom 2599 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2600` holds, as checked by `relOKD`. -/
theorem relOK_3_38 :
    allFrom 2600 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2601` holds, as checked by `relOKD`. -/
theorem relOK_3_39 :
    allFrom 2601 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2602` holds, as checked by `relOKD`. -/
theorem relOK_3_40 :
    allFrom 2602 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2603` holds, as checked by `relOKD`. -/
theorem relOK_3_41 :
    allFrom 2603 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2604` holds, as checked by `relOKD`. -/
theorem relOK_3_42 :
    allFrom 2604 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2605` holds, as checked by `relOKD`. -/
theorem relOK_3_43 :
    allFrom 2605 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2606` holds, as checked by `relOKD`. -/
theorem relOK_3_44 :
    allFrom 2606 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2607` holds, as checked by `relOKD`. -/
theorem relOK_3_45 :
    allFrom 2607 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2608` holds, as checked by `relOKD`. -/
theorem relOK_3_46 :
    allFrom 2608 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2609` holds, as checked by `relOKD`. -/
theorem relOK_3_47 :
    allFrom 2609 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2610` holds, as checked by `relOKD`. -/
theorem relOK_3_48 :
    allFrom 2610 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2611` holds, as checked by `relOKD`. -/
theorem relOK_3_49 :
    allFrom 2611 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2612` holds, as checked by `relOKD`. -/
theorem relOK_3_50 :
    allFrom 2612 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2613` holds, as checked by `relOKD`. -/
theorem relOK_3_51 :
    allFrom 2613 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2614` holds, as checked by `relOKD`. -/
theorem relOK_3_52 :
    allFrom 2614 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2615` holds, as checked by `relOKD`. -/
theorem relOK_3_53 :
    allFrom 2615 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2616` holds, as checked by `relOKD`. -/
theorem relOK_3_54 :
    allFrom 2616 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2617` holds, as checked by `relOKD`. -/
theorem relOK_3_55 :
    allFrom 2617 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2618` holds, as checked by `relOKD`. -/
theorem relOK_3_56 :
    allFrom 2618 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2619` holds, as checked by `relOKD`. -/
theorem relOK_3_57 :
    allFrom 2619 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2620` holds, as checked by `relOKD`. -/
theorem relOK_3_58 :
    allFrom 2620 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2621` holds, as checked by `relOKD`. -/
theorem relOK_3_59 :
    allFrom 2621 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2622` holds, as checked by `relOKD`. -/
theorem relOK_3_60 :
    allFrom 2622 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2623` holds, as checked by `relOKD`. -/
theorem relOK_3_61 :
    allFrom 2623 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2624` holds, as checked by `relOKD`. -/
theorem relOK_3_62 :
    allFrom 2624 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2625` holds, as checked by `relOKD`. -/
theorem relOK_3_63 :
    allFrom 2625 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2626` holds, as checked by `relOKD`. -/
theorem relOK_3_64 :
    allFrom 2626 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2627` holds, as checked by `relOKD`. -/
theorem relOK_3_65 :
    allFrom 2627 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2628` holds, as checked by `relOKD`. -/
theorem relOK_3_66 :
    allFrom 2628 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2629` holds, as checked by `relOKD`. -/
theorem relOK_3_67 :
    allFrom 2629 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2630` holds, as checked by `relOKD`. -/
theorem relOK_3_68 :
    allFrom 2630 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2631` holds, as checked by `relOKD`. -/
theorem relOK_3_69 :
    allFrom 2631 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2632` holds, as checked by `relOKD`. -/
theorem relOK_3_70 :
    allFrom 2632 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2633` holds, as checked by `relOKD`. -/
theorem relOK_3_71 :
    allFrom 2633 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2634` holds, as checked by `relOKD`. -/
theorem relOK_3_72 :
    allFrom 2634 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2635` holds, as checked by `relOKD`. -/
theorem relOK_3_73 :
    allFrom 2635 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2636` holds, as checked by `relOKD`. -/
theorem relOK_3_74 :
    allFrom 2636 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2637` holds, as checked by `relOKD`. -/
theorem relOK_3_75 :
    allFrom 2637 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2638` holds, as checked by `relOKD`. -/
theorem relOK_3_76 :
    allFrom 2638 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2639` holds, as checked by `relOKD`. -/
theorem relOK_3_77 :
    allFrom 2639 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2640` holds, as checked by `relOKD`. -/
theorem relOK_3_78 :
    allFrom 2640 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2641` holds, as checked by `relOKD`. -/
theorem relOK_3_79 :
    allFrom 2641 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2642` holds, as checked by `relOKD`. -/
theorem relOK_3_80 :
    allFrom 2642 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2643` holds, as checked by `relOKD`. -/
theorem relOK_3_81 :
    allFrom 2643 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2644` holds, as checked by `relOKD`. -/
theorem relOK_3_82 :
    allFrom 2644 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2645` holds, as checked by `relOKD`. -/
theorem relOK_3_83 :
    allFrom 2645 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2646` holds, as checked by `relOKD`. -/
theorem relOK_3_84 :
    allFrom 2646 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2647` holds, as checked by `relOKD`. -/
theorem relOK_3_85 :
    allFrom 2647 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2648` holds, as checked by `relOKD`. -/
theorem relOK_3_86 :
    allFrom 2648 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2649` holds, as checked by `relOKD`. -/
theorem relOK_3_87 :
    allFrom 2649 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2650` holds, as checked by `relOKD`. -/
theorem relOK_3_88 :
    allFrom 2650 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2651` holds, as checked by `relOKD`. -/
theorem relOK_3_89 :
    allFrom 2651 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2652` holds, as checked by `relOKD`. -/
theorem relOK_3_90 :
    allFrom 2652 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2653` holds, as checked by `relOKD`. -/
theorem relOK_3_91 :
    allFrom 2653 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2654` holds, as checked by `relOKD`. -/
theorem relOK_3_92 :
    allFrom 2654 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2655` holds, as checked by `relOKD`. -/
theorem relOK_3_93 :
    allFrom 2655 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2656` holds, as checked by `relOKD`. -/
theorem relOK_3_94 :
    allFrom 2656 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2657` holds, as checked by `relOKD`. -/
theorem relOK_3_95 :
    allFrom 2657 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2658` holds, as checked by `relOKD`. -/
theorem relOK_3_96 :
    allFrom 2658 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2659` holds, as checked by `relOKD`. -/
theorem relOK_3_97 :
    allFrom 2659 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2660` holds, as checked by `relOKD`. -/
theorem relOK_3_98 :
    allFrom 2660 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2661` holds, as checked by `relOKD`. -/
theorem relOK_3_99 :
    allFrom 2661 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2662` holds, as checked by `relOKD`. -/
theorem relOK_3_100 :
    allFrom 2662 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2663` holds, as checked by `relOKD`. -/
theorem relOK_3_101 :
    allFrom 2663 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2664` holds, as checked by `relOKD`. -/
theorem relOK_3_102 :
    allFrom 2664 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2665` holds, as checked by `relOKD`. -/
theorem relOK_3_103 :
    allFrom 2665 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2666` holds, as checked by `relOKD`. -/
theorem relOK_3_104 :
    allFrom 2666 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2667` holds, as checked by `relOKD`. -/
theorem relOK_3_105 :
    allFrom 2667 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2668` holds, as checked by `relOKD`. -/
theorem relOK_3_106 :
    allFrom 2668 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2669` holds, as checked by `relOKD`. -/
theorem relOK_3_107 :
    allFrom 2669 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2670` holds, as checked by `relOKD`. -/
theorem relOK_3_108 :
    allFrom 2670 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2671` holds, as checked by `relOKD`. -/
theorem relOK_3_109 :
    allFrom 2671 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2672` holds, as checked by `relOKD`. -/
theorem relOK_3_110 :
    allFrom 2672 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2673` holds, as checked by `relOKD`. -/
theorem relOK_3_111 :
    allFrom 2673 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2674` holds, as checked by `relOKD`. -/
theorem relOK_3_112 :
    allFrom 2674 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2675` holds, as checked by `relOKD`. -/
theorem relOK_3_113 :
    allFrom 2675 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2676` holds, as checked by `relOKD`. -/
theorem relOK_3_114 :
    allFrom 2676 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2677` holds, as checked by `relOKD`. -/
theorem relOK_3_115 :
    allFrom 2677 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2678` holds, as checked by `relOKD`. -/
theorem relOK_3_116 :
    allFrom 2678 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2679` holds, as checked by `relOKD`. -/
theorem relOK_3_117 :
    allFrom 2679 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2680` holds, as checked by `relOKD`. -/
theorem relOK_3_118 :
    allFrom 2680 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2681` holds, as checked by `relOKD`. -/
theorem relOK_3_119 :
    allFrom 2681 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2682` holds, as checked by `relOKD`. -/
theorem relOK_3_120 :
    allFrom 2682 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2683` holds, as checked by `relOKD`. -/
theorem relOK_3_121 :
    allFrom 2683 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2684` holds, as checked by `relOKD`. -/
theorem relOK_3_122 :
    allFrom 2684 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2685` holds, as checked by `relOKD`. -/
theorem relOK_3_123 :
    allFrom 2685 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2686` holds, as checked by `relOKD`. -/
theorem relOK_3_124 :
    allFrom 2686 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2687` holds, as checked by `relOKD`. -/
theorem relOK_3_125 :
    allFrom 2687 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2688` holds, as checked by `relOKD`. -/
theorem relOK_3_126 :
    allFrom 2688 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2689` holds, as checked by `relOKD`. -/
theorem relOK_3_127 :
    allFrom 2689 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2690` holds, as checked by `relOKD`. -/
theorem relOK_3_128 :
    allFrom 2690 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2691` holds, as checked by `relOKD`. -/
theorem relOK_3_129 :
    allFrom 2691 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2692` holds, as checked by `relOKD`. -/
theorem relOK_3_130 :
    allFrom 2692 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2693` holds, as checked by `relOKD`. -/
theorem relOK_3_131 :
    allFrom 2693 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2694` holds, as checked by `relOKD`. -/
theorem relOK_3_132 :
    allFrom 2694 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2695` holds, as checked by `relOKD`. -/
theorem relOK_3_133 :
    allFrom 2695 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2696` holds, as checked by `relOKD`. -/
theorem relOK_3_134 :
    allFrom 2696 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2697` holds, as checked by `relOKD`. -/
theorem relOK_3_135 :
    allFrom 2697 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2698` holds, as checked by `relOKD`. -/
theorem relOK_3_136 :
    allFrom 2698 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2699` holds, as checked by `relOKD`. -/
theorem relOK_3_137 :
    allFrom 2699 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2700` holds, as checked by `relOKD`. -/
theorem relOK_3_138 :
    allFrom 2700 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2701` holds, as checked by `relOKD`. -/
theorem relOK_3_139 :
    allFrom 2701 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2702` holds, as checked by `relOKD`. -/
theorem relOK_3_140 :
    allFrom 2702 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2703` holds, as checked by `relOKD`. -/
theorem relOK_3_141 :
    allFrom 2703 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2704` holds, as checked by `relOKD`. -/
theorem relOK_3_142 :
    allFrom 2704 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2705` holds, as checked by `relOKD`. -/
theorem relOK_3_143 :
    allFrom 2705 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2706` holds, as checked by `relOKD`. -/
theorem relOK_3_144 :
    allFrom 2706 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2707` holds, as checked by `relOKD`. -/
theorem relOK_3_145 :
    allFrom 2707 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2708` holds, as checked by `relOKD`. -/
theorem relOK_3_146 :
    allFrom 2708 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2709` holds, as checked by `relOKD`. -/
theorem relOK_3_147 :
    allFrom 2709 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2710` holds, as checked by `relOKD`. -/
theorem relOK_3_148 :
    allFrom 2710 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2711` holds, as checked by `relOKD`. -/
theorem relOK_3_149 :
    allFrom 2711 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2712` holds, as checked by `relOKD`. -/
theorem relOK_3_150 :
    allFrom 2712 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2713` holds, as checked by `relOKD`. -/
theorem relOK_3_151 :
    allFrom 2713 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2714` holds, as checked by `relOKD`. -/
theorem relOK_3_152 :
    allFrom 2714 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2715` holds, as checked by `relOKD`. -/
theorem relOK_3_153 :
    allFrom 2715 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2716` holds, as checked by `relOKD`. -/
theorem relOK_3_154 :
    allFrom 2716 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2717` holds, as checked by `relOKD`. -/
theorem relOK_3_155 :
    allFrom 2717 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2718` holds, as checked by `relOKD`. -/
theorem relOK_3_156 :
    allFrom 2718 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2719` holds, as checked by `relOKD`. -/
theorem relOK_3_157 :
    allFrom 2719 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2720` holds, as checked by `relOKD`. -/
theorem relOK_3_158 :
    allFrom 2720 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2721` holds, as checked by `relOKD`. -/
theorem relOK_3_159 :
    allFrom 2721 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2722` holds, as checked by `relOKD`. -/
theorem relOK_3_160 :
    allFrom 2722 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2723` holds, as checked by `relOKD`. -/
theorem relOK_3_161 :
    allFrom 2723 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2724` holds, as checked by `relOKD`. -/
theorem relOK_3_162 :
    allFrom 2724 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2725` holds, as checked by `relOKD`. -/
theorem relOK_3_163 :
    allFrom 2725 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2726` holds, as checked by `relOKD`. -/
theorem relOK_3_164 :
    allFrom 2726 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2727` holds, as checked by `relOKD`. -/
theorem relOK_3_165 :
    allFrom 2727 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2728` holds, as checked by `relOKD`. -/
theorem relOK_3_166 :
    allFrom 2728 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2729` holds, as checked by `relOKD`. -/
theorem relOK_3_167 :
    allFrom 2729 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2730` holds, as checked by `relOKD`. -/
theorem relOK_3_168 :
    allFrom 2730 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2731` holds, as checked by `relOKD`. -/
theorem relOK_3_169 :
    allFrom 2731 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2732` holds, as checked by `relOKD`. -/
theorem relOK_3_170 :
    allFrom 2732 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2733` holds, as checked by `relOKD`. -/
theorem relOK_3_171 :
    allFrom 2733 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2734` holds, as checked by `relOKD`. -/
theorem relOK_3_172 :
    allFrom 2734 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2735` holds, as checked by `relOKD`. -/
theorem relOK_3_173 :
    allFrom 2735 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2736` holds, as checked by `relOKD`. -/
theorem relOK_3_174 :
    allFrom 2736 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2737` holds, as checked by `relOKD`. -/
theorem relOK_3_175 :
    allFrom 2737 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2738` holds, as checked by `relOKD`. -/
theorem relOK_3_176 :
    allFrom 2738 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2739` holds, as checked by `relOKD`. -/
theorem relOK_3_177 :
    allFrom 2739 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2740` holds, as checked by `relOKD`. -/
theorem relOK_3_178 :
    allFrom 2740 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2741` holds, as checked by `relOKD`. -/
theorem relOK_3_179 :
    allFrom 2741 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2742` holds, as checked by `relOKD`. -/
theorem relOK_3_180 :
    allFrom 2742 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2743` holds, as checked by `relOKD`. -/
theorem relOK_3_181 :
    allFrom 2743 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2744` holds, as checked by `relOKD`. -/
theorem relOK_3_182 :
    allFrom 2744 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2745` holds, as checked by `relOKD`. -/
theorem relOK_3_183 :
    allFrom 2745 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2746` holds, as checked by `relOKD`. -/
theorem relOK_3_184 :
    allFrom 2746 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2747` holds, as checked by `relOKD`. -/
theorem relOK_3_185 :
    allFrom 2747 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2748` holds, as checked by `relOKD`. -/
theorem relOK_3_186 :
    allFrom 2748 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2749` holds, as checked by `relOKD`. -/
theorem relOK_3_187 :
    allFrom 2749 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2750` holds, as checked by `relOKD`. -/
theorem relOK_3_188 :
    allFrom 2750 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2751` holds, as checked by `relOKD`. -/
theorem relOK_3_189 :
    allFrom 2751 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2752` holds, as checked by `relOKD`. -/
theorem relOK_3_190 :
    allFrom 2752 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2753` holds, as checked by `relOKD`. -/
theorem relOK_3_191 :
    allFrom 2753 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2754` holds, as checked by `relOKD`. -/
theorem relOK_3_192 :
    allFrom 2754 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2755` holds, as checked by `relOKD`. -/
theorem relOK_3_193 :
    allFrom 2755 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2756` holds, as checked by `relOKD`. -/
theorem relOK_3_194 :
    allFrom 2756 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2757` holds, as checked by `relOKD`. -/
theorem relOK_3_195 :
    allFrom 2757 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2758` holds, as checked by `relOKD`. -/
theorem relOK_3_196 :
    allFrom 2758 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2759` holds, as checked by `relOKD`. -/
theorem relOK_3_197 :
    allFrom 2759 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2760` holds, as checked by `relOKD`. -/
theorem relOK_3_198 :
    allFrom 2760 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2761` holds, as checked by `relOKD`. -/
theorem relOK_3_199 :
    allFrom 2761 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2762` holds, as checked by `relOKD`. -/
theorem relOK_3_200 :
    allFrom 2762 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2763` holds, as checked by `relOKD`. -/
theorem relOK_3_201 :
    allFrom 2763 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2764` holds, as checked by `relOKD`. -/
theorem relOK_3_202 :
    allFrom 2764 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2765` holds, as checked by `relOKD`. -/
theorem relOK_3_203 :
    allFrom 2765 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2766` holds, as checked by `relOKD`. -/
theorem relOK_3_204 :
    allFrom 2766 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2767` holds, as checked by `relOKD`. -/
theorem relOK_3_205 :
    allFrom 2767 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2768` holds, as checked by `relOKD`. -/
theorem relOK_3_206 :
    allFrom 2768 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2769` holds, as checked by `relOKD`. -/
theorem relOK_3_207 :
    allFrom 2769 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2770` holds, as checked by `relOKD`. -/
theorem relOK_3_208 :
    allFrom 2770 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2771` holds, as checked by `relOKD`. -/
theorem relOK_3_209 :
    allFrom 2771 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2772` holds, as checked by `relOKD`. -/
theorem relOK_3_210 :
    allFrom 2772 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2773` holds, as checked by `relOKD`. -/
theorem relOK_3_211 :
    allFrom 2773 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2774` holds, as checked by `relOKD`. -/
theorem relOK_3_212 :
    allFrom 2774 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2775` holds, as checked by `relOKD`. -/
theorem relOK_3_213 :
    allFrom 2775 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2776` holds, as checked by `relOKD`. -/
theorem relOK_3_214 :
    allFrom 2776 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2777` holds, as checked by `relOKD`. -/
theorem relOK_3_215 :
    allFrom 2777 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2778` holds, as checked by `relOKD`. -/
theorem relOK_3_216 :
    allFrom 2778 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2779` holds, as checked by `relOKD`. -/
theorem relOK_3_217 :
    allFrom 2779 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2780` holds, as checked by `relOKD`. -/
theorem relOK_3_218 :
    allFrom 2780 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2781` holds, as checked by `relOKD`. -/
theorem relOK_3_219 :
    allFrom 2781 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2782` holds, as checked by `relOKD`. -/
theorem relOK_3_220 :
    allFrom 2782 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2783` holds, as checked by `relOKD`. -/
theorem relOK_3_221 :
    allFrom 2783 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2784` holds, as checked by `relOKD`. -/
theorem relOK_3_222 :
    allFrom 2784 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2785` holds, as checked by `relOKD`. -/
theorem relOK_3_223 :
    allFrom 2785 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2786` holds, as checked by `relOKD`. -/
theorem relOK_3_224 :
    allFrom 2786 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2787` holds, as checked by `relOKD`. -/
theorem relOK_3_225 :
    allFrom 2787 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2788` holds, as checked by `relOKD`. -/
theorem relOK_3_226 :
    allFrom 2788 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2789` holds, as checked by `relOKD`. -/
theorem relOK_3_227 :
    allFrom 2789 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2790` holds, as checked by `relOKD`. -/
theorem relOK_3_228 :
    allFrom 2790 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2791` holds, as checked by `relOKD`. -/
theorem relOK_3_229 :
    allFrom 2791 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2792` holds, as checked by `relOKD`. -/
theorem relOK_3_230 :
    allFrom 2792 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2793` holds, as checked by `relOKD`. -/
theorem relOK_3_231 :
    allFrom 2793 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2794` holds, as checked by `relOKD`. -/
theorem relOK_3_232 :
    allFrom 2794 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2795` holds, as checked by `relOKD`. -/
theorem relOK_3_233 :
    allFrom 2795 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2796` holds, as checked by `relOKD`. -/
theorem relOK_3_234 :
    allFrom 2796 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2797` holds, as checked by `relOKD`. -/
theorem relOK_3_235 :
    allFrom 2797 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2798` holds, as checked by `relOKD`. -/
theorem relOK_3_236 :
    allFrom 2798 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2799` holds, as checked by `relOKD`. -/
theorem relOK_3_237 :
    allFrom 2799 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2800` holds, as checked by `relOKD`. -/
theorem relOK_3_238 :
    allFrom 2800 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2801` holds, as checked by `relOKD`. -/
theorem relOK_3_239 :
    allFrom 2801 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2802` holds, as checked by `relOKD`. -/
theorem relOK_3_240 :
    allFrom 2802 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2803` holds, as checked by `relOKD`. -/
theorem relOK_3_241 :
    allFrom 2803 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2804` holds, as checked by `relOKD`. -/
theorem relOK_3_242 :
    allFrom 2804 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2805` holds, as checked by `relOKD`. -/
theorem relOK_3_243 :
    allFrom 2805 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2806` holds, as checked by `relOKD`. -/
theorem relOK_3_244 :
    allFrom 2806 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2807` holds, as checked by `relOKD`. -/
theorem relOK_3_245 :
    allFrom 2807 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2808` holds, as checked by `relOKD`. -/
theorem relOK_3_246 :
    allFrom 2808 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2809` holds, as checked by `relOKD`. -/
theorem relOK_3_247 :
    allFrom 2809 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2810` holds, as checked by `relOKD`. -/
theorem relOK_3_248 :
    allFrom 2810 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2811` holds, as checked by `relOKD`. -/
theorem relOK_3_249 :
    allFrom 2811 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2812` holds, as checked by `relOKD`. -/
theorem relOK_3_250 :
    allFrom 2812 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2813` holds, as checked by `relOKD`. -/
theorem relOK_3_251 :
    allFrom 2813 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2814` holds, as checked by `relOKD`. -/
theorem relOK_3_252 :
    allFrom 2814 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2815` holds, as checked by `relOKD`. -/
theorem relOK_3_253 :
    allFrom 2815 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2816` holds, as checked by `relOKD`. -/
theorem relOK_3_254 :
    allFrom 2816 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2817` holds, as checked by `relOKD`. -/
theorem relOK_3_255 :
    allFrom 2817 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2818` holds, as checked by `relOKD`. -/
theorem relOK_3_256 :
    allFrom 2818 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2819` holds, as checked by `relOKD`. -/
theorem relOK_3_257 :
    allFrom 2819 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2820` holds, as checked by `relOKD`. -/
theorem relOK_3_258 :
    allFrom 2820 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2821` holds, as checked by `relOKD`. -/
theorem relOK_3_259 :
    allFrom 2821 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2822` holds, as checked by `relOKD`. -/
theorem relOK_3_260 :
    allFrom 2822 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2823` holds, as checked by `relOKD`. -/
theorem relOK_3_261 :
    allFrom 2823 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2824` holds, as checked by `relOKD`. -/
theorem relOK_3_262 :
    allFrom 2824 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2825` holds, as checked by `relOKD`. -/
theorem relOK_3_263 :
    allFrom 2825 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2826` holds, as checked by `relOKD`. -/
theorem relOK_3_264 :
    allFrom 2826 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2827` holds, as checked by `relOKD`. -/
theorem relOK_3_265 :
    allFrom 2827 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2828` holds, as checked by `relOKD`. -/
theorem relOK_3_266 :
    allFrom 2828 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2829` holds, as checked by `relOKD`. -/
theorem relOK_3_267 :
    allFrom 2829 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2830` holds, as checked by `relOKD`. -/
theorem relOK_3_268 :
    allFrom 2830 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2831` holds, as checked by `relOKD`. -/
theorem relOK_3_269 :
    allFrom 2831 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2832` holds, as checked by `relOKD`. -/
theorem relOK_3_270 :
    allFrom 2832 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2833` holds, as checked by `relOKD`. -/
theorem relOK_3_271 :
    allFrom 2833 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2834` holds, as checked by `relOKD`. -/
theorem relOK_3_272 :
    allFrom 2834 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2835` holds, as checked by `relOKD`. -/
theorem relOK_3_273 :
    allFrom 2835 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2836` holds, as checked by `relOKD`. -/
theorem relOK_3_274 :
    allFrom 2836 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2837` holds, as checked by `relOKD`. -/
theorem relOK_3_275 :
    allFrom 2837 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2838` holds, as checked by `relOKD`. -/
theorem relOK_3_276 :
    allFrom 2838 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2839` holds, as checked by `relOKD`. -/
theorem relOK_3_277 :
    allFrom 2839 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2840` holds, as checked by `relOKD`. -/
theorem relOK_3_278 :
    allFrom 2840 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2841` holds, as checked by `relOKD`. -/
theorem relOK_3_279 :
    allFrom 2841 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2842` holds, as checked by `relOKD`. -/
theorem relOK_3_280 :
    allFrom 2842 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2843` holds, as checked by `relOKD`. -/
theorem relOK_3_281 :
    allFrom 2843 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2844` holds, as checked by `relOKD`. -/
theorem relOK_3_282 :
    allFrom 2844 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2845` holds, as checked by `relOKD`. -/
theorem relOK_3_283 :
    allFrom 2845 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2846` holds, as checked by `relOKD`. -/
theorem relOK_3_284 :
    allFrom 2846 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2847` holds, as checked by `relOKD`. -/
theorem relOK_3_285 :
    allFrom 2847 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2848` holds, as checked by `relOKD`. -/
theorem relOK_3_286 :
    allFrom 2848 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2849` holds, as checked by `relOKD`. -/
theorem relOK_3_287 :
    allFrom 2849 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2850` holds, as checked by `relOKD`. -/
theorem relOK_3_288 :
    allFrom 2850 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2851` holds, as checked by `relOKD`. -/
theorem relOK_3_289 :
    allFrom 2851 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2852` holds, as checked by `relOKD`. -/
theorem relOK_3_290 :
    allFrom 2852 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2853` holds, as checked by `relOKD`. -/
theorem relOK_3_291 :
    allFrom 2853 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2854` holds, as checked by `relOKD`. -/
theorem relOK_3_292 :
    allFrom 2854 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2855` holds, as checked by `relOKD`. -/
theorem relOK_3_293 :
    allFrom 2855 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2856` holds, as checked by `relOKD`. -/
theorem relOK_3_294 :
    allFrom 2856 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2857` holds, as checked by `relOKD`. -/
theorem relOK_3_295 :
    allFrom 2857 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2858` holds, as checked by `relOKD`. -/
theorem relOK_3_296 :
    allFrom 2858 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2859` holds, as checked by `relOKD`. -/
theorem relOK_3_297 :
    allFrom 2859 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2860` holds, as checked by `relOKD`. -/
theorem relOK_3_298 :
    allFrom 2860 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2861` holds, as checked by `relOKD`. -/
theorem relOK_3_299 :
    allFrom 2861 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2862` holds, as checked by `relOKD`. -/
theorem relOK_3_300 :
    allFrom 2862 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of `raw` with index `2863` holds, as checked by `relOKD`. -/
theorem relOK_3_301 :
    allFrom 2863 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2562, 2864)` hold, as checked by
`relOKD`. -/
theorem relOK_3 :
    allFrom 2562 302
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true :=
  allFrom_add (a := 151) (b := 151)
      (allFrom_add (a := 75) (b := 76)
          (allFrom_add (a := 37) (b := 38)
              (allFrom_add (a := 18) (b := 19)
                  (allFrom_add (a := 9) (b := 9)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_0
                                  relOK_3_1)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_2
                                  relOK_3_3))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_4
                                  relOK_3_5)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_6
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_7
                                      relOK_3_8))))
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_9
                                  relOK_3_10)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_11
                                  relOK_3_12))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_13
                                  relOK_3_14)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_15
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_16
                                      relOK_3_17)))))
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_18
                                  relOK_3_19)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_20
                                  relOK_3_21))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_22
                                  relOK_3_23)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_24
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_25
                                      relOK_3_26))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_27
                                  relOK_3_28)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_29
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_30
                                      relOK_3_31)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_32
                                  relOK_3_33)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_34
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_35
                                      relOK_3_36))))))
              (allFrom_add (a := 19) (b := 19)
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_37
                                  relOK_3_38)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_39
                                  relOK_3_40))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_41
                                  relOK_3_42)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_43
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_44
                                      relOK_3_45))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_46
                                  relOK_3_47)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_48
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_49
                                      relOK_3_50)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_51
                                  relOK_3_52)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_53
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_54
                                      relOK_3_55)))))
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_56
                                  relOK_3_57)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_58
                                  relOK_3_59))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_60
                                  relOK_3_61)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_62
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_63
                                      relOK_3_64))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_65
                                  relOK_3_66)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_67
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_68
                                      relOK_3_69)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_70
                                  relOK_3_71)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_72
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_73
                                      relOK_3_74)))))))
          (allFrom_add (a := 38) (b := 38)
              (allFrom_add (a := 19) (b := 19)
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_75
                                  relOK_3_76)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_77
                                  relOK_3_78))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_79
                                  relOK_3_80)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_81
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_82
                                      relOK_3_83))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_84
                                  relOK_3_85)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_86
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_87
                                      relOK_3_88)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_89
                                  relOK_3_90)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_91
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_92
                                      relOK_3_93)))))
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_94
                                  relOK_3_95)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_96
                                  relOK_3_97))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_98
                                  relOK_3_99)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_100
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_101
                                      relOK_3_102))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_103
                                  relOK_3_104)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_105
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_106
                                      relOK_3_107)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_108
                                  relOK_3_109)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_110
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_111
                                      relOK_3_112))))))
              (allFrom_add (a := 19) (b := 19)
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_113
                                  relOK_3_114)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_115
                                  relOK_3_116))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_117
                                  relOK_3_118)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_119
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_120
                                      relOK_3_121))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_122
                                  relOK_3_123)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_124
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_125
                                      relOK_3_126)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_127
                                  relOK_3_128)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_129
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_130
                                      relOK_3_131)))))
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_132
                                  relOK_3_133)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_134
                                  relOK_3_135))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_136
                                  relOK_3_137)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_138
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_139
                                      relOK_3_140))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_141
                                  relOK_3_142)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_143
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_144
                                      relOK_3_145)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_146
                                  relOK_3_147)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_148
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_149
                                      relOK_3_150))))))))
      (allFrom_add (a := 75) (b := 76)
          (allFrom_add (a := 37) (b := 38)
              (allFrom_add (a := 18) (b := 19)
                  (allFrom_add (a := 9) (b := 9)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_151
                                  relOK_3_152)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_153
                                  relOK_3_154))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_155
                                  relOK_3_156)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_157
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_158
                                      relOK_3_159))))
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_160
                                  relOK_3_161)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_162
                                  relOK_3_163))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_164
                                  relOK_3_165)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_166
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_167
                                      relOK_3_168)))))
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_169
                                  relOK_3_170)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_171
                                  relOK_3_172))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_173
                                  relOK_3_174)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_175
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_176
                                      relOK_3_177))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_178
                                  relOK_3_179)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_180
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_181
                                      relOK_3_182)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_183
                                  relOK_3_184)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_185
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_186
                                      relOK_3_187))))))
              (allFrom_add (a := 19) (b := 19)
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_188
                                  relOK_3_189)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_190
                                  relOK_3_191))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_192
                                  relOK_3_193)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_194
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_195
                                      relOK_3_196))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_197
                                  relOK_3_198)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_199
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_200
                                      relOK_3_201)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_202
                                  relOK_3_203)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_204
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_205
                                      relOK_3_206)))))
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_207
                                  relOK_3_208)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_209
                                  relOK_3_210))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_211
                                  relOK_3_212)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_213
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_214
                                      relOK_3_215))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_216
                                  relOK_3_217)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_218
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_219
                                      relOK_3_220)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_221
                                  relOK_3_222)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_223
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_224
                                      relOK_3_225)))))))
          (allFrom_add (a := 38) (b := 38)
              (allFrom_add (a := 19) (b := 19)
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_226
                                  relOK_3_227)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_228
                                  relOK_3_229))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_230
                                  relOK_3_231)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_232
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_233
                                      relOK_3_234))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_235
                                  relOK_3_236)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_237
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_238
                                      relOK_3_239)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_240
                                  relOK_3_241)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_242
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_243
                                      relOK_3_244)))))
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_245
                                  relOK_3_246)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_247
                                  relOK_3_248))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_249
                                  relOK_3_250)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_251
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_252
                                      relOK_3_253))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_254
                                  relOK_3_255)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_256
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_257
                                      relOK_3_258)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_259
                                  relOK_3_260)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_261
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_262
                                      relOK_3_263))))))
              (allFrom_add (a := 19) (b := 19)
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_264
                                  relOK_3_265)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_266
                                  relOK_3_267))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_268
                                  relOK_3_269)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_270
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_271
                                      relOK_3_272))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_273
                                  relOK_3_274)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_275
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_276
                                      relOK_3_277)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_278
                                  relOK_3_279)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_280
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_281
                                      relOK_3_282)))))
                  (allFrom_add (a := 9) (b := 10)
                      (allFrom_add (a := 4) (b := 5)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_283
                                  relOK_3_284)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_285
                                  relOK_3_286))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_287
                                  relOK_3_288)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_289
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_290
                                      relOK_3_291))))
                      (allFrom_add (a := 5) (b := 5)
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_292
                                  relOK_3_293)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_294
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_295
                                      relOK_3_296)))
                          (allFrom_add (a := 2) (b := 3)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_3_297
                                  relOK_3_298)
                              (allFrom_add (a := 1) (b := 2)
                                  relOK_3_299
                                  (allFrom_add (a := 1) (b := 1)
                                      relOK_3_300
                                      relOK_3_301))))))))

end ClusterAlgebras.CertificateData.E8

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of seeds `17556` to `18809` of the `E8` certificate

The kernel checks `transOK` at every transition `(a, k)` of the `E8` certificate with
`17556 ≤ a < 18810`, in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add`.

## Main results

* `transOK_14`: `transOK` holds at every transition `(a, k)` with `17556 ≤ a < 18810`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17556 ≤ a < 17564`. -/
theorem transOK_14_0 :
    allFrom 17556 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17564 ≤ a < 17572`. -/
theorem transOK_14_1 :
    allFrom 17564 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17572 ≤ a < 17580`. -/
theorem transOK_14_2 :
    allFrom 17572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17580 ≤ a < 17588`. -/
theorem transOK_14_3 :
    allFrom 17580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17588 ≤ a < 17596`. -/
theorem transOK_14_4 :
    allFrom 17588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17596 ≤ a < 17604`. -/
theorem transOK_14_5 :
    allFrom 17596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17604 ≤ a < 17612`. -/
theorem transOK_14_6 :
    allFrom 17604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17612 ≤ a < 17620`. -/
theorem transOK_14_7 :
    allFrom 17612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17620 ≤ a < 17628`. -/
theorem transOK_14_8 :
    allFrom 17620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17628 ≤ a < 17636`. -/
theorem transOK_14_9 :
    allFrom 17628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17636 ≤ a < 17644`. -/
theorem transOK_14_10 :
    allFrom 17636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17644 ≤ a < 17652`. -/
theorem transOK_14_11 :
    allFrom 17644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17652 ≤ a < 17660`. -/
theorem transOK_14_12 :
    allFrom 17652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17660 ≤ a < 17668`. -/
theorem transOK_14_13 :
    allFrom 17660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17668 ≤ a < 17676`. -/
theorem transOK_14_14 :
    allFrom 17668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17676 ≤ a < 17684`. -/
theorem transOK_14_15 :
    allFrom 17676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17684 ≤ a < 17692`. -/
theorem transOK_14_16 :
    allFrom 17684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17692 ≤ a < 17700`. -/
theorem transOK_14_17 :
    allFrom 17692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17700 ≤ a < 17708`. -/
theorem transOK_14_18 :
    allFrom 17700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17708 ≤ a < 17716`. -/
theorem transOK_14_19 :
    allFrom 17708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17716 ≤ a < 17724`. -/
theorem transOK_14_20 :
    allFrom 17716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17724 ≤ a < 17732`. -/
theorem transOK_14_21 :
    allFrom 17724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17732 ≤ a < 17740`. -/
theorem transOK_14_22 :
    allFrom 17732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17740 ≤ a < 17748`. -/
theorem transOK_14_23 :
    allFrom 17740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17748 ≤ a < 17756`. -/
theorem transOK_14_24 :
    allFrom 17748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17756 ≤ a < 17764`. -/
theorem transOK_14_25 :
    allFrom 17756 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17764 ≤ a < 17772`. -/
theorem transOK_14_26 :
    allFrom 17764 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17772 ≤ a < 17780`. -/
theorem transOK_14_27 :
    allFrom 17772 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17780 ≤ a < 17788`. -/
theorem transOK_14_28 :
    allFrom 17780 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17788 ≤ a < 17796`. -/
theorem transOK_14_29 :
    allFrom 17788 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17796 ≤ a < 17804`. -/
theorem transOK_14_30 :
    allFrom 17796 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17804 ≤ a < 17812`. -/
theorem transOK_14_31 :
    allFrom 17804 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17812 ≤ a < 17820`. -/
theorem transOK_14_32 :
    allFrom 17812 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17820 ≤ a < 17828`. -/
theorem transOK_14_33 :
    allFrom 17820 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17828 ≤ a < 17836`. -/
theorem transOK_14_34 :
    allFrom 17828 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17836 ≤ a < 17844`. -/
theorem transOK_14_35 :
    allFrom 17836 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17844 ≤ a < 17852`. -/
theorem transOK_14_36 :
    allFrom 17844 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17852 ≤ a < 17860`. -/
theorem transOK_14_37 :
    allFrom 17852 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17860 ≤ a < 17868`. -/
theorem transOK_14_38 :
    allFrom 17860 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17868 ≤ a < 17876`. -/
theorem transOK_14_39 :
    allFrom 17868 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17876 ≤ a < 17884`. -/
theorem transOK_14_40 :
    allFrom 17876 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17884 ≤ a < 17892`. -/
theorem transOK_14_41 :
    allFrom 17884 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17892 ≤ a < 17900`. -/
theorem transOK_14_42 :
    allFrom 17892 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17900 ≤ a < 17908`. -/
theorem transOK_14_43 :
    allFrom 17900 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17908 ≤ a < 17916`. -/
theorem transOK_14_44 :
    allFrom 17908 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17916 ≤ a < 17924`. -/
theorem transOK_14_45 :
    allFrom 17916 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17924 ≤ a < 17932`. -/
theorem transOK_14_46 :
    allFrom 17924 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17932 ≤ a < 17940`. -/
theorem transOK_14_47 :
    allFrom 17932 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17940 ≤ a < 17948`. -/
theorem transOK_14_48 :
    allFrom 17940 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17948 ≤ a < 17956`. -/
theorem transOK_14_49 :
    allFrom 17948 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17956 ≤ a < 17964`. -/
theorem transOK_14_50 :
    allFrom 17956 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17964 ≤ a < 17972`. -/
theorem transOK_14_51 :
    allFrom 17964 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17972 ≤ a < 17980`. -/
theorem transOK_14_52 :
    allFrom 17972 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17980 ≤ a < 17988`. -/
theorem transOK_14_53 :
    allFrom 17980 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17988 ≤ a < 17996`. -/
theorem transOK_14_54 :
    allFrom 17988 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17996 ≤ a < 18004`. -/
theorem transOK_14_55 :
    allFrom 17996 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18004 ≤ a < 18012`. -/
theorem transOK_14_56 :
    allFrom 18004 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18012 ≤ a < 18020`. -/
theorem transOK_14_57 :
    allFrom 18012 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18020 ≤ a < 18028`. -/
theorem transOK_14_58 :
    allFrom 18020 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18028 ≤ a < 18036`. -/
theorem transOK_14_59 :
    allFrom 18028 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18036 ≤ a < 18044`. -/
theorem transOK_14_60 :
    allFrom 18036 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18044 ≤ a < 18052`. -/
theorem transOK_14_61 :
    allFrom 18044 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18052 ≤ a < 18060`. -/
theorem transOK_14_62 :
    allFrom 18052 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18060 ≤ a < 18068`. -/
theorem transOK_14_63 :
    allFrom 18060 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18068 ≤ a < 18076`. -/
theorem transOK_14_64 :
    allFrom 18068 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18076 ≤ a < 18084`. -/
theorem transOK_14_65 :
    allFrom 18076 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18084 ≤ a < 18092`. -/
theorem transOK_14_66 :
    allFrom 18084 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18092 ≤ a < 18100`. -/
theorem transOK_14_67 :
    allFrom 18092 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18100 ≤ a < 18108`. -/
theorem transOK_14_68 :
    allFrom 18100 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18108 ≤ a < 18116`. -/
theorem transOK_14_69 :
    allFrom 18108 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18116 ≤ a < 18124`. -/
theorem transOK_14_70 :
    allFrom 18116 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18124 ≤ a < 18132`. -/
theorem transOK_14_71 :
    allFrom 18124 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18132 ≤ a < 18140`. -/
theorem transOK_14_72 :
    allFrom 18132 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18140 ≤ a < 18148`. -/
theorem transOK_14_73 :
    allFrom 18140 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18148 ≤ a < 18156`. -/
theorem transOK_14_74 :
    allFrom 18148 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18156 ≤ a < 18164`. -/
theorem transOK_14_75 :
    allFrom 18156 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18164 ≤ a < 18172`. -/
theorem transOK_14_76 :
    allFrom 18164 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18172 ≤ a < 18180`. -/
theorem transOK_14_77 :
    allFrom 18172 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18180 ≤ a < 18188`. -/
theorem transOK_14_78 :
    allFrom 18180 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18188 ≤ a < 18196`. -/
theorem transOK_14_79 :
    allFrom 18188 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18196 ≤ a < 18204`. -/
theorem transOK_14_80 :
    allFrom 18196 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18204 ≤ a < 18212`. -/
theorem transOK_14_81 :
    allFrom 18204 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18212 ≤ a < 18220`. -/
theorem transOK_14_82 :
    allFrom 18212 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18220 ≤ a < 18228`. -/
theorem transOK_14_83 :
    allFrom 18220 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18228 ≤ a < 18236`. -/
theorem transOK_14_84 :
    allFrom 18228 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18236 ≤ a < 18244`. -/
theorem transOK_14_85 :
    allFrom 18236 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18244 ≤ a < 18252`. -/
theorem transOK_14_86 :
    allFrom 18244 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18252 ≤ a < 18260`. -/
theorem transOK_14_87 :
    allFrom 18252 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18260 ≤ a < 18268`. -/
theorem transOK_14_88 :
    allFrom 18260 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18268 ≤ a < 18276`. -/
theorem transOK_14_89 :
    allFrom 18268 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18276 ≤ a < 18284`. -/
theorem transOK_14_90 :
    allFrom 18276 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18284 ≤ a < 18292`. -/
theorem transOK_14_91 :
    allFrom 18284 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18292 ≤ a < 18300`. -/
theorem transOK_14_92 :
    allFrom 18292 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18300 ≤ a < 18308`. -/
theorem transOK_14_93 :
    allFrom 18300 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18308 ≤ a < 18316`. -/
theorem transOK_14_94 :
    allFrom 18308 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18316 ≤ a < 18324`. -/
theorem transOK_14_95 :
    allFrom 18316 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18324 ≤ a < 18332`. -/
theorem transOK_14_96 :
    allFrom 18324 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18332 ≤ a < 18340`. -/
theorem transOK_14_97 :
    allFrom 18332 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18340 ≤ a < 18348`. -/
theorem transOK_14_98 :
    allFrom 18340 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18348 ≤ a < 18356`. -/
theorem transOK_14_99 :
    allFrom 18348 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18356 ≤ a < 18364`. -/
theorem transOK_14_100 :
    allFrom 18356 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18364 ≤ a < 18372`. -/
theorem transOK_14_101 :
    allFrom 18364 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18372 ≤ a < 18380`. -/
theorem transOK_14_102 :
    allFrom 18372 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18380 ≤ a < 18388`. -/
theorem transOK_14_103 :
    allFrom 18380 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18388 ≤ a < 18396`. -/
theorem transOK_14_104 :
    allFrom 18388 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18396 ≤ a < 18404`. -/
theorem transOK_14_105 :
    allFrom 18396 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18404 ≤ a < 18412`. -/
theorem transOK_14_106 :
    allFrom 18404 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18412 ≤ a < 18420`. -/
theorem transOK_14_107 :
    allFrom 18412 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18420 ≤ a < 18428`. -/
theorem transOK_14_108 :
    allFrom 18420 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18428 ≤ a < 18436`. -/
theorem transOK_14_109 :
    allFrom 18428 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18436 ≤ a < 18444`. -/
theorem transOK_14_110 :
    allFrom 18436 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18444 ≤ a < 18452`. -/
theorem transOK_14_111 :
    allFrom 18444 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18452 ≤ a < 18460`. -/
theorem transOK_14_112 :
    allFrom 18452 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18460 ≤ a < 18468`. -/
theorem transOK_14_113 :
    allFrom 18460 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18468 ≤ a < 18476`. -/
theorem transOK_14_114 :
    allFrom 18468 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18476 ≤ a < 18484`. -/
theorem transOK_14_115 :
    allFrom 18476 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18484 ≤ a < 18492`. -/
theorem transOK_14_116 :
    allFrom 18484 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18492 ≤ a < 18500`. -/
theorem transOK_14_117 :
    allFrom 18492 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18500 ≤ a < 18508`. -/
theorem transOK_14_118 :
    allFrom 18500 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18508 ≤ a < 18516`. -/
theorem transOK_14_119 :
    allFrom 18508 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18516 ≤ a < 18524`. -/
theorem transOK_14_120 :
    allFrom 18516 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18524 ≤ a < 18532`. -/
theorem transOK_14_121 :
    allFrom 18524 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18532 ≤ a < 18540`. -/
theorem transOK_14_122 :
    allFrom 18532 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18540 ≤ a < 18548`. -/
theorem transOK_14_123 :
    allFrom 18540 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18548 ≤ a < 18556`. -/
theorem transOK_14_124 :
    allFrom 18548 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18556 ≤ a < 18564`. -/
theorem transOK_14_125 :
    allFrom 18556 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18564 ≤ a < 18572`. -/
theorem transOK_14_126 :
    allFrom 18564 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18572 ≤ a < 18580`. -/
theorem transOK_14_127 :
    allFrom 18572 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18580 ≤ a < 18588`. -/
theorem transOK_14_128 :
    allFrom 18580 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18588 ≤ a < 18596`. -/
theorem transOK_14_129 :
    allFrom 18588 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18596 ≤ a < 18604`. -/
theorem transOK_14_130 :
    allFrom 18596 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18604 ≤ a < 18612`. -/
theorem transOK_14_131 :
    allFrom 18604 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18612 ≤ a < 18620`. -/
theorem transOK_14_132 :
    allFrom 18612 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18620 ≤ a < 18628`. -/
theorem transOK_14_133 :
    allFrom 18620 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18628 ≤ a < 18636`. -/
theorem transOK_14_134 :
    allFrom 18628 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18636 ≤ a < 18644`. -/
theorem transOK_14_135 :
    allFrom 18636 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18644 ≤ a < 18652`. -/
theorem transOK_14_136 :
    allFrom 18644 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18652 ≤ a < 18660`. -/
theorem transOK_14_137 :
    allFrom 18652 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18660 ≤ a < 18668`. -/
theorem transOK_14_138 :
    allFrom 18660 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18668 ≤ a < 18676`. -/
theorem transOK_14_139 :
    allFrom 18668 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18676 ≤ a < 18684`. -/
theorem transOK_14_140 :
    allFrom 18676 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18684 ≤ a < 18692`. -/
theorem transOK_14_141 :
    allFrom 18684 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18692 ≤ a < 18700`. -/
theorem transOK_14_142 :
    allFrom 18692 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18700 ≤ a < 18708`. -/
theorem transOK_14_143 :
    allFrom 18700 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18708 ≤ a < 18716`. -/
theorem transOK_14_144 :
    allFrom 18708 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18716 ≤ a < 18724`. -/
theorem transOK_14_145 :
    allFrom 18716 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18724 ≤ a < 18732`. -/
theorem transOK_14_146 :
    allFrom 18724 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18732 ≤ a < 18740`. -/
theorem transOK_14_147 :
    allFrom 18732 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18740 ≤ a < 18748`. -/
theorem transOK_14_148 :
    allFrom 18740 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18748 ≤ a < 18756`. -/
theorem transOK_14_149 :
    allFrom 18748 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18756 ≤ a < 18764`. -/
theorem transOK_14_150 :
    allFrom 18756 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18764 ≤ a < 18772`. -/
theorem transOK_14_151 :
    allFrom 18764 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18772 ≤ a < 18780`. -/
theorem transOK_14_152 :
    allFrom 18772 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18780 ≤ a < 18788`. -/
theorem transOK_14_153 :
    allFrom 18780 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18788 ≤ a < 18796`. -/
theorem transOK_14_154 :
    allFrom 18788 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18796 ≤ a < 18804`. -/
theorem transOK_14_155 :
    allFrom 18796 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `18804 ≤ a < 18810`. -/
theorem transOK_14_156 :
    allFrom 18804 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `transOK` holds at every transition `(a, k)` of the `E8` certificate, `17556 ≤ a < 18810`. -/
theorem transOK_14 :
    allFrom 17556 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_0
                              transOK_14_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_2
                              transOK_14_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_4
                              transOK_14_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_7
                                  transOK_14_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_9
                              transOK_14_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_12
                                  transOK_14_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_14
                              transOK_14_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_17
                                  transOK_14_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_19
                              transOK_14_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_22
                                  transOK_14_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_24
                              transOK_14_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_27
                                  transOK_14_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_29
                              transOK_14_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_32
                                  transOK_14_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_34
                              transOK_14_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_37
                                  transOK_14_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_39
                              transOK_14_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_41
                              transOK_14_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_43
                              transOK_14_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_46
                                  transOK_14_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_48
                              transOK_14_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_51
                                  transOK_14_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_53
                              transOK_14_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_56
                                  transOK_14_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_58
                              transOK_14_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_61
                                  transOK_14_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_63
                              transOK_14_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_66
                                  transOK_14_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_68
                              transOK_14_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_71
                                  transOK_14_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_73
                              transOK_14_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_76
                                  transOK_14_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_78
                              transOK_14_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_80
                              transOK_14_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_82
                              transOK_14_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_85
                                  transOK_14_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_87
                              transOK_14_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_90
                                  transOK_14_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_92
                              transOK_14_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_95
                                  transOK_14_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_97
                              transOK_14_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_100
                                  transOK_14_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_102
                              transOK_14_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_105
                                  transOK_14_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_107
                              transOK_14_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_110
                                  transOK_14_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_112
                              transOK_14_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_115
                                  transOK_14_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_117
                              transOK_14_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_120
                                  transOK_14_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_122
                              transOK_14_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_125
                                  transOK_14_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_127
                              transOK_14_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_130
                                  transOK_14_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_132
                              transOK_14_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_135
                                  transOK_14_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_137
                              transOK_14_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_140
                                  transOK_14_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_142
                              transOK_14_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_145
                                  transOK_14_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_147
                              transOK_14_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_14_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_14_150
                                  transOK_14_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_14_152
                              transOK_14_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_14_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_14_155
                                  transOK_14_156)))))))

end ClusterAlgebras.CertificateData.E8

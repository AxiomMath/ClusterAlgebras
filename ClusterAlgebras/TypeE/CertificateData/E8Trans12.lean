/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-! # Kernel check of the transitions of seeds `[15048, 16302)` of the `E8` certificate,
in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_0 :
    allFrom 15048 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_1 :
    allFrom 15056 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_2 :
    allFrom 15064 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_3 :
    allFrom 15072 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_4 :
    allFrom 15080 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_5 :
    allFrom 15088 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_6 :
    allFrom 15096 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_7 :
    allFrom 15104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_8 :
    allFrom 15112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_9 :
    allFrom 15120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_10 :
    allFrom 15128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_11 :
    allFrom 15136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_12 :
    allFrom 15144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_13 :
    allFrom 15152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_14 :
    allFrom 15160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_15 :
    allFrom 15168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_16 :
    allFrom 15176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_17 :
    allFrom 15184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_18 :
    allFrom 15192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_19 :
    allFrom 15200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_20 :
    allFrom 15208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_21 :
    allFrom 15216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_22 :
    allFrom 15224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_23 :
    allFrom 15232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_24 :
    allFrom 15240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_25 :
    allFrom 15248 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_26 :
    allFrom 15256 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_27 :
    allFrom 15264 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_28 :
    allFrom 15272 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_29 :
    allFrom 15280 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_30 :
    allFrom 15288 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_31 :
    allFrom 15296 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_32 :
    allFrom 15304 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_33 :
    allFrom 15312 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_34 :
    allFrom 15320 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_35 :
    allFrom 15328 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_36 :
    allFrom 15336 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_37 :
    allFrom 15344 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_38 :
    allFrom 15352 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_39 :
    allFrom 15360 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_40 :
    allFrom 15368 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_41 :
    allFrom 15376 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_42 :
    allFrom 15384 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_43 :
    allFrom 15392 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_44 :
    allFrom 15400 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_45 :
    allFrom 15408 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_46 :
    allFrom 15416 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_47 :
    allFrom 15424 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_48 :
    allFrom 15432 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_49 :
    allFrom 15440 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_50 :
    allFrom 15448 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_51 :
    allFrom 15456 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_52 :
    allFrom 15464 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_53 :
    allFrom 15472 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_54 :
    allFrom 15480 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_55 :
    allFrom 15488 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_56 :
    allFrom 15496 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_57 :
    allFrom 15504 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_58 :
    allFrom 15512 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_59 :
    allFrom 15520 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_60 :
    allFrom 15528 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_61 :
    allFrom 15536 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_62 :
    allFrom 15544 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_63 :
    allFrom 15552 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_64 :
    allFrom 15560 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_65 :
    allFrom 15568 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_66 :
    allFrom 15576 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_67 :
    allFrom 15584 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_68 :
    allFrom 15592 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_69 :
    allFrom 15600 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_70 :
    allFrom 15608 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_71 :
    allFrom 15616 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_72 :
    allFrom 15624 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_73 :
    allFrom 15632 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_74 :
    allFrom 15640 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_75 :
    allFrom 15648 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_76 :
    allFrom 15656 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_77 :
    allFrom 15664 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_78 :
    allFrom 15672 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_79 :
    allFrom 15680 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_80 :
    allFrom 15688 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_81 :
    allFrom 15696 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_82 :
    allFrom 15704 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_83 :
    allFrom 15712 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_84 :
    allFrom 15720 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_85 :
    allFrom 15728 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_86 :
    allFrom 15736 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_87 :
    allFrom 15744 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_88 :
    allFrom 15752 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_89 :
    allFrom 15760 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_90 :
    allFrom 15768 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_91 :
    allFrom 15776 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_92 :
    allFrom 15784 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_93 :
    allFrom 15792 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_94 :
    allFrom 15800 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_95 :
    allFrom 15808 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_96 :
    allFrom 15816 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_97 :
    allFrom 15824 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_98 :
    allFrom 15832 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_99 :
    allFrom 15840 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_100 :
    allFrom 15848 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_101 :
    allFrom 15856 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_102 :
    allFrom 15864 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_103 :
    allFrom 15872 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_104 :
    allFrom 15880 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_105 :
    allFrom 15888 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_106 :
    allFrom 15896 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_107 :
    allFrom 15904 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_108 :
    allFrom 15912 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_109 :
    allFrom 15920 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_110 :
    allFrom 15928 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_111 :
    allFrom 15936 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_112 :
    allFrom 15944 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_113 :
    allFrom 15952 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_114 :
    allFrom 15960 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_115 :
    allFrom 15968 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_116 :
    allFrom 15976 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_117 :
    allFrom 15984 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_118 :
    allFrom 15992 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_119 :
    allFrom 16000 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_120 :
    allFrom 16008 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_121 :
    allFrom 16016 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_122 :
    allFrom 16024 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_123 :
    allFrom 16032 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_124 :
    allFrom 16040 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_125 :
    allFrom 16048 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_126 :
    allFrom 16056 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_127 :
    allFrom 16064 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_128 :
    allFrom 16072 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_129 :
    allFrom 16080 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_130 :
    allFrom 16088 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_131 :
    allFrom 16096 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_132 :
    allFrom 16104 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_133 :
    allFrom 16112 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_134 :
    allFrom 16120 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_135 :
    allFrom 16128 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_136 :
    allFrom 16136 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_137 :
    allFrom 16144 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_138 :
    allFrom 16152 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_139 :
    allFrom 16160 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_140 :
    allFrom 16168 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_141 :
    allFrom 16176 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_142 :
    allFrom 16184 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_143 :
    allFrom 16192 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_144 :
    allFrom 16200 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_145 :
    allFrom 16208 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_146 :
    allFrom 16216 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_147 :
    allFrom 16224 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_148 :
    allFrom 16232 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_149 :
    allFrom 16240 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_150 :
    allFrom 16248 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_151 :
    allFrom 16256 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_152 :
    allFrom 16264 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_153 :
    allFrom 16272 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_154 :
    allFrom 16280 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_155 :
    allFrom 16288 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds of
this piece, passes `raw.transOK`. -/
theorem transOK_12_156 :
    allFrom 16296 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- Every transition `(a, k)` with `k < 8` of the `E8` certificate, for `a` among the seeds
`[15048, 16302)`, passes `raw.transOK`. -/
theorem transOK_12 :
    allFrom 15048 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_0
                              transOK_12_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_2
                              transOK_12_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_4
                              transOK_12_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_7
                                  transOK_12_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_9
                              transOK_12_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_12
                                  transOK_12_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_14
                              transOK_12_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_17
                                  transOK_12_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_19
                              transOK_12_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_22
                                  transOK_12_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_24
                              transOK_12_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_27
                                  transOK_12_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_29
                              transOK_12_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_32
                                  transOK_12_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_34
                              transOK_12_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_37
                                  transOK_12_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_39
                              transOK_12_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_41
                              transOK_12_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_43
                              transOK_12_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_46
                                  transOK_12_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_48
                              transOK_12_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_51
                                  transOK_12_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_53
                              transOK_12_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_56
                                  transOK_12_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_58
                              transOK_12_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_61
                                  transOK_12_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_63
                              transOK_12_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_66
                                  transOK_12_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_68
                              transOK_12_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_71
                                  transOK_12_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_73
                              transOK_12_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_76
                                  transOK_12_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_78
                              transOK_12_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_80
                              transOK_12_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_82
                              transOK_12_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_85
                                  transOK_12_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_87
                              transOK_12_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_90
                                  transOK_12_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_92
                              transOK_12_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_95
                                  transOK_12_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_97
                              transOK_12_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_100
                                  transOK_12_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_102
                              transOK_12_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_105
                                  transOK_12_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_107
                              transOK_12_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_110
                                  transOK_12_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_112
                              transOK_12_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_115
                                  transOK_12_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_117
                              transOK_12_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_120
                                  transOK_12_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_122
                              transOK_12_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_125
                                  transOK_12_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_127
                              transOK_12_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_130
                                  transOK_12_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_132
                              transOK_12_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_135
                                  transOK_12_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_137
                              transOK_12_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_140
                                  transOK_12_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_142
                              transOK_12_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_145
                                  transOK_12_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_147
                              transOK_12_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_12_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_12_150
                                  transOK_12_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_12_152
                              transOK_12_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_12_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_12_155
                                  transOK_12_156)))))))

end ClusterAlgebras.CertificateData.E8

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Transitions of the seeds `[13794, 15048)` of the `E8` certificate

The transition check `raw.transOK` holds at every seed `a` with `13794 ≤ a < 15048` and every
direction `k < 8`. It is proved by kernel evaluation in pieces of `8` seeds, assembled by
`CertificateCheck.allFrom_add`.

## Main results

* `transOK_11`: the transition check holds at the seeds `[13794, 15048)` in every direction.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- `raw.transOK` holds at every seed `a` with `13794 ≤ a < 13802` and every direction `k < 8`. -/
theorem transOK_11_0 :
    allFrom 13794 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13802 ≤ a < 13810` and every direction `k < 8`. -/
theorem transOK_11_1 :
    allFrom 13802 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13810 ≤ a < 13818` and every direction `k < 8`. -/
theorem transOK_11_2 :
    allFrom 13810 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13818 ≤ a < 13826` and every direction `k < 8`. -/
theorem transOK_11_3 :
    allFrom 13818 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13826 ≤ a < 13834` and every direction `k < 8`. -/
theorem transOK_11_4 :
    allFrom 13826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13834 ≤ a < 13842` and every direction `k < 8`. -/
theorem transOK_11_5 :
    allFrom 13834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13842 ≤ a < 13850` and every direction `k < 8`. -/
theorem transOK_11_6 :
    allFrom 13842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13850 ≤ a < 13858` and every direction `k < 8`. -/
theorem transOK_11_7 :
    allFrom 13850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13858 ≤ a < 13866` and every direction `k < 8`. -/
theorem transOK_11_8 :
    allFrom 13858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13866 ≤ a < 13874` and every direction `k < 8`. -/
theorem transOK_11_9 :
    allFrom 13866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13874 ≤ a < 13882` and every direction `k < 8`. -/
theorem transOK_11_10 :
    allFrom 13874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13882 ≤ a < 13890` and every direction `k < 8`. -/
theorem transOK_11_11 :
    allFrom 13882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13890 ≤ a < 13898` and every direction `k < 8`. -/
theorem transOK_11_12 :
    allFrom 13890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13898 ≤ a < 13906` and every direction `k < 8`. -/
theorem transOK_11_13 :
    allFrom 13898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13906 ≤ a < 13914` and every direction `k < 8`. -/
theorem transOK_11_14 :
    allFrom 13906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13914 ≤ a < 13922` and every direction `k < 8`. -/
theorem transOK_11_15 :
    allFrom 13914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13922 ≤ a < 13930` and every direction `k < 8`. -/
theorem transOK_11_16 :
    allFrom 13922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13930 ≤ a < 13938` and every direction `k < 8`. -/
theorem transOK_11_17 :
    allFrom 13930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13938 ≤ a < 13946` and every direction `k < 8`. -/
theorem transOK_11_18 :
    allFrom 13938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13946 ≤ a < 13954` and every direction `k < 8`. -/
theorem transOK_11_19 :
    allFrom 13946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13954 ≤ a < 13962` and every direction `k < 8`. -/
theorem transOK_11_20 :
    allFrom 13954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13962 ≤ a < 13970` and every direction `k < 8`. -/
theorem transOK_11_21 :
    allFrom 13962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13970 ≤ a < 13978` and every direction `k < 8`. -/
theorem transOK_11_22 :
    allFrom 13970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13978 ≤ a < 13986` and every direction `k < 8`. -/
theorem transOK_11_23 :
    allFrom 13978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13986 ≤ a < 13994` and every direction `k < 8`. -/
theorem transOK_11_24 :
    allFrom 13986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `13994 ≤ a < 14002` and every direction `k < 8`. -/
theorem transOK_11_25 :
    allFrom 13994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14002 ≤ a < 14010` and every direction `k < 8`. -/
theorem transOK_11_26 :
    allFrom 14002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14010 ≤ a < 14018` and every direction `k < 8`. -/
theorem transOK_11_27 :
    allFrom 14010 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14018 ≤ a < 14026` and every direction `k < 8`. -/
theorem transOK_11_28 :
    allFrom 14018 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14026 ≤ a < 14034` and every direction `k < 8`. -/
theorem transOK_11_29 :
    allFrom 14026 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14034 ≤ a < 14042` and every direction `k < 8`. -/
theorem transOK_11_30 :
    allFrom 14034 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14042 ≤ a < 14050` and every direction `k < 8`. -/
theorem transOK_11_31 :
    allFrom 14042 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14050 ≤ a < 14058` and every direction `k < 8`. -/
theorem transOK_11_32 :
    allFrom 14050 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14058 ≤ a < 14066` and every direction `k < 8`. -/
theorem transOK_11_33 :
    allFrom 14058 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14066 ≤ a < 14074` and every direction `k < 8`. -/
theorem transOK_11_34 :
    allFrom 14066 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14074 ≤ a < 14082` and every direction `k < 8`. -/
theorem transOK_11_35 :
    allFrom 14074 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14082 ≤ a < 14090` and every direction `k < 8`. -/
theorem transOK_11_36 :
    allFrom 14082 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14090 ≤ a < 14098` and every direction `k < 8`. -/
theorem transOK_11_37 :
    allFrom 14090 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14098 ≤ a < 14106` and every direction `k < 8`. -/
theorem transOK_11_38 :
    allFrom 14098 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14106 ≤ a < 14114` and every direction `k < 8`. -/
theorem transOK_11_39 :
    allFrom 14106 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14114 ≤ a < 14122` and every direction `k < 8`. -/
theorem transOK_11_40 :
    allFrom 14114 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14122 ≤ a < 14130` and every direction `k < 8`. -/
theorem transOK_11_41 :
    allFrom 14122 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14130 ≤ a < 14138` and every direction `k < 8`. -/
theorem transOK_11_42 :
    allFrom 14130 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14138 ≤ a < 14146` and every direction `k < 8`. -/
theorem transOK_11_43 :
    allFrom 14138 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14146 ≤ a < 14154` and every direction `k < 8`. -/
theorem transOK_11_44 :
    allFrom 14146 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14154 ≤ a < 14162` and every direction `k < 8`. -/
theorem transOK_11_45 :
    allFrom 14154 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14162 ≤ a < 14170` and every direction `k < 8`. -/
theorem transOK_11_46 :
    allFrom 14162 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14170 ≤ a < 14178` and every direction `k < 8`. -/
theorem transOK_11_47 :
    allFrom 14170 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14178 ≤ a < 14186` and every direction `k < 8`. -/
theorem transOK_11_48 :
    allFrom 14178 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14186 ≤ a < 14194` and every direction `k < 8`. -/
theorem transOK_11_49 :
    allFrom 14186 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14194 ≤ a < 14202` and every direction `k < 8`. -/
theorem transOK_11_50 :
    allFrom 14194 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14202 ≤ a < 14210` and every direction `k < 8`. -/
theorem transOK_11_51 :
    allFrom 14202 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14210 ≤ a < 14218` and every direction `k < 8`. -/
theorem transOK_11_52 :
    allFrom 14210 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14218 ≤ a < 14226` and every direction `k < 8`. -/
theorem transOK_11_53 :
    allFrom 14218 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14226 ≤ a < 14234` and every direction `k < 8`. -/
theorem transOK_11_54 :
    allFrom 14226 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14234 ≤ a < 14242` and every direction `k < 8`. -/
theorem transOK_11_55 :
    allFrom 14234 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14242 ≤ a < 14250` and every direction `k < 8`. -/
theorem transOK_11_56 :
    allFrom 14242 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14250 ≤ a < 14258` and every direction `k < 8`. -/
theorem transOK_11_57 :
    allFrom 14250 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14258 ≤ a < 14266` and every direction `k < 8`. -/
theorem transOK_11_58 :
    allFrom 14258 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14266 ≤ a < 14274` and every direction `k < 8`. -/
theorem transOK_11_59 :
    allFrom 14266 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14274 ≤ a < 14282` and every direction `k < 8`. -/
theorem transOK_11_60 :
    allFrom 14274 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14282 ≤ a < 14290` and every direction `k < 8`. -/
theorem transOK_11_61 :
    allFrom 14282 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14290 ≤ a < 14298` and every direction `k < 8`. -/
theorem transOK_11_62 :
    allFrom 14290 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14298 ≤ a < 14306` and every direction `k < 8`. -/
theorem transOK_11_63 :
    allFrom 14298 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14306 ≤ a < 14314` and every direction `k < 8`. -/
theorem transOK_11_64 :
    allFrom 14306 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14314 ≤ a < 14322` and every direction `k < 8`. -/
theorem transOK_11_65 :
    allFrom 14314 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14322 ≤ a < 14330` and every direction `k < 8`. -/
theorem transOK_11_66 :
    allFrom 14322 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14330 ≤ a < 14338` and every direction `k < 8`. -/
theorem transOK_11_67 :
    allFrom 14330 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14338 ≤ a < 14346` and every direction `k < 8`. -/
theorem transOK_11_68 :
    allFrom 14338 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14346 ≤ a < 14354` and every direction `k < 8`. -/
theorem transOK_11_69 :
    allFrom 14346 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14354 ≤ a < 14362` and every direction `k < 8`. -/
theorem transOK_11_70 :
    allFrom 14354 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14362 ≤ a < 14370` and every direction `k < 8`. -/
theorem transOK_11_71 :
    allFrom 14362 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14370 ≤ a < 14378` and every direction `k < 8`. -/
theorem transOK_11_72 :
    allFrom 14370 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14378 ≤ a < 14386` and every direction `k < 8`. -/
theorem transOK_11_73 :
    allFrom 14378 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14386 ≤ a < 14394` and every direction `k < 8`. -/
theorem transOK_11_74 :
    allFrom 14386 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14394 ≤ a < 14402` and every direction `k < 8`. -/
theorem transOK_11_75 :
    allFrom 14394 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14402 ≤ a < 14410` and every direction `k < 8`. -/
theorem transOK_11_76 :
    allFrom 14402 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14410 ≤ a < 14418` and every direction `k < 8`. -/
theorem transOK_11_77 :
    allFrom 14410 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14418 ≤ a < 14426` and every direction `k < 8`. -/
theorem transOK_11_78 :
    allFrom 14418 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14426 ≤ a < 14434` and every direction `k < 8`. -/
theorem transOK_11_79 :
    allFrom 14426 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14434 ≤ a < 14442` and every direction `k < 8`. -/
theorem transOK_11_80 :
    allFrom 14434 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14442 ≤ a < 14450` and every direction `k < 8`. -/
theorem transOK_11_81 :
    allFrom 14442 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14450 ≤ a < 14458` and every direction `k < 8`. -/
theorem transOK_11_82 :
    allFrom 14450 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14458 ≤ a < 14466` and every direction `k < 8`. -/
theorem transOK_11_83 :
    allFrom 14458 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14466 ≤ a < 14474` and every direction `k < 8`. -/
theorem transOK_11_84 :
    allFrom 14466 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14474 ≤ a < 14482` and every direction `k < 8`. -/
theorem transOK_11_85 :
    allFrom 14474 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14482 ≤ a < 14490` and every direction `k < 8`. -/
theorem transOK_11_86 :
    allFrom 14482 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14490 ≤ a < 14498` and every direction `k < 8`. -/
theorem transOK_11_87 :
    allFrom 14490 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14498 ≤ a < 14506` and every direction `k < 8`. -/
theorem transOK_11_88 :
    allFrom 14498 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14506 ≤ a < 14514` and every direction `k < 8`. -/
theorem transOK_11_89 :
    allFrom 14506 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14514 ≤ a < 14522` and every direction `k < 8`. -/
theorem transOK_11_90 :
    allFrom 14514 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14522 ≤ a < 14530` and every direction `k < 8`. -/
theorem transOK_11_91 :
    allFrom 14522 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14530 ≤ a < 14538` and every direction `k < 8`. -/
theorem transOK_11_92 :
    allFrom 14530 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14538 ≤ a < 14546` and every direction `k < 8`. -/
theorem transOK_11_93 :
    allFrom 14538 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14546 ≤ a < 14554` and every direction `k < 8`. -/
theorem transOK_11_94 :
    allFrom 14546 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14554 ≤ a < 14562` and every direction `k < 8`. -/
theorem transOK_11_95 :
    allFrom 14554 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14562 ≤ a < 14570` and every direction `k < 8`. -/
theorem transOK_11_96 :
    allFrom 14562 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14570 ≤ a < 14578` and every direction `k < 8`. -/
theorem transOK_11_97 :
    allFrom 14570 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14578 ≤ a < 14586` and every direction `k < 8`. -/
theorem transOK_11_98 :
    allFrom 14578 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14586 ≤ a < 14594` and every direction `k < 8`. -/
theorem transOK_11_99 :
    allFrom 14586 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14594 ≤ a < 14602` and every direction `k < 8`. -/
theorem transOK_11_100 :
    allFrom 14594 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14602 ≤ a < 14610` and every direction `k < 8`. -/
theorem transOK_11_101 :
    allFrom 14602 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14610 ≤ a < 14618` and every direction `k < 8`. -/
theorem transOK_11_102 :
    allFrom 14610 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14618 ≤ a < 14626` and every direction `k < 8`. -/
theorem transOK_11_103 :
    allFrom 14618 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14626 ≤ a < 14634` and every direction `k < 8`. -/
theorem transOK_11_104 :
    allFrom 14626 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14634 ≤ a < 14642` and every direction `k < 8`. -/
theorem transOK_11_105 :
    allFrom 14634 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14642 ≤ a < 14650` and every direction `k < 8`. -/
theorem transOK_11_106 :
    allFrom 14642 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14650 ≤ a < 14658` and every direction `k < 8`. -/
theorem transOK_11_107 :
    allFrom 14650 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14658 ≤ a < 14666` and every direction `k < 8`. -/
theorem transOK_11_108 :
    allFrom 14658 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14666 ≤ a < 14674` and every direction `k < 8`. -/
theorem transOK_11_109 :
    allFrom 14666 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14674 ≤ a < 14682` and every direction `k < 8`. -/
theorem transOK_11_110 :
    allFrom 14674 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14682 ≤ a < 14690` and every direction `k < 8`. -/
theorem transOK_11_111 :
    allFrom 14682 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14690 ≤ a < 14698` and every direction `k < 8`. -/
theorem transOK_11_112 :
    allFrom 14690 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14698 ≤ a < 14706` and every direction `k < 8`. -/
theorem transOK_11_113 :
    allFrom 14698 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14706 ≤ a < 14714` and every direction `k < 8`. -/
theorem transOK_11_114 :
    allFrom 14706 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14714 ≤ a < 14722` and every direction `k < 8`. -/
theorem transOK_11_115 :
    allFrom 14714 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14722 ≤ a < 14730` and every direction `k < 8`. -/
theorem transOK_11_116 :
    allFrom 14722 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14730 ≤ a < 14738` and every direction `k < 8`. -/
theorem transOK_11_117 :
    allFrom 14730 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14738 ≤ a < 14746` and every direction `k < 8`. -/
theorem transOK_11_118 :
    allFrom 14738 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14746 ≤ a < 14754` and every direction `k < 8`. -/
theorem transOK_11_119 :
    allFrom 14746 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14754 ≤ a < 14762` and every direction `k < 8`. -/
theorem transOK_11_120 :
    allFrom 14754 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14762 ≤ a < 14770` and every direction `k < 8`. -/
theorem transOK_11_121 :
    allFrom 14762 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14770 ≤ a < 14778` and every direction `k < 8`. -/
theorem transOK_11_122 :
    allFrom 14770 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14778 ≤ a < 14786` and every direction `k < 8`. -/
theorem transOK_11_123 :
    allFrom 14778 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14786 ≤ a < 14794` and every direction `k < 8`. -/
theorem transOK_11_124 :
    allFrom 14786 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14794 ≤ a < 14802` and every direction `k < 8`. -/
theorem transOK_11_125 :
    allFrom 14794 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14802 ≤ a < 14810` and every direction `k < 8`. -/
theorem transOK_11_126 :
    allFrom 14802 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14810 ≤ a < 14818` and every direction `k < 8`. -/
theorem transOK_11_127 :
    allFrom 14810 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14818 ≤ a < 14826` and every direction `k < 8`. -/
theorem transOK_11_128 :
    allFrom 14818 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14826 ≤ a < 14834` and every direction `k < 8`. -/
theorem transOK_11_129 :
    allFrom 14826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14834 ≤ a < 14842` and every direction `k < 8`. -/
theorem transOK_11_130 :
    allFrom 14834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14842 ≤ a < 14850` and every direction `k < 8`. -/
theorem transOK_11_131 :
    allFrom 14842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14850 ≤ a < 14858` and every direction `k < 8`. -/
theorem transOK_11_132 :
    allFrom 14850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14858 ≤ a < 14866` and every direction `k < 8`. -/
theorem transOK_11_133 :
    allFrom 14858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14866 ≤ a < 14874` and every direction `k < 8`. -/
theorem transOK_11_134 :
    allFrom 14866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14874 ≤ a < 14882` and every direction `k < 8`. -/
theorem transOK_11_135 :
    allFrom 14874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14882 ≤ a < 14890` and every direction `k < 8`. -/
theorem transOK_11_136 :
    allFrom 14882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14890 ≤ a < 14898` and every direction `k < 8`. -/
theorem transOK_11_137 :
    allFrom 14890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14898 ≤ a < 14906` and every direction `k < 8`. -/
theorem transOK_11_138 :
    allFrom 14898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14906 ≤ a < 14914` and every direction `k < 8`. -/
theorem transOK_11_139 :
    allFrom 14906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14914 ≤ a < 14922` and every direction `k < 8`. -/
theorem transOK_11_140 :
    allFrom 14914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14922 ≤ a < 14930` and every direction `k < 8`. -/
theorem transOK_11_141 :
    allFrom 14922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14930 ≤ a < 14938` and every direction `k < 8`. -/
theorem transOK_11_142 :
    allFrom 14930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14938 ≤ a < 14946` and every direction `k < 8`. -/
theorem transOK_11_143 :
    allFrom 14938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14946 ≤ a < 14954` and every direction `k < 8`. -/
theorem transOK_11_144 :
    allFrom 14946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14954 ≤ a < 14962` and every direction `k < 8`. -/
theorem transOK_11_145 :
    allFrom 14954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14962 ≤ a < 14970` and every direction `k < 8`. -/
theorem transOK_11_146 :
    allFrom 14962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14970 ≤ a < 14978` and every direction `k < 8`. -/
theorem transOK_11_147 :
    allFrom 14970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14978 ≤ a < 14986` and every direction `k < 8`. -/
theorem transOK_11_148 :
    allFrom 14978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14986 ≤ a < 14994` and every direction `k < 8`. -/
theorem transOK_11_149 :
    allFrom 14986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `14994 ≤ a < 15002` and every direction `k < 8`. -/
theorem transOK_11_150 :
    allFrom 14994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `15002 ≤ a < 15010` and every direction `k < 8`. -/
theorem transOK_11_151 :
    allFrom 15002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `15010 ≤ a < 15018` and every direction `k < 8`. -/
theorem transOK_11_152 :
    allFrom 15010 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `15018 ≤ a < 15026` and every direction `k < 8`. -/
theorem transOK_11_153 :
    allFrom 15018 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `15026 ≤ a < 15034` and every direction `k < 8`. -/
theorem transOK_11_154 :
    allFrom 15026 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `15034 ≤ a < 15042` and every direction `k < 8`. -/
theorem transOK_11_155 :
    allFrom 15034 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds at every seed `a` with `15042 ≤ a < 15048` and every direction `k < 8`. -/
theorem transOK_11_156 :
    allFrom 15042 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds at every seed `a` with `13794 ≤ a < 15048` and every
direction `k < 8`. -/
theorem transOK_11 :
    allFrom 13794 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_0
                              transOK_11_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_2
                              transOK_11_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_4
                              transOK_11_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_7
                                  transOK_11_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_9
                              transOK_11_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_12
                                  transOK_11_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_14
                              transOK_11_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_17
                                  transOK_11_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_19
                              transOK_11_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_22
                                  transOK_11_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_24
                              transOK_11_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_27
                                  transOK_11_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_29
                              transOK_11_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_32
                                  transOK_11_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_34
                              transOK_11_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_37
                                  transOK_11_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_39
                              transOK_11_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_41
                              transOK_11_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_43
                              transOK_11_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_46
                                  transOK_11_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_48
                              transOK_11_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_51
                                  transOK_11_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_53
                              transOK_11_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_56
                                  transOK_11_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_58
                              transOK_11_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_61
                                  transOK_11_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_63
                              transOK_11_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_66
                                  transOK_11_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_68
                              transOK_11_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_71
                                  transOK_11_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_73
                              transOK_11_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_76
                                  transOK_11_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_78
                              transOK_11_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_80
                              transOK_11_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_82
                              transOK_11_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_85
                                  transOK_11_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_87
                              transOK_11_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_90
                                  transOK_11_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_92
                              transOK_11_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_95
                                  transOK_11_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_97
                              transOK_11_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_100
                                  transOK_11_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_102
                              transOK_11_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_105
                                  transOK_11_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_107
                              transOK_11_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_110
                                  transOK_11_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_112
                              transOK_11_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_115
                                  transOK_11_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_117
                              transOK_11_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_120
                                  transOK_11_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_122
                              transOK_11_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_125
                                  transOK_11_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_127
                              transOK_11_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_130
                                  transOK_11_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_132
                              transOK_11_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_135
                                  transOK_11_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_137
                              transOK_11_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_140
                                  transOK_11_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_142
                              transOK_11_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_145
                                  transOK_11_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_147
                              transOK_11_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_11_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_11_150
                                  transOK_11_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_11_152
                              transOK_11_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_11_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_11_155
                                  transOK_11_156)))))))

end ClusterAlgebras.CertificateData.E8

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-! # Kernel check of the transitions of seeds `[8778, 10032)` of the `E8` certificate,
in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8778, 8786)` of the `E8` certificate. -/
theorem transOK_7_0 :
    allFrom 8778 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8786, 8794)` of the `E8` certificate. -/
theorem transOK_7_1 :
    allFrom 8786 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8794, 8802)` of the `E8` certificate. -/
theorem transOK_7_2 :
    allFrom 8794 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8802, 8810)` of the `E8` certificate. -/
theorem transOK_7_3 :
    allFrom 8802 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8810, 8818)` of the `E8` certificate. -/
theorem transOK_7_4 :
    allFrom 8810 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8818, 8826)` of the `E8` certificate. -/
theorem transOK_7_5 :
    allFrom 8818 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8826, 8834)` of the `E8` certificate. -/
theorem transOK_7_6 :
    allFrom 8826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8834, 8842)` of the `E8` certificate. -/
theorem transOK_7_7 :
    allFrom 8834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8842, 8850)` of the `E8` certificate. -/
theorem transOK_7_8 :
    allFrom 8842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8850, 8858)` of the `E8` certificate. -/
theorem transOK_7_9 :
    allFrom 8850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8858, 8866)` of the `E8` certificate. -/
theorem transOK_7_10 :
    allFrom 8858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8866, 8874)` of the `E8` certificate. -/
theorem transOK_7_11 :
    allFrom 8866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8874, 8882)` of the `E8` certificate. -/
theorem transOK_7_12 :
    allFrom 8874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8882, 8890)` of the `E8` certificate. -/
theorem transOK_7_13 :
    allFrom 8882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8890, 8898)` of the `E8` certificate. -/
theorem transOK_7_14 :
    allFrom 8890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8898, 8906)` of the `E8` certificate. -/
theorem transOK_7_15 :
    allFrom 8898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8906, 8914)` of the `E8` certificate. -/
theorem transOK_7_16 :
    allFrom 8906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8914, 8922)` of the `E8` certificate. -/
theorem transOK_7_17 :
    allFrom 8914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8922, 8930)` of the `E8` certificate. -/
theorem transOK_7_18 :
    allFrom 8922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8930, 8938)` of the `E8` certificate. -/
theorem transOK_7_19 :
    allFrom 8930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8938, 8946)` of the `E8` certificate. -/
theorem transOK_7_20 :
    allFrom 8938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8946, 8954)` of the `E8` certificate. -/
theorem transOK_7_21 :
    allFrom 8946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8954, 8962)` of the `E8` certificate. -/
theorem transOK_7_22 :
    allFrom 8954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8962, 8970)` of the `E8` certificate. -/
theorem transOK_7_23 :
    allFrom 8962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8970, 8978)` of the `E8` certificate. -/
theorem transOK_7_24 :
    allFrom 8970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8978, 8986)` of the `E8` certificate. -/
theorem transOK_7_25 :
    allFrom 8978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8986, 8994)` of the `E8` certificate. -/
theorem transOK_7_26 :
    allFrom 8986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8994, 9002)` of the `E8` certificate. -/
theorem transOK_7_27 :
    allFrom 8994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9002, 9010)` of the `E8` certificate. -/
theorem transOK_7_28 :
    allFrom 9002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9010, 9018)` of the `E8` certificate. -/
theorem transOK_7_29 :
    allFrom 9010 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9018, 9026)` of the `E8` certificate. -/
theorem transOK_7_30 :
    allFrom 9018 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9026, 9034)` of the `E8` certificate. -/
theorem transOK_7_31 :
    allFrom 9026 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9034, 9042)` of the `E8` certificate. -/
theorem transOK_7_32 :
    allFrom 9034 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9042, 9050)` of the `E8` certificate. -/
theorem transOK_7_33 :
    allFrom 9042 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9050, 9058)` of the `E8` certificate. -/
theorem transOK_7_34 :
    allFrom 9050 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9058, 9066)` of the `E8` certificate. -/
theorem transOK_7_35 :
    allFrom 9058 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9066, 9074)` of the `E8` certificate. -/
theorem transOK_7_36 :
    allFrom 9066 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9074, 9082)` of the `E8` certificate. -/
theorem transOK_7_37 :
    allFrom 9074 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9082, 9090)` of the `E8` certificate. -/
theorem transOK_7_38 :
    allFrom 9082 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9090, 9098)` of the `E8` certificate. -/
theorem transOK_7_39 :
    allFrom 9090 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9098, 9106)` of the `E8` certificate. -/
theorem transOK_7_40 :
    allFrom 9098 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9106, 9114)` of the `E8` certificate. -/
theorem transOK_7_41 :
    allFrom 9106 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9114, 9122)` of the `E8` certificate. -/
theorem transOK_7_42 :
    allFrom 9114 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9122, 9130)` of the `E8` certificate. -/
theorem transOK_7_43 :
    allFrom 9122 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9130, 9138)` of the `E8` certificate. -/
theorem transOK_7_44 :
    allFrom 9130 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9138, 9146)` of the `E8` certificate. -/
theorem transOK_7_45 :
    allFrom 9138 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9146, 9154)` of the `E8` certificate. -/
theorem transOK_7_46 :
    allFrom 9146 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9154, 9162)` of the `E8` certificate. -/
theorem transOK_7_47 :
    allFrom 9154 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9162, 9170)` of the `E8` certificate. -/
theorem transOK_7_48 :
    allFrom 9162 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9170, 9178)` of the `E8` certificate. -/
theorem transOK_7_49 :
    allFrom 9170 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9178, 9186)` of the `E8` certificate. -/
theorem transOK_7_50 :
    allFrom 9178 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9186, 9194)` of the `E8` certificate. -/
theorem transOK_7_51 :
    allFrom 9186 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9194, 9202)` of the `E8` certificate. -/
theorem transOK_7_52 :
    allFrom 9194 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9202, 9210)` of the `E8` certificate. -/
theorem transOK_7_53 :
    allFrom 9202 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9210, 9218)` of the `E8` certificate. -/
theorem transOK_7_54 :
    allFrom 9210 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9218, 9226)` of the `E8` certificate. -/
theorem transOK_7_55 :
    allFrom 9218 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9226, 9234)` of the `E8` certificate. -/
theorem transOK_7_56 :
    allFrom 9226 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9234, 9242)` of the `E8` certificate. -/
theorem transOK_7_57 :
    allFrom 9234 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9242, 9250)` of the `E8` certificate. -/
theorem transOK_7_58 :
    allFrom 9242 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9250, 9258)` of the `E8` certificate. -/
theorem transOK_7_59 :
    allFrom 9250 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9258, 9266)` of the `E8` certificate. -/
theorem transOK_7_60 :
    allFrom 9258 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9266, 9274)` of the `E8` certificate. -/
theorem transOK_7_61 :
    allFrom 9266 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9274, 9282)` of the `E8` certificate. -/
theorem transOK_7_62 :
    allFrom 9274 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9282, 9290)` of the `E8` certificate. -/
theorem transOK_7_63 :
    allFrom 9282 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9290, 9298)` of the `E8` certificate. -/
theorem transOK_7_64 :
    allFrom 9290 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9298, 9306)` of the `E8` certificate. -/
theorem transOK_7_65 :
    allFrom 9298 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9306, 9314)` of the `E8` certificate. -/
theorem transOK_7_66 :
    allFrom 9306 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9314, 9322)` of the `E8` certificate. -/
theorem transOK_7_67 :
    allFrom 9314 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9322, 9330)` of the `E8` certificate. -/
theorem transOK_7_68 :
    allFrom 9322 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9330, 9338)` of the `E8` certificate. -/
theorem transOK_7_69 :
    allFrom 9330 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9338, 9346)` of the `E8` certificate. -/
theorem transOK_7_70 :
    allFrom 9338 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9346, 9354)` of the `E8` certificate. -/
theorem transOK_7_71 :
    allFrom 9346 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9354, 9362)` of the `E8` certificate. -/
theorem transOK_7_72 :
    allFrom 9354 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9362, 9370)` of the `E8` certificate. -/
theorem transOK_7_73 :
    allFrom 9362 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9370, 9378)` of the `E8` certificate. -/
theorem transOK_7_74 :
    allFrom 9370 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9378, 9386)` of the `E8` certificate. -/
theorem transOK_7_75 :
    allFrom 9378 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9386, 9394)` of the `E8` certificate. -/
theorem transOK_7_76 :
    allFrom 9386 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9394, 9402)` of the `E8` certificate. -/
theorem transOK_7_77 :
    allFrom 9394 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9402, 9410)` of the `E8` certificate. -/
theorem transOK_7_78 :
    allFrom 9402 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9410, 9418)` of the `E8` certificate. -/
theorem transOK_7_79 :
    allFrom 9410 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9418, 9426)` of the `E8` certificate. -/
theorem transOK_7_80 :
    allFrom 9418 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9426, 9434)` of the `E8` certificate. -/
theorem transOK_7_81 :
    allFrom 9426 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9434, 9442)` of the `E8` certificate. -/
theorem transOK_7_82 :
    allFrom 9434 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9442, 9450)` of the `E8` certificate. -/
theorem transOK_7_83 :
    allFrom 9442 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9450, 9458)` of the `E8` certificate. -/
theorem transOK_7_84 :
    allFrom 9450 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9458, 9466)` of the `E8` certificate. -/
theorem transOK_7_85 :
    allFrom 9458 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9466, 9474)` of the `E8` certificate. -/
theorem transOK_7_86 :
    allFrom 9466 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9474, 9482)` of the `E8` certificate. -/
theorem transOK_7_87 :
    allFrom 9474 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9482, 9490)` of the `E8` certificate. -/
theorem transOK_7_88 :
    allFrom 9482 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9490, 9498)` of the `E8` certificate. -/
theorem transOK_7_89 :
    allFrom 9490 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9498, 9506)` of the `E8` certificate. -/
theorem transOK_7_90 :
    allFrom 9498 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9506, 9514)` of the `E8` certificate. -/
theorem transOK_7_91 :
    allFrom 9506 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9514, 9522)` of the `E8` certificate. -/
theorem transOK_7_92 :
    allFrom 9514 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9522, 9530)` of the `E8` certificate. -/
theorem transOK_7_93 :
    allFrom 9522 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9530, 9538)` of the `E8` certificate. -/
theorem transOK_7_94 :
    allFrom 9530 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9538, 9546)` of the `E8` certificate. -/
theorem transOK_7_95 :
    allFrom 9538 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9546, 9554)` of the `E8` certificate. -/
theorem transOK_7_96 :
    allFrom 9546 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9554, 9562)` of the `E8` certificate. -/
theorem transOK_7_97 :
    allFrom 9554 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9562, 9570)` of the `E8` certificate. -/
theorem transOK_7_98 :
    allFrom 9562 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9570, 9578)` of the `E8` certificate. -/
theorem transOK_7_99 :
    allFrom 9570 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9578, 9586)` of the `E8` certificate. -/
theorem transOK_7_100 :
    allFrom 9578 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9586, 9594)` of the `E8` certificate. -/
theorem transOK_7_101 :
    allFrom 9586 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9594, 9602)` of the `E8` certificate. -/
theorem transOK_7_102 :
    allFrom 9594 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9602, 9610)` of the `E8` certificate. -/
theorem transOK_7_103 :
    allFrom 9602 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9610, 9618)` of the `E8` certificate. -/
theorem transOK_7_104 :
    allFrom 9610 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9618, 9626)` of the `E8` certificate. -/
theorem transOK_7_105 :
    allFrom 9618 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9626, 9634)` of the `E8` certificate. -/
theorem transOK_7_106 :
    allFrom 9626 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9634, 9642)` of the `E8` certificate. -/
theorem transOK_7_107 :
    allFrom 9634 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9642, 9650)` of the `E8` certificate. -/
theorem transOK_7_108 :
    allFrom 9642 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9650, 9658)` of the `E8` certificate. -/
theorem transOK_7_109 :
    allFrom 9650 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9658, 9666)` of the `E8` certificate. -/
theorem transOK_7_110 :
    allFrom 9658 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9666, 9674)` of the `E8` certificate. -/
theorem transOK_7_111 :
    allFrom 9666 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9674, 9682)` of the `E8` certificate. -/
theorem transOK_7_112 :
    allFrom 9674 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9682, 9690)` of the `E8` certificate. -/
theorem transOK_7_113 :
    allFrom 9682 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9690, 9698)` of the `E8` certificate. -/
theorem transOK_7_114 :
    allFrom 9690 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9698, 9706)` of the `E8` certificate. -/
theorem transOK_7_115 :
    allFrom 9698 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9706, 9714)` of the `E8` certificate. -/
theorem transOK_7_116 :
    allFrom 9706 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9714, 9722)` of the `E8` certificate. -/
theorem transOK_7_117 :
    allFrom 9714 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9722, 9730)` of the `E8` certificate. -/
theorem transOK_7_118 :
    allFrom 9722 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9730, 9738)` of the `E8` certificate. -/
theorem transOK_7_119 :
    allFrom 9730 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9738, 9746)` of the `E8` certificate. -/
theorem transOK_7_120 :
    allFrom 9738 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9746, 9754)` of the `E8` certificate. -/
theorem transOK_7_121 :
    allFrom 9746 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9754, 9762)` of the `E8` certificate. -/
theorem transOK_7_122 :
    allFrom 9754 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9762, 9770)` of the `E8` certificate. -/
theorem transOK_7_123 :
    allFrom 9762 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9770, 9778)` of the `E8` certificate. -/
theorem transOK_7_124 :
    allFrom 9770 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9778, 9786)` of the `E8` certificate. -/
theorem transOK_7_125 :
    allFrom 9778 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9786, 9794)` of the `E8` certificate. -/
theorem transOK_7_126 :
    allFrom 9786 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9794, 9802)` of the `E8` certificate. -/
theorem transOK_7_127 :
    allFrom 9794 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9802, 9810)` of the `E8` certificate. -/
theorem transOK_7_128 :
    allFrom 9802 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9810, 9818)` of the `E8` certificate. -/
theorem transOK_7_129 :
    allFrom 9810 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9818, 9826)` of the `E8` certificate. -/
theorem transOK_7_130 :
    allFrom 9818 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9826, 9834)` of the `E8` certificate. -/
theorem transOK_7_131 :
    allFrom 9826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9834, 9842)` of the `E8` certificate. -/
theorem transOK_7_132 :
    allFrom 9834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9842, 9850)` of the `E8` certificate. -/
theorem transOK_7_133 :
    allFrom 9842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9850, 9858)` of the `E8` certificate. -/
theorem transOK_7_134 :
    allFrom 9850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9858, 9866)` of the `E8` certificate. -/
theorem transOK_7_135 :
    allFrom 9858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9866, 9874)` of the `E8` certificate. -/
theorem transOK_7_136 :
    allFrom 9866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9874, 9882)` of the `E8` certificate. -/
theorem transOK_7_137 :
    allFrom 9874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9882, 9890)` of the `E8` certificate. -/
theorem transOK_7_138 :
    allFrom 9882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9890, 9898)` of the `E8` certificate. -/
theorem transOK_7_139 :
    allFrom 9890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9898, 9906)` of the `E8` certificate. -/
theorem transOK_7_140 :
    allFrom 9898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9906, 9914)` of the `E8` certificate. -/
theorem transOK_7_141 :
    allFrom 9906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9914, 9922)` of the `E8` certificate. -/
theorem transOK_7_142 :
    allFrom 9914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9922, 9930)` of the `E8` certificate. -/
theorem transOK_7_143 :
    allFrom 9922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9930, 9938)` of the `E8` certificate. -/
theorem transOK_7_144 :
    allFrom 9930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9938, 9946)` of the `E8` certificate. -/
theorem transOK_7_145 :
    allFrom 9938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9946, 9954)` of the `E8` certificate. -/
theorem transOK_7_146 :
    allFrom 9946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9954, 9962)` of the `E8` certificate. -/
theorem transOK_7_147 :
    allFrom 9954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9962, 9970)` of the `E8` certificate. -/
theorem transOK_7_148 :
    allFrom 9962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9970, 9978)` of the `E8` certificate. -/
theorem transOK_7_149 :
    allFrom 9970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9978, 9986)` of the `E8` certificate. -/
theorem transOK_7_150 :
    allFrom 9978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9986, 9994)` of the `E8` certificate. -/
theorem transOK_7_151 :
    allFrom 9986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[9994, 10002)` of the `E8` certificate. -/
theorem transOK_7_152 :
    allFrom 9994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[10002, 10010)` of the `E8` certificate. -/
theorem transOK_7_153 :
    allFrom 10002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[10010, 10018)` of the `E8` certificate. -/
theorem transOK_7_154 :
    allFrom 10010 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[10018, 10026)` of the `E8` certificate. -/
theorem transOK_7_155 :
    allFrom 10018 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[10026, 10032)` of the `E8` certificate. -/
theorem transOK_7_156 :
    allFrom 10026 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- The transition check `raw.transOK` holds in every direction `k < 8` at each of the seeds
`[8778, 10032)` of the `E8` certificate. -/
theorem transOK_7 :
    allFrom 8778 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_0
                              transOK_7_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_2
                              transOK_7_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_4
                              transOK_7_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_7
                                  transOK_7_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_9
                              transOK_7_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_12
                                  transOK_7_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_14
                              transOK_7_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_17
                                  transOK_7_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_19
                              transOK_7_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_22
                                  transOK_7_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_24
                              transOK_7_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_27
                                  transOK_7_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_29
                              transOK_7_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_32
                                  transOK_7_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_34
                              transOK_7_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_37
                                  transOK_7_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_39
                              transOK_7_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_41
                              transOK_7_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_43
                              transOK_7_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_46
                                  transOK_7_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_48
                              transOK_7_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_51
                                  transOK_7_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_53
                              transOK_7_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_56
                                  transOK_7_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_58
                              transOK_7_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_61
                                  transOK_7_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_63
                              transOK_7_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_66
                                  transOK_7_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_68
                              transOK_7_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_71
                                  transOK_7_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_73
                              transOK_7_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_76
                                  transOK_7_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_78
                              transOK_7_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_80
                              transOK_7_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_82
                              transOK_7_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_85
                                  transOK_7_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_87
                              transOK_7_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_90
                                  transOK_7_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_92
                              transOK_7_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_95
                                  transOK_7_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_97
                              transOK_7_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_100
                                  transOK_7_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_102
                              transOK_7_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_105
                                  transOK_7_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_107
                              transOK_7_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_110
                                  transOK_7_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_112
                              transOK_7_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_115
                                  transOK_7_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_117
                              transOK_7_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_120
                                  transOK_7_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_122
                              transOK_7_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_125
                                  transOK_7_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_127
                              transOK_7_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_130
                                  transOK_7_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_132
                              transOK_7_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_135
                                  transOK_7_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_137
                              transOK_7_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_140
                                  transOK_7_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_142
                              transOK_7_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_145
                                  transOK_7_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_147
                              transOK_7_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_7_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_7_150
                                  transOK_7_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_7_152
                              transOK_7_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_7_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_7_155
                                  transOK_7_156)))))))

end ClusterAlgebras.CertificateData.E8

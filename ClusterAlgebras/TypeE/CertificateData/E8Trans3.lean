/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck
public import ClusterAlgebras.TypeE.CertificateData.E8

/-! # Kernel check of the transitions of seeds `[3762, 5016)` of the `E8` certificate,
in pieces of `8` seeds assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- `raw.transOK` holds for every seed in `[3762, 3770)` and every direction `k < 8`. -/
theorem transOK_3_0 :
    allFrom 3762 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3770, 3778)` and every direction `k < 8`. -/
theorem transOK_3_1 :
    allFrom 3770 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3778, 3786)` and every direction `k < 8`. -/
theorem transOK_3_2 :
    allFrom 3778 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3786, 3794)` and every direction `k < 8`. -/
theorem transOK_3_3 :
    allFrom 3786 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3794, 3802)` and every direction `k < 8`. -/
theorem transOK_3_4 :
    allFrom 3794 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3802, 3810)` and every direction `k < 8`. -/
theorem transOK_3_5 :
    allFrom 3802 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3810, 3818)` and every direction `k < 8`. -/
theorem transOK_3_6 :
    allFrom 3810 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3818, 3826)` and every direction `k < 8`. -/
theorem transOK_3_7 :
    allFrom 3818 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3826, 3834)` and every direction `k < 8`. -/
theorem transOK_3_8 :
    allFrom 3826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3834, 3842)` and every direction `k < 8`. -/
theorem transOK_3_9 :
    allFrom 3834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3842, 3850)` and every direction `k < 8`. -/
theorem transOK_3_10 :
    allFrom 3842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3850, 3858)` and every direction `k < 8`. -/
theorem transOK_3_11 :
    allFrom 3850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3858, 3866)` and every direction `k < 8`. -/
theorem transOK_3_12 :
    allFrom 3858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3866, 3874)` and every direction `k < 8`. -/
theorem transOK_3_13 :
    allFrom 3866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3874, 3882)` and every direction `k < 8`. -/
theorem transOK_3_14 :
    allFrom 3874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3882, 3890)` and every direction `k < 8`. -/
theorem transOK_3_15 :
    allFrom 3882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3890, 3898)` and every direction `k < 8`. -/
theorem transOK_3_16 :
    allFrom 3890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3898, 3906)` and every direction `k < 8`. -/
theorem transOK_3_17 :
    allFrom 3898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3906, 3914)` and every direction `k < 8`. -/
theorem transOK_3_18 :
    allFrom 3906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3914, 3922)` and every direction `k < 8`. -/
theorem transOK_3_19 :
    allFrom 3914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3922, 3930)` and every direction `k < 8`. -/
theorem transOK_3_20 :
    allFrom 3922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3930, 3938)` and every direction `k < 8`. -/
theorem transOK_3_21 :
    allFrom 3930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3938, 3946)` and every direction `k < 8`. -/
theorem transOK_3_22 :
    allFrom 3938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3946, 3954)` and every direction `k < 8`. -/
theorem transOK_3_23 :
    allFrom 3946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3954, 3962)` and every direction `k < 8`. -/
theorem transOK_3_24 :
    allFrom 3954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3962, 3970)` and every direction `k < 8`. -/
theorem transOK_3_25 :
    allFrom 3962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3970, 3978)` and every direction `k < 8`. -/
theorem transOK_3_26 :
    allFrom 3970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3978, 3986)` and every direction `k < 8`. -/
theorem transOK_3_27 :
    allFrom 3978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3986, 3994)` and every direction `k < 8`. -/
theorem transOK_3_28 :
    allFrom 3986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3994, 4002)` and every direction `k < 8`. -/
theorem transOK_3_29 :
    allFrom 3994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4002, 4010)` and every direction `k < 8`. -/
theorem transOK_3_30 :
    allFrom 4002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4010, 4018)` and every direction `k < 8`. -/
theorem transOK_3_31 :
    allFrom 4010 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4018, 4026)` and every direction `k < 8`. -/
theorem transOK_3_32 :
    allFrom 4018 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4026, 4034)` and every direction `k < 8`. -/
theorem transOK_3_33 :
    allFrom 4026 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4034, 4042)` and every direction `k < 8`. -/
theorem transOK_3_34 :
    allFrom 4034 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4042, 4050)` and every direction `k < 8`. -/
theorem transOK_3_35 :
    allFrom 4042 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4050, 4058)` and every direction `k < 8`. -/
theorem transOK_3_36 :
    allFrom 4050 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4058, 4066)` and every direction `k < 8`. -/
theorem transOK_3_37 :
    allFrom 4058 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4066, 4074)` and every direction `k < 8`. -/
theorem transOK_3_38 :
    allFrom 4066 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4074, 4082)` and every direction `k < 8`. -/
theorem transOK_3_39 :
    allFrom 4074 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4082, 4090)` and every direction `k < 8`. -/
theorem transOK_3_40 :
    allFrom 4082 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4090, 4098)` and every direction `k < 8`. -/
theorem transOK_3_41 :
    allFrom 4090 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4098, 4106)` and every direction `k < 8`. -/
theorem transOK_3_42 :
    allFrom 4098 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4106, 4114)` and every direction `k < 8`. -/
theorem transOK_3_43 :
    allFrom 4106 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4114, 4122)` and every direction `k < 8`. -/
theorem transOK_3_44 :
    allFrom 4114 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4122, 4130)` and every direction `k < 8`. -/
theorem transOK_3_45 :
    allFrom 4122 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4130, 4138)` and every direction `k < 8`. -/
theorem transOK_3_46 :
    allFrom 4130 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4138, 4146)` and every direction `k < 8`. -/
theorem transOK_3_47 :
    allFrom 4138 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4146, 4154)` and every direction `k < 8`. -/
theorem transOK_3_48 :
    allFrom 4146 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4154, 4162)` and every direction `k < 8`. -/
theorem transOK_3_49 :
    allFrom 4154 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4162, 4170)` and every direction `k < 8`. -/
theorem transOK_3_50 :
    allFrom 4162 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4170, 4178)` and every direction `k < 8`. -/
theorem transOK_3_51 :
    allFrom 4170 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4178, 4186)` and every direction `k < 8`. -/
theorem transOK_3_52 :
    allFrom 4178 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4186, 4194)` and every direction `k < 8`. -/
theorem transOK_3_53 :
    allFrom 4186 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4194, 4202)` and every direction `k < 8`. -/
theorem transOK_3_54 :
    allFrom 4194 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4202, 4210)` and every direction `k < 8`. -/
theorem transOK_3_55 :
    allFrom 4202 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4210, 4218)` and every direction `k < 8`. -/
theorem transOK_3_56 :
    allFrom 4210 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4218, 4226)` and every direction `k < 8`. -/
theorem transOK_3_57 :
    allFrom 4218 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4226, 4234)` and every direction `k < 8`. -/
theorem transOK_3_58 :
    allFrom 4226 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4234, 4242)` and every direction `k < 8`. -/
theorem transOK_3_59 :
    allFrom 4234 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4242, 4250)` and every direction `k < 8`. -/
theorem transOK_3_60 :
    allFrom 4242 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4250, 4258)` and every direction `k < 8`. -/
theorem transOK_3_61 :
    allFrom 4250 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4258, 4266)` and every direction `k < 8`. -/
theorem transOK_3_62 :
    allFrom 4258 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4266, 4274)` and every direction `k < 8`. -/
theorem transOK_3_63 :
    allFrom 4266 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4274, 4282)` and every direction `k < 8`. -/
theorem transOK_3_64 :
    allFrom 4274 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4282, 4290)` and every direction `k < 8`. -/
theorem transOK_3_65 :
    allFrom 4282 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4290, 4298)` and every direction `k < 8`. -/
theorem transOK_3_66 :
    allFrom 4290 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4298, 4306)` and every direction `k < 8`. -/
theorem transOK_3_67 :
    allFrom 4298 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4306, 4314)` and every direction `k < 8`. -/
theorem transOK_3_68 :
    allFrom 4306 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4314, 4322)` and every direction `k < 8`. -/
theorem transOK_3_69 :
    allFrom 4314 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4322, 4330)` and every direction `k < 8`. -/
theorem transOK_3_70 :
    allFrom 4322 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4330, 4338)` and every direction `k < 8`. -/
theorem transOK_3_71 :
    allFrom 4330 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4338, 4346)` and every direction `k < 8`. -/
theorem transOK_3_72 :
    allFrom 4338 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4346, 4354)` and every direction `k < 8`. -/
theorem transOK_3_73 :
    allFrom 4346 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4354, 4362)` and every direction `k < 8`. -/
theorem transOK_3_74 :
    allFrom 4354 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4362, 4370)` and every direction `k < 8`. -/
theorem transOK_3_75 :
    allFrom 4362 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4370, 4378)` and every direction `k < 8`. -/
theorem transOK_3_76 :
    allFrom 4370 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4378, 4386)` and every direction `k < 8`. -/
theorem transOK_3_77 :
    allFrom 4378 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4386, 4394)` and every direction `k < 8`. -/
theorem transOK_3_78 :
    allFrom 4386 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4394, 4402)` and every direction `k < 8`. -/
theorem transOK_3_79 :
    allFrom 4394 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4402, 4410)` and every direction `k < 8`. -/
theorem transOK_3_80 :
    allFrom 4402 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4410, 4418)` and every direction `k < 8`. -/
theorem transOK_3_81 :
    allFrom 4410 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4418, 4426)` and every direction `k < 8`. -/
theorem transOK_3_82 :
    allFrom 4418 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4426, 4434)` and every direction `k < 8`. -/
theorem transOK_3_83 :
    allFrom 4426 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4434, 4442)` and every direction `k < 8`. -/
theorem transOK_3_84 :
    allFrom 4434 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4442, 4450)` and every direction `k < 8`. -/
theorem transOK_3_85 :
    allFrom 4442 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4450, 4458)` and every direction `k < 8`. -/
theorem transOK_3_86 :
    allFrom 4450 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4458, 4466)` and every direction `k < 8`. -/
theorem transOK_3_87 :
    allFrom 4458 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4466, 4474)` and every direction `k < 8`. -/
theorem transOK_3_88 :
    allFrom 4466 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4474, 4482)` and every direction `k < 8`. -/
theorem transOK_3_89 :
    allFrom 4474 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4482, 4490)` and every direction `k < 8`. -/
theorem transOK_3_90 :
    allFrom 4482 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4490, 4498)` and every direction `k < 8`. -/
theorem transOK_3_91 :
    allFrom 4490 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4498, 4506)` and every direction `k < 8`. -/
theorem transOK_3_92 :
    allFrom 4498 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4506, 4514)` and every direction `k < 8`. -/
theorem transOK_3_93 :
    allFrom 4506 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4514, 4522)` and every direction `k < 8`. -/
theorem transOK_3_94 :
    allFrom 4514 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4522, 4530)` and every direction `k < 8`. -/
theorem transOK_3_95 :
    allFrom 4522 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4530, 4538)` and every direction `k < 8`. -/
theorem transOK_3_96 :
    allFrom 4530 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4538, 4546)` and every direction `k < 8`. -/
theorem transOK_3_97 :
    allFrom 4538 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4546, 4554)` and every direction `k < 8`. -/
theorem transOK_3_98 :
    allFrom 4546 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4554, 4562)` and every direction `k < 8`. -/
theorem transOK_3_99 :
    allFrom 4554 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4562, 4570)` and every direction `k < 8`. -/
theorem transOK_3_100 :
    allFrom 4562 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4570, 4578)` and every direction `k < 8`. -/
theorem transOK_3_101 :
    allFrom 4570 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4578, 4586)` and every direction `k < 8`. -/
theorem transOK_3_102 :
    allFrom 4578 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4586, 4594)` and every direction `k < 8`. -/
theorem transOK_3_103 :
    allFrom 4586 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4594, 4602)` and every direction `k < 8`. -/
theorem transOK_3_104 :
    allFrom 4594 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4602, 4610)` and every direction `k < 8`. -/
theorem transOK_3_105 :
    allFrom 4602 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4610, 4618)` and every direction `k < 8`. -/
theorem transOK_3_106 :
    allFrom 4610 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4618, 4626)` and every direction `k < 8`. -/
theorem transOK_3_107 :
    allFrom 4618 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4626, 4634)` and every direction `k < 8`. -/
theorem transOK_3_108 :
    allFrom 4626 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4634, 4642)` and every direction `k < 8`. -/
theorem transOK_3_109 :
    allFrom 4634 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4642, 4650)` and every direction `k < 8`. -/
theorem transOK_3_110 :
    allFrom 4642 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4650, 4658)` and every direction `k < 8`. -/
theorem transOK_3_111 :
    allFrom 4650 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4658, 4666)` and every direction `k < 8`. -/
theorem transOK_3_112 :
    allFrom 4658 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4666, 4674)` and every direction `k < 8`. -/
theorem transOK_3_113 :
    allFrom 4666 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4674, 4682)` and every direction `k < 8`. -/
theorem transOK_3_114 :
    allFrom 4674 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4682, 4690)` and every direction `k < 8`. -/
theorem transOK_3_115 :
    allFrom 4682 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4690, 4698)` and every direction `k < 8`. -/
theorem transOK_3_116 :
    allFrom 4690 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4698, 4706)` and every direction `k < 8`. -/
theorem transOK_3_117 :
    allFrom 4698 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4706, 4714)` and every direction `k < 8`. -/
theorem transOK_3_118 :
    allFrom 4706 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4714, 4722)` and every direction `k < 8`. -/
theorem transOK_3_119 :
    allFrom 4714 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4722, 4730)` and every direction `k < 8`. -/
theorem transOK_3_120 :
    allFrom 4722 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4730, 4738)` and every direction `k < 8`. -/
theorem transOK_3_121 :
    allFrom 4730 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4738, 4746)` and every direction `k < 8`. -/
theorem transOK_3_122 :
    allFrom 4738 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4746, 4754)` and every direction `k < 8`. -/
theorem transOK_3_123 :
    allFrom 4746 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4754, 4762)` and every direction `k < 8`. -/
theorem transOK_3_124 :
    allFrom 4754 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4762, 4770)` and every direction `k < 8`. -/
theorem transOK_3_125 :
    allFrom 4762 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4770, 4778)` and every direction `k < 8`. -/
theorem transOK_3_126 :
    allFrom 4770 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4778, 4786)` and every direction `k < 8`. -/
theorem transOK_3_127 :
    allFrom 4778 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4786, 4794)` and every direction `k < 8`. -/
theorem transOK_3_128 :
    allFrom 4786 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4794, 4802)` and every direction `k < 8`. -/
theorem transOK_3_129 :
    allFrom 4794 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4802, 4810)` and every direction `k < 8`. -/
theorem transOK_3_130 :
    allFrom 4802 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4810, 4818)` and every direction `k < 8`. -/
theorem transOK_3_131 :
    allFrom 4810 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4818, 4826)` and every direction `k < 8`. -/
theorem transOK_3_132 :
    allFrom 4818 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4826, 4834)` and every direction `k < 8`. -/
theorem transOK_3_133 :
    allFrom 4826 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4834, 4842)` and every direction `k < 8`. -/
theorem transOK_3_134 :
    allFrom 4834 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4842, 4850)` and every direction `k < 8`. -/
theorem transOK_3_135 :
    allFrom 4842 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4850, 4858)` and every direction `k < 8`. -/
theorem transOK_3_136 :
    allFrom 4850 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4858, 4866)` and every direction `k < 8`. -/
theorem transOK_3_137 :
    allFrom 4858 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4866, 4874)` and every direction `k < 8`. -/
theorem transOK_3_138 :
    allFrom 4866 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4874, 4882)` and every direction `k < 8`. -/
theorem transOK_3_139 :
    allFrom 4874 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4882, 4890)` and every direction `k < 8`. -/
theorem transOK_3_140 :
    allFrom 4882 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4890, 4898)` and every direction `k < 8`. -/
theorem transOK_3_141 :
    allFrom 4890 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4898, 4906)` and every direction `k < 8`. -/
theorem transOK_3_142 :
    allFrom 4898 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4906, 4914)` and every direction `k < 8`. -/
theorem transOK_3_143 :
    allFrom 4906 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4914, 4922)` and every direction `k < 8`. -/
theorem transOK_3_144 :
    allFrom 4914 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4922, 4930)` and every direction `k < 8`. -/
theorem transOK_3_145 :
    allFrom 4922 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4930, 4938)` and every direction `k < 8`. -/
theorem transOK_3_146 :
    allFrom 4930 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4938, 4946)` and every direction `k < 8`. -/
theorem transOK_3_147 :
    allFrom 4938 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4946, 4954)` and every direction `k < 8`. -/
theorem transOK_3_148 :
    allFrom 4946 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4954, 4962)` and every direction `k < 8`. -/
theorem transOK_3_149 :
    allFrom 4954 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4962, 4970)` and every direction `k < 8`. -/
theorem transOK_3_150 :
    allFrom 4962 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4970, 4978)` and every direction `k < 8`. -/
theorem transOK_3_151 :
    allFrom 4970 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4978, 4986)` and every direction `k < 8`. -/
theorem transOK_3_152 :
    allFrom 4978 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4986, 4994)` and every direction `k < 8`. -/
theorem transOK_3_153 :
    allFrom 4986 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[4994, 5002)` and every direction `k < 8`. -/
theorem transOK_3_154 :
    allFrom 4994 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[5002, 5010)` and every direction `k < 8`. -/
theorem transOK_3_155 :
    allFrom 5002 8 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[5010, 5016)` and every direction `k < 8`. -/
theorem transOK_3_156 :
    allFrom 5010 6 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true := by
  decide +kernel

/-- `raw.transOK` holds for every seed in `[3762, 5016)` and every direction `k < 8`. -/
theorem transOK_3 :
    allFrom 3762 1254 (fun a => allBelow 8 fun k => raw.transOK 8 8 128 25080 3120 a k) = true :=
  allFrom_add (a := 624) (b := 630)
      (allFrom_add (a := 312) (b := 312)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_0
                              transOK_3_1)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_2
                              transOK_3_3))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_4
                              transOK_3_5)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_6
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_7
                                  transOK_3_8))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_9
                              transOK_3_10)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_11
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_12
                                  transOK_3_13)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_14
                              transOK_3_15)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_16
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_17
                                  transOK_3_18)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_19
                              transOK_3_20)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_21
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_22
                                  transOK_3_23)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_24
                              transOK_3_25)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_26
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_27
                                  transOK_3_28))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_29
                              transOK_3_30)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_31
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_32
                                  transOK_3_33)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_34
                              transOK_3_35)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_36
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_37
                                  transOK_3_38))))))
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_39
                              transOK_3_40)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_41
                              transOK_3_42))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_43
                              transOK_3_44)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_45
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_46
                                  transOK_3_47))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_48
                              transOK_3_49)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_50
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_51
                                  transOK_3_52)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_53
                              transOK_3_54)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_55
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_56
                                  transOK_3_57)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_58
                              transOK_3_59)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_60
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_61
                                  transOK_3_62)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_63
                              transOK_3_64)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_65
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_66
                                  transOK_3_67))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_68
                              transOK_3_69)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_70
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_71
                                  transOK_3_72)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_73
                              transOK_3_74)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_75
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_76
                                  transOK_3_77)))))))
      (allFrom_add (a := 312) (b := 318)
          (allFrom_add (a := 152) (b := 160)
              (allFrom_add (a := 72) (b := 80)
                  (allFrom_add (a := 32) (b := 40)
                      (allFrom_add (a := 16) (b := 16)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_78
                              transOK_3_79)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_80
                              transOK_3_81))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_82
                              transOK_3_83)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_84
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_85
                                  transOK_3_86))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_87
                              transOK_3_88)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_89
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_90
                                  transOK_3_91)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_92
                              transOK_3_93)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_94
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_95
                                  transOK_3_96)))))
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_97
                              transOK_3_98)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_99
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_100
                                  transOK_3_101)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_102
                              transOK_3_103)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_104
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_105
                                  transOK_3_106))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_107
                              transOK_3_108)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_109
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_110
                                  transOK_3_111)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_112
                              transOK_3_113)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_114
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_115
                                  transOK_3_116))))))
          (allFrom_add (a := 160) (b := 158)
              (allFrom_add (a := 80) (b := 80)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_117
                              transOK_3_118)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_119
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_120
                                  transOK_3_121)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_122
                              transOK_3_123)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_124
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_125
                                  transOK_3_126))))
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_127
                              transOK_3_128)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_129
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_130
                                  transOK_3_131)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_132
                              transOK_3_133)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_134
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_135
                                  transOK_3_136)))))
              (allFrom_add (a := 80) (b := 78)
                  (allFrom_add (a := 40) (b := 40)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_137
                              transOK_3_138)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_139
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_140
                                  transOK_3_141)))
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_142
                              transOK_3_143)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_144
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_145
                                  transOK_3_146))))
                  (allFrom_add (a := 40) (b := 38)
                      (allFrom_add (a := 16) (b := 24)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_147
                              transOK_3_148)
                          (allFrom_add (a := 8) (b := 16)
                              transOK_3_149
                              (allFrom_add (a := 8) (b := 8)
                                  transOK_3_150
                                  transOK_3_151)))
                      (allFrom_add (a := 16) (b := 22)
                          (allFrom_add (a := 8) (b := 8)
                              transOK_3_152
                              transOK_3_153)
                          (allFrom_add (a := 8) (b := 14)
                              transOK_3_154
                              (allFrom_add (a := 8) (b := 6)
                                  transOK_3_155
                                  transOK_3_156)))))))

end ClusterAlgebras.CertificateData.E8

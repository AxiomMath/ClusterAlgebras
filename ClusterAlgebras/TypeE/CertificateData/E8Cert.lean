/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateDense
public import ClusterAlgebras.TypeE.CertificateData.E8Trans0
public import ClusterAlgebras.TypeE.CertificateData.E8Trans1
public import ClusterAlgebras.TypeE.CertificateData.E8Trans2
public import ClusterAlgebras.TypeE.CertificateData.E8Trans3
public import ClusterAlgebras.TypeE.CertificateData.E8Trans4
public import ClusterAlgebras.TypeE.CertificateData.E8Trans5
public import ClusterAlgebras.TypeE.CertificateData.E8Trans6
public import ClusterAlgebras.TypeE.CertificateData.E8Trans7
public import ClusterAlgebras.TypeE.CertificateData.E8Trans8
public import ClusterAlgebras.TypeE.CertificateData.E8Trans9
public import ClusterAlgebras.TypeE.CertificateData.E8Trans10
public import ClusterAlgebras.TypeE.CertificateData.E8Trans11
public import ClusterAlgebras.TypeE.CertificateData.E8Trans12
public import ClusterAlgebras.TypeE.CertificateData.E8Trans13
public import ClusterAlgebras.TypeE.CertificateData.E8Trans14
public import ClusterAlgebras.TypeE.CertificateData.E8Trans15
public import ClusterAlgebras.TypeE.CertificateData.E8Trans16
public import ClusterAlgebras.TypeE.CertificateData.E8Trans17
public import ClusterAlgebras.TypeE.CertificateData.E8Trans18
public import ClusterAlgebras.TypeE.CertificateData.E8Trans19
public import ClusterAlgebras.TypeE.CertificateData.E8Rel0
public import ClusterAlgebras.TypeE.CertificateData.E8Rel1
public import ClusterAlgebras.TypeE.CertificateData.E8Rel2
public import ClusterAlgebras.TypeE.CertificateData.E8Rel3
public import ClusterAlgebras.TypeE.CertificateData.E8Rel4
public import ClusterAlgebras.TypeE.CertificateData.E8Rel5

/-!
# The `E8` exchange certificate

Assembles the kernel checks of the `E8` data into an exchange certificate, through the
soundness theorem `CertificateCheck.Raw.nonempty_exchangeCertificate`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- The seed-indexed and pair-indexed checks are split into theorems of their own, so that the
-- kernel's caches are dropped between them; with `Elab.async`, the kernel checks would hold
-- their memory until the end of the file.
set_option Elab.async false

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The initial seed of `raw` passes the check `raw.initOK 8 8`. -/
theorem initOK : raw.initOK 8 8 = true := by decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_0 :
    allFrom 0 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_1 :
    allFrom 128 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_2 :
    allFrom 256 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_3 :
    allFrom 384 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_4 :
    allFrom 512 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_5 :
    allFrom 640 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_6 :
    allFrom 768 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_7 :
    allFrom 896 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_8 :
    allFrom 1024 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_9 :
    allFrom 1152 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_10 :
    allFrom 1280 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_11 :
    allFrom 1408 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_12 :
    allFrom 1536 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_13 :
    allFrom 1664 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_14 :
    allFrom 1792 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_15 :
    allFrom 1920 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_16 :
    allFrom 2048 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_17 :
    allFrom 2176 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_18 :
    allFrom 2304 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_19 :
    allFrom 2432 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_20 :
    allFrom 2560 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_21 :
    allFrom 2688 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_22 :
    allFrom 2816 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_23 :
    allFrom 2944 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_24 :
    allFrom 3072 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_25 :
    allFrom 3200 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_26 :
    allFrom 3328 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_27 :
    allFrom 3456 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_28 :
    allFrom 3584 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_29 :
    allFrom 3712 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_30 :
    allFrom 3840 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_31 :
    allFrom 3968 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_32 :
    allFrom 4096 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_33 :
    allFrom 4224 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_34 :
    allFrom 4352 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_35 :
    allFrom 4480 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_36 :
    allFrom 4608 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_37 :
    allFrom 4736 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_38 :
    allFrom 4864 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_39 :
    allFrom 4992 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_40 :
    allFrom 5120 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_41 :
    allFrom 5248 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_42 :
    allFrom 5376 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_43 :
    allFrom 5504 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_44 :
    allFrom 5632 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_45 :
    allFrom 5760 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_46 :
    allFrom 5888 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_47 :
    allFrom 6016 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_48 :
    allFrom 6144 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_49 :
    allFrom 6272 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_50 :
    allFrom 6400 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_51 :
    allFrom 6528 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_52 :
    allFrom 6656 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_53 :
    allFrom 6784 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_54 :
    allFrom 6912 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_55 :
    allFrom 7040 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_56 :
    allFrom 7168 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_57 :
    allFrom 7296 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_58 :
    allFrom 7424 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_59 :
    allFrom 7552 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_60 :
    allFrom 7680 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_61 :
    allFrom 7808 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_62 :
    allFrom 7936 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_63 :
    allFrom 8064 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_64 :
    allFrom 8192 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_65 :
    allFrom 8320 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_66 :
    allFrom 8448 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_67 :
    allFrom 8576 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_68 :
    allFrom 8704 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_69 :
    allFrom 8832 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_70 :
    allFrom 8960 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_71 :
    allFrom 9088 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_72 :
    allFrom 9216 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_73 :
    allFrom 9344 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_74 :
    allFrom 9472 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_75 :
    allFrom 9600 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_76 :
    allFrom 9728 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_77 :
    allFrom 9856 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_78 :
    allFrom 9984 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_79 :
    allFrom 10112 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_80 :
    allFrom 10240 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_81 :
    allFrom 10368 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_82 :
    allFrom 10496 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_83 :
    allFrom 10624 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_84 :
    allFrom 10752 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_85 :
    allFrom 10880 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_86 :
    allFrom 11008 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_87 :
    allFrom 11136 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_88 :
    allFrom 11264 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_89 :
    allFrom 11392 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_90 :
    allFrom 11520 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_91 :
    allFrom 11648 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_92 :
    allFrom 11776 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_93 :
    allFrom 11904 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_94 :
    allFrom 12032 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_95 :
    allFrom 12160 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_96 :
    allFrom 12288 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_97 :
    allFrom 12416 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_98 :
    allFrom 12544 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_99 :
    allFrom 12672 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_100 :
    allFrom 12800 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_101 :
    allFrom 12928 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_102 :
    allFrom 13056 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_103 :
    allFrom 13184 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_104 :
    allFrom 13312 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_105 :
    allFrom 13440 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_106 :
    allFrom 13568 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_107 :
    allFrom 13696 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_108 :
    allFrom 13824 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_109 :
    allFrom 13952 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_110 :
    allFrom 14080 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_111 :
    allFrom 14208 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_112 :
    allFrom 14336 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_113 :
    allFrom 14464 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_114 :
    allFrom 14592 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_115 :
    allFrom 14720 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_116 :
    allFrom 14848 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_117 :
    allFrom 14976 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_118 :
    allFrom 15104 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_119 :
    allFrom 15232 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_120 :
    allFrom 15360 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_121 :
    allFrom 15488 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_122 :
    allFrom 15616 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_123 :
    allFrom 15744 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_124 :
    allFrom 15872 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_125 :
    allFrom 16000 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_126 :
    allFrom 16128 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_127 :
    allFrom 16256 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_128 :
    allFrom 16384 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_129 :
    allFrom 16512 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_130 :
    allFrom 16640 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_131 :
    allFrom 16768 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_132 :
    allFrom 16896 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_133 :
    allFrom 17024 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_134 :
    allFrom 17152 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_135 :
    allFrom 17280 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_136 :
    allFrom 17408 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_137 :
    allFrom 17536 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_138 :
    allFrom 17664 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_139 :
    allFrom 17792 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_140 :
    allFrom 17920 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_141 :
    allFrom 18048 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_142 :
    allFrom 18176 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_143 :
    allFrom 18304 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_144 :
    allFrom 18432 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_145 :
    allFrom 18560 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_146 :
    allFrom 18688 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_147 :
    allFrom 18816 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_148 :
    allFrom 18944 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_149 :
    allFrom 19072 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_150 :
    allFrom 19200 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_151 :
    allFrom 19328 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_152 :
    allFrom 19456 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_153 :
    allFrom 19584 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_154 :
    allFrom 19712 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_155 :
    allFrom 19840 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_156 :
    allFrom 19968 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_157 :
    allFrom 20096 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_158 :
    allFrom 20224 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_159 :
    allFrom 20352 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_160 :
    allFrom 20480 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_161 :
    allFrom 20608 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_162 :
    allFrom 20736 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_163 :
    allFrom 20864 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_164 :
    allFrom 20992 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_165 :
    allFrom 21120 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_166 :
    allFrom 21248 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_167 :
    allFrom 21376 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_168 :
    allFrom 21504 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_169 :
    allFrom 21632 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_170 :
    allFrom 21760 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_171 :
    allFrom 21888 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_172 :
    allFrom 22016 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_173 :
    allFrom 22144 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_174 :
    allFrom 22272 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_175 :
    allFrom 22400 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_176 :
    allFrom 22528 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_177 :
    allFrom 22656 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_178 :
    allFrom 22784 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_179 :
    allFrom 22912 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_180 :
    allFrom 23040 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_181 :
    allFrom 23168 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_182 :
    allFrom 23296 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_183 :
    allFrom 23424 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_184 :
    allFrom 23552 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_185 :
    allFrom 23680 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_186 :
    allFrom 23808 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_187 :
    allFrom 23936 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_188 :
    allFrom 24064 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_189 :
    allFrom 24192 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_190 :
    allFrom 24320 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_191 :
    allFrom 24448 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_192 :
    allFrom 24576 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_193 :
    allFrom 24704 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_194 :
    allFrom 24832 128 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds on a block of consecutive seed indices. -/
theorem seedOK_195 :
    allFrom 24960 120 (fun a => raw.seedOK 8 128 a) = true := by
  decide +kernel

/-- The seed check `raw.seedOK 8 128` holds at every seed index below `25080`. -/
theorem seedOK :
    allFrom 0 25080 (fun a => raw.seedOK 8 128 a) = true :=
  allFrom_add (a := 12544) (b := 12536)
      (allFrom_add (a := 6272) (b := 6272)
          (allFrom_add (a := 3072) (b := 3200)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_0
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_1
                                  seedOK_2))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_3
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_4
                                  seedOK_5)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_6
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_7
                                  seedOK_8))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_9
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_10
                                  seedOK_11))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_12
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_13
                                  seedOK_14))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_15
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_16
                                  seedOK_17)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_18
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_19
                                  seedOK_20))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_21
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_22
                                  seedOK_23)))))
              (allFrom_add (a := 1536) (b := 1664)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_24
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_25
                                  seedOK_26))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_27
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_28
                                  seedOK_29)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_30
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_31
                                  seedOK_32))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_33
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_34
                                  seedOK_35))))
                  (allFrom_add (a := 768) (b := 896)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_36
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_37
                                  seedOK_38))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_39
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_40
                                  seedOK_41)))
                      (allFrom_add (a := 384) (b := 512)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_42
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_43
                                  seedOK_44))
                          (allFrom_add (a := 256) (b := 256)
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_45
                                  seedOK_46)
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_47
                                  seedOK_48))))))
          (allFrom_add (a := 3072) (b := 3200)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_49
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_50
                                  seedOK_51))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_52
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_53
                                  seedOK_54)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_55
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_56
                                  seedOK_57))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_58
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_59
                                  seedOK_60))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_61
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_62
                                  seedOK_63))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_64
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_65
                                  seedOK_66)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_67
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_68
                                  seedOK_69))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_70
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_71
                                  seedOK_72)))))
              (allFrom_add (a := 1536) (b := 1664)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_73
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_74
                                  seedOK_75))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_76
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_77
                                  seedOK_78)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_79
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_80
                                  seedOK_81))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_82
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_83
                                  seedOK_84))))
                  (allFrom_add (a := 768) (b := 896)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_85
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_86
                                  seedOK_87))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_88
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_89
                                  seedOK_90)))
                      (allFrom_add (a := 384) (b := 512)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_91
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_92
                                  seedOK_93))
                          (allFrom_add (a := 256) (b := 256)
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_94
                                  seedOK_95)
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_96
                                  seedOK_97)))))))
      (allFrom_add (a := 6272) (b := 6264)
          (allFrom_add (a := 3072) (b := 3200)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_98
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_99
                                  seedOK_100))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_101
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_102
                                  seedOK_103)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_104
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_105
                                  seedOK_106))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_107
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_108
                                  seedOK_109))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_110
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_111
                                  seedOK_112))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_113
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_114
                                  seedOK_115)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_116
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_117
                                  seedOK_118))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_119
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_120
                                  seedOK_121)))))
              (allFrom_add (a := 1536) (b := 1664)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_122
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_123
                                  seedOK_124))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_125
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_126
                                  seedOK_127)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_128
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_129
                                  seedOK_130))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_131
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_132
                                  seedOK_133))))
                  (allFrom_add (a := 768) (b := 896)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_134
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_135
                                  seedOK_136))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_137
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_138
                                  seedOK_139)))
                      (allFrom_add (a := 384) (b := 512)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_140
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_141
                                  seedOK_142))
                          (allFrom_add (a := 256) (b := 256)
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_143
                                  seedOK_144)
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_145
                                  seedOK_146))))))
          (allFrom_add (a := 3072) (b := 3192)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_147
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_148
                                  seedOK_149))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_150
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_151
                                  seedOK_152)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_153
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_154
                                  seedOK_155))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_156
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_157
                                  seedOK_158))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_159
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_160
                                  seedOK_161))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_162
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_163
                                  seedOK_164)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_165
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_166
                                  seedOK_167))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_168
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_169
                                  seedOK_170)))))
              (allFrom_add (a := 1536) (b := 1656)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_171
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_172
                                  seedOK_173))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_174
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_175
                                  seedOK_176)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_177
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_178
                                  seedOK_179))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_180
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_181
                                  seedOK_182))))
                  (allFrom_add (a := 768) (b := 888)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_183
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_184
                                  seedOK_185))
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_186
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_187
                                  seedOK_188)))
                      (allFrom_add (a := 384) (b := 504)
                          (allFrom_add (a := 128) (b := 256)
                              seedOK_189
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_190
                                  seedOK_191))
                          (allFrom_add (a := 256) (b := 248)
                              (allFrom_add (a := 128) (b := 128)
                                  seedOK_192
                                  seedOK_193)
                              (allFrom_add (a := 128) (b := 120)
                                  seedOK_194
                                  seedOK_195)))))))

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_0 :
    allFrom 0 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_1 :
    allFrom 128 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_2 :
    allFrom 256 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_3 :
    allFrom 384 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_4 :
    allFrom 512 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_5 :
    allFrom 640 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_6 :
    allFrom 768 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_7 :
    allFrom 896 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_8 :
    allFrom 1024 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_9 :
    allFrom 1152 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_10 :
    allFrom 1280 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_11 :
    allFrom 1408 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_12 :
    allFrom 1536 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_13 :
    allFrom 1664 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_14 :
    allFrom 1792 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_15 :
    allFrom 1920 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_16 :
    allFrom 2048 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_17 :
    allFrom 2176 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_18 :
    allFrom 2304 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_19 :
    allFrom 2432 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_20 :
    allFrom 2560 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_21 :
    allFrom 2688 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_22 :
    allFrom 2816 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_23 :
    allFrom 2944 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_24 :
    allFrom 3072 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_25 :
    allFrom 3200 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_26 :
    allFrom 3328 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_27 :
    allFrom 3456 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_28 :
    allFrom 3584 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_29 :
    allFrom 3712 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_30 :
    allFrom 3840 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_31 :
    allFrom 3968 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_32 :
    allFrom 4096 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_33 :
    allFrom 4224 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_34 :
    allFrom 4352 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_35 :
    allFrom 4480 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_36 :
    allFrom 4608 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_37 :
    allFrom 4736 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_38 :
    allFrom 4864 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_39 :
    allFrom 4992 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_40 :
    allFrom 5120 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_41 :
    allFrom 5248 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_42 :
    allFrom 5376 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_43 :
    allFrom 5504 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_44 :
    allFrom 5632 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_45 :
    allFrom 5760 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_46 :
    allFrom 5888 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_47 :
    allFrom 6016 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_48 :
    allFrom 6144 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_49 :
    allFrom 6272 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_50 :
    allFrom 6400 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_51 :
    allFrom 6528 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_52 :
    allFrom 6656 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_53 :
    allFrom 6784 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_54 :
    allFrom 6912 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_55 :
    allFrom 7040 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_56 :
    allFrom 7168 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_57 :
    allFrom 7296 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_58 :
    allFrom 7424 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_59 :
    allFrom 7552 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_60 :
    allFrom 7680 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_61 :
    allFrom 7808 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_62 :
    allFrom 7936 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_63 :
    allFrom 8064 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_64 :
    allFrom 8192 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_65 :
    allFrom 8320 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_66 :
    allFrom 8448 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_67 :
    allFrom 8576 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_68 :
    allFrom 8704 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_69 :
    allFrom 8832 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_70 :
    allFrom 8960 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_71 :
    allFrom 9088 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_72 :
    allFrom 9216 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_73 :
    allFrom 9344 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_74 :
    allFrom 9472 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_75 :
    allFrom 9600 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_76 :
    allFrom 9728 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_77 :
    allFrom 9856 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_78 :
    allFrom 9984 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_79 :
    allFrom 10112 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_80 :
    allFrom 10240 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_81 :
    allFrom 10368 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_82 :
    allFrom 10496 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_83 :
    allFrom 10624 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_84 :
    allFrom 10752 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_85 :
    allFrom 10880 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_86 :
    allFrom 11008 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_87 :
    allFrom 11136 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_88 :
    allFrom 11264 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_89 :
    allFrom 11392 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_90 :
    allFrom 11520 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_91 :
    allFrom 11648 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_92 :
    allFrom 11776 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_93 :
    allFrom 11904 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_94 :
    allFrom 12032 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_95 :
    allFrom 12160 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_96 :
    allFrom 12288 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_97 :
    allFrom 12416 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_98 :
    allFrom 12544 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_99 :
    allFrom 12672 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_100 :
    allFrom 12800 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_101 :
    allFrom 12928 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_102 :
    allFrom 13056 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_103 :
    allFrom 13184 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_104 :
    allFrom 13312 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_105 :
    allFrom 13440 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_106 :
    allFrom 13568 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_107 :
    allFrom 13696 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_108 :
    allFrom 13824 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_109 :
    allFrom 13952 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_110 :
    allFrom 14080 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_111 :
    allFrom 14208 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_112 :
    allFrom 14336 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_113 :
    allFrom 14464 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_114 :
    allFrom 14592 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_115 :
    allFrom 14720 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_116 :
    allFrom 14848 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_117 :
    allFrom 14976 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_118 :
    allFrom 15104 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_119 :
    allFrom 15232 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_120 :
    allFrom 15360 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_121 :
    allFrom 15488 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_122 :
    allFrom 15616 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_123 :
    allFrom 15744 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_124 :
    allFrom 15872 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_125 :
    allFrom 16000 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_126 :
    allFrom 16128 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_127 :
    allFrom 16256 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_128 :
    allFrom 16384 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_129 :
    allFrom 16512 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_130 :
    allFrom 16640 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_131 :
    allFrom 16768 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_132 :
    allFrom 16896 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_133 :
    allFrom 17024 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_134 :
    allFrom 17152 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_135 :
    allFrom 17280 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_136 :
    allFrom 17408 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_137 :
    allFrom 17536 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_138 :
    allFrom 17664 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_139 :
    allFrom 17792 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_140 :
    allFrom 17920 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_141 :
    allFrom 18048 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_142 :
    allFrom 18176 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_143 :
    allFrom 18304 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_144 :
    allFrom 18432 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_145 :
    allFrom 18560 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_146 :
    allFrom 18688 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_147 :
    allFrom 18816 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_148 :
    allFrom 18944 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_149 :
    allFrom 19072 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_150 :
    allFrom 19200 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_151 :
    allFrom 19328 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_152 :
    allFrom 19456 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_153 :
    allFrom 19584 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_154 :
    allFrom 19712 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_155 :
    allFrom 19840 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_156 :
    allFrom 19968 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_157 :
    allFrom 20096 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_158 :
    allFrom 20224 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_159 :
    allFrom 20352 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_160 :
    allFrom 20480 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_161 :
    allFrom 20608 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_162 :
    allFrom 20736 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_163 :
    allFrom 20864 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_164 :
    allFrom 20992 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_165 :
    allFrom 21120 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_166 :
    allFrom 21248 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_167 :
    allFrom 21376 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_168 :
    allFrom 21504 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_169 :
    allFrom 21632 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_170 :
    allFrom 21760 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_171 :
    allFrom 21888 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_172 :
    allFrom 22016 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_173 :
    allFrom 22144 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_174 :
    allFrom 22272 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_175 :
    allFrom 22400 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_176 :
    allFrom 22528 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_177 :
    allFrom 22656 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_178 :
    allFrom 22784 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_179 :
    allFrom 22912 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_180 :
    allFrom 23040 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_181 :
    allFrom 23168 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_182 :
    allFrom 23296 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_183 :
    allFrom 23424 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_184 :
    allFrom 23552 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_185 :
    allFrom 23680 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_186 :
    allFrom 23808 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_187 :
    allFrom 23936 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_188 :
    allFrom 24064 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_189 :
    allFrom 24192 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_190 :
    allFrom 24320 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_191 :
    allFrom 24448 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_192 :
    allFrom 24576 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_193 :
    allFrom 24704 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_194 :
    allFrom 24832 128 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds on a block of consecutive seed indices. -/
theorem lexOK_195 :
    allFrom 24960 119 (fun a => raw.lexOK 8 128 a) = true := by
  decide +kernel

/-- The ordering check `raw.lexOK 8 128` holds at every seed index below `25079`. -/
theorem lexOK :
    allFrom 0 25079 (fun a => raw.lexOK 8 128 a) = true :=
  allFrom_add (a := 12544) (b := 12535)
      (allFrom_add (a := 6272) (b := 6272)
          (allFrom_add (a := 3072) (b := 3200)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_0
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_1
                                  lexOK_2))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_3
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_4
                                  lexOK_5)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_6
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_7
                                  lexOK_8))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_9
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_10
                                  lexOK_11))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_12
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_13
                                  lexOK_14))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_15
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_16
                                  lexOK_17)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_18
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_19
                                  lexOK_20))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_21
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_22
                                  lexOK_23)))))
              (allFrom_add (a := 1536) (b := 1664)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_24
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_25
                                  lexOK_26))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_27
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_28
                                  lexOK_29)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_30
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_31
                                  lexOK_32))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_33
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_34
                                  lexOK_35))))
                  (allFrom_add (a := 768) (b := 896)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_36
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_37
                                  lexOK_38))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_39
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_40
                                  lexOK_41)))
                      (allFrom_add (a := 384) (b := 512)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_42
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_43
                                  lexOK_44))
                          (allFrom_add (a := 256) (b := 256)
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_45
                                  lexOK_46)
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_47
                                  lexOK_48))))))
          (allFrom_add (a := 3072) (b := 3200)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_49
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_50
                                  lexOK_51))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_52
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_53
                                  lexOK_54)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_55
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_56
                                  lexOK_57))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_58
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_59
                                  lexOK_60))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_61
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_62
                                  lexOK_63))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_64
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_65
                                  lexOK_66)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_67
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_68
                                  lexOK_69))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_70
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_71
                                  lexOK_72)))))
              (allFrom_add (a := 1536) (b := 1664)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_73
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_74
                                  lexOK_75))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_76
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_77
                                  lexOK_78)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_79
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_80
                                  lexOK_81))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_82
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_83
                                  lexOK_84))))
                  (allFrom_add (a := 768) (b := 896)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_85
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_86
                                  lexOK_87))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_88
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_89
                                  lexOK_90)))
                      (allFrom_add (a := 384) (b := 512)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_91
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_92
                                  lexOK_93))
                          (allFrom_add (a := 256) (b := 256)
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_94
                                  lexOK_95)
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_96
                                  lexOK_97)))))))
      (allFrom_add (a := 6272) (b := 6263)
          (allFrom_add (a := 3072) (b := 3200)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_98
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_99
                                  lexOK_100))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_101
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_102
                                  lexOK_103)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_104
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_105
                                  lexOK_106))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_107
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_108
                                  lexOK_109))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_110
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_111
                                  lexOK_112))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_113
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_114
                                  lexOK_115)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_116
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_117
                                  lexOK_118))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_119
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_120
                                  lexOK_121)))))
              (allFrom_add (a := 1536) (b := 1664)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_122
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_123
                                  lexOK_124))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_125
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_126
                                  lexOK_127)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_128
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_129
                                  lexOK_130))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_131
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_132
                                  lexOK_133))))
                  (allFrom_add (a := 768) (b := 896)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_134
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_135
                                  lexOK_136))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_137
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_138
                                  lexOK_139)))
                      (allFrom_add (a := 384) (b := 512)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_140
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_141
                                  lexOK_142))
                          (allFrom_add (a := 256) (b := 256)
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_143
                                  lexOK_144)
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_145
                                  lexOK_146))))))
          (allFrom_add (a := 3072) (b := 3191)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_147
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_148
                                  lexOK_149))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_150
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_151
                                  lexOK_152)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_153
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_154
                                  lexOK_155))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_156
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_157
                                  lexOK_158))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_159
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_160
                                  lexOK_161))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_162
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_163
                                  lexOK_164)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_165
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_166
                                  lexOK_167))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_168
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_169
                                  lexOK_170)))))
              (allFrom_add (a := 1536) (b := 1655)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_171
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_172
                                  lexOK_173))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_174
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_175
                                  lexOK_176)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_177
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_178
                                  lexOK_179))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_180
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_181
                                  lexOK_182))))
                  (allFrom_add (a := 768) (b := 887)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_183
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_184
                                  lexOK_185))
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_186
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_187
                                  lexOK_188)))
                      (allFrom_add (a := 384) (b := 503)
                          (allFrom_add (a := 128) (b := 256)
                              lexOK_189
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_190
                                  lexOK_191))
                          (allFrom_add (a := 256) (b := 247)
                              (allFrom_add (a := 128) (b := 128)
                                  lexOK_192
                                  lexOK_193)
                              (allFrom_add (a := 128) (b := 119)
                                  lexOK_194
                                  lexOK_195)))))))

-- The variables are told apart by their values at `Xᵢ = 2^(2^i)`, each computed once.
/-- Any two distinct variable codes below `128` pass the distinctness check `distOKD`. -/
theorem distOK :
    allBelow 128 (fun c' => allBelow c' fun c =>
      distOKD (fun c => varList.getD c []) 8 1 (fun i => Nat.pow 2 i) c c') = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The cover check `raw.coverOK 8 25080` holds for every variable code below `128`. -/
theorem coverOK : allBelow 128 (raw.coverOK 8 25080) = true := by decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_0 :
    allFrom 0 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_1 :
    allFrom 128 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_2 :
    allFrom 256 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_3 :
    allFrom 384 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_4 :
    allFrom 512 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_5 :
    allFrom 640 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_6 :
    allFrom 768 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_7 :
    allFrom 896 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_8 :
    allFrom 1024 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_9 :
    allFrom 1152 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_10 :
    allFrom 1280 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_11 :
    allFrom 1408 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_12 :
    allFrom 1536 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_13 :
    allFrom 1664 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_14 :
    allFrom 1792 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_15 :
    allFrom 1920 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_16 :
    allFrom 2048 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_17 :
    allFrom 2176 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_18 :
    allFrom 2304 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_19 :
    allFrom 2432 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_20 :
    allFrom 2560 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_21 :
    allFrom 2688 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_22 :
    allFrom 2816 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_23 :
    allFrom 2944 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_24 :
    allFrom 3072 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_25 :
    allFrom 3200 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_26 :
    allFrom 3328 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_27 :
    allFrom 3456 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_28 :
    allFrom 3584 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_29 :
    allFrom 3712 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_30 :
    allFrom 3840 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_31 :
    allFrom 3968 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_32 :
    allFrom 4096 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_33 :
    allFrom 4224 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_34 :
    allFrom 4352 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_35 :
    allFrom 4480 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_36 :
    allFrom 4608 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_37 :
    allFrom 4736 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_38 :
    allFrom 4864 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_39 :
    allFrom 4992 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_40 :
    allFrom 5120 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_41 :
    allFrom 5248 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_42 :
    allFrom 5376 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_43 :
    allFrom 5504 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_44 :
    allFrom 5632 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_45 :
    allFrom 5760 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_46 :
    allFrom 5888 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_47 :
    allFrom 6016 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_48 :
    allFrom 6144 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_49 :
    allFrom 6272 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_50 :
    allFrom 6400 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_51 :
    allFrom 6528 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_52 :
    allFrom 6656 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_53 :
    allFrom 6784 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_54 :
    allFrom 6912 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_55 :
    allFrom 7040 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_56 :
    allFrom 7168 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_57 :
    allFrom 7296 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_58 :
    allFrom 7424 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_59 :
    allFrom 7552 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_60 :
    allFrom 7680 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_61 :
    allFrom 7808 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_62 :
    allFrom 7936 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_63 :
    allFrom 8064 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_64 :
    allFrom 8192 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_65 :
    allFrom 8320 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_66 :
    allFrom 8448 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_67 :
    allFrom 8576 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_68 :
    allFrom 8704 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_69 :
    allFrom 8832 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_70 :
    allFrom 8960 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_71 :
    allFrom 9088 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_72 :
    allFrom 9216 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_73 :
    allFrom 9344 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_74 :
    allFrom 9472 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_75 :
    allFrom 9600 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_76 :
    allFrom 9728 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_77 :
    allFrom 9856 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_78 :
    allFrom 9984 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_79 :
    allFrom 10112 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_80 :
    allFrom 10240 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_81 :
    allFrom 10368 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_82 :
    allFrom 10496 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_83 :
    allFrom 10624 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_84 :
    allFrom 10752 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_85 :
    allFrom 10880 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_86 :
    allFrom 11008 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_87 :
    allFrom 11136 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_88 :
    allFrom 11264 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_89 :
    allFrom 11392 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_90 :
    allFrom 11520 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_91 :
    allFrom 11648 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_92 :
    allFrom 11776 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_93 :
    allFrom 11904 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_94 :
    allFrom 12032 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_95 :
    allFrom 12160 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_96 :
    allFrom 12288 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_97 :
    allFrom 12416 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_98 :
    allFrom 12544 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_99 :
    allFrom 12672 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_100 :
    allFrom 12800 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_101 :
    allFrom 12928 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_102 :
    allFrom 13056 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_103 :
    allFrom 13184 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_104 :
    allFrom 13312 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_105 :
    allFrom 13440 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_106 :
    allFrom 13568 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_107 :
    allFrom 13696 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_108 :
    allFrom 13824 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_109 :
    allFrom 13952 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_110 :
    allFrom 14080 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_111 :
    allFrom 14208 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_112 :
    allFrom 14336 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_113 :
    allFrom 14464 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_114 :
    allFrom 14592 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_115 :
    allFrom 14720 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_116 :
    allFrom 14848 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_117 :
    allFrom 14976 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_118 :
    allFrom 15104 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_119 :
    allFrom 15232 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_120 :
    allFrom 15360 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_121 :
    allFrom 15488 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_122 :
    allFrom 15616 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_123 :
    allFrom 15744 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_124 :
    allFrom 15872 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_125 :
    allFrom 16000 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_126 :
    allFrom 16128 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_127 :
    allFrom 16256 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_128 :
    allFrom 16384 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_129 :
    allFrom 16512 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_130 :
    allFrom 16640 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_131 :
    allFrom 16768 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_132 :
    allFrom 16896 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_133 :
    allFrom 17024 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_134 :
    allFrom 17152 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_135 :
    allFrom 17280 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_136 :
    allFrom 17408 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_137 :
    allFrom 17536 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_138 :
    allFrom 17664 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_139 :
    allFrom 17792 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_140 :
    allFrom 17920 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_141 :
    allFrom 18048 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_142 :
    allFrom 18176 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_143 :
    allFrom 18304 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_144 :
    allFrom 18432 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_145 :
    allFrom 18560 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_146 :
    allFrom 18688 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_147 :
    allFrom 18816 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_148 :
    allFrom 18944 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_149 :
    allFrom 19072 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_150 :
    allFrom 19200 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_151 :
    allFrom 19328 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_152 :
    allFrom 19456 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_153 :
    allFrom 19584 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_154 :
    allFrom 19712 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_155 :
    allFrom 19840 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_156 :
    allFrom 19968 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_157 :
    allFrom 20096 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_158 :
    allFrom 20224 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_159 :
    allFrom 20352 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_160 :
    allFrom 20480 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_161 :
    allFrom 20608 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_162 :
    allFrom 20736 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_163 :
    allFrom 20864 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_164 :
    allFrom 20992 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_165 :
    allFrom 21120 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_166 :
    allFrom 21248 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_167 :
    allFrom 21376 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_168 :
    allFrom 21504 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_169 :
    allFrom 21632 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_170 :
    allFrom 21760 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_171 :
    allFrom 21888 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_172 :
    allFrom 22016 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_173 :
    allFrom 22144 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_174 :
    allFrom 22272 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_175 :
    allFrom 22400 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_176 :
    allFrom 22528 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_177 :
    allFrom 22656 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_178 :
    allFrom 22784 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_179 :
    allFrom 22912 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_180 :
    allFrom 23040 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_181 :
    allFrom 23168 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_182 :
    allFrom 23296 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_183 :
    allFrom 23424 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_184 :
    allFrom 23552 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_185 :
    allFrom 23680 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_186 :
    allFrom 23808 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_187 :
    allFrom 23936 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_188 :
    allFrom 24064 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_189 :
    allFrom 24192 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_190 :
    allFrom 24320 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_191 :
    allFrom 24448 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_192 :
    allFrom 24576 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_193 :
    allFrom 24704 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_194 :
    allFrom 24832 128 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds on a block of consecutive seed indices. -/
theorem treeOK_195 :
    allFrom 24960 120 (fun a => raw.treeOK 8 25080 a) = true := by
  decide +kernel

/-- The tree check `raw.treeOK 8 25080` holds at every seed index below `25080`. -/
theorem treeOK :
    allFrom 0 25080 (fun a => raw.treeOK 8 25080 a) = true :=
  allFrom_add (a := 12544) (b := 12536)
      (allFrom_add (a := 6272) (b := 6272)
          (allFrom_add (a := 3072) (b := 3200)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_0
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_1
                                  treeOK_2))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_3
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_4
                                  treeOK_5)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_6
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_7
                                  treeOK_8))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_9
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_10
                                  treeOK_11))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_12
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_13
                                  treeOK_14))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_15
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_16
                                  treeOK_17)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_18
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_19
                                  treeOK_20))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_21
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_22
                                  treeOK_23)))))
              (allFrom_add (a := 1536) (b := 1664)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_24
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_25
                                  treeOK_26))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_27
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_28
                                  treeOK_29)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_30
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_31
                                  treeOK_32))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_33
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_34
                                  treeOK_35))))
                  (allFrom_add (a := 768) (b := 896)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_36
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_37
                                  treeOK_38))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_39
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_40
                                  treeOK_41)))
                      (allFrom_add (a := 384) (b := 512)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_42
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_43
                                  treeOK_44))
                          (allFrom_add (a := 256) (b := 256)
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_45
                                  treeOK_46)
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_47
                                  treeOK_48))))))
          (allFrom_add (a := 3072) (b := 3200)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_49
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_50
                                  treeOK_51))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_52
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_53
                                  treeOK_54)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_55
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_56
                                  treeOK_57))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_58
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_59
                                  treeOK_60))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_61
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_62
                                  treeOK_63))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_64
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_65
                                  treeOK_66)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_67
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_68
                                  treeOK_69))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_70
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_71
                                  treeOK_72)))))
              (allFrom_add (a := 1536) (b := 1664)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_73
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_74
                                  treeOK_75))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_76
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_77
                                  treeOK_78)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_79
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_80
                                  treeOK_81))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_82
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_83
                                  treeOK_84))))
                  (allFrom_add (a := 768) (b := 896)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_85
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_86
                                  treeOK_87))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_88
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_89
                                  treeOK_90)))
                      (allFrom_add (a := 384) (b := 512)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_91
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_92
                                  treeOK_93))
                          (allFrom_add (a := 256) (b := 256)
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_94
                                  treeOK_95)
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_96
                                  treeOK_97)))))))
      (allFrom_add (a := 6272) (b := 6264)
          (allFrom_add (a := 3072) (b := 3200)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_98
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_99
                                  treeOK_100))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_101
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_102
                                  treeOK_103)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_104
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_105
                                  treeOK_106))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_107
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_108
                                  treeOK_109))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_110
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_111
                                  treeOK_112))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_113
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_114
                                  treeOK_115)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_116
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_117
                                  treeOK_118))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_119
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_120
                                  treeOK_121)))))
              (allFrom_add (a := 1536) (b := 1664)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_122
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_123
                                  treeOK_124))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_125
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_126
                                  treeOK_127)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_128
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_129
                                  treeOK_130))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_131
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_132
                                  treeOK_133))))
                  (allFrom_add (a := 768) (b := 896)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_134
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_135
                                  treeOK_136))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_137
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_138
                                  treeOK_139)))
                      (allFrom_add (a := 384) (b := 512)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_140
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_141
                                  treeOK_142))
                          (allFrom_add (a := 256) (b := 256)
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_143
                                  treeOK_144)
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_145
                                  treeOK_146))))))
          (allFrom_add (a := 3072) (b := 3192)
              (allFrom_add (a := 1536) (b := 1536)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_147
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_148
                                  treeOK_149))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_150
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_151
                                  treeOK_152)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_153
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_154
                                  treeOK_155))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_156
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_157
                                  treeOK_158))))
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_159
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_160
                                  treeOK_161))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_162
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_163
                                  treeOK_164)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_165
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_166
                                  treeOK_167))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_168
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_169
                                  treeOK_170)))))
              (allFrom_add (a := 1536) (b := 1656)
                  (allFrom_add (a := 768) (b := 768)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_171
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_172
                                  treeOK_173))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_174
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_175
                                  treeOK_176)))
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_177
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_178
                                  treeOK_179))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_180
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_181
                                  treeOK_182))))
                  (allFrom_add (a := 768) (b := 888)
                      (allFrom_add (a := 384) (b := 384)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_183
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_184
                                  treeOK_185))
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_186
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_187
                                  treeOK_188)))
                      (allFrom_add (a := 384) (b := 504)
                          (allFrom_add (a := 128) (b := 256)
                              treeOK_189
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_190
                                  treeOK_191))
                          (allFrom_add (a := 256) (b := 248)
                              (allFrom_add (a := 128) (b := 128)
                                  treeOK_192
                                  treeOK_193)
                              (allFrom_add (a := 128) (b := 120)
                                  treeOK_194
                                  treeOK_195)))))))

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The shape check `raw.relShapeOK` holds for every relation index below `3120`. -/
theorem relShapeOK : allBelow 3120 raw.relShapeOK = true := by decide +kernel

/-- The initial matrix of the certificate. -/
noncomputable def initMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j => raw.entry 0 i j

/-- There is an exchange certificate for `initMatrix` with `128` variables and `25080` seeds. -/
theorem nonempty_exchangeCertificate (hmn : 8 ≤ 8) :
    Nonempty (ExchangeCertificate hmn initMatrix 128 25080) := by
  refine Raw.nonempty_exchangeCertificate (numRel := 3120) hmn initMatrix raw (by decide)
    (by decide) initOK (fun _ _ => rfl) (by decide) (fun _ _ _ => Nat.mod_lt _ (by decide))
    (fun a ha => allFrom_iff.1 seedOK a (Nat.zero_le _) (by omega))
    (fun a ha => allFrom_iff.1 lexOK a (Nat.zero_le _) (by omega)) ?_ ?_
    (fun r hr => allBelow_iff.1 relShapeOK r hr)
    (fun c' hc' c hc =>
      toL_codes_ne_of_distOKD (allBelow_iff.1 (allBelow_iff.1 distOK c' hc') c hc))
    (fun c hc => allBelow_iff.1 coverOK c hc)
    (fun a ha => allFrom_iff.1 treeOK a (Nat.zero_le _) (by omega))
  · intro a ha k hk
    refine allBelow_iff.1 ?_ k hk
    have h :=
      allFrom_add (a := 1254) (b := 23826) transOK_0
        (allFrom_add (a := 1254) (b := 22572) transOK_1
          (allFrom_add (a := 1254) (b := 21318) transOK_2
            (allFrom_add (a := 1254) (b := 20064) transOK_3
              (allFrom_add (a := 1254) (b := 18810) transOK_4
                (allFrom_add (a := 1254) (b := 17556) transOK_5
                  (allFrom_add (a := 1254) (b := 16302) transOK_6
                    (allFrom_add (a := 1254) (b := 15048) transOK_7
                      (allFrom_add (a := 1254) (b := 13794) transOK_8
                        (allFrom_add (a := 1254) (b := 12540) transOK_9
                          (allFrom_add (a := 1254) (b := 11286) transOK_10
                            (allFrom_add (a := 1254) (b := 10032) transOK_11
                              (allFrom_add (a := 1254) (b := 8778) transOK_12
                                (allFrom_add (a := 1254) (b := 7524) transOK_13
                                  (allFrom_add (a := 1254) (b := 6270) transOK_14
                                    (allFrom_add (a := 1254) (b := 5016) transOK_15
                                      (allFrom_add (a := 1254) (b := 3762) transOK_16
                                        (allFrom_add (a := 1254) (b := 2508) transOK_17
                                          (allFrom_add (a := 1254) (b := 1254) transOK_18
                                            transOK_19))))))))))))))))))
    exact allFrom_iff.1 h a (Nat.zero_le _) (by omega)
  · intro r hr
    refine Raw.toL_relOKD (codes := fun c => varList.getD c []) (fun _ _ => rfl) ?_
    have h :=
      allFrom_add (a := 1047) (b := 2073) relOK_0
        (allFrom_add (a := 837) (b := 1236) relOK_1
          (allFrom_add (a := 678) (b := 558) relOK_2
            (allFrom_add (a := 302) (b := 256) relOK_3
              (allFrom_add (a := 225) (b := 31) relOK_4
                relOK_5))))
    exact allFrom_iff.1 h r (Nat.zero_le _) (by omega)

end ClusterAlgebras.CertificateData.E8

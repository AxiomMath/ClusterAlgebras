/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7

/-! # Kernel check of the exchange relations `[0, 808)` of the `E7` certificate,
in pieces of `16` relations assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relations with indices in `[0, 16)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_0 :
    allFrom 0 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[16, 32)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_1 :
    allFrom 16 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[32, 48)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_2 :
    allFrom 32 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[48, 64)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_3 :
    allFrom 48 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[64, 80)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_4 :
    allFrom 64 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[80, 96)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_5 :
    allFrom 80 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[96, 112)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_6 :
    allFrom 96 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[112, 128)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_7 :
    allFrom 112 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[128, 144)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_8 :
    allFrom 128 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[144, 160)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_9 :
    allFrom 144 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[160, 176)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_10 :
    allFrom 160 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[176, 192)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_11 :
    allFrom 176 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[192, 208)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_12 :
    allFrom 192 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[208, 224)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_13 :
    allFrom 208 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[224, 240)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_14 :
    allFrom 224 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[240, 256)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_15 :
    allFrom 240 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[256, 272)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_16 :
    allFrom 256 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[272, 288)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_17 :
    allFrom 272 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[288, 304)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_18 :
    allFrom 288 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[304, 320)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_19 :
    allFrom 304 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[320, 336)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_20 :
    allFrom 320 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[336, 352)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_21 :
    allFrom 336 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[352, 368)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_22 :
    allFrom 352 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[368, 384)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_23 :
    allFrom 368 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[384, 400)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_24 :
    allFrom 384 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[400, 416)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_25 :
    allFrom 400 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[416, 432)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_26 :
    allFrom 416 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[432, 448)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_27 :
    allFrom 432 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[448, 464)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_28 :
    allFrom 448 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[464, 480)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_29 :
    allFrom 464 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[480, 496)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_30 :
    allFrom 480 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[496, 512)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_31 :
    allFrom 496 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[512, 528)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_32 :
    allFrom 512 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[528, 544)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_33 :
    allFrom 528 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[544, 560)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_34 :
    allFrom 544 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[560, 576)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_35 :
    allFrom 560 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[576, 592)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_36 :
    allFrom 576 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[592, 608)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_37 :
    allFrom 592 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[608, 624)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_38 :
    allFrom 608 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[624, 640)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_39 :
    allFrom 624 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[640, 656)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_40 :
    allFrom 640 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[656, 672)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_41 :
    allFrom 656 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[672, 688)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_42 :
    allFrom 672 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[688, 704)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_43 :
    allFrom 688 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[704, 720)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_44 :
    allFrom 704 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[720, 736)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_45 :
    allFrom 720 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[736, 752)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_46 :
    allFrom 736 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[752, 768)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_47 :
    allFrom 752 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[768, 784)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_48 :
    allFrom 768 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[784, 800)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_49 :
    allFrom 784 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[800, 808)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0_50 :
    allFrom 800 8
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relations with indices in `[0, 808)` of the `E7` certificate pass
`CertificateCheck.Raw.relOKD`. -/
theorem relOK_0 :
    allFrom 0 808
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true :=
  allFrom_add (a := 400) (b := 408)
      (allFrom_add (a := 192) (b := 208)
          (allFrom_add (a := 96) (b := 96)
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_0
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_1
                          relOK_0_2))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_3
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_4
                          relOK_0_5)))
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_6
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_7
                          relOK_0_8))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_9
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_10
                          relOK_0_11))))
          (allFrom_add (a := 96) (b := 112)
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_12
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_13
                          relOK_0_14))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_15
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_16
                          relOK_0_17)))
              (allFrom_add (a := 48) (b := 64)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_18
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_19
                          relOK_0_20))
                  (allFrom_add (a := 32) (b := 32)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_21
                          relOK_0_22)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_23
                          relOK_0_24)))))
      (allFrom_add (a := 208) (b := 200)
          (allFrom_add (a := 96) (b := 112)
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_25
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_26
                          relOK_0_27))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_28
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_29
                          relOK_0_30)))
              (allFrom_add (a := 48) (b := 64)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_31
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_32
                          relOK_0_33))
                  (allFrom_add (a := 32) (b := 32)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_34
                          relOK_0_35)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_36
                          relOK_0_37))))
          (allFrom_add (a := 96) (b := 104)
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_38
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_39
                          relOK_0_40))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_41
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_42
                          relOK_0_43)))
              (allFrom_add (a := 48) (b := 56)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_44
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_45
                          relOK_0_46))
                  (allFrom_add (a := 32) (b := 24)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_47
                          relOK_0_48)
                      (allFrom_add (a := 16) (b := 8)
                          relOK_0_49
                          relOK_0_50)))))

end ClusterAlgebras.CertificateData.E7

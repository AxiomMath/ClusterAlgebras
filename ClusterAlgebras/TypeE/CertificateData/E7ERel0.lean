/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7E

/-!
# Exchange relations `[0, 803)` of the `E7E` certificate

Every exchange relation of `raw` with index in `[0, 803)` passes `CertificateCheck.Raw.relOKD`,
checked by the kernel in pieces of `16` relations assembled by `CertificateCheck.allFrom_add`.

## Main results

* `relOK_0`: every exchange relation of `raw` with index in `[0, 803)` passes `Raw.relOKD`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7E

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- Every exchange relation of `raw` with index in `[0, 16)` passes `Raw.relOKD`. -/
theorem relOK_0_0 :
    allFrom 0 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[16, 32)` passes `Raw.relOKD`. -/
theorem relOK_0_1 :
    allFrom 16 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[32, 48)` passes `Raw.relOKD`. -/
theorem relOK_0_2 :
    allFrom 32 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[48, 64)` passes `Raw.relOKD`. -/
theorem relOK_0_3 :
    allFrom 48 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[64, 80)` passes `Raw.relOKD`. -/
theorem relOK_0_4 :
    allFrom 64 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[80, 96)` passes `Raw.relOKD`. -/
theorem relOK_0_5 :
    allFrom 80 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[96, 112)` passes `Raw.relOKD`. -/
theorem relOK_0_6 :
    allFrom 96 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[112, 128)` passes `Raw.relOKD`. -/
theorem relOK_0_7 :
    allFrom 112 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[128, 144)` passes `Raw.relOKD`. -/
theorem relOK_0_8 :
    allFrom 128 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[144, 160)` passes `Raw.relOKD`. -/
theorem relOK_0_9 :
    allFrom 144 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[160, 176)` passes `Raw.relOKD`. -/
theorem relOK_0_10 :
    allFrom 160 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[176, 192)` passes `Raw.relOKD`. -/
theorem relOK_0_11 :
    allFrom 176 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[192, 208)` passes `Raw.relOKD`. -/
theorem relOK_0_12 :
    allFrom 192 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[208, 224)` passes `Raw.relOKD`. -/
theorem relOK_0_13 :
    allFrom 208 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[224, 240)` passes `Raw.relOKD`. -/
theorem relOK_0_14 :
    allFrom 224 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[240, 256)` passes `Raw.relOKD`. -/
theorem relOK_0_15 :
    allFrom 240 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[256, 272)` passes `Raw.relOKD`. -/
theorem relOK_0_16 :
    allFrom 256 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[272, 288)` passes `Raw.relOKD`. -/
theorem relOK_0_17 :
    allFrom 272 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[288, 304)` passes `Raw.relOKD`. -/
theorem relOK_0_18 :
    allFrom 288 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[304, 320)` passes `Raw.relOKD`. -/
theorem relOK_0_19 :
    allFrom 304 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[320, 336)` passes `Raw.relOKD`. -/
theorem relOK_0_20 :
    allFrom 320 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[336, 352)` passes `Raw.relOKD`. -/
theorem relOK_0_21 :
    allFrom 336 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[352, 368)` passes `Raw.relOKD`. -/
theorem relOK_0_22 :
    allFrom 352 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[368, 384)` passes `Raw.relOKD`. -/
theorem relOK_0_23 :
    allFrom 368 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[384, 400)` passes `Raw.relOKD`. -/
theorem relOK_0_24 :
    allFrom 384 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[400, 416)` passes `Raw.relOKD`. -/
theorem relOK_0_25 :
    allFrom 400 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[416, 432)` passes `Raw.relOKD`. -/
theorem relOK_0_26 :
    allFrom 416 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[432, 448)` passes `Raw.relOKD`. -/
theorem relOK_0_27 :
    allFrom 432 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[448, 464)` passes `Raw.relOKD`. -/
theorem relOK_0_28 :
    allFrom 448 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[464, 480)` passes `Raw.relOKD`. -/
theorem relOK_0_29 :
    allFrom 464 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[480, 496)` passes `Raw.relOKD`. -/
theorem relOK_0_30 :
    allFrom 480 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[496, 512)` passes `Raw.relOKD`. -/
theorem relOK_0_31 :
    allFrom 496 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[512, 528)` passes `Raw.relOKD`. -/
theorem relOK_0_32 :
    allFrom 512 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[528, 544)` passes `Raw.relOKD`. -/
theorem relOK_0_33 :
    allFrom 528 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[544, 560)` passes `Raw.relOKD`. -/
theorem relOK_0_34 :
    allFrom 544 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[560, 576)` passes `Raw.relOKD`. -/
theorem relOK_0_35 :
    allFrom 560 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[576, 592)` passes `Raw.relOKD`. -/
theorem relOK_0_36 :
    allFrom 576 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[592, 608)` passes `Raw.relOKD`. -/
theorem relOK_0_37 :
    allFrom 592 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[608, 624)` passes `Raw.relOKD`. -/
theorem relOK_0_38 :
    allFrom 608 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[624, 640)` passes `Raw.relOKD`. -/
theorem relOK_0_39 :
    allFrom 624 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[640, 656)` passes `Raw.relOKD`. -/
theorem relOK_0_40 :
    allFrom 640 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[656, 672)` passes `Raw.relOKD`. -/
theorem relOK_0_41 :
    allFrom 656 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[672, 688)` passes `Raw.relOKD`. -/
theorem relOK_0_42 :
    allFrom 672 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[688, 704)` passes `Raw.relOKD`. -/
theorem relOK_0_43 :
    allFrom 688 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[704, 720)` passes `Raw.relOKD`. -/
theorem relOK_0_44 :
    allFrom 704 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[720, 736)` passes `Raw.relOKD`. -/
theorem relOK_0_45 :
    allFrom 720 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[736, 752)` passes `Raw.relOKD`. -/
theorem relOK_0_46 :
    allFrom 736 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[752, 768)` passes `Raw.relOKD`. -/
theorem relOK_0_47 :
    allFrom 752 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[768, 784)` passes `Raw.relOKD`. -/
theorem relOK_0_48 :
    allFrom 768 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[784, 800)` passes `Raw.relOKD`. -/
theorem relOK_0_49 :
    allFrom 784 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[800, 803)` passes `Raw.relOKD`. -/
theorem relOK_0_50 :
    allFrom 800 3
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- Every exchange relation of `raw` with index in `[0, 803)` passes `Raw.relOKD`. -/
theorem relOK_0 :
    allFrom 0 803
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true :=
  allFrom_add (a := 400) (b := 403)
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
      (allFrom_add (a := 208) (b := 195)
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
          (allFrom_add (a := 96) (b := 99)
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
              (allFrom_add (a := 48) (b := 51)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_0_44
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_45
                          relOK_0_46))
                  (allFrom_add (a := 32) (b := 19)
                      (allFrom_add (a := 16) (b := 16)
                          relOK_0_47
                          relOK_0_48)
                      (allFrom_add (a := 16) (b := 3)
                          relOK_0_49
                          relOK_0_50)))))

end ClusterAlgebras.CertificateData.E7E

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E6

/-!
# Exchange relations `[0, 385)` of the `E6` certificate

The exchange relations of `raw` with indices in `[0, 385)` are checked by kernel evaluation of
`relOKD`, in pieces of `16` relations assembled by `CertificateCheck.allFrom_add`.

## Main results

* `relOK_0`: the exchange relations of `raw` with indices in `[0, 385)` hold.

## Implementation notes

Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the cost
of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel checks of the
pieces would hold their memory until the end of the file, so it is disabled.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E6

open CertificateCheck

set_option Elab.async false

/-- The exchange relations of `raw` with indices in `[0, 16)` hold, as checked by `relOKD`. -/
theorem relOK_0_0 :
    allFrom 0 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[16, 32)` hold, as checked by `relOKD`. -/
theorem relOK_0_1 :
    allFrom 16 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[32, 48)` hold, as checked by `relOKD`. -/
theorem relOK_0_2 :
    allFrom 32 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[48, 64)` hold, as checked by `relOKD`. -/
theorem relOK_0_3 :
    allFrom 48 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[64, 80)` hold, as checked by `relOKD`. -/
theorem relOK_0_4 :
    allFrom 64 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[80, 96)` hold, as checked by `relOKD`. -/
theorem relOK_0_5 :
    allFrom 80 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[96, 112)` hold, as checked by `relOKD`. -/
theorem relOK_0_6 :
    allFrom 96 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[112, 128)` hold, as checked by `relOKD`. -/
theorem relOK_0_7 :
    allFrom 112 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[128, 144)` hold, as checked by `relOKD`. -/
theorem relOK_0_8 :
    allFrom 128 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[144, 160)` hold, as checked by `relOKD`. -/
theorem relOK_0_9 :
    allFrom 144 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[160, 176)` hold, as checked by `relOKD`. -/
theorem relOK_0_10 :
    allFrom 160 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[176, 192)` hold, as checked by `relOKD`. -/
theorem relOK_0_11 :
    allFrom 176 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[192, 208)` hold, as checked by `relOKD`. -/
theorem relOK_0_12 :
    allFrom 192 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[208, 224)` hold, as checked by `relOKD`. -/
theorem relOK_0_13 :
    allFrom 208 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[224, 240)` hold, as checked by `relOKD`. -/
theorem relOK_0_14 :
    allFrom 224 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[240, 256)` hold, as checked by `relOKD`. -/
theorem relOK_0_15 :
    allFrom 240 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[256, 272)` hold, as checked by `relOKD`. -/
theorem relOK_0_16 :
    allFrom 256 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[272, 288)` hold, as checked by `relOKD`. -/
theorem relOK_0_17 :
    allFrom 272 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[288, 304)` hold, as checked by `relOKD`. -/
theorem relOK_0_18 :
    allFrom 288 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[304, 320)` hold, as checked by `relOKD`. -/
theorem relOK_0_19 :
    allFrom 304 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[320, 336)` hold, as checked by `relOKD`. -/
theorem relOK_0_20 :
    allFrom 320 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[336, 352)` hold, as checked by `relOKD`. -/
theorem relOK_0_21 :
    allFrom 336 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[352, 368)` hold, as checked by `relOKD`. -/
theorem relOK_0_22 :
    allFrom 352 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[368, 384)` hold, as checked by `relOKD`. -/
theorem relOK_0_23 :
    allFrom 368 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[384, 385)` hold, as checked by `relOKD`. -/
theorem relOK_0_24 :
    allFrom 384 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[0, 385)` hold, as checked by `relOKD`. -/
theorem relOK_0 :
    allFrom 0 385
      (fun r => raw.relOKD (fun c => varList.getD c []) 6 42 r) = true :=
  allFrom_add (a := 192) (b := 193)
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
      (allFrom_add (a := 96) (b := 97)
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
          (allFrom_add (a := 48) (b := 49)
              (allFrom_add (a := 16) (b := 32)
                  relOK_0_18
                  (allFrom_add (a := 16) (b := 16)
                      relOK_0_19
                      relOK_0_20))
              (allFrom_add (a := 32) (b := 17)
                  (allFrom_add (a := 16) (b := 16)
                      relOK_0_21
                      relOK_0_22)
                  (allFrom_add (a := 16) (b := 1)
                      relOK_0_23
                      relOK_0_24))))

end ClusterAlgebras.CertificateData.E6

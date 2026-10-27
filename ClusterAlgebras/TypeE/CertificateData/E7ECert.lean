/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateDense
public import ClusterAlgebras.TypeE.CertificateData.E7ETrans0
public import ClusterAlgebras.TypeE.CertificateData.E7ETrans1
public import ClusterAlgebras.TypeE.CertificateData.E7ERel0
public import ClusterAlgebras.TypeE.CertificateData.E7ERel1
public import ClusterAlgebras.TypeE.CertificateData.E7ERel2
public import ClusterAlgebras.TypeE.CertificateData.E7ERel3
public import ClusterAlgebras.TypeE.CertificateData.E7ERel4
public import ClusterAlgebras.TypeE.CertificateData.E7ERel5
public import ClusterAlgebras.TypeE.CertificateData.E7ERel6
public import ClusterAlgebras.TypeE.CertificateData.E7ERel7

/-!
# The `E7E` exchange certificate

Assembles the kernel checks of the `E7E` data into an exchange certificate, through the
soundness theorem `CertificateCheck.Raw.nonempty_exchangeCertificate`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7E

open CertificateCheck

-- The seed-indexed and pair-indexed checks are split into theorems of their own, so that the
-- kernel's caches are dropped between them; with `Elab.async`, the kernel checks would hold
-- their memory until the end of the file.
set_option Elab.async false

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- `raw` passes the initial-seed check `raw.initOK 8 7`. -/
theorem initOK : raw.initOK 8 7 = true := by decide +kernel

/-- The seeds in `[0, 128)` pass `raw.seedOK`. -/
theorem seedOK_0 :
    allFrom 0 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[128, 256)` pass `raw.seedOK`. -/
theorem seedOK_1 :
    allFrom 128 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[256, 384)` pass `raw.seedOK`. -/
theorem seedOK_2 :
    allFrom 256 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[384, 512)` pass `raw.seedOK`. -/
theorem seedOK_3 :
    allFrom 384 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[512, 640)` pass `raw.seedOK`. -/
theorem seedOK_4 :
    allFrom 512 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[640, 768)` pass `raw.seedOK`. -/
theorem seedOK_5 :
    allFrom 640 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[768, 896)` pass `raw.seedOK`. -/
theorem seedOK_6 :
    allFrom 768 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[896, 1024)` pass `raw.seedOK`. -/
theorem seedOK_7 :
    allFrom 896 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1024, 1152)` pass `raw.seedOK`. -/
theorem seedOK_8 :
    allFrom 1024 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1152, 1280)` pass `raw.seedOK`. -/
theorem seedOK_9 :
    allFrom 1152 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1280, 1408)` pass `raw.seedOK`. -/
theorem seedOK_10 :
    allFrom 1280 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1408, 1536)` pass `raw.seedOK`. -/
theorem seedOK_11 :
    allFrom 1408 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1536, 1664)` pass `raw.seedOK`. -/
theorem seedOK_12 :
    allFrom 1536 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1664, 1792)` pass `raw.seedOK`. -/
theorem seedOK_13 :
    allFrom 1664 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1792, 1920)` pass `raw.seedOK`. -/
theorem seedOK_14 :
    allFrom 1792 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1920, 2048)` pass `raw.seedOK`. -/
theorem seedOK_15 :
    allFrom 1920 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2048, 2176)` pass `raw.seedOK`. -/
theorem seedOK_16 :
    allFrom 2048 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2176, 2304)` pass `raw.seedOK`. -/
theorem seedOK_17 :
    allFrom 2176 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2304, 2432)` pass `raw.seedOK`. -/
theorem seedOK_18 :
    allFrom 2304 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2432, 2560)` pass `raw.seedOK`. -/
theorem seedOK_19 :
    allFrom 2432 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2560, 2688)` pass `raw.seedOK`. -/
theorem seedOK_20 :
    allFrom 2560 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2688, 2816)` pass `raw.seedOK`. -/
theorem seedOK_21 :
    allFrom 2688 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2816, 2944)` pass `raw.seedOK`. -/
theorem seedOK_22 :
    allFrom 2816 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2944, 3072)` pass `raw.seedOK`. -/
theorem seedOK_23 :
    allFrom 2944 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3072, 3200)` pass `raw.seedOK`. -/
theorem seedOK_24 :
    allFrom 3072 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3200, 3328)` pass `raw.seedOK`. -/
theorem seedOK_25 :
    allFrom 3200 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3328, 3456)` pass `raw.seedOK`. -/
theorem seedOK_26 :
    allFrom 3328 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3456, 3584)` pass `raw.seedOK`. -/
theorem seedOK_27 :
    allFrom 3456 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3584, 3712)` pass `raw.seedOK`. -/
theorem seedOK_28 :
    allFrom 3584 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3712, 3840)` pass `raw.seedOK`. -/
theorem seedOK_29 :
    allFrom 3712 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3840, 3968)` pass `raw.seedOK`. -/
theorem seedOK_30 :
    allFrom 3840 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3968, 4096)` pass `raw.seedOK`. -/
theorem seedOK_31 :
    allFrom 3968 128 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[4096, 4160)` pass `raw.seedOK`. -/
theorem seedOK_32 :
    allFrom 4096 64 (fun a => raw.seedOK 7 70 a) = true := by
  decide +kernel

/-- All `4160` seeds of `raw` pass `raw.seedOK`. -/
theorem seedOK :
    allFrom 0 4160 (fun a => raw.seedOK 7 70 a) = true :=
  allFrom_add (a := 2048) (b := 2112)
      (allFrom_add (a := 1024) (b := 1024)
          (allFrom_add (a := 512) (b := 512)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_0
                      seedOK_1)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_2
                      seedOK_3))
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_4
                      seedOK_5)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_6
                      seedOK_7)))
          (allFrom_add (a := 512) (b := 512)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_8
                      seedOK_9)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_10
                      seedOK_11))
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_12
                      seedOK_13)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_14
                      seedOK_15))))
      (allFrom_add (a := 1024) (b := 1088)
          (allFrom_add (a := 512) (b := 512)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_16
                      seedOK_17)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_18
                      seedOK_19))
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_20
                      seedOK_21)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_22
                      seedOK_23)))
          (allFrom_add (a := 512) (b := 576)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_24
                      seedOK_25)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_26
                      seedOK_27))
              (allFrom_add (a := 256) (b := 320)
                  (allFrom_add (a := 128) (b := 128)
                      seedOK_28
                      seedOK_29)
                  (allFrom_add (a := 128) (b := 192)
                      seedOK_30
                      (allFrom_add (a := 128) (b := 64)
                          seedOK_31
                          seedOK_32)))))

/-- The seeds in `[0, 128)` pass `raw.lexOK`. -/
theorem lexOK_0 :
    allFrom 0 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[128, 256)` pass `raw.lexOK`. -/
theorem lexOK_1 :
    allFrom 128 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[256, 384)` pass `raw.lexOK`. -/
theorem lexOK_2 :
    allFrom 256 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[384, 512)` pass `raw.lexOK`. -/
theorem lexOK_3 :
    allFrom 384 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[512, 640)` pass `raw.lexOK`. -/
theorem lexOK_4 :
    allFrom 512 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[640, 768)` pass `raw.lexOK`. -/
theorem lexOK_5 :
    allFrom 640 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[768, 896)` pass `raw.lexOK`. -/
theorem lexOK_6 :
    allFrom 768 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[896, 1024)` pass `raw.lexOK`. -/
theorem lexOK_7 :
    allFrom 896 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1024, 1152)` pass `raw.lexOK`. -/
theorem lexOK_8 :
    allFrom 1024 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1152, 1280)` pass `raw.lexOK`. -/
theorem lexOK_9 :
    allFrom 1152 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1280, 1408)` pass `raw.lexOK`. -/
theorem lexOK_10 :
    allFrom 1280 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1408, 1536)` pass `raw.lexOK`. -/
theorem lexOK_11 :
    allFrom 1408 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1536, 1664)` pass `raw.lexOK`. -/
theorem lexOK_12 :
    allFrom 1536 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1664, 1792)` pass `raw.lexOK`. -/
theorem lexOK_13 :
    allFrom 1664 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1792, 1920)` pass `raw.lexOK`. -/
theorem lexOK_14 :
    allFrom 1792 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[1920, 2048)` pass `raw.lexOK`. -/
theorem lexOK_15 :
    allFrom 1920 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2048, 2176)` pass `raw.lexOK`. -/
theorem lexOK_16 :
    allFrom 2048 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2176, 2304)` pass `raw.lexOK`. -/
theorem lexOK_17 :
    allFrom 2176 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2304, 2432)` pass `raw.lexOK`. -/
theorem lexOK_18 :
    allFrom 2304 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2432, 2560)` pass `raw.lexOK`. -/
theorem lexOK_19 :
    allFrom 2432 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2560, 2688)` pass `raw.lexOK`. -/
theorem lexOK_20 :
    allFrom 2560 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2688, 2816)` pass `raw.lexOK`. -/
theorem lexOK_21 :
    allFrom 2688 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2816, 2944)` pass `raw.lexOK`. -/
theorem lexOK_22 :
    allFrom 2816 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[2944, 3072)` pass `raw.lexOK`. -/
theorem lexOK_23 :
    allFrom 2944 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3072, 3200)` pass `raw.lexOK`. -/
theorem lexOK_24 :
    allFrom 3072 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3200, 3328)` pass `raw.lexOK`. -/
theorem lexOK_25 :
    allFrom 3200 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3328, 3456)` pass `raw.lexOK`. -/
theorem lexOK_26 :
    allFrom 3328 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3456, 3584)` pass `raw.lexOK`. -/
theorem lexOK_27 :
    allFrom 3456 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3584, 3712)` pass `raw.lexOK`. -/
theorem lexOK_28 :
    allFrom 3584 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3712, 3840)` pass `raw.lexOK`. -/
theorem lexOK_29 :
    allFrom 3712 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3840, 3968)` pass `raw.lexOK`. -/
theorem lexOK_30 :
    allFrom 3840 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[3968, 4096)` pass `raw.lexOK`. -/
theorem lexOK_31 :
    allFrom 3968 128 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The seeds in `[4096, 4159)` pass `raw.lexOK`. -/
theorem lexOK_32 :
    allFrom 4096 63 (fun a => raw.lexOK 7 70 a) = true := by
  decide +kernel

/-- The first `4159` seeds of `raw` pass `raw.lexOK`, so the seed codes strictly increase. -/
theorem lexOK :
    allFrom 0 4159 (fun a => raw.lexOK 7 70 a) = true :=
  allFrom_add (a := 2048) (b := 2111)
      (allFrom_add (a := 1024) (b := 1024)
          (allFrom_add (a := 512) (b := 512)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_0
                      lexOK_1)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_2
                      lexOK_3))
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_4
                      lexOK_5)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_6
                      lexOK_7)))
          (allFrom_add (a := 512) (b := 512)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_8
                      lexOK_9)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_10
                      lexOK_11))
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_12
                      lexOK_13)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_14
                      lexOK_15))))
      (allFrom_add (a := 1024) (b := 1087)
          (allFrom_add (a := 512) (b := 512)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_16
                      lexOK_17)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_18
                      lexOK_19))
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_20
                      lexOK_21)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_22
                      lexOK_23)))
          (allFrom_add (a := 512) (b := 575)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_24
                      lexOK_25)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_26
                      lexOK_27))
              (allFrom_add (a := 256) (b := 319)
                  (allFrom_add (a := 128) (b := 128)
                      lexOK_28
                      lexOK_29)
                  (allFrom_add (a := 128) (b := 191)
                      lexOK_30
                      (allFrom_add (a := 128) (b := 63)
                          lexOK_31
                          lexOK_32)))))

-- The variables are told apart by their values at `Xᵢ = 2^(2^i)`, each computed once.
/-- The `70` variables of `raw` pass `distOKD`, so they are pairwise distinct. -/
theorem distOK :
    allBelow 70 (fun c' => allBelow c' fun c =>
      distOKD (fun c => varList.getD c []) 8 1 (fun i => Nat.pow 2 i) c c') = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- All `70` variables of `raw` pass `raw.coverOK`: each occurs in some seed. -/
theorem coverOK : allBelow 70 (fun c => raw.coverOK 7 4160 c) = true := by decide +kernel

/-- The seeds in `[0, 128)` pass `raw.treeOK`. -/
theorem treeOK_0 :
    allFrom 0 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[128, 256)` pass `raw.treeOK`. -/
theorem treeOK_1 :
    allFrom 128 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[256, 384)` pass `raw.treeOK`. -/
theorem treeOK_2 :
    allFrom 256 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[384, 512)` pass `raw.treeOK`. -/
theorem treeOK_3 :
    allFrom 384 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[512, 640)` pass `raw.treeOK`. -/
theorem treeOK_4 :
    allFrom 512 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[640, 768)` pass `raw.treeOK`. -/
theorem treeOK_5 :
    allFrom 640 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[768, 896)` pass `raw.treeOK`. -/
theorem treeOK_6 :
    allFrom 768 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[896, 1024)` pass `raw.treeOK`. -/
theorem treeOK_7 :
    allFrom 896 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[1024, 1152)` pass `raw.treeOK`. -/
theorem treeOK_8 :
    allFrom 1024 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[1152, 1280)` pass `raw.treeOK`. -/
theorem treeOK_9 :
    allFrom 1152 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[1280, 1408)` pass `raw.treeOK`. -/
theorem treeOK_10 :
    allFrom 1280 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[1408, 1536)` pass `raw.treeOK`. -/
theorem treeOK_11 :
    allFrom 1408 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[1536, 1664)` pass `raw.treeOK`. -/
theorem treeOK_12 :
    allFrom 1536 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[1664, 1792)` pass `raw.treeOK`. -/
theorem treeOK_13 :
    allFrom 1664 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[1792, 1920)` pass `raw.treeOK`. -/
theorem treeOK_14 :
    allFrom 1792 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[1920, 2048)` pass `raw.treeOK`. -/
theorem treeOK_15 :
    allFrom 1920 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[2048, 2176)` pass `raw.treeOK`. -/
theorem treeOK_16 :
    allFrom 2048 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[2176, 2304)` pass `raw.treeOK`. -/
theorem treeOK_17 :
    allFrom 2176 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[2304, 2432)` pass `raw.treeOK`. -/
theorem treeOK_18 :
    allFrom 2304 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[2432, 2560)` pass `raw.treeOK`. -/
theorem treeOK_19 :
    allFrom 2432 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[2560, 2688)` pass `raw.treeOK`. -/
theorem treeOK_20 :
    allFrom 2560 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[2688, 2816)` pass `raw.treeOK`. -/
theorem treeOK_21 :
    allFrom 2688 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[2816, 2944)` pass `raw.treeOK`. -/
theorem treeOK_22 :
    allFrom 2816 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[2944, 3072)` pass `raw.treeOK`. -/
theorem treeOK_23 :
    allFrom 2944 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[3072, 3200)` pass `raw.treeOK`. -/
theorem treeOK_24 :
    allFrom 3072 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[3200, 3328)` pass `raw.treeOK`. -/
theorem treeOK_25 :
    allFrom 3200 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[3328, 3456)` pass `raw.treeOK`. -/
theorem treeOK_26 :
    allFrom 3328 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[3456, 3584)` pass `raw.treeOK`. -/
theorem treeOK_27 :
    allFrom 3456 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[3584, 3712)` pass `raw.treeOK`. -/
theorem treeOK_28 :
    allFrom 3584 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[3712, 3840)` pass `raw.treeOK`. -/
theorem treeOK_29 :
    allFrom 3712 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[3840, 3968)` pass `raw.treeOK`. -/
theorem treeOK_30 :
    allFrom 3840 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[3968, 4096)` pass `raw.treeOK`. -/
theorem treeOK_31 :
    allFrom 3968 128 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- The seeds in `[4096, 4160)` pass `raw.treeOK`. -/
theorem treeOK_32 :
    allFrom 4096 64 (fun a => raw.treeOK 7 4160 a) = true := by
  decide +kernel

/-- All `4160` seeds of `raw` pass `raw.treeOK`. -/
theorem treeOK :
    allFrom 0 4160 (fun a => raw.treeOK 7 4160 a) = true :=
  allFrom_add (a := 2048) (b := 2112)
      (allFrom_add (a := 1024) (b := 1024)
          (allFrom_add (a := 512) (b := 512)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_0
                      treeOK_1)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_2
                      treeOK_3))
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_4
                      treeOK_5)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_6
                      treeOK_7)))
          (allFrom_add (a := 512) (b := 512)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_8
                      treeOK_9)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_10
                      treeOK_11))
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_12
                      treeOK_13)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_14
                      treeOK_15))))
      (allFrom_add (a := 1024) (b := 1088)
          (allFrom_add (a := 512) (b := 512)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_16
                      treeOK_17)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_18
                      treeOK_19))
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_20
                      treeOK_21)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_22
                      treeOK_23)))
          (allFrom_add (a := 512) (b := 576)
              (allFrom_add (a := 256) (b := 256)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_24
                      treeOK_25)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_26
                      treeOK_27))
              (allFrom_add (a := 256) (b := 320)
                  (allFrom_add (a := 128) (b := 128)
                      treeOK_28
                      treeOK_29)
                  (allFrom_add (a := 128) (b := 192)
                      treeOK_30
                      (allFrom_add (a := 128) (b := 64)
                          treeOK_31
                          treeOK_32)))))

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- All `1050` relations of `raw` pass `raw.relShapeOK`. -/
theorem relShapeOK : allBelow 1050 raw.relShapeOK = true := by decide +kernel

/-- The initial matrix of the certificate. -/
noncomputable def initMatrix : Matrix (Fin 8) (Fin 7) ℤ :=
  Matrix.of fun i j => raw.entry 0 i j

/-- There is an exchange certificate for `initMatrix` with `70` variables and `4160` seeds. -/
theorem nonempty_exchangeCertificate (hmn : 7 ≤ 8) :
    Nonempty (ExchangeCertificate hmn initMatrix 70 4160) := by
  refine Raw.nonempty_exchangeCertificate (numRel := 1050) hmn initMatrix raw (by decide)
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
      allFrom_add (a := 2080) (b := 2080) transOK_0
        transOK_1
    exact allFrom_iff.1 h a (Nat.zero_le _) (by omega)
  · intro r hr
    refine Raw.toL_relOKD (codes := fun c => varList.getD c []) (fun _ _ => rfl) ?_
    have h :=
      allFrom_add (a := 803) (b := 247) relOK_0
        (allFrom_add (a := 104) (b := 143) relOK_1
          (allFrom_add (a := 68) (b := 75) relOK_2
            (allFrom_add (a := 20) (b := 55) relOK_3
              (allFrom_add (a := 10) (b := 45) relOK_4
                (allFrom_add (a := 12) (b := 33) relOK_5
                  (allFrom_add (a := 25) (b := 8) relOK_6
                    relOK_7))))))
    exact allFrom_iff.1 h r (Nat.zero_le _) (by omega)

end ClusterAlgebras.CertificateData.E7E

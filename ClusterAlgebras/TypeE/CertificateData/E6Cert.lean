/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateDense
public import ClusterAlgebras.TypeE.CertificateData.E6Trans0
public import ClusterAlgebras.TypeE.CertificateData.E6Rel0

/-!
# The `E6` exchange certificate

Assembles the kernel checks of the `E6` data into an exchange certificate, through the
soundness theorem `CertificateCheck.Raw.nonempty_exchangeCertificate`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E6

open CertificateCheck

-- The seed-indexed and pair-indexed checks are split into theorems of their own, so that the
-- kernel's caches are dropped between them; with `Elab.async`, the kernel checks would hold
-- their memory until the end of the file.
set_option Elab.async false

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The certificate's data at the initial seed satisfies `CertificateCheck.Raw.initOK`. -/
theorem initOK : raw.initOK 6 6 = true := by decide +kernel

/-- For every `a` with `0 ≤ a < 128`, the cluster of the seed `a` is strictly increasing
with values below `42`. -/
theorem seedOK_0 :
    allFrom 0 128 (fun a => raw.seedOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `128 ≤ a < 256`, the cluster of the seed `a` is strictly increasing
with values below `42`. -/
theorem seedOK_1 :
    allFrom 128 128 (fun a => raw.seedOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `256 ≤ a < 384`, the cluster of the seed `a` is strictly increasing
with values below `42`. -/
theorem seedOK_2 :
    allFrom 256 128 (fun a => raw.seedOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `384 ≤ a < 512`, the cluster of the seed `a` is strictly increasing
with values below `42`. -/
theorem seedOK_3 :
    allFrom 384 128 (fun a => raw.seedOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `512 ≤ a < 640`, the cluster of the seed `a` is strictly increasing
with values below `42`. -/
theorem seedOK_4 :
    allFrom 512 128 (fun a => raw.seedOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `640 ≤ a < 768`, the cluster of the seed `a` is strictly increasing
with values below `42`. -/
theorem seedOK_5 :
    allFrom 640 128 (fun a => raw.seedOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `768 ≤ a < 833`, the cluster of the seed `a` is strictly increasing
with values below `42`. -/
theorem seedOK_6 :
    allFrom 768 65 (fun a => raw.seedOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `0 ≤ a < 833`, the cluster of the seed `a` is strictly increasing
with values below `42`. -/
theorem seedOK :
    allFrom 0 833 (fun a => raw.seedOK 6 42 a) = true :=
  allFrom_add (a := 384) (b := 449)
      (allFrom_add (a := 128) (b := 256)
          seedOK_0
          (allFrom_add (a := 128) (b := 128)
              seedOK_1
              seedOK_2))
      (allFrom_add (a := 256) (b := 193)
          (allFrom_add (a := 128) (b := 128)
              seedOK_3
              seedOK_4)
          (allFrom_add (a := 128) (b := 65)
              seedOK_5
              seedOK_6))

/-- For every `a` with `0 ≤ a < 128`, the codes of the seeds `a` and `a + 1` increase. -/
theorem lexOK_0 :
    allFrom 0 128 (fun a => raw.lexOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `128 ≤ a < 256`, the codes of the seeds `a` and `a + 1` increase. -/
theorem lexOK_1 :
    allFrom 128 128 (fun a => raw.lexOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `256 ≤ a < 384`, the codes of the seeds `a` and `a + 1` increase. -/
theorem lexOK_2 :
    allFrom 256 128 (fun a => raw.lexOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `384 ≤ a < 512`, the codes of the seeds `a` and `a + 1` increase. -/
theorem lexOK_3 :
    allFrom 384 128 (fun a => raw.lexOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `512 ≤ a < 640`, the codes of the seeds `a` and `a + 1` increase. -/
theorem lexOK_4 :
    allFrom 512 128 (fun a => raw.lexOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `640 ≤ a < 768`, the codes of the seeds `a` and `a + 1` increase. -/
theorem lexOK_5 :
    allFrom 640 128 (fun a => raw.lexOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `768 ≤ a < 832`, the codes of the seeds `a` and `a + 1` increase. -/
theorem lexOK_6 :
    allFrom 768 64 (fun a => raw.lexOK 6 42 a) = true := by
  decide +kernel

/-- For every `a` with `0 ≤ a < 832`, the codes of the seeds `a` and `a + 1` increase. -/
theorem lexOK :
    allFrom 0 832 (fun a => raw.lexOK 6 42 a) = true :=
  allFrom_add (a := 384) (b := 448)
      (allFrom_add (a := 128) (b := 256)
          lexOK_0
          (allFrom_add (a := 128) (b := 128)
              lexOK_1
              lexOK_2))
      (allFrom_add (a := 256) (b := 192)
          (allFrom_add (a := 128) (b := 128)
              lexOK_3
              lexOK_4)
          (allFrom_add (a := 128) (b := 64)
              lexOK_5
              lexOK_6))

/-- Any two distinct variables of the certificate take different values at `Xᵢ = 2^(2^i)`. -/
theorem distOK :
    allBelow 42 (fun c' => allBelow c' fun c =>
      distOKD (fun c => varList.getD c []) 6 1 (fun i => Nat.pow 2 i) c c') = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- Every variable of the certificate passes the covering check `CertificateCheck.Raw.coverOK`. -/
theorem coverOK : allBelow 42 (fun c => raw.coverOK 6 833 c) = true := by decide +kernel

/-- For every `a` with `0 ≤ a < 128`, the spanning-tree check `CertificateCheck.Raw.treeOK`
holds at the seed `a`. -/
theorem treeOK_0 :
    allFrom 0 128 (fun a => raw.treeOK 6 833 a) = true := by
  decide +kernel

/-- For every `a` with `128 ≤ a < 256`, the spanning-tree check `CertificateCheck.Raw.treeOK`
holds at the seed `a`. -/
theorem treeOK_1 :
    allFrom 128 128 (fun a => raw.treeOK 6 833 a) = true := by
  decide +kernel

/-- For every `a` with `256 ≤ a < 384`, the spanning-tree check `CertificateCheck.Raw.treeOK`
holds at the seed `a`. -/
theorem treeOK_2 :
    allFrom 256 128 (fun a => raw.treeOK 6 833 a) = true := by
  decide +kernel

/-- For every `a` with `384 ≤ a < 512`, the spanning-tree check `CertificateCheck.Raw.treeOK`
holds at the seed `a`. -/
theorem treeOK_3 :
    allFrom 384 128 (fun a => raw.treeOK 6 833 a) = true := by
  decide +kernel

/-- For every `a` with `512 ≤ a < 640`, the spanning-tree check `CertificateCheck.Raw.treeOK`
holds at the seed `a`. -/
theorem treeOK_4 :
    allFrom 512 128 (fun a => raw.treeOK 6 833 a) = true := by
  decide +kernel

/-- For every `a` with `640 ≤ a < 768`, the spanning-tree check `CertificateCheck.Raw.treeOK`
holds at the seed `a`. -/
theorem treeOK_5 :
    allFrom 640 128 (fun a => raw.treeOK 6 833 a) = true := by
  decide +kernel

/-- For every `a` with `768 ≤ a < 833`, the spanning-tree check `CertificateCheck.Raw.treeOK`
holds at the seed `a`. -/
theorem treeOK_6 :
    allFrom 768 65 (fun a => raw.treeOK 6 833 a) = true := by
  decide +kernel

/-- For every `a` with `0 ≤ a < 833`, the spanning-tree check `CertificateCheck.Raw.treeOK`
holds at the seed `a`. -/
theorem treeOK :
    allFrom 0 833 (fun a => raw.treeOK 6 833 a) = true :=
  allFrom_add (a := 384) (b := 449)
      (allFrom_add (a := 128) (b := 256)
          treeOK_0
          (allFrom_add (a := 128) (b := 128)
              treeOK_1
              treeOK_2))
      (allFrom_add (a := 256) (b := 193)
          (allFrom_add (a := 128) (b := 128)
              treeOK_3
              treeOK_4)
          (allFrom_add (a := 128) (b := 65)
              treeOK_5
              treeOK_6))

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- Every exchange relation of the certificate passes `CertificateCheck.Raw.relShapeOK`. -/
theorem relShapeOK : allBelow 385 raw.relShapeOK = true := by decide +kernel

/-- The initial matrix of the certificate. -/
noncomputable def initMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j => raw.entry 0 i j

/-- There is an exchange certificate for `initMatrix` with `42` variables and `833` seeds. -/
theorem nonempty_exchangeCertificate (hmn : 6 ≤ 6) :
    Nonempty (ExchangeCertificate hmn initMatrix 42 833) := by
  refine Raw.nonempty_exchangeCertificate (numRel := 385) hmn initMatrix raw (by decide)
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
    exact allFrom_iff.1 transOK_0 a (by omega) (by omega)
  · intro r hr
    refine Raw.toL_relOKD (codes := fun c => varList.getD c []) (fun _ _ => rfl) ?_
    exact allFrom_iff.1 relOK_0 r (by omega) (by omega)

end ClusterAlgebras.CertificateData.E6

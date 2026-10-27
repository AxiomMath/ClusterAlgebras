/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificatePack
public import ClusterAlgebras.TypeFG.CertificateData.G2ETrans0
public import ClusterAlgebras.TypeFG.CertificateData.G2ERel0

/-!
# The `G2E` exchange certificate

Assembles the kernel checks of the `G2E` data into an exchange certificate, through the
soundness theorem `CertificateCheck.Raw.nonempty_exchangeCertificate`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.G2E

open CertificateCheck

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The initial-matrix check of `raw` holds in dimensions `4 × 2`. -/
theorem initOK : raw.initOK 4 2 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The seed check of `raw` holds at every index below `8`. -/
theorem seedOK : allBelow 8 (fun a => raw.seedOK 2 8 a) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The lexicographic-order check of `raw` holds at every index below `7`. -/
theorem lexOK : allBelow 7 (fun a => raw.lexOK 2 8 a) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The distinctness check of `raw` holds for every pair of indices `c < c' < 8`. -/
theorem distOK :
    allBelow 8 (fun c' => allBelow c' fun c => raw.distOK 4 c c') = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The variable check of `raw` holds at every index below `8`. -/
theorem varOK : allBelow 8 (fun c => raw.varOK 4 3 c) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The covering check of `raw` holds at every index below `8`. -/
theorem coverOK : allBelow 8 (fun c => raw.coverOK 2 8 c) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The tree check of `raw` holds at every index below `8`. -/
theorem treeOK : allBelow 8 (fun a => raw.treeOK 2 8 a) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The shape check of `raw` holds at every relation index below `8`. -/
theorem relShapeOK : allBelow 8 raw.relShapeOK = true := by decide +kernel

/-- The initial matrix of the certificate. -/
noncomputable def initMatrix : Matrix (Fin 4) (Fin 2) ℤ :=
  Matrix.of fun i j => raw.entry 0 i j

/-- There is an exchange certificate for `initMatrix` with `8` variables and `8` seeds. -/
theorem nonempty_exchangeCertificate (hmn : 2 ≤ 4) :
    Nonempty (ExchangeCertificate hmn initMatrix 8 8) := by
  refine Raw.nonempty_exchangeCertificate (numRel := 8) hmn initMatrix raw (by decide)
    (by decide) initOK (fun _ _ => rfl) (by decide) (fun _ _ _ => Nat.mod_lt _ (by decide))
    (allBelow_iff.1 seedOK)
    (fun a ha => allBelow_iff.1 lexOK a (by omega)) ?_ ?_
    (allBelow_iff.1 relShapeOK)
    (fun c' hc' c hc => Raw.toL_ne_of_distOK (allBelow_iff.1 (allBelow_iff.1 distOK c' hc') c hc))
    (allBelow_iff.1 coverOK) (allBelow_iff.1 treeOK)
  · intro a ha k hk
    refine allBelow_iff.1 ?_ k hk
    exact allFrom_iff.1 transOK_0 a (by omega) (by omega)
  · intro r hr
    refine Raw.toL_relOKN (B := 4096) (β := 3) (D := 1024)
      (allBelow_iff.1 varOK) ?_
    exact allFrom_iff.1 relOK_0 r (by omega) (by omega)

end ClusterAlgebras.CertificateData.G2E

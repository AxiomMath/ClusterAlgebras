/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificatePack
public import ClusterAlgebras.TypeFG.CertificateData.F4Trans0
public import ClusterAlgebras.TypeFG.CertificateData.F4Rel0

/-!
# The `F4` exchange certificate

Assembles the kernel checks of the `F4` data into an exchange certificate, through the
soundness theorem `CertificateCheck.Raw.nonempty_exchangeCertificate`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.F4

open CertificateCheck

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The initial seed of `raw` has the identity cluster and its variables are the generators. -/
theorem initOK : raw.initOK 4 4 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The cluster of each of the `105` seeds of `raw` is strictly increasing with values below
`28`. -/
theorem seedOK : allBelow 105 (fun a => raw.seedOK 4 28 a) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The codes of consecutive seeds of `raw` are strictly increasing. -/
theorem lexOK : allBelow 104 (fun a => raw.lexOK 4 28 a) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The `28` variables of `raw` are pairwise distinct: `CertificateCheck.Raw.distOK` passes for
all `c < c' < 28`. -/
theorem distOK :
    allBelow 28 (fun c' => allBelow c' fun c => raw.distOK 4 c c') = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- Each of the `28` variables of `raw` has nonnegative coefficients and bounded exponents. -/
theorem varOK : allBelow 28 (fun c => raw.varOK 4 4 c) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- Each of the `28` variables of `raw` lies in the cluster of one of the `105` seeds. -/
theorem coverOK : allBelow 28 (fun c => raw.coverOK 4 105 c) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- Every seed of `raw` satisfies the spanning-tree check `CertificateCheck.Raw.treeOK`. -/
theorem treeOK : allBelow 105 (fun a => raw.treeOK 4 105 a) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The monomials of each of the `98` exchange relations of `raw` are good lists of atoms. -/
theorem relShapeOK : allBelow 98 raw.relShapeOK = true := by decide +kernel

/-- The initial matrix of the certificate. -/
noncomputable def initMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => raw.entry 0 i j

/-- There is an exchange certificate for `initMatrix` with `28` variables and `105` seeds. -/
theorem nonempty_exchangeCertificate (hmn : 4 ≤ 4) :
    Nonempty (ExchangeCertificate hmn initMatrix 28 105) := by
  refine Raw.nonempty_exchangeCertificate (numRel := 98) hmn initMatrix raw (by decide)
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
    refine Raw.toL_relOKN (B := 4096) (β := 4) (D := 1024)
      (allBelow_iff.1 varOK) ?_
    exact allFrom_iff.1 relOK_0 r (by omega) (by omega)

end ClusterAlgebras.CertificateData.F4

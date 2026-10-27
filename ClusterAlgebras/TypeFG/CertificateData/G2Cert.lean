/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificatePack
public import ClusterAlgebras.TypeFG.CertificateData.G2Trans0
public import ClusterAlgebras.TypeFG.CertificateData.G2Rel0

/-!
# The `G2` exchange certificate

Assembles the kernel checks of the `G2` data into an exchange certificate, through the
soundness theorem `CertificateCheck.Raw.nonempty_exchangeCertificate`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.G2

open CertificateCheck

/-- The data `raw` satisfies `Raw.initOK` at the initial seed: `α₁ = id` and `vᵢ = Xᵢ`. -/
theorem initOK : raw.initOK 2 2 = true := by decide +kernel

/-- The cluster of each of the `8` seeds of `raw` is strictly increasing with values below `8`. -/
theorem seedOK : allBelow 8 (fun a => raw.seedOK 2 8 a) = true := by decide +kernel

/-- The codes of consecutive seeds of `raw` increase (`Raw.lexOK`). -/
theorem lexOK : allBelow 7 (fun a => raw.lexOK 2 8 a) = true := by decide +kernel

/-- Any two distinct of the `8` cluster variables of `raw` differ (`Raw.distOK`). -/
theorem distOK :
    allBelow 8 (fun c' => allBelow c' fun c => raw.distOK 2 c c') = true := by
  decide +kernel

/-- Each of the `8` cluster variables of `raw` has nonnegative coefficients and exponents of
absolute value at most `3`. -/
theorem varOK : allBelow 8 (fun c => raw.varOK 2 3 c) = true := by decide +kernel

/-- Each of the `8` cluster variables of `raw` lies in the cluster of its covering seed
(`Raw.coverOK`). -/
theorem coverOK : allBelow 8 (fun c => raw.coverOK 2 8 c) = true := by decide +kernel

/-- The spanning-tree data of `raw` is valid at each of the `8` seeds (`Raw.treeOK`). -/
theorem treeOK : allBelow 8 (fun a => raw.treeOK 2 8 a) = true := by decide +kernel

/-- The monomials of each of the `8` exchange relations of `raw` are good lists of atoms
(`Raw.relShapeOK`). -/
theorem relShapeOK : allBelow 8 raw.relShapeOK = true := by decide +kernel

/-- The initial matrix of the certificate. -/
noncomputable def initMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.of fun i j => raw.entry 0 i j

/-- There is an exchange certificate for `initMatrix` with `8` variables and `8` seeds. -/
theorem nonempty_exchangeCertificate (hmn : 2 ≤ 2) :
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

end ClusterAlgebras.CertificateData.G2

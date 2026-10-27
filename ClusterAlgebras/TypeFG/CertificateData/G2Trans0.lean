/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeFG.CertificateData.G2

/-! # Kernel check of the transitions of seeds `[0, 8)` of the `G2` certificate -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.G2

open CertificateCheck

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- Every transition check `raw.transOK` of the `G2` certificate data holds for the seeds
`a ∈ [0, 8)` and the directions `k < 2`. -/
theorem transOK_0 :
    allFrom 0 8 (fun a => allBelow 2 fun k => raw.transOK 2 2 8 8 8 a k) = true := by
  decide +kernel

end ClusterAlgebras.CertificateData.G2

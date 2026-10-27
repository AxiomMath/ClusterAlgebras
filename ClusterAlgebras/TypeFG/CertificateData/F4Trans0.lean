/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeFG.CertificateData.F4

/-! # Kernel check of the transitions of seeds `[0, 105)` of the `F4` certificate -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.F4

open CertificateCheck

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The `F4` certificate `raw` passes `transOK` at every transition `(a, k)` with seed
`a ∈ [0, 105)` and direction `k < 4`. -/
theorem transOK_0 :
    allFrom 0 105 (fun a => allBelow 4 fun k => raw.transOK 4 4 28 105 98 a k) = true := by
  decide +kernel

end ClusterAlgebras.CertificateData.F4

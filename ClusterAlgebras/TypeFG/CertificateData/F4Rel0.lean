/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificatePack
public import ClusterAlgebras.TypeFG.CertificateData.F4

/-! # Kernel check of the exchange relations `[0, 98)` of the `F4` certificate -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.F4

open CertificateCheck

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- The exchange relations of `raw` with indices in `[0, 98)` hold, as checked by `relOKN`. -/
theorem relOK_0 :
    allFrom 0 98 (fun r => raw.relOKN 4 28 4096 4 1024 r) = true := by
  decide +kernel

end ClusterAlgebras.CertificateData.F4

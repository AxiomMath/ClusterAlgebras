/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificatePack
public import ClusterAlgebras.TypeFG.CertificateData.G2E

/-! # Kernel check of the exchange relations `[0, 8)` of the `G2E` certificate -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.G2E

open CertificateCheck

set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- Every exchange relation `r` with `0 ≤ r < 8` of the raw `G2E` certificate passes the
check `relOKN` with parameters `m = 4`, `N = 8`, `B = 4096`, `β = 3` and `D = 1024`. -/
theorem relOK_0 :
    allFrom 0 8 (fun r => raw.relOKN 4 8 4096 3 1024 r) = true := by
  decide +kernel

end ClusterAlgebras.CertificateData.G2E

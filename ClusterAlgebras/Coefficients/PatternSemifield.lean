/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.LaurentPhenomenon.Trivialization
public import ClusterAlgebras.YPattern.Defs

/-!
# The seeds of a pattern lie in the universal semifield of any one of them

Let `Σ` be a seed pattern and `x̃ = x̃(t₀)` the extended cluster of its seed at a vertex `t₀`.
Every entry `x_{i;t}` of every seed `Σ(t)` lies in the universal semifield `ℚ_sf(x̃)`, as does
every entry `ŷ_{k;t}` of its `ŷ`-tuple. Indeed `Σ(t)` is obtained from `Σ(t₀)` by a sequence of
seed mutations, whose cluster variables are subtraction-free rational expressions in `x̃`, and
`ℚ_sf(x̃)` is closed under integer powers and products.

## Main results

* `ClusterAlgebras.IsSeedPattern.extCluster_mem_universalSemifield`: `x_{i;t} ∈ ℚ_sf(x̃(t₀))`.
* `ClusterAlgebras.IsSeedPattern.yHat_mem_universalSemifield`: `ŷ_{k;t} ∈ ℚ_sf(x̃(t₀))`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- **Every extended cluster of a pattern lies in `ℚ_sf(x̃(t₀))`**: each entry `x_{i;t}` of the
seed at `t` is a subtraction-free rational expression in the extended cluster of the seed at
any vertex `t₀`. -/
theorem IsSeedPattern.extCluster_mem_universalSemifield (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ t : RegularTree n)
    (i : Fin m) : (P t).extCluster i ∈ universalSemifield (P t₀).extCluster := by
  rw [hP.apply_eq_seedMutationSeq hmn t₀ t]
  exact seedMutationSeq_extCluster_mem_universalSemifield_self hmn _ _ i

/-- **Every `ŷ`-tuple of a pattern lies in `ℚ_sf(x̃(t₀))`**: `ŷ_{k;t} = ∏ᵢ x_{i;t} ^ b_{ik}(t)`
is a product of integer powers of elements of `ℚ_sf(x̃(t₀))`. -/
theorem IsSeedPattern.yHat_mem_universalSemifield (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ t : RegularTree n)
    (k : Fin n) : yHat (P t) k ∈ universalSemifield (P t₀).extCluster :=
  prod_mem_universalSemifield fun i _ =>
    zpow_mem_universalSemifield (hP.extCluster_mem_universalSemifield hmn t₀ t i) _

end ClusterAlgebras

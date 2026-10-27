/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.WiringDiagram.Chamber

/-!
# Every moment and gap gives a chamber

For a wiring diagram `D`, a moment `t ∈ [0, N]` and a gap `g`, the wires lying at or below `g`
after `t` crossings, `{u_t(1), …, u_t(g)}`, form the chamber set of a chamber of gap `g`: the one
whose span contains `t`.

## Main results

* `belowSet_eq_map_wire`: the wires at or below a gap after `t` crossings are the images under
  `D.wire t` of the levels at or below it.
* `exists_chamberSet_eq_map_wire`: for `t ≤ N` and a gap `g`, some chamber of gap `g` has chamber
  set `{u_t(1), …, u_t(g)}`.

## Implementation notes

Indices are 0-based, as in `ClusterAlgebras.WiringDiagram.Basic`: the gap `g : Fin (n + 1)`
has the levels `0, …, g` at or below it, so the set `{u_t(1), …, u_t(g)}` is the image of
`Finset.Iic g.castSucc` under `u_t = D.wire t`.
-/
@[expose] public section

namespace ClusterAlgebras

namespace WiringDiagram

variable {n : ℕ} (D : WiringDiagram n)

/-- The wires at or below the gap `g` after `t` crossings are the images under `D.wire t` of the
levels at or below `g`, so `D.belowSet t g` is the set `{u_t(1), …, u_t(g)}`. -/
theorem belowSet_eq_map_wire (t : ℕ) (g : Fin (n + 1)) :
    D.belowSet t g = (Finset.Iic g.castSucc).map (D.wire t).toEmbedding := by
  ext v
  rw [mem_belowSet, Finset.mem_map]
  constructor
  · exact fun h => ⟨D.levelOf t v, Finset.mem_Iic.2 h, by simp [levelOf]⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [levelOf] using Finset.mem_Iic.1 hx

/-- **Every moment and gap gives a chamber.** For `t ≤ N` and a gap `g` there is a chamber of gap
`g` whose chamber set is `{u_t(1), …, u_t(g)}`. -/
@[cluster_algebras "lem_chamber_set_at_time"]
theorem exists_chamberSet_eq_map_wire {t : ℕ} (ht : t ≤ D.word.length) (g : Fin (n + 1)) :
    ∃ c : D.Chamber, c.gap = g ∧
      c.chamberSet = (Finset.Iic g.castSucc).map (D.wire t).toEmbedding :=
  ⟨D.chamberAt g t ht, rfl, by
    rw [Chamber.chamberSet_eq_belowSet _ ht (D.inSpan_chamberAt g ht), gap_chamberAt,
      belowSet_eq_map_wire]⟩

/-- For `t ≤ N` and a gap `g` there is a chamber of gap `g` whose chamber set is
`D.belowSet t g`. -/
theorem exists_chamberSet_eq_belowSet {t : ℕ} (ht : t ≤ D.word.length) (g : Fin (n + 1)) :
    ∃ c : D.Chamber, c.gap = g ∧ c.chamberSet = D.belowSet t g := by
  rw [belowSet_eq_map_wire]
  exact D.exists_chamberSet_eq_map_wire ht g

end WiringDiagram

end ClusterAlgebras

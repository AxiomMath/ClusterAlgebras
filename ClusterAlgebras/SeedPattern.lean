/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Seed

/-!
# The regular tree and seed patterns

The `n`-regular tree `𝕋ₙ` has as vertices the finite sequences in `[1, n]` with no two
consecutive entries equal, joined by an edge labelled `k` when one is the other with `k`
appended. A *seed pattern* assigns a labeled seed to every vertex so that the two ends of
each edge labelled `k` are related by seed mutation in direction `k`.

The ground field is not assumed to have characteristic zero; the one result here that needs
it carries it as a hypothesis.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- A vertex of the **`n`-regular tree** `𝕋ₙ`: a finite sequence of elements of `[1, n]` in
which no two consecutive entries are equal. FWZ take `n ≥ 1`; nothing here uses
it. -/
@[cluster_algebras "def_regular_tree"]
structure RegularTree (n : ℕ) where
  /-- The sequence `(k₁, …, k_r)`. -/
  word : List (Fin n)
  /-- No two consecutive entries are equal. -/
  isChain_ne : word.IsChain (· ≠ ·)

/-- Two vertices of `𝕋ₙ` are joined by an **edge labelled `k`**, written `t —k— t'`, when
one is obtained from the other by appending `k` at the end. -/
@[cluster_algebras "def_regular_tree"]
def RegularTree.Adj (k : Fin n) (t t' : RegularTree n) : Prop :=
  t'.word = t.word ++ [k] ∨ t.word = t'.word ++ [k]

/-- The **root** of `𝕋ₙ`: the empty sequence. -/
def RegularTree.root : RegularTree n := ⟨[], List.isChain_nil⟩

/-- The word of the root is empty. -/
@[simp]
theorem RegularTree.word_root : (RegularTree.root : RegularTree n).word = [] := rfl

/-- Deleting the last entry of a vertex gives a vertex, joined to it by an edge labelled by
that entry. -/
theorem RegularTree.adj_of_word_eq_append {t : RegularTree n} {w : List (Fin n)} {k : Fin n}
    (h : t.word = w ++ [k]) :
    RegularTree.Adj k t ⟨w, (h ▸ t.isChain_ne).left_of_append⟩ :=
  Or.inr h

/-- Every vertex of `𝕋ₙ` has a neighbour along an edge with any given label. -/
theorem RegularTree.exists_adj (t : RegularTree n) (k : Fin n) :
    ∃ t', RegularTree.Adj k t t' := by
  obtain ⟨w, hw⟩ := t
  cases w using List.reverseRecOn with
  | nil => exact ⟨⟨[k], List.isChain_singleton k⟩, Or.inl rfl⟩
  | append_singleton w j =>
    by_cases hjk : j = k
    · subst hjk
      exact ⟨_, RegularTree.adj_of_word_eq_append (t := ⟨_, hw⟩) rfl⟩
    · exact ⟨⟨w ++ [j] ++ [k], hw.append (List.isChain_singleton k) (by simpa using hjk)⟩,
        Or.inl rfl⟩

/-- A walk from `u` to `t'` extends to a walk from `t` to `t'` along an edge `t —k— u`. -/
private theorem RegularTree.exists_walk_of_adj_of_exists_walk {k : Fin n}
    {t u t' : RegularTree n} (h : RegularTree.Adj k t u)
    (hw : ∃ (d : ℕ) (s : Fin (d + 1) → RegularTree n) (k : Fin d → Fin n),
      s 0 = u ∧ s (Fin.last d) = t' ∧
        ∀ i : Fin d, RegularTree.Adj (k i) (s i.castSucc) (s i.succ)) :
    ∃ (d : ℕ) (s : Fin (d + 1) → RegularTree n) (k : Fin d → Fin n),
      s 0 = t ∧ s (Fin.last d) = t' ∧
        ∀ i : Fin d, RegularTree.Adj (k i) (s i.castSucc) (s i.succ) := by
  obtain ⟨d, s, κ, h0, hl, hs⟩ := hw
  refine ⟨d + 1, Fin.cons t s, Fin.cons k κ, rfl, by rw [← Fin.succ_last, Fin.cons_succ, hl],
    fun i ↦ ?_⟩
  cases i using Fin.cases with
  | zero => simpa [h0] using h
  | succ j => simpa [← Fin.succ_castSucc] using hs j

/-- A walk from `t` to `u` extends to a walk from `t` to `t'` along an edge `u —k— t'`. -/
private theorem RegularTree.exists_walk_of_exists_walk_of_adj {k : Fin n}
    {t u t' : RegularTree n}
    (hw : ∃ (d : ℕ) (s : Fin (d + 1) → RegularTree n) (k : Fin d → Fin n),
      s 0 = t ∧ s (Fin.last d) = u ∧
        ∀ i : Fin d, RegularTree.Adj (k i) (s i.castSucc) (s i.succ))
    (h : RegularTree.Adj k u t') :
    ∃ (d : ℕ) (s : Fin (d + 1) → RegularTree n) (k : Fin d → Fin n),
      s 0 = t ∧ s (Fin.last d) = t' ∧
        ∀ i : Fin d, RegularTree.Adj (k i) (s i.castSucc) (s i.succ) := by
  obtain ⟨d, s, κ, h0, hl, hs⟩ := hw
  refine ⟨d + 1, Fin.snoc s t', Fin.snoc κ k, ?_, Fin.snoc_last _ _, fun i ↦ ?_⟩
  · rw [← Fin.castSucc_zero, Fin.snoc_castSucc, h0]
  cases i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.succ_last, hl] using h
  | cast j =>
    simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
    exact hs j

/-- **Any two vertices of the tree are joined by a walk**: vertices `t = s₀, s₁, …, s_d = t'`
and labels `k₁, …, k_d` with `sᵢ₋₁ —kᵢ— sᵢ` for every `i`. -/
@[cluster_algebras "lem_tree_path"]
theorem RegularTree.exists_walk (t t' : RegularTree n) :
    ∃ (d : ℕ) (s : Fin (d + 1) → RegularTree n) (k : Fin d → Fin n),
      s 0 = t ∧ s (Fin.last d) = t' ∧
        ∀ i : Fin d, RegularTree.Adj (k i) (s i.castSucc) (s i.succ) := by
  have hroot : ∀ t' : RegularTree n, ∃ (d : ℕ) (s : Fin (d + 1) → RegularTree n)
      (k : Fin d → Fin n), s 0 = .root ∧ s (Fin.last d) = t' ∧
        ∀ i : Fin d, RegularTree.Adj (k i) (s i.castSucc) (s i.succ) := by
    rintro ⟨w, hw⟩
    induction w using List.reverseRecOn with
    | nil => exact ⟨0, fun _ ↦ .root, Fin.elim0, rfl, rfl, fun i ↦ i.elim0⟩
    | append_singleton w k ih =>
      exact RegularTree.exists_walk_of_exists_walk_of_adj (ih hw.left_of_append)
        (Or.inl rfl)
  obtain ⟨w, hw⟩ := t
  induction w using List.reverseRecOn with
  | nil => exact hroot t'
  | append_singleton w k ih =>
    exact RegularTree.exists_walk_of_adj_of_exists_walk
      (RegularTree.adj_of_word_eq_append (t := ⟨_, hw⟩) rfl) (ih hw.left_of_append)

variable (K) in
/-- `P` is a **seed pattern** of rank `n` in `F` over `K` when it assigns a labeled seed to
every vertex of `𝕋ₙ` and the seeds at the two ends of an edge labelled `k` are related by
seed mutation in direction `k`. FWZ take `K` of characteristic zero and `n ≥ 1`;
the definition uses neither, so neither is assumed here. -/
@[cluster_algebras "def_seed_pattern"]
def IsSeedPattern (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) : Prop :=
  (∀ t, IsLabeledSeed K hmn (P t)) ∧
    ∀ (k : Fin n) (t t' : RegularTree n), RegularTree.Adj k t t' → P t' = seedMutation hmn (P t) k

/-- Mutating a labeled seed along the reverse of `s`, then along `s`, returns it. -/
theorem seedMutationSeq_seedMutationSeq_reverse [CharZero K] (hmn : n ≤ m)
    {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) (s : List (Fin n)) :
    seedMutationSeq hmn (seedMutationSeq hmn S s.reverse) s = S := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    rw [List.reverse_cons, seedMutationSeq_append, seedMutationSeq_cons,
      seedMutationSeq_cons, seedMutationSeq_nil,
      seedMutation_seedMutation hmn (hS.seedMutationSeq hmn s.reverse), ih]

/-- **A seed pattern exists through any seed**: given a vertex `t₀` and a labeled seed `S₀`,
some seed pattern takes the value `S₀` at `t₀`. -/
@[cluster_algebras "lem_seed_pattern_exists"]
theorem exists_isSeedPattern [CharZero K] (hmn : n ≤ m) (t₀ : RegularTree n)
    {S₀ : SeedData F m n} (hS₀ : IsLabeledSeed K hmn S₀) :
    ∃ P : RegularTree n → SeedData F m n, IsSeedPattern K hmn P ∧ P t₀ = S₀ := by
  set R := seedMutationSeq hmn S₀ t₀.word.reverse
  have hR : IsLabeledSeed K hmn R := hS₀.seedMutationSeq hmn _
  refine ⟨fun t ↦ seedMutationSeq hmn R t.word, ⟨fun t ↦ hR.seedMutationSeq hmn _, ?_⟩,
    seedMutationSeq_seedMutationSeq_reverse hmn hS₀ _⟩
  rintro k t t' (h | h)
  · simp [h]
  · simp only [h, seedMutationSeq_append, seedMutationSeq_cons, seedMutationSeq_nil]
    exact (seedMutation_seedMutation hmn (hR.seedMutationSeq hmn _) k).symm

/-- The seed of a pattern at `t` is the mutation of the seed at the root along `t`. -/
theorem IsSeedPattern.apply_eq_seedMutationSeq_root (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t : RegularTree n) :
    P t = seedMutationSeq hmn (P .root) t.word := by
  obtain ⟨w, hw⟩ := t
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w k ih =>
    rw [seedMutationSeq_append, ← ih hw.left_of_append]
    exact hP.2 k _ _ (Or.inl rfl)

/-- The seed of a pattern at the root is the mutation of the seed at `t` along the reverse
of `t`. -/
theorem IsSeedPattern.apply_root_eq_seedMutationSeq (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t : RegularTree n) :
    P .root = seedMutationSeq hmn (P t) t.word.reverse := by
  obtain ⟨w, hw⟩ := t
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w k ih =>
    rw [ih hw.left_of_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append, seedMutationSeq_cons,
      ← hP.2 k _ _ (RegularTree.adj_of_word_eq_append (t := ⟨_, hw⟩) rfl)]

/-- The seed of a pattern at `t` is the mutation of the seed at `t₀` along the reverse of
`t₀` followed by `t`. -/
theorem IsSeedPattern.apply_eq_seedMutationSeq (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ t : RegularTree n) :
    P t = seedMutationSeq hmn (P t₀) (t₀.word.reverse ++ t.word) := by
  rw [seedMutationSeq_append, ← hP.apply_root_eq_seedMutationSeq hmn,
    hP.apply_eq_seedMutationSeq_root hmn]

/-- **A seed pattern is determined by any one of its seeds**: two seed patterns that agree at
one vertex agree everywhere. -/
@[cluster_algebras "lem_seed_pattern_unique"]
theorem IsSeedPattern.eq_of_apply_eq (hmn : n ≤ m) {P P' : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern K hmn P) (hP' : IsSeedPattern K hmn P') {t₀ : RegularTree n}
    (h : P t₀ = P' t₀) : P = P' := by
  funext t
  rw [hP.apply_eq_seedMutationSeq hmn t₀, hP'.apply_eq_seedMutationSeq hmn t₀, h]

/-- **Seeds of a pattern are mutations of any one of them**: the seed at `t` is obtained from
the seed at `t₀` by mutation along some sequence. -/
@[cluster_algebras "lem_pattern_path"]
theorem IsSeedPattern.exists_seedMutationSeq_eq (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ t : RegularTree n) :
    ∃ s : List (Fin n), P t = seedMutationSeq hmn (P t₀) s :=
  ⟨_, hP.apply_eq_seedMutationSeq hmn t₀ t⟩

/-- **Every mutation of a seed of a pattern is a seed of the pattern**: mutating the seed at
`t₀` along any sequence gives the seed at some vertex. -/
@[cluster_algebras "lem_pattern_walk"]
theorem IsSeedPattern.seedMutationSeq_mem_range (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ : RegularTree n)
    (s : List (Fin n)) : seedMutationSeq hmn (P t₀) s ∈ Set.range P := by
  induction s generalizing t₀ with
  | nil => exact ⟨t₀, rfl⟩
  | cons k s ih =>
    obtain ⟨t₁, h⟩ := t₀.exists_adj k
    rw [seedMutationSeq_cons, ← hP.2 k _ _ h]
    exact ih t₁

end ClusterAlgebras

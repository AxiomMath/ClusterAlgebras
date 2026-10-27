/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

/-!
# The computational core of the exchange-certificate checks

The definitions that the kernel evaluates when it checks the data of an exchange certificate:
bounded conjunctions, the compact encodings of the data (`CertificateCheck.NatTree`,
`CertificateCheck.decodeTerm`, `CertificateCheck.decodeAtoms`), the raw certificate
`CertificateCheck.Raw`, and the check of an exchange relation by evaluation at a power of two
(`CertificateCheck.Raw.relOKD`). They use the core library only, so that a module stating such a
check imports no more than its data. What the checks mean is proved in
`ClusterAlgebras.TypeE.CertificateCheck` and `ClusterAlgebras.TypeE.CertificateDense`.
-/

@[expose] public section

namespace ClusterAlgebras

namespace CertificateCheck

/-! ### Bounded checks -/

/-- `allBelow n p` is `p (n - 1) && ⋯ && p 0`, by primitive recursion, which the kernel
evaluates without building intermediate lists. -/
def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec true (fun i acc => p i && acc) n

/-- `allBelow (n + 1) p` is `p n && allBelow n p`. -/
theorem allBelow_succ (n : Nat) (p : Nat → Bool) : allBelow (n + 1) p = (p n && allBelow n p) :=
  rfl

/-- `allBelow n p` holds if and only if `p i` holds for every `i < n`. -/
theorem allBelow_iff {n : Nat} {p : Nat → Bool} : allBelow n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih => rw [allBelow_succ, Bool.and_eq_true, ih, Nat.forall_lt_succ_right, and_comm]

/-- `allFrom lo len p` checks `p` on `[lo, lo + len)`. -/
def allFrom (lo len : Nat) (p : Nat → Bool) : Bool :=
  allBelow len fun i => p (lo + i)

/-- `allFrom lo len p` holds if and only if `p i` holds for every `i` with `lo ≤ i < lo + len`. -/
theorem allFrom_iff {lo len : Nat} {p : Nat → Bool} :
    allFrom lo len p = true ↔ ∀ i, lo ≤ i → i < lo + len → p i = true := by
  rw [allFrom, allBelow_iff]
  refine ⟨fun h i h₁ h₂ => ?_, fun h i hi => h (lo + i) (by omega) (by omega)⟩
  simpa [Nat.add_sub_cancel' h₁] using h (i - lo) (by omega)

/-- A check on `[lo, lo + a + b)` is assembled from checks on `[lo, lo + a)` and
`[lo + a, lo + a + b)`, so that it can be evaluated by the kernel in small pieces. -/
theorem allFrom_add {lo a b : Nat} {p : Nat → Bool} (h₁ : allFrom lo a p = true)
    (h₂ : allFrom (lo + a) b p = true) : allFrom lo (a + b) p = true := by
  rw [allFrom_iff] at *
  intro i h1 h2
  by_cases h : i < lo + a
  · exact h₁ i h1 h
  · exact h₂ i (by omega) (by omega)

/-- `∑_{i < n} f i`, by primitive recursion. -/
def sumBelow (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec 0 (fun i acc => Nat.add (f i) acc) n

/-- `sumBelow (n + 1) f` is `f n + sumBelow n f`. -/
theorem sumBelow_succ (n : Nat) (f : Nat → Nat) : sumBelow (n + 1) f = f n + sumBelow n f :=
  rfl

/-! ### Compact data -/

/-- A Laurent polynomial as a list of terms `(exponent vector, coefficient)`. -/
abbrev Poly : Type := List (List Int × Int)

/-- A binary tree of natural numbers, for logarithmic-time lookup of data in the kernel. -/
inductive NatTree
  /-- The empty tree. -/
  | leaf
  /-- A node with a left subtree, a value and a right subtree. -/
  | node (left : NatTree) (val : Nat) (right : NatTree)

/-- Lookup in a `NatTree`: index `0` is the root, indices `2i + 1` and `2i + 2` are index `i`
of the left and right subtrees. Missing entries are `0`. -/
def NatTree.get : NatTree → Nat → Nat
  | .leaf, _ => 0
  | .node l v r, i =>
    bif Nat.beq i 0 then v
    else bif Nat.beq (Nat.mod (i - 1) 2) 0 then l.get (Nat.div (i - 1) 2)
    else r.get (Nat.div (i - 1) 2)

/-- The digit of `x` in position `i` in base `b`. -/
def digit (x b i : Nat) : Nat :=
  Nat.mod (Nat.div x (Nat.pow b i)) b

/-- A term `(e, c)` decoded from its code `c · 32^m + ∑ᵢ (eᵢ + 16) 32^i`. -/
def decodeTerm (m x : Nat) : List Int × Int :=
  ((List.range m).map fun i => ((digit x 32 i : Nat) : Int) - 16,
    ((Nat.div x (Nat.pow 32 m) : Nat) : Int))

/-- A term list decoded from the base-`W` digits of `x` (at most `fuel` terms). -/
def decodePoly (m W : Nat) : Nat → Nat → Poly
  | 0, _ => []
  | fuel + 1, x =>
    bif Nat.beq x 0 then [] else decodeTerm m (Nat.mod x W) :: decodePoly m W fuel (Nat.div x W)

/-- A list of atoms with exponents, decoded from base-`4096` digits `16 · atom + exponent + 1`. -/
def decodeAtoms : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, x =>
    bif Nat.beq x 0 then []
    else (Nat.div (Nat.mod x 4096 - 1) 16, Nat.mod (Nat.mod x 4096 - 1) 16) ::
      decodeAtoms fuel (Nat.div x 4096)

/-! ### Raw certificates -/

/-- The data of an exchange certificate as functions of natural numbers.
* `var c`: the term list of `v_c`;
* `alpha a i`: the index `α_a(i)`;
* `matD a i j`: the entry `(i, j)` of `B̃_a`, plus `bias`;
* `next a k`, `perm a k j`: `ν(a, k)` and `π_{a,k}(j)`;
* `rel a k`: the index of the verified exchange relation used by the transition `(a, k)`, and
  `relX r`, `relY r`, `relPos r`, `relNeg r` the relation `v_X v_Y = ∏ P + ∏ Q`, where an
  atom `c < N` stands for `v_c` and an atom `N + i` for the frozen indeterminate `X_i`;
* `parent a`, `parentDir a`, `depth a`: a spanning tree of the transitions, for (D4);
* `cover c`: a seed whose cluster contains `c`, for (D3). -/
structure Raw where
  /-- The bias of the matrix digits. -/
  bias : Nat
  /-- The variables. -/
  var : Nat → Poly
  /-- The clusters. -/
  alpha : Nat → Nat → Nat
  /-- The matrix digits. -/
  matD : Nat → Nat → Nat → Nat
  /-- The transitions. -/
  next : Nat → Nat → Nat
  /-- The relabellings of the transitions. -/
  perm : Nat → Nat → Nat → Nat
  /-- The relation used by a transition. -/
  rel : Nat → Nat → Nat
  /-- The first variable of a relation. -/
  relX : Nat → Nat
  /-- The second variable of a relation. -/
  relY : Nat → Nat
  /-- The first monomial of a relation. -/
  relPos : Nat → List (Nat × Nat)
  /-- The second monomial of a relation. -/
  relNeg : Nat → List (Nat × Nat)
  /-- The depth in the spanning tree. -/
  depth : Nat → Nat
  /-- The parent in the spanning tree. -/
  parent : Nat → Nat
  /-- The direction from the parent. -/
  parentDir : Nat → Nat
  /-- A seed containing a variable. -/
  cover : Nat → Nat

/-! ### Exchange relations by evaluation at a power of two -/

/-- `∏_{i < n} f i`, by primitive recursion. -/
def prodBelow (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec 1 (fun i acc => Nat.mul (f i) acc) n

/-- The block of the sum of two blocks, at the smaller of their keys. -/
def comb (k : Nat) (x y : Nat × Nat) : Nat × Nat :=
  bif Nat.blt x.1 y.1 then (x.1, Nat.add x.2 (Nat.shiftLeft y.2 (Nat.mul k (Nat.sub y.1 x.1))))
  else (y.1, Nat.add (Nat.shiftLeft x.2 (Nat.mul k (Nat.sub x.1 y.1))) y.2)

/-- Combining adjacent pairs of a list of blocks. -/
def pairs (k : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | x :: y :: rest => comb k x y :: pairs k rest
  | l => l

/-- One block for a list of blocks, by rounds of `pairs`. -/
def collapse (k : Nat) : Nat → List (Nat × Nat) → Nat × Nat
  | _, [] => (0, 0)
  | _, [x] => x
  | 0, x :: y :: rest => (x :: y :: rest).foldr (comb k) (0, 0)
  | f + 1, x :: y :: rest => collapse k f (pairs k (x :: y :: rest))

/-- `∑ c · 2^{k a}` over a list of blocks `(a, c)`. Adjacent blocks are combined in rounds, so that
the numbers built have about the total length, times the number of rounds, when the keys are
sorted. -/
def evalBlocks (k : Nat) (l : List (Nat × Nat)) : Nat :=
  Nat.shiftLeft (collapse k 16 l).2 (Nat.mul k (collapse k 16 l).1)

/-- The digit of exponent `i` of the term with code `x`. -/
abbrev dg (x i : Nat) : Nat :=
  digit x 32 i

/-- The least digit of exponent `i` among the codes `cs` (`32` if there is none). -/
def loDig (cs : List Nat) (i : Nat) : Nat :=
  cs.foldr (fun x a => bif Nat.blt (dg x i) a then dg x i else a) 32

/-- The largest digit of exponent `i` among the codes `cs` (`0` if there is none). -/
def hiDig (cs : List Nat) (i : Nat) : Nat :=
  cs.foldr (fun x a => bif Nat.blt a (dg x i) then dg x i else a) 0

/-- The sum of the coefficients of the terms with codes `cs`. -/
def csum (m : Nat) (cs : List Nat) : Nat :=
  (cs.map fun x => Nat.div x (Nat.pow 32 m)).sum

/-- The key `∑ᵢ (dᵢ - loᵢ) wᵢ` of the term with code `x`, `dᵢ` its digits. -/
def termKey (m : Nat) (lo w : Nat → Nat) (x : Nat) : Nat :=
  sumBelow m fun i => Nat.mul (Nat.sub (dg x i) (lo i)) (w i)

/-- The number `∑ c · 2^{k · key}` of the terms with codes `cs`, keys relative to their least
digits. -/
def atomNum (m k : Nat) (w : Nat → Nat) (cs : List Nat) : Nat :=
  evalBlocks k (cs.map fun x => (termKey m (loDig cs) w x, Nat.div x (Nat.pow 32 m)))

/-- The code of the term `Xᵢ` (see `decodeTerm`): digits `16`, `17` at `i`, coefficient `1`. -/
def unitCode (m i : Nat) : Nat :=
  Nat.add (sumBelow m fun j => Nat.mul (bif Nat.beq j i then 17 else 16) (Nat.pow 32 j))
    (Nat.pow 32 m)

/-- The term codes of an atom: those of `v_c` for `c < N`, that of `X_{c - N}` otherwise. -/
def atomCodes (codes : Nat → List Nat) (m N c : Nat) : List Nat :=
  bif Nat.blt c N then codes c else [unitCode m (c - N)]

/-- `∑ e · loDig` over the atoms `(c, e)` of a monomial. -/
def monoLo (codes : Nat → List Nat) (m N : Nat) (l : List (Nat × Nat)) (i : Nat) : Nat :=
  (l.map fun t => Nat.mul t.2 (loDig (atomCodes codes m N t.1) i)).sum

/-- `∑ e · hiDig` over the atoms `(c, e)` of a monomial. -/
def monoHi (codes : Nat → List Nat) (m N : Nat) (l : List (Nat × Nat)) (i : Nat) : Nat :=
  (l.map fun t => Nat.mul t.2 (hiDig (atomCodes codes m N t.1) i)).sum

/-- `∏ csum^e` over the atoms `(c, e)` of a monomial. -/
def monoSum (codes : Nat → List Nat) (m N : Nat) (l : List (Nat × Nat)) : Nat :=
  l.foldr (fun t acc => Nat.mul (Nat.pow (csum m (atomCodes codes m N t.1)) t.2) acc) 1

/-- `∏ atomNum^e` over the atoms `(c, e)` of a monomial. -/
def monoNum (codes : Nat → List Nat) (m N k : Nat) (w : Nat → Nat) (l : List (Nat × Nat)) : Nat :=
  l.foldr (fun t acc => Nat.mul (Nat.pow (atomNum m k w (atomCodes codes m N t.1)) t.2) acc) 1

/-- `∑ᵢ loDig cs i · wᵢ`. -/
def loKey (m : Nat) (w : Nat → Nat) (cs : List Nat) : Nat :=
  sumBelow m fun i => Nat.mul (loDig cs i) (w i)

/-- The variables with term codes `codes c` and `codes c'` take different values at
`Xᵢ = 2^{k wᵢ}`, both values being multiplied by `2^{16 k ∑ wᵢ}` to make them natural numbers. -/
def distOKD (codes : Nat → List Nat) (m k : Nat) (w : Nat → Nat) (c c' : Nat) : Bool :=
  !Nat.beq (Nat.shiftLeft (atomNum m k w (codes c)) (Nat.mul k (loKey m w (codes c))))
    (Nat.shiftLeft (atomNum m k w (codes c')) (Nat.mul k (loKey m w (codes c'))))

namespace Raw

variable (R : Raw)

/-- The sum of the exponents of a list of atoms. -/
def degAtoms (l : List (Nat × Nat)) : Nat :=
  (l.map fun t => t.2).sum

/-- `loDig v_X + loDig v_Y` in exponent `i`, for the relation `r`. -/
def relLo (codes : Nat → List Nat) (m N r i : Nat) : Nat :=
  Nat.add (loDig (atomCodes codes m N (R.relX r)) i) (loDig (atomCodes codes m N (R.relY r)) i)

/-- `hiDig v_X + hiDig v_Y` in exponent `i`, for the relation `r`. -/
def relHi (codes : Nat → List Nat) (m N r i : Nat) : Nat :=
  Nat.add (hiDig (atomCodes codes m N (R.relX r)) i) (hiDig (atomCodes codes m N (R.relY r)) i)

/-- The width in exponent `i` of the box of `v_X v_Y`. -/
def relRad (codes : Nat → List Nat) (m N r i : Nat) : Nat :=
  Nat.sub (Nat.add (R.relHi codes m N r i) 1) (R.relLo codes m N r i)

/-- The mixed-radix weights of the box of `v_X v_Y`. -/
def relW (codes : Nat → List Nat) (m N r i : Nat) : Nat :=
  prodBelow i (R.relRad codes m N r)

/-- A bound for the coefficients of both sides of the relation `r`, through the sums of the
coefficients. -/
def relBound (codes : Nat → List Nat) (m N r : Nat) : Nat :=
  Nat.max
    (Nat.mul (csum m (atomCodes codes m N (R.relX r))) (csum m (atomCodes codes m N (R.relY r))))
    (Nat.add (monoSum codes m N (R.relPos r)) (monoSum codes m N (R.relNeg r)))

/-- The number of binary digits given to a coefficient. -/
def relK (codes : Nat → List Nat) (m N r : Nat) : Nat :=
  Nat.add (Nat.log2 (R.relBound codes m N r)) 1

/-- The box of the monomial `l` lies in that of `v_X v_Y`. -/
def monoBoxOK (codes : Nat → List Nat) (m N r : Nat) (l : List (Nat × Nat)) : Bool :=
  allBelow m fun i =>
    Nat.ble (Nat.add (R.relLo codes m N r i) (Nat.mul 16 (degAtoms l)))
        (Nat.add (monoLo codes m N l i) 32) &&
      Nat.ble (Nat.add (monoHi codes m N l i) 32)
        (Nat.add (R.relHi codes m N r i) (Nat.mul 16 (degAtoms l)))

/-- The key of the corner of the box of the monomial `l` in that of `v_X v_Y`. -/
def monoShift (codes : Nat → List Nat) (m N r : Nat) (l : List (Nat × Nat)) : Nat :=
  sumBelow m fun i =>
    Nat.mul (Nat.sub (Nat.add (monoLo codes m N l i) 32)
      (Nat.add (R.relLo codes m N r i) (Nat.mul 16 (degAtoms l)))) (R.relW codes m N r i)

/-- The relation `r` holds, checked by evaluation at `Xᵢ = 2^{k wᵢ}`, the variables being given by
their term codes `codes`. -/
def relOKD (codes : Nat → List Nat) (m N r : Nat) : Bool :=
  Nat.blt (R.relX r) N && Nat.blt (R.relY r) N && R.monoBoxOK codes m N r (R.relPos r) &&
    R.monoBoxOK codes m N r (R.relNeg r) &&
    Nat.blt (R.relBound codes m N r) (Nat.pow 2 (R.relK codes m N r)) &&
    Nat.beq
      (Nat.mul (atomNum m (R.relK codes m N r) (R.relW codes m N r)
          (atomCodes codes m N (R.relX r)))
        (atomNum m (R.relK codes m N r) (R.relW codes m N r) (atomCodes codes m N (R.relY r))))
      (Nat.add
        (Nat.shiftLeft (monoNum codes m N (R.relK codes m N r) (R.relW codes m N r) (R.relPos r))
          (Nat.mul (R.relK codes m N r) (R.monoShift codes m N r (R.relPos r))))
        (Nat.shiftLeft (monoNum codes m N (R.relK codes m N r) (R.relW codes m N r) (R.relNeg r))
          (Nat.mul (R.relK codes m N r) (R.monoShift codes m N r (R.relNeg r)))))

end Raw

end CertificateCheck

end ClusterAlgebras

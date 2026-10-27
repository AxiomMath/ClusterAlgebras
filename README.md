[![](logo.svg)](https://axiommath.ai/)

# Introduction to Cluster Algebras

This is a Lean formalization of Chapters 1–7 of Fomin, Williams and Zelevinsky's *Introduction to Cluster Algebras*.

## Main Results

* Mutating a quiver and then taking its extended exchange matrix agrees with mutating the matrix.
* Matrix mutation preserves the determinant when the mutated diagonal entry vanishes.
* Matrix mutation preserves the rank when the mutated diagonal entry vanishes.
* Matrix mutation preserves the gcd of the entries, assuming mutation in that direction is an involution.
* A skew-symmetrizing vector of a matrix with connected diagram is unique up to a scalar.
* The Markov quiver is isomorphic to each of its mutations.
* The arrows between the chambers of a wiring diagram form a quiver.
* A braid move of a wiring diagram mutates its quiver.
* A double wiring diagram on `n + 2` strands has `(n + 2)²` chambers, `(n + 1)²` of them bounded.
* Orientations of non-isomorphic finite trees are not mutation equivalent, assuming the Caldero–Keller theorem.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only depends on Mathlib. It contains formal statements of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:
```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck

/-!
# Exchange-certificate data: `G2`

Exchange-certificate data for the `2 × 2` exchange matrix `[[0, 3], [-1, 0]]` of type `G2`:
`8` variables, `8` seeds, `8` distinct exchange relations. Seeds are listed in increasing
lexicographic order of their (increasing) clusters; seed `0` is the initial seed. Each seed is
one natural number whose bit fields hold its cluster, its matrix digits (entry plus `8`, four
bits each), its transitions, their relabellings and relations, and its position in a
breadth-first spanning tree.

## Implementation notes

The definitions are `noncomputable`: only the kernel evaluates them.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.G2

open CertificateCheck NatTree

set_option maxRecDepth 1000000

/-- The seeds. -/
noncomputable def seedTree : NatTree :=
  (node (node (node (node leaf
    106359009325604851726657810225159472902 leaf)
    42545680696523705575064148136020149250 leaf)
    1334420371874106642746374416020013824 (node leaf
    63818521005171474735057439932259239428 leaf))
    79228238090575089067420549376 (node (node leaf
    21278032684738098020158230736546563331 leaf)
    5192296862166345900601342334337537 (node leaf
    85086169016959500418303747700146308869 leaf)))

/-- The variables, each a list of term codes. -/
noncomputable def varList : List (List ℕ) :=
  [[1553],
    [1584],
    [1583, 1551],
    [1523, 1520],
    [1613, 3629, 3597, 1520, 1517],
    [1551, 1522, 1519],
    [1582, 2574, 1521, 1518],
    [1581, 3597, 3568, 3565, 1491, 2512, 1485]]

/-- The exchange relations. -/
noncomputable def relTree : NatTree :=
  (node (node (node (node leaf
    7472645 leaf)
    43521329506126650289423361 leaf)
    262913 (node leaf
    5506819 leaf))
    21760664753063325144711680 (node (node leaf
    79789104094565525530609154 leaf)
    3278080 (node leaf
    120892581961462917470619396 leaf)))

/-- A seed containing each variable. -/
noncomputable def coverTree : NatTree :=
  (node (node (node (node leaf
    6 leaf)
    1 leaf)
    0 (node leaf
    4 leaf))
    0 (node (node leaf
    3 leaf)
    2 (node leaf
    5 leaf)))

/-- The raw certificate. -/
noncomputable def raw : Raw where
  bias := 8
  var c := (varList.getD c []).map (decodeTerm 2)
  alpha a i := digit (seedTree.get a) 256 i
  matD a i j := digit (Nat.div (seedTree.get a) 65536) 16 (i * 2 + j)
  next a k := digit (Nat.div (seedTree.get a) 4294967296) 65536 k
  perm a k j := digit (Nat.div (seedTree.get a) 18446744073709551616) 16 (k * 2 + j)
  rel a k := digit (Nat.div (seedTree.get a) 1208925819614629174706176) 65536 k
  relX r := Nat.mod (relTree.get r) 256
  relY r := Nat.mod (Nat.div (relTree.get r) 256) 256
  relPos r := decodeAtoms 8 (Nat.mod (Nat.div (relTree.get r) 65536) 18446744073709551616)
  relNeg r := decodeAtoms 8 (Nat.div (relTree.get r) 1208925819614629174706176)
  depth a := Nat.mod (Nat.div (seedTree.get a) 5192296858534827628530496329220096) 256
  parent a := Nat.div (seedTree.get a) 21267647932558653966460912964485513216
  parentDir a := Nat.mod (Nat.div (seedTree.get a) 1329227995784915872903807060280344576) 16
  cover c := coverTree.get c

end ClusterAlgebras.CertificateData.G2

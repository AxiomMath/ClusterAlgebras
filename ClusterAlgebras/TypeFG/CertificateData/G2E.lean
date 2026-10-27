/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck

/-!
# Exchange-certificate data: `G2E`

Exchange-certificate data for the `4 × 2` matrix `[[0, 3], [-1, 0], [1, 0], [0, 1]]`: `8`
variables, `8` seeds, `8` distinct exchange relations. Seeds are listed in increasing
lexicographic order of their (increasing) clusters; seed `0` is the initial seed. Each seed is
one natural number whose bit fields hold its cluster, its matrix digits (entry plus `8`, four
bits each), its transitions, their relabellings and relations, and its position in a
breadth-first spanning tree. The checks are in the `Check` files; nothing here is trusted. The
definitions are `noncomputable`: only the kernel evaluates them.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.G2E

open CertificateCheck NatTree

set_option maxRecDepth 1000000

/-- The seeds. -/
noncomputable def seedTree : NatTree :=
  (node (node (node (node leaf
    6970344035162839562758246250882660004529926 leaf)
    2788273730127377568567404012226421821277186 leaf)
    87452573491141452939026393709808635609856 (node leaf
    4182410592594917768236724383388255754126852 leaf))
    5192301811503929037140965218320640 (node (node leaf
    1394477150026995991849089809545919783765251 leaf)
    340282367158933644941809575498844996097 (node leaf
    5576207172695457819413954409292385710769925 leaf)))

/-- The variables, each a list of term codes. -/
noncomputable def varList : List (List ℕ) :=
  [[1589777],
    [1589808],
    [1590799, 1589807],
    [1622515, 1589744],
    [1625584, 1592813, 3688973, 3687981, 1589837],
    [1623538, 1590767, 1589775],
    [1624561, 1591790, 2639374, 1589806],
    [1658323, 2674128, 3721712, 1592781, 3688941, 3687949, 1589805]]

/-- The exchange relations. -/
noncomputable def relTree : NatTree :=
  (node (node (node (node leaf
    881609153953968325654486320645 leaf)
    43521329506126698081682433 leaf)
    47781774081 (node leaf
    215188795891403993103206147 leaf))
    21760664753063325155328512 (node (node leaf
    79789104094565573322802690 leaf)
    43489821952 (node leaf
    120892581961462965531313924 leaf)))

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
  var c := (varList.getD c []).map (decodeTerm 4)
  alpha a i := digit (seedTree.get a) 256 i
  matD a i j := digit (Nat.div (seedTree.get a) 65536) 16 (i * 2 + j)
  next a k := digit (Nat.div (seedTree.get a) 281474976710656) 65536 k
  perm a k j := digit (Nat.div (seedTree.get a) 1208925819614629174706176) 16 (k * 2 + j)
  rel a k := digit (Nat.div (seedTree.get a) 79228162514264337593543950336) 65536 k
  relX r := Nat.mod (relTree.get r) 256
  relY r := Nat.mod (Nat.div (relTree.get r) 256) 256
  relPos r := decodeAtoms 8 (Nat.mod (Nat.div (relTree.get r) 65536) 18446744073709551616)
  relNeg r := decodeAtoms 8 (Nat.div (relTree.get r) 1208925819614629174706176)
  depth a := Nat.mod (Nat.div (seedTree.get a) 340282366920938463463374607431768211456) 256
  parent a := Nat.div (seedTree.get a) 1393796574908163946345982392040522594123776
  parentDir a := Nat.mod (Nat.div (seedTree.get a) 87112285931760246646623899502532662132736) 16
  cover c := coverTree.get c

end ClusterAlgebras.CertificateData.G2E

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E8

/-!
# Exchange relations `[1884, 2562)` of the `E8` certificate

The exchange relations of `raw` with indices in `[1884, 2562)` are checked by kernel evaluation of
`relOKD`, in pieces of `16` relations assembled by `CertificateCheck.allFrom_add`.

## Main results

* `relOK_2`: the exchange relations of `raw` with indices in `[1884, 2562)` hold.

## Implementation notes

Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the cost
of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel checks of the
pieces would hold their memory until the end of the file, so it is disabled.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

set_option Elab.async false

/-- The exchange relations of `raw` with indices in `[1884, 1900)` hold, as checked by `relOKD`. -/
theorem relOK_2_0 :
    allFrom 1884 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1900, 1916)` hold, as checked by `relOKD`. -/
theorem relOK_2_1 :
    allFrom 1900 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1916, 1932)` hold, as checked by `relOKD`. -/
theorem relOK_2_2 :
    allFrom 1916 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1932, 1948)` hold, as checked by `relOKD`. -/
theorem relOK_2_3 :
    allFrom 1932 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1948, 1964)` hold, as checked by `relOKD`. -/
theorem relOK_2_4 :
    allFrom 1948 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1964, 1980)` hold, as checked by `relOKD`. -/
theorem relOK_2_5 :
    allFrom 1964 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1980, 1996)` hold, as checked by `relOKD`. -/
theorem relOK_2_6 :
    allFrom 1980 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1996, 2012)` hold, as checked by `relOKD`. -/
theorem relOK_2_7 :
    allFrom 1996 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2012, 2028)` hold, as checked by `relOKD`. -/
theorem relOK_2_8 :
    allFrom 2012 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2028, 2044)` hold, as checked by `relOKD`. -/
theorem relOK_2_9 :
    allFrom 2028 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2044, 2060)` hold, as checked by `relOKD`. -/
theorem relOK_2_10 :
    allFrom 2044 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2060, 2076)` hold, as checked by `relOKD`. -/
theorem relOK_2_11 :
    allFrom 2060 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2076, 2092)` hold, as checked by `relOKD`. -/
theorem relOK_2_12 :
    allFrom 2076 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2092, 2108)` hold, as checked by `relOKD`. -/
theorem relOK_2_13 :
    allFrom 2092 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2108, 2124)` hold, as checked by `relOKD`. -/
theorem relOK_2_14 :
    allFrom 2108 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2124, 2140)` hold, as checked by `relOKD`. -/
theorem relOK_2_15 :
    allFrom 2124 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2140, 2156)` hold, as checked by `relOKD`. -/
theorem relOK_2_16 :
    allFrom 2140 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2156, 2172)` hold, as checked by `relOKD`. -/
theorem relOK_2_17 :
    allFrom 2156 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2172, 2188)` hold, as checked by `relOKD`. -/
theorem relOK_2_18 :
    allFrom 2172 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2188, 2204)` hold, as checked by `relOKD`. -/
theorem relOK_2_19 :
    allFrom 2188 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2204, 2220)` hold, as checked by `relOKD`. -/
theorem relOK_2_20 :
    allFrom 2204 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2220, 2236)` hold, as checked by `relOKD`. -/
theorem relOK_2_21 :
    allFrom 2220 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2236, 2252)` hold, as checked by `relOKD`. -/
theorem relOK_2_22 :
    allFrom 2236 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2252, 2268)` hold, as checked by `relOKD`. -/
theorem relOK_2_23 :
    allFrom 2252 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2268, 2284)` hold, as checked by `relOKD`. -/
theorem relOK_2_24 :
    allFrom 2268 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2284, 2300)` hold, as checked by `relOKD`. -/
theorem relOK_2_25 :
    allFrom 2284 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2300, 2316)` hold, as checked by `relOKD`. -/
theorem relOK_2_26 :
    allFrom 2300 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2316, 2332)` hold, as checked by `relOKD`. -/
theorem relOK_2_27 :
    allFrom 2316 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2332, 2348)` hold, as checked by `relOKD`. -/
theorem relOK_2_28 :
    allFrom 2332 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2348, 2364)` hold, as checked by `relOKD`. -/
theorem relOK_2_29 :
    allFrom 2348 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2364, 2380)` hold, as checked by `relOKD`. -/
theorem relOK_2_30 :
    allFrom 2364 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2380, 2396)` hold, as checked by `relOKD`. -/
theorem relOK_2_31 :
    allFrom 2380 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2396, 2412)` hold, as checked by `relOKD`. -/
theorem relOK_2_32 :
    allFrom 2396 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2412, 2428)` hold, as checked by `relOKD`. -/
theorem relOK_2_33 :
    allFrom 2412 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2428, 2444)` hold, as checked by `relOKD`. -/
theorem relOK_2_34 :
    allFrom 2428 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2444, 2460)` hold, as checked by `relOKD`. -/
theorem relOK_2_35 :
    allFrom 2444 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2460, 2476)` hold, as checked by `relOKD`. -/
theorem relOK_2_36 :
    allFrom 2460 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2476, 2492)` hold, as checked by `relOKD`. -/
theorem relOK_2_37 :
    allFrom 2476 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2492, 2508)` hold, as checked by `relOKD`. -/
theorem relOK_2_38 :
    allFrom 2492 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2508, 2524)` hold, as checked by `relOKD`. -/
theorem relOK_2_39 :
    allFrom 2508 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2524, 2540)` hold, as checked by `relOKD`. -/
theorem relOK_2_40 :
    allFrom 2524 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2540, 2556)` hold, as checked by `relOKD`. -/
theorem relOK_2_41 :
    allFrom 2540 16
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[2556, 2562)` hold, as checked by `relOKD`. -/
theorem relOK_2_42 :
    allFrom 2556 6
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relations of `raw` with indices in `[1884, 2562)` hold, as checked by `relOKD`. -/
theorem relOK_2 :
    allFrom 1884 678
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true :=
  allFrom_add (a := 336) (b := 342)
      (allFrom_add (a := 160) (b := 176)
          (allFrom_add (a := 80) (b := 80)
              (allFrom_add (a := 32) (b := 48)
                  (allFrom_add (a := 16) (b := 16)
                      relOK_2_0
                      relOK_2_1)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_2
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_3
                          relOK_2_4)))
              (allFrom_add (a := 32) (b := 48)
                  (allFrom_add (a := 16) (b := 16)
                      relOK_2_5
                      relOK_2_6)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_7
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_8
                          relOK_2_9))))
          (allFrom_add (a := 80) (b := 96)
              (allFrom_add (a := 32) (b := 48)
                  (allFrom_add (a := 16) (b := 16)
                      relOK_2_10
                      relOK_2_11)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_12
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_13
                          relOK_2_14)))
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_15
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_16
                          relOK_2_17))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_18
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_19
                          relOK_2_20)))))
      (allFrom_add (a := 176) (b := 166)
          (allFrom_add (a := 80) (b := 96)
              (allFrom_add (a := 32) (b := 48)
                  (allFrom_add (a := 16) (b := 16)
                      relOK_2_21
                      relOK_2_22)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_23
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_24
                          relOK_2_25)))
              (allFrom_add (a := 48) (b := 48)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_26
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_27
                          relOK_2_28))
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_29
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_30
                          relOK_2_31))))
          (allFrom_add (a := 80) (b := 86)
              (allFrom_add (a := 32) (b := 48)
                  (allFrom_add (a := 16) (b := 16)
                      relOK_2_32
                      relOK_2_33)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_34
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_35
                          relOK_2_36)))
              (allFrom_add (a := 48) (b := 38)
                  (allFrom_add (a := 16) (b := 32)
                      relOK_2_37
                      (allFrom_add (a := 16) (b := 16)
                          relOK_2_38
                          relOK_2_39))
                  (allFrom_add (a := 16) (b := 22)
                      relOK_2_40
                      (allFrom_add (a := 16) (b := 6)
                          relOK_2_41
                          relOK_2_42)))))

end ClusterAlgebras.CertificateData.E8

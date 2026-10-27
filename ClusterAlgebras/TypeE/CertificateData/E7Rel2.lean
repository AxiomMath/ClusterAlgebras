/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7

/-!
# Exchange relations `[911, 982)` of the `E7` certificate

Each exchange relation of index in `[911, 982)` of the `E7` certificate data `raw` passes the
check `relOKD`.

## Main results

* `relOK_2_0`, …, `relOK_2_70`: the exchange relation of index `911 + i` passes `relOKD`.
* `relOK_2`: every exchange relation of index in `[911, 982)` passes `relOKD`.

## Implementation notes

Each relation is checked by `decide +kernel` in its own theorem, so that the kernel's caches are
dropped between relations: the cost of a kernel evaluation grows faster than its length. The
option `Elab.async` is disabled, since otherwise the kernel checks would hold their memory until
the end of the file. The pieces are assembled by `CertificateCheck.allFrom_add`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7

open CertificateCheck

set_option Elab.async false

/-- The exchange relation `911` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_0 :
    allFrom 911 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `912` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_1 :
    allFrom 912 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `913` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_2 :
    allFrom 913 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `914` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_3 :
    allFrom 914 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `915` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_4 :
    allFrom 915 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `916` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_5 :
    allFrom 916 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `917` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_6 :
    allFrom 917 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `918` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_7 :
    allFrom 918 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `919` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_8 :
    allFrom 919 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `920` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_9 :
    allFrom 920 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `921` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_10 :
    allFrom 921 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `922` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_11 :
    allFrom 922 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `923` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_12 :
    allFrom 923 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `924` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_13 :
    allFrom 924 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `925` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_14 :
    allFrom 925 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `926` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_15 :
    allFrom 926 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `927` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_16 :
    allFrom 927 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `928` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_17 :
    allFrom 928 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `929` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_18 :
    allFrom 929 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `930` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_19 :
    allFrom 930 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `931` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_20 :
    allFrom 931 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `932` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_21 :
    allFrom 932 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `933` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_22 :
    allFrom 933 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `934` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_23 :
    allFrom 934 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `935` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_24 :
    allFrom 935 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `936` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_25 :
    allFrom 936 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `937` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_26 :
    allFrom 937 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `938` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_27 :
    allFrom 938 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `939` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_28 :
    allFrom 939 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `940` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_29 :
    allFrom 940 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `941` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_30 :
    allFrom 941 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `942` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_31 :
    allFrom 942 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `943` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_32 :
    allFrom 943 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `944` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_33 :
    allFrom 944 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `945` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_34 :
    allFrom 945 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `946` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_35 :
    allFrom 946 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `947` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_36 :
    allFrom 947 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `948` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_37 :
    allFrom 948 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `949` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_38 :
    allFrom 949 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `950` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_39 :
    allFrom 950 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `951` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_40 :
    allFrom 951 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `952` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_41 :
    allFrom 952 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `953` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_42 :
    allFrom 953 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `954` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_43 :
    allFrom 954 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `955` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_44 :
    allFrom 955 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `956` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_45 :
    allFrom 956 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `957` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_46 :
    allFrom 957 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `958` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_47 :
    allFrom 958 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `959` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_48 :
    allFrom 959 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `960` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_49 :
    allFrom 960 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `961` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_50 :
    allFrom 961 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `962` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_51 :
    allFrom 962 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `963` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_52 :
    allFrom 963 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `964` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_53 :
    allFrom 964 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `965` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_54 :
    allFrom 965 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `966` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_55 :
    allFrom 966 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `967` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_56 :
    allFrom 967 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `968` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_57 :
    allFrom 968 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `969` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_58 :
    allFrom 969 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `970` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_59 :
    allFrom 970 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `971` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_60 :
    allFrom 971 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `972` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_61 :
    allFrom 972 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `973` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_62 :
    allFrom 973 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `974` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_63 :
    allFrom 974 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `975` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_64 :
    allFrom 975 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `976` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_65 :
    allFrom 976 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `977` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_66 :
    allFrom 977 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `978` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_67 :
    allFrom 978 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `979` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_68 :
    allFrom 979 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `980` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_69 :
    allFrom 980 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- The exchange relation `981` of the `E7` certificate `raw` passes `relOKD`. -/
theorem relOK_2_70 :
    allFrom 981 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true := by
  decide +kernel

/-- Every exchange relation of index in `[911, 982)` of the `E7` certificate `raw` passes
`relOKD`. -/
theorem relOK_2 :
    allFrom 911 71
      (fun r => raw.relOKD (fun c => varList.getD c []) 7 70 r) = true :=
  allFrom_add (a := 35) (b := 36)
      (allFrom_add (a := 17) (b := 18)
          (allFrom_add (a := 8) (b := 9)
              (allFrom_add (a := 4) (b := 4)
                  (allFrom_add (a := 2) (b := 2)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_0
                          relOK_2_1)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_2
                          relOK_2_3))
                  (allFrom_add (a := 2) (b := 2)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_4
                          relOK_2_5)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_6
                          relOK_2_7)))
              (allFrom_add (a := 4) (b := 5)
                  (allFrom_add (a := 2) (b := 2)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_8
                          relOK_2_9)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_10
                          relOK_2_11))
                  (allFrom_add (a := 2) (b := 3)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_12
                          relOK_2_13)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_2_14
                          (allFrom_add (a := 1) (b := 1)
                              relOK_2_15
                              relOK_2_16)))))
          (allFrom_add (a := 9) (b := 9)
              (allFrom_add (a := 4) (b := 5)
                  (allFrom_add (a := 2) (b := 2)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_17
                          relOK_2_18)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_19
                          relOK_2_20))
                  (allFrom_add (a := 2) (b := 3)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_21
                          relOK_2_22)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_2_23
                          (allFrom_add (a := 1) (b := 1)
                              relOK_2_24
                              relOK_2_25))))
              (allFrom_add (a := 4) (b := 5)
                  (allFrom_add (a := 2) (b := 2)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_26
                          relOK_2_27)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_28
                          relOK_2_29))
                  (allFrom_add (a := 2) (b := 3)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_30
                          relOK_2_31)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_2_32
                          (allFrom_add (a := 1) (b := 1)
                              relOK_2_33
                              relOK_2_34))))))
      (allFrom_add (a := 18) (b := 18)
          (allFrom_add (a := 9) (b := 9)
              (allFrom_add (a := 4) (b := 5)
                  (allFrom_add (a := 2) (b := 2)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_35
                          relOK_2_36)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_37
                          relOK_2_38))
                  (allFrom_add (a := 2) (b := 3)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_39
                          relOK_2_40)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_2_41
                          (allFrom_add (a := 1) (b := 1)
                              relOK_2_42
                              relOK_2_43))))
              (allFrom_add (a := 4) (b := 5)
                  (allFrom_add (a := 2) (b := 2)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_44
                          relOK_2_45)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_46
                          relOK_2_47))
                  (allFrom_add (a := 2) (b := 3)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_48
                          relOK_2_49)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_2_50
                          (allFrom_add (a := 1) (b := 1)
                              relOK_2_51
                              relOK_2_52)))))
          (allFrom_add (a := 9) (b := 9)
              (allFrom_add (a := 4) (b := 5)
                  (allFrom_add (a := 2) (b := 2)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_53
                          relOK_2_54)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_55
                          relOK_2_56))
                  (allFrom_add (a := 2) (b := 3)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_57
                          relOK_2_58)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_2_59
                          (allFrom_add (a := 1) (b := 1)
                              relOK_2_60
                              relOK_2_61))))
              (allFrom_add (a := 4) (b := 5)
                  (allFrom_add (a := 2) (b := 2)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_62
                          relOK_2_63)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_64
                          relOK_2_65))
                  (allFrom_add (a := 2) (b := 3)
                      (allFrom_add (a := 1) (b := 1)
                          relOK_2_66
                          relOK_2_67)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_2_68
                          (allFrom_add (a := 1) (b := 1)
                              relOK_2_69
                              relOK_2_70))))))

end ClusterAlgebras.CertificateData.E7

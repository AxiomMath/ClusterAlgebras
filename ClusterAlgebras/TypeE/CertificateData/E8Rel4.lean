/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E8

/-! # Kernel check of the exchange relations `[2864, 3089)` of the `E8` certificate,
one relation per theorem, assembled by `CertificateCheck.allFrom_add` -/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_0 :
    allFrom 2864 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_1 :
    allFrom 2865 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_2 :
    allFrom 2866 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_3 :
    allFrom 2867 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_4 :
    allFrom 2868 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_5 :
    allFrom 2869 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_6 :
    allFrom 2870 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_7 :
    allFrom 2871 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_8 :
    allFrom 2872 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_9 :
    allFrom 2873 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_10 :
    allFrom 2874 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_11 :
    allFrom 2875 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_12 :
    allFrom 2876 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_13 :
    allFrom 2877 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_14 :
    allFrom 2878 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_15 :
    allFrom 2879 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_16 :
    allFrom 2880 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_17 :
    allFrom 2881 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_18 :
    allFrom 2882 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_19 :
    allFrom 2883 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_20 :
    allFrom 2884 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_21 :
    allFrom 2885 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_22 :
    allFrom 2886 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_23 :
    allFrom 2887 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_24 :
    allFrom 2888 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_25 :
    allFrom 2889 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_26 :
    allFrom 2890 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_27 :
    allFrom 2891 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_28 :
    allFrom 2892 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_29 :
    allFrom 2893 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_30 :
    allFrom 2894 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_31 :
    allFrom 2895 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_32 :
    allFrom 2896 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_33 :
    allFrom 2897 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_34 :
    allFrom 2898 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_35 :
    allFrom 2899 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_36 :
    allFrom 2900 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_37 :
    allFrom 2901 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_38 :
    allFrom 2902 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_39 :
    allFrom 2903 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_40 :
    allFrom 2904 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_41 :
    allFrom 2905 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_42 :
    allFrom 2906 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_43 :
    allFrom 2907 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_44 :
    allFrom 2908 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_45 :
    allFrom 2909 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_46 :
    allFrom 2910 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_47 :
    allFrom 2911 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_48 :
    allFrom 2912 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_49 :
    allFrom 2913 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_50 :
    allFrom 2914 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_51 :
    allFrom 2915 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_52 :
    allFrom 2916 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_53 :
    allFrom 2917 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_54 :
    allFrom 2918 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_55 :
    allFrom 2919 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_56 :
    allFrom 2920 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_57 :
    allFrom 2921 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_58 :
    allFrom 2922 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_59 :
    allFrom 2923 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_60 :
    allFrom 2924 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_61 :
    allFrom 2925 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_62 :
    allFrom 2926 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_63 :
    allFrom 2927 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_64 :
    allFrom 2928 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_65 :
    allFrom 2929 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_66 :
    allFrom 2930 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_67 :
    allFrom 2931 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_68 :
    allFrom 2932 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_69 :
    allFrom 2933 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_70 :
    allFrom 2934 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_71 :
    allFrom 2935 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_72 :
    allFrom 2936 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_73 :
    allFrom 2937 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_74 :
    allFrom 2938 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_75 :
    allFrom 2939 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_76 :
    allFrom 2940 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_77 :
    allFrom 2941 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_78 :
    allFrom 2942 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_79 :
    allFrom 2943 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_80 :
    allFrom 2944 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_81 :
    allFrom 2945 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_82 :
    allFrom 2946 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_83 :
    allFrom 2947 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_84 :
    allFrom 2948 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_85 :
    allFrom 2949 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_86 :
    allFrom 2950 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_87 :
    allFrom 2951 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_88 :
    allFrom 2952 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_89 :
    allFrom 2953 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_90 :
    allFrom 2954 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_91 :
    allFrom 2955 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_92 :
    allFrom 2956 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_93 :
    allFrom 2957 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_94 :
    allFrom 2958 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_95 :
    allFrom 2959 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_96 :
    allFrom 2960 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_97 :
    allFrom 2961 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_98 :
    allFrom 2962 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_99 :
    allFrom 2963 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_100 :
    allFrom 2964 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_101 :
    allFrom 2965 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_102 :
    allFrom 2966 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_103 :
    allFrom 2967 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_104 :
    allFrom 2968 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_105 :
    allFrom 2969 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_106 :
    allFrom 2970 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_107 :
    allFrom 2971 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_108 :
    allFrom 2972 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_109 :
    allFrom 2973 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_110 :
    allFrom 2974 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_111 :
    allFrom 2975 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_112 :
    allFrom 2976 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_113 :
    allFrom 2977 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_114 :
    allFrom 2978 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_115 :
    allFrom 2979 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_116 :
    allFrom 2980 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_117 :
    allFrom 2981 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_118 :
    allFrom 2982 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_119 :
    allFrom 2983 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_120 :
    allFrom 2984 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_121 :
    allFrom 2985 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_122 :
    allFrom 2986 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_123 :
    allFrom 2987 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_124 :
    allFrom 2988 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_125 :
    allFrom 2989 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_126 :
    allFrom 2990 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_127 :
    allFrom 2991 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_128 :
    allFrom 2992 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_129 :
    allFrom 2993 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_130 :
    allFrom 2994 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_131 :
    allFrom 2995 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_132 :
    allFrom 2996 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_133 :
    allFrom 2997 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_134 :
    allFrom 2998 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_135 :
    allFrom 2999 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_136 :
    allFrom 3000 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_137 :
    allFrom 3001 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_138 :
    allFrom 3002 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_139 :
    allFrom 3003 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_140 :
    allFrom 3004 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_141 :
    allFrom 3005 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_142 :
    allFrom 3006 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_143 :
    allFrom 3007 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_144 :
    allFrom 3008 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_145 :
    allFrom 3009 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_146 :
    allFrom 3010 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_147 :
    allFrom 3011 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_148 :
    allFrom 3012 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_149 :
    allFrom 3013 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_150 :
    allFrom 3014 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_151 :
    allFrom 3015 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_152 :
    allFrom 3016 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_153 :
    allFrom 3017 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_154 :
    allFrom 3018 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_155 :
    allFrom 3019 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_156 :
    allFrom 3020 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_157 :
    allFrom 3021 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_158 :
    allFrom 3022 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_159 :
    allFrom 3023 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_160 :
    allFrom 3024 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_161 :
    allFrom 3025 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_162 :
    allFrom 3026 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_163 :
    allFrom 3027 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_164 :
    allFrom 3028 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_165 :
    allFrom 3029 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_166 :
    allFrom 3030 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_167 :
    allFrom 3031 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_168 :
    allFrom 3032 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_169 :
    allFrom 3033 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_170 :
    allFrom 3034 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_171 :
    allFrom 3035 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_172 :
    allFrom 3036 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_173 :
    allFrom 3037 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_174 :
    allFrom 3038 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_175 :
    allFrom 3039 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_176 :
    allFrom 3040 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_177 :
    allFrom 3041 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_178 :
    allFrom 3042 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_179 :
    allFrom 3043 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_180 :
    allFrom 3044 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_181 :
    allFrom 3045 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_182 :
    allFrom 3046 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_183 :
    allFrom 3047 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_184 :
    allFrom 3048 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_185 :
    allFrom 3049 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_186 :
    allFrom 3050 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_187 :
    allFrom 3051 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_188 :
    allFrom 3052 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_189 :
    allFrom 3053 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_190 :
    allFrom 3054 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_191 :
    allFrom 3055 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_192 :
    allFrom 3056 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_193 :
    allFrom 3057 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_194 :
    allFrom 3058 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_195 :
    allFrom 3059 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_196 :
    allFrom 3060 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_197 :
    allFrom 3061 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_198 :
    allFrom 3062 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_199 :
    allFrom 3063 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_200 :
    allFrom 3064 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_201 :
    allFrom 3065 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_202 :
    allFrom 3066 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_203 :
    allFrom 3067 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_204 :
    allFrom 3068 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_205 :
    allFrom 3069 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_206 :
    allFrom 3070 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_207 :
    allFrom 3071 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_208 :
    allFrom 3072 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_209 :
    allFrom 3073 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_210 :
    allFrom 3074 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_211 :
    allFrom 3075 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_212 :
    allFrom 3076 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_213 :
    allFrom 3077 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_214 :
    allFrom 3078 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_215 :
    allFrom 3079 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_216 :
    allFrom 3080 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_217 :
    allFrom 3081 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_218 :
    allFrom 3082 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_219 :
    allFrom 3083 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_220 :
    allFrom 3084 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_221 :
    allFrom 3085 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_222 :
    allFrom 3086 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_223 :
    allFrom 3087 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- The exchange relation of the `E8` certificate `raw` at the stated index passes `raw.relOKD`. -/
theorem relOK_4_224 :
    allFrom 3088 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true := by
  decide +kernel

/-- Every exchange relation of the `E8` certificate `raw` with index in `[2864, 3089)` passes
`raw.relOKD`. -/
theorem relOK_4 :
    allFrom 2864 225
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 128 r) = true :=
  allFrom_add (a := 112) (b := 113)
      (allFrom_add (a := 56) (b := 56)
          (allFrom_add (a := 28) (b := 28)
              (allFrom_add (a := 14) (b := 14)
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_0
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_1
                                  relOK_4_2))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_3
                                  relOK_4_4)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_5
                                  relOK_4_6)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_7
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_8
                                  relOK_4_9))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_10
                                  relOK_4_11)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_12
                                  relOK_4_13))))
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_14
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_15
                                  relOK_4_16))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_17
                                  relOK_4_18)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_19
                                  relOK_4_20)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_21
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_22
                                  relOK_4_23))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_24
                                  relOK_4_25)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_26
                                  relOK_4_27)))))
              (allFrom_add (a := 14) (b := 14)
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_28
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_29
                                  relOK_4_30))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_31
                                  relOK_4_32)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_33
                                  relOK_4_34)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_35
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_36
                                  relOK_4_37))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_38
                                  relOK_4_39)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_40
                                  relOK_4_41))))
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_42
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_43
                                  relOK_4_44))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_45
                                  relOK_4_46)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_47
                                  relOK_4_48)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_49
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_50
                                  relOK_4_51))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_52
                                  relOK_4_53)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_54
                                  relOK_4_55))))))
          (allFrom_add (a := 28) (b := 28)
              (allFrom_add (a := 14) (b := 14)
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_56
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_57
                                  relOK_4_58))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_59
                                  relOK_4_60)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_61
                                  relOK_4_62)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_63
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_64
                                  relOK_4_65))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_66
                                  relOK_4_67)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_68
                                  relOK_4_69))))
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_70
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_71
                                  relOK_4_72))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_73
                                  relOK_4_74)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_75
                                  relOK_4_76)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_77
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_78
                                  relOK_4_79))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_80
                                  relOK_4_81)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_82
                                  relOK_4_83)))))
              (allFrom_add (a := 14) (b := 14)
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_84
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_85
                                  relOK_4_86))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_87
                                  relOK_4_88)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_89
                                  relOK_4_90)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_91
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_92
                                  relOK_4_93))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_94
                                  relOK_4_95)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_96
                                  relOK_4_97))))
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_98
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_99
                                  relOK_4_100))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_101
                                  relOK_4_102)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_103
                                  relOK_4_104)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_105
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_106
                                  relOK_4_107))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_108
                                  relOK_4_109)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_110
                                  relOK_4_111)))))))
      (allFrom_add (a := 56) (b := 57)
          (allFrom_add (a := 28) (b := 28)
              (allFrom_add (a := 14) (b := 14)
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_112
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_113
                                  relOK_4_114))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_115
                                  relOK_4_116)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_117
                                  relOK_4_118)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_119
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_120
                                  relOK_4_121))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_122
                                  relOK_4_123)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_124
                                  relOK_4_125))))
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_126
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_127
                                  relOK_4_128))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_129
                                  relOK_4_130)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_131
                                  relOK_4_132)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_133
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_134
                                  relOK_4_135))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_136
                                  relOK_4_137)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_138
                                  relOK_4_139)))))
              (allFrom_add (a := 14) (b := 14)
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_140
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_141
                                  relOK_4_142))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_143
                                  relOK_4_144)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_145
                                  relOK_4_146)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_147
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_148
                                  relOK_4_149))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_150
                                  relOK_4_151)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_152
                                  relOK_4_153))))
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_154
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_155
                                  relOK_4_156))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_157
                                  relOK_4_158)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_159
                                  relOK_4_160)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_161
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_162
                                  relOK_4_163))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_164
                                  relOK_4_165)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_166
                                  relOK_4_167))))))
          (allFrom_add (a := 28) (b := 29)
              (allFrom_add (a := 14) (b := 14)
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_168
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_169
                                  relOK_4_170))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_171
                                  relOK_4_172)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_173
                                  relOK_4_174)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_175
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_176
                                  relOK_4_177))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_178
                                  relOK_4_179)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_180
                                  relOK_4_181))))
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_182
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_183
                                  relOK_4_184))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_185
                                  relOK_4_186)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_187
                                  relOK_4_188)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_189
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_190
                                  relOK_4_191))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_192
                                  relOK_4_193)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_194
                                  relOK_4_195)))))
              (allFrom_add (a := 14) (b := 15)
                  (allFrom_add (a := 7) (b := 7)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_196
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_197
                                  relOK_4_198))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_199
                                  relOK_4_200)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_201
                                  relOK_4_202)))
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_203
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_204
                                  relOK_4_205))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_206
                                  relOK_4_207)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_208
                                  relOK_4_209))))
                  (allFrom_add (a := 7) (b := 8)
                      (allFrom_add (a := 3) (b := 4)
                          (allFrom_add (a := 1) (b := 2)
                              relOK_4_210
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_211
                                  relOK_4_212))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_213
                                  relOK_4_214)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_215
                                  relOK_4_216)))
                      (allFrom_add (a := 4) (b := 4)
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_217
                                  relOK_4_218)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_219
                                  relOK_4_220))
                          (allFrom_add (a := 2) (b := 2)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_221
                                  relOK_4_222)
                              (allFrom_add (a := 1) (b := 1)
                                  relOK_4_223
                                  relOK_4_224)))))))

end ClusterAlgebras.CertificateData.E8

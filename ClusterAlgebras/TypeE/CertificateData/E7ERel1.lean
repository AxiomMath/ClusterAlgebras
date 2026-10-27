/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCore
public import ClusterAlgebras.TypeE.CertificateData.E7E

/-!
# Exchange relations `[803, 907)` of the `E7E` certificate

The exchange relations `[803, 907)` of the certificate `raw` pass the check `relOKD`, one
relation per theorem, assembled by `CertificateCheck.allFrom_add`.

## Main results

* `relOK_1`: The exchange relations `[803, 907)` of `raw` pass `relOKD`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7E

open CertificateCheck

-- Each piece is its own theorem, so that the kernel's caches are dropped between pieces: the
-- cost of a kernel evaluation grows faster than its length. With `Elab.async`, the kernel
-- checks of the pieces would hold their memory until the end of the file.
set_option Elab.async false

/-- The exchange relation `803` of `raw` passes `relOKD`. -/
theorem relOK_1_0 :
    allFrom 803 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `804` of `raw` passes `relOKD`. -/
theorem relOK_1_1 :
    allFrom 804 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `805` of `raw` passes `relOKD`. -/
theorem relOK_1_2 :
    allFrom 805 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `806` of `raw` passes `relOKD`. -/
theorem relOK_1_3 :
    allFrom 806 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `807` of `raw` passes `relOKD`. -/
theorem relOK_1_4 :
    allFrom 807 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `808` of `raw` passes `relOKD`. -/
theorem relOK_1_5 :
    allFrom 808 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `809` of `raw` passes `relOKD`. -/
theorem relOK_1_6 :
    allFrom 809 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `810` of `raw` passes `relOKD`. -/
theorem relOK_1_7 :
    allFrom 810 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `811` of `raw` passes `relOKD`. -/
theorem relOK_1_8 :
    allFrom 811 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `812` of `raw` passes `relOKD`. -/
theorem relOK_1_9 :
    allFrom 812 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `813` of `raw` passes `relOKD`. -/
theorem relOK_1_10 :
    allFrom 813 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `814` of `raw` passes `relOKD`. -/
theorem relOK_1_11 :
    allFrom 814 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `815` of `raw` passes `relOKD`. -/
theorem relOK_1_12 :
    allFrom 815 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `816` of `raw` passes `relOKD`. -/
theorem relOK_1_13 :
    allFrom 816 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `817` of `raw` passes `relOKD`. -/
theorem relOK_1_14 :
    allFrom 817 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `818` of `raw` passes `relOKD`. -/
theorem relOK_1_15 :
    allFrom 818 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `819` of `raw` passes `relOKD`. -/
theorem relOK_1_16 :
    allFrom 819 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `820` of `raw` passes `relOKD`. -/
theorem relOK_1_17 :
    allFrom 820 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `821` of `raw` passes `relOKD`. -/
theorem relOK_1_18 :
    allFrom 821 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `822` of `raw` passes `relOKD`. -/
theorem relOK_1_19 :
    allFrom 822 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `823` of `raw` passes `relOKD`. -/
theorem relOK_1_20 :
    allFrom 823 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `824` of `raw` passes `relOKD`. -/
theorem relOK_1_21 :
    allFrom 824 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `825` of `raw` passes `relOKD`. -/
theorem relOK_1_22 :
    allFrom 825 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `826` of `raw` passes `relOKD`. -/
theorem relOK_1_23 :
    allFrom 826 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `827` of `raw` passes `relOKD`. -/
theorem relOK_1_24 :
    allFrom 827 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `828` of `raw` passes `relOKD`. -/
theorem relOK_1_25 :
    allFrom 828 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `829` of `raw` passes `relOKD`. -/
theorem relOK_1_26 :
    allFrom 829 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `830` of `raw` passes `relOKD`. -/
theorem relOK_1_27 :
    allFrom 830 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `831` of `raw` passes `relOKD`. -/
theorem relOK_1_28 :
    allFrom 831 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `832` of `raw` passes `relOKD`. -/
theorem relOK_1_29 :
    allFrom 832 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `833` of `raw` passes `relOKD`. -/
theorem relOK_1_30 :
    allFrom 833 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `834` of `raw` passes `relOKD`. -/
theorem relOK_1_31 :
    allFrom 834 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `835` of `raw` passes `relOKD`. -/
theorem relOK_1_32 :
    allFrom 835 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `836` of `raw` passes `relOKD`. -/
theorem relOK_1_33 :
    allFrom 836 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `837` of `raw` passes `relOKD`. -/
theorem relOK_1_34 :
    allFrom 837 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `838` of `raw` passes `relOKD`. -/
theorem relOK_1_35 :
    allFrom 838 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `839` of `raw` passes `relOKD`. -/
theorem relOK_1_36 :
    allFrom 839 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `840` of `raw` passes `relOKD`. -/
theorem relOK_1_37 :
    allFrom 840 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `841` of `raw` passes `relOKD`. -/
theorem relOK_1_38 :
    allFrom 841 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `842` of `raw` passes `relOKD`. -/
theorem relOK_1_39 :
    allFrom 842 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `843` of `raw` passes `relOKD`. -/
theorem relOK_1_40 :
    allFrom 843 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `844` of `raw` passes `relOKD`. -/
theorem relOK_1_41 :
    allFrom 844 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `845` of `raw` passes `relOKD`. -/
theorem relOK_1_42 :
    allFrom 845 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `846` of `raw` passes `relOKD`. -/
theorem relOK_1_43 :
    allFrom 846 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `847` of `raw` passes `relOKD`. -/
theorem relOK_1_44 :
    allFrom 847 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `848` of `raw` passes `relOKD`. -/
theorem relOK_1_45 :
    allFrom 848 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `849` of `raw` passes `relOKD`. -/
theorem relOK_1_46 :
    allFrom 849 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `850` of `raw` passes `relOKD`. -/
theorem relOK_1_47 :
    allFrom 850 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `851` of `raw` passes `relOKD`. -/
theorem relOK_1_48 :
    allFrom 851 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `852` of `raw` passes `relOKD`. -/
theorem relOK_1_49 :
    allFrom 852 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `853` of `raw` passes `relOKD`. -/
theorem relOK_1_50 :
    allFrom 853 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `854` of `raw` passes `relOKD`. -/
theorem relOK_1_51 :
    allFrom 854 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `855` of `raw` passes `relOKD`. -/
theorem relOK_1_52 :
    allFrom 855 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `856` of `raw` passes `relOKD`. -/
theorem relOK_1_53 :
    allFrom 856 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `857` of `raw` passes `relOKD`. -/
theorem relOK_1_54 :
    allFrom 857 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `858` of `raw` passes `relOKD`. -/
theorem relOK_1_55 :
    allFrom 858 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `859` of `raw` passes `relOKD`. -/
theorem relOK_1_56 :
    allFrom 859 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `860` of `raw` passes `relOKD`. -/
theorem relOK_1_57 :
    allFrom 860 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `861` of `raw` passes `relOKD`. -/
theorem relOK_1_58 :
    allFrom 861 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `862` of `raw` passes `relOKD`. -/
theorem relOK_1_59 :
    allFrom 862 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `863` of `raw` passes `relOKD`. -/
theorem relOK_1_60 :
    allFrom 863 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `864` of `raw` passes `relOKD`. -/
theorem relOK_1_61 :
    allFrom 864 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `865` of `raw` passes `relOKD`. -/
theorem relOK_1_62 :
    allFrom 865 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `866` of `raw` passes `relOKD`. -/
theorem relOK_1_63 :
    allFrom 866 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `867` of `raw` passes `relOKD`. -/
theorem relOK_1_64 :
    allFrom 867 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `868` of `raw` passes `relOKD`. -/
theorem relOK_1_65 :
    allFrom 868 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `869` of `raw` passes `relOKD`. -/
theorem relOK_1_66 :
    allFrom 869 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `870` of `raw` passes `relOKD`. -/
theorem relOK_1_67 :
    allFrom 870 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `871` of `raw` passes `relOKD`. -/
theorem relOK_1_68 :
    allFrom 871 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `872` of `raw` passes `relOKD`. -/
theorem relOK_1_69 :
    allFrom 872 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `873` of `raw` passes `relOKD`. -/
theorem relOK_1_70 :
    allFrom 873 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `874` of `raw` passes `relOKD`. -/
theorem relOK_1_71 :
    allFrom 874 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `875` of `raw` passes `relOKD`. -/
theorem relOK_1_72 :
    allFrom 875 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `876` of `raw` passes `relOKD`. -/
theorem relOK_1_73 :
    allFrom 876 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `877` of `raw` passes `relOKD`. -/
theorem relOK_1_74 :
    allFrom 877 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `878` of `raw` passes `relOKD`. -/
theorem relOK_1_75 :
    allFrom 878 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `879` of `raw` passes `relOKD`. -/
theorem relOK_1_76 :
    allFrom 879 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `880` of `raw` passes `relOKD`. -/
theorem relOK_1_77 :
    allFrom 880 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `881` of `raw` passes `relOKD`. -/
theorem relOK_1_78 :
    allFrom 881 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `882` of `raw` passes `relOKD`. -/
theorem relOK_1_79 :
    allFrom 882 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `883` of `raw` passes `relOKD`. -/
theorem relOK_1_80 :
    allFrom 883 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `884` of `raw` passes `relOKD`. -/
theorem relOK_1_81 :
    allFrom 884 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `885` of `raw` passes `relOKD`. -/
theorem relOK_1_82 :
    allFrom 885 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `886` of `raw` passes `relOKD`. -/
theorem relOK_1_83 :
    allFrom 886 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `887` of `raw` passes `relOKD`. -/
theorem relOK_1_84 :
    allFrom 887 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `888` of `raw` passes `relOKD`. -/
theorem relOK_1_85 :
    allFrom 888 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `889` of `raw` passes `relOKD`. -/
theorem relOK_1_86 :
    allFrom 889 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `890` of `raw` passes `relOKD`. -/
theorem relOK_1_87 :
    allFrom 890 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `891` of `raw` passes `relOKD`. -/
theorem relOK_1_88 :
    allFrom 891 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `892` of `raw` passes `relOKD`. -/
theorem relOK_1_89 :
    allFrom 892 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `893` of `raw` passes `relOKD`. -/
theorem relOK_1_90 :
    allFrom 893 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `894` of `raw` passes `relOKD`. -/
theorem relOK_1_91 :
    allFrom 894 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `895` of `raw` passes `relOKD`. -/
theorem relOK_1_92 :
    allFrom 895 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `896` of `raw` passes `relOKD`. -/
theorem relOK_1_93 :
    allFrom 896 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `897` of `raw` passes `relOKD`. -/
theorem relOK_1_94 :
    allFrom 897 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `898` of `raw` passes `relOKD`. -/
theorem relOK_1_95 :
    allFrom 898 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `899` of `raw` passes `relOKD`. -/
theorem relOK_1_96 :
    allFrom 899 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `900` of `raw` passes `relOKD`. -/
theorem relOK_1_97 :
    allFrom 900 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `901` of `raw` passes `relOKD`. -/
theorem relOK_1_98 :
    allFrom 901 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `902` of `raw` passes `relOKD`. -/
theorem relOK_1_99 :
    allFrom 902 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `903` of `raw` passes `relOKD`. -/
theorem relOK_1_100 :
    allFrom 903 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `904` of `raw` passes `relOKD`. -/
theorem relOK_1_101 :
    allFrom 904 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `905` of `raw` passes `relOKD`. -/
theorem relOK_1_102 :
    allFrom 905 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relation `906` of `raw` passes `relOKD`. -/
theorem relOK_1_103 :
    allFrom 906 1
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true := by
  decide +kernel

/-- The exchange relations `[803, 907)` of `raw` pass `relOKD`. -/
theorem relOK_1 :
    allFrom 803 104
      (fun r => raw.relOKD (fun c => varList.getD c []) 8 70 r) = true :=
  allFrom_add (a := 52) (b := 52)
      (allFrom_add (a := 26) (b := 26)
          (allFrom_add (a := 13) (b := 13)
              (allFrom_add (a := 6) (b := 7)
                  (allFrom_add (a := 3) (b := 3)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_0
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_1
                              relOK_1_2))
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_3
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_4
                              relOK_1_5)))
                  (allFrom_add (a := 3) (b := 4)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_6
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_7
                              relOK_1_8))
                      (allFrom_add (a := 2) (b := 2)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_9
                              relOK_1_10)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_11
                              relOK_1_12))))
              (allFrom_add (a := 6) (b := 7)
                  (allFrom_add (a := 3) (b := 3)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_13
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_14
                              relOK_1_15))
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_16
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_17
                              relOK_1_18)))
                  (allFrom_add (a := 3) (b := 4)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_19
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_20
                              relOK_1_21))
                      (allFrom_add (a := 2) (b := 2)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_22
                              relOK_1_23)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_24
                              relOK_1_25)))))
          (allFrom_add (a := 13) (b := 13)
              (allFrom_add (a := 6) (b := 7)
                  (allFrom_add (a := 3) (b := 3)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_26
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_27
                              relOK_1_28))
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_29
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_30
                              relOK_1_31)))
                  (allFrom_add (a := 3) (b := 4)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_32
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_33
                              relOK_1_34))
                      (allFrom_add (a := 2) (b := 2)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_35
                              relOK_1_36)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_37
                              relOK_1_38))))
              (allFrom_add (a := 6) (b := 7)
                  (allFrom_add (a := 3) (b := 3)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_39
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_40
                              relOK_1_41))
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_42
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_43
                              relOK_1_44)))
                  (allFrom_add (a := 3) (b := 4)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_45
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_46
                              relOK_1_47))
                      (allFrom_add (a := 2) (b := 2)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_48
                              relOK_1_49)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_50
                              relOK_1_51))))))
      (allFrom_add (a := 26) (b := 26)
          (allFrom_add (a := 13) (b := 13)
              (allFrom_add (a := 6) (b := 7)
                  (allFrom_add (a := 3) (b := 3)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_52
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_53
                              relOK_1_54))
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_55
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_56
                              relOK_1_57)))
                  (allFrom_add (a := 3) (b := 4)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_58
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_59
                              relOK_1_60))
                      (allFrom_add (a := 2) (b := 2)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_61
                              relOK_1_62)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_63
                              relOK_1_64))))
              (allFrom_add (a := 6) (b := 7)
                  (allFrom_add (a := 3) (b := 3)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_65
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_66
                              relOK_1_67))
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_68
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_69
                              relOK_1_70)))
                  (allFrom_add (a := 3) (b := 4)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_71
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_72
                              relOK_1_73))
                      (allFrom_add (a := 2) (b := 2)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_74
                              relOK_1_75)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_76
                              relOK_1_77)))))
          (allFrom_add (a := 13) (b := 13)
              (allFrom_add (a := 6) (b := 7)
                  (allFrom_add (a := 3) (b := 3)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_78
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_79
                              relOK_1_80))
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_81
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_82
                              relOK_1_83)))
                  (allFrom_add (a := 3) (b := 4)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_84
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_85
                              relOK_1_86))
                      (allFrom_add (a := 2) (b := 2)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_87
                              relOK_1_88)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_89
                              relOK_1_90))))
              (allFrom_add (a := 6) (b := 7)
                  (allFrom_add (a := 3) (b := 3)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_91
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_92
                              relOK_1_93))
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_94
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_95
                              relOK_1_96)))
                  (allFrom_add (a := 3) (b := 4)
                      (allFrom_add (a := 1) (b := 2)
                          relOK_1_97
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_98
                              relOK_1_99))
                      (allFrom_add (a := 2) (b := 2)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_100
                              relOK_1_101)
                          (allFrom_add (a := 1) (b := 1)
                              relOK_1_102
                              relOK_1_103))))))

end ClusterAlgebras.CertificateData.E7E

Require Import ConcreteExpressionClosure ConcreteScalarExpressions ConcreteGroundOperations.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Ltac solve_joint_register_ready :=
 first [apply closure_scalar; solve [repeat first [eapply scalar_ready_ref; eassumption | apply scalar_ready_const | apply scalar_ready_unary | apply scalar_ready_binary | apply scalar_ready_cast]]
 | apply closure_mux; solve_joint_register_ready | apply closure_unary; solve_joint_register_ready | apply closure_binary; solve_joint_register_ready].
Definition joint_register_update_142 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 761))).
Lemma joint_register_ready_142 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 761 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_142.
Proof.
 intros [g116 [b116 H116]].
 intros [g761 [b761 H761]].
 unfold joint_register_update_142. solve_joint_register_ready.
Qed.
Definition joint_register_update_143 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 762))).
Lemma joint_register_ready_143 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 762 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_143.
Proof.
 intros [g116 [b116 H116]].
 intros [g762 [b762 H762]].
 unfold joint_register_update_143. solve_joint_register_ready.
Qed.
Definition joint_register_update_144 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 767))).
Lemma joint_register_ready_144 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 767 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_144.
Proof.
 intros [g116 [b116 H116]].
 intros [g767 [b767 H767]].
 unfold joint_register_update_144. solve_joint_register_ready.
Qed.
Definition joint_register_update_145 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 769))).
Lemma joint_register_ready_145 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 769 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_145.
Proof.
 intros [g116 [b116 H116]].
 intros [g769 [b769 H769]].
 unfold joint_register_update_145. solve_joint_register_ready.
Qed.
Definition joint_register_update_146 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 768))).
Lemma joint_register_ready_146 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 768 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_146.
Proof.
 intros [g116 [b116 H116]].
 intros [g768 [b768 H768]].
 unfold joint_register_update_146. solve_joint_register_ready.
Qed.
Definition joint_register_update_147 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 770))).
Lemma joint_register_ready_147 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 770 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_147.
Proof.
 intros [g116 [b116 H116]].
 intros [g770 [b770 H770]].
 unfold joint_register_update_147. solve_joint_register_ready.
Qed.
Definition joint_register_update_150 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 752))).
Lemma joint_register_ready_150 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 752 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_150.
Proof.
 intros [g116 [b116 H116]].
 intros [g752 [b752 H752]].
 unfold joint_register_update_150. solve_joint_register_ready.
Qed.
Definition joint_register_update_151 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 754))).
Lemma joint_register_ready_151 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 754 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_151.
Proof.
 intros [g116 [b116 H116]].
 intros [g754 [b754 H754]].
 unfold joint_register_update_151. solve_joint_register_ready.
Qed.
Definition joint_register_update_152 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 753))).
Lemma joint_register_ready_152 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 753 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_152.
Proof.
 intros [g116 [b116 H116]].
 intros [g753 [b753 H753]].
 unfold joint_register_update_152. solve_joint_register_ready.
Qed.
Definition joint_register_update_153 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 755))).
Lemma joint_register_ready_153 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 755 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_153.
Proof.
 intros [g116 [b116 H116]].
 intros [g755 [b755 H755]].
 unfold joint_register_update_153. solve_joint_register_ready.
Qed.
Definition joint_register_update_167 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 757))).
Lemma joint_register_ready_167 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 757 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_167.
Proof.
 intros [g116 [b116 H116]].
 intros [g757 [b757 H757]].
 unfold joint_register_update_167. solve_joint_register_ready.
Qed.
Definition joint_register_update_168 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 759))).
Lemma joint_register_ready_168 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 759 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_168.
Proof.
 intros [g116 [b116 H116]].
 intros [g759 [b759 H759]].
 unfold joint_register_update_168. solve_joint_register_ready.
Qed.
Definition joint_register_update_169 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 758))).
Lemma joint_register_ready_169 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 758 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_169.
Proof.
 intros [g116 [b116 H116]].
 intros [g758 [b758 H758]].
 unfold joint_register_update_169. solve_joint_register_ready.
Qed.
Definition joint_register_update_170 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 760))).
Lemma joint_register_ready_170 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 760 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_170.
Proof.
 intros [g116 [b116 H116]].
 intros [g760 [b760 H760]].
 unfold joint_register_update_170. solve_joint_register_ready.
Qed.
Definition joint_register_update_187 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 763)).
Lemma joint_register_ready_187 old :
 (exists ground bits, VM.find 763 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_187.
Proof.
 intros [g763 [b763 H763]].
 unfold joint_register_update_187. solve_joint_register_ready.
Qed.
Definition joint_register_update_188 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 764)).
Lemma joint_register_ready_188 old :
 (exists ground bits, VM.find 764 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_188.
Proof.
 intros [g764 [b764 H764]].
 unfold joint_register_update_188. solve_joint_register_ready.
Qed.
Definition joint_register_update_189 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 750))).
Lemma joint_register_ready_189 old :
 (exists ground bits, VM.find 750 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_189.
Proof.
 intros [g750 [b750 H750]].
 unfold joint_register_update_189. solve_joint_register_ready.
Qed.
Definition joint_register_update_190 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 751)).
Lemma joint_register_ready_190 old :
 (exists ground bits, VM.find 751 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_190.
Proof.
 intros [g751 [b751 H751]].
 unfold joint_register_update_190. solve_joint_register_ready.
Qed.
Definition joint_register_update_191 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 756)).
Lemma joint_register_ready_191 old :
 (exists ground bits, VM.find 756 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_191.
Proof.
 intros [g756 [b756 H756]].
 unfold joint_register_update_191. solve_joint_register_ready.
Qed.
Definition joint_register_update_192 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 765))).
Lemma joint_register_ready_192 old :
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 765 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_192.
Proof.
 intros [g116 [b116 H116]].
 intros [g765 [b765 H765]].
 unfold joint_register_update_192. solve_joint_register_ready.
Qed.
Definition joint_register_update_193 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 766)).
Lemma joint_register_ready_193 old :
 (exists ground bits, VM.find 766 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_193.
Proof.
 intros [g766 [b766 H766]].
 unfold joint_register_update_193. solve_joint_register_ready.
Qed.
Definition joint_register_update_851 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1085)) (@Eref VarOrder.T (@Eid VarOrder.T 1021))).
Lemma joint_register_ready_851 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1021 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1085 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_851.
Proof.
 intros [g779 [b779 H779]].
 intros [g1021 [b1021 H1021]].
 intros [g1085 [b1085 H1085]].
 unfold joint_register_update_851. solve_joint_register_ready.
Qed.
Definition joint_register_update_852 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1086)) (@Eref VarOrder.T (@Eid VarOrder.T 1022))).
Lemma joint_register_ready_852 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1022 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1086 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_852.
Proof.
 intros [g779 [b779 H779]].
 intros [g1022 [b1022 H1022]].
 intros [g1086 [b1086 H1086]].
 unfold joint_register_update_852. solve_joint_register_ready.
Qed.
Definition joint_register_update_853 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1087)) (@Eref VarOrder.T (@Eid VarOrder.T 1023))).
Lemma joint_register_ready_853 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1023 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1087 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_853.
Proof.
 intros [g779 [b779 H779]].
 intros [g1023 [b1023 H1023]].
 intros [g1087 [b1087 H1087]].
 unfold joint_register_update_853. solve_joint_register_ready.
Qed.
Definition joint_register_update_854 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1088)) (@Eref VarOrder.T (@Eid VarOrder.T 1024))).
Lemma joint_register_ready_854 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1024 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1088 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_854.
Proof.
 intros [g779 [b779 H779]].
 intros [g1024 [b1024 H1024]].
 intros [g1088 [b1088 H1088]].
 unfold joint_register_update_854. solve_joint_register_ready.
Qed.
Definition joint_register_update_855 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1089)) (@Eref VarOrder.T (@Eid VarOrder.T 1025))).
Lemma joint_register_ready_855 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1025 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1089 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_855.
Proof.
 intros [g779 [b779 H779]].
 intros [g1025 [b1025 H1025]].
 intros [g1089 [b1089 H1089]].
 unfold joint_register_update_855. solve_joint_register_ready.
Qed.
Definition joint_register_update_856 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1090)) (@Eref VarOrder.T (@Eid VarOrder.T 1026))).
Lemma joint_register_ready_856 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1026 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1090 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_856.
Proof.
 intros [g779 [b779 H779]].
 intros [g1026 [b1026 H1026]].
 intros [g1090 [b1090 H1090]].
 unfold joint_register_update_856. solve_joint_register_ready.
Qed.
Definition joint_register_update_857 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1091)) (@Eref VarOrder.T (@Eid VarOrder.T 1027))).
Lemma joint_register_ready_857 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1027 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1091 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_857.
Proof.
 intros [g779 [b779 H779]].
 intros [g1027 [b1027 H1027]].
 intros [g1091 [b1091 H1091]].
 unfold joint_register_update_857. solve_joint_register_ready.
Qed.
Definition joint_register_update_858 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1092)) (@Eref VarOrder.T (@Eid VarOrder.T 1028))).
Lemma joint_register_ready_858 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1028 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1092 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_858.
Proof.
 intros [g779 [b779 H779]].
 intros [g1028 [b1028 H1028]].
 intros [g1092 [b1092 H1092]].
 unfold joint_register_update_858. solve_joint_register_ready.
Qed.
Definition joint_register_update_859 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1093)) (@Eref VarOrder.T (@Eid VarOrder.T 1029))).
Lemma joint_register_ready_859 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1029 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1093 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_859.
Proof.
 intros [g779 [b779 H779]].
 intros [g1029 [b1029 H1029]].
 intros [g1093 [b1093 H1093]].
 unfold joint_register_update_859. solve_joint_register_ready.
Qed.
Definition joint_register_update_860 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1094)) (@Eref VarOrder.T (@Eid VarOrder.T 1030))).
Lemma joint_register_ready_860 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1030 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1094 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_860.
Proof.
 intros [g779 [b779 H779]].
 intros [g1030 [b1030 H1030]].
 intros [g1094 [b1094 H1094]].
 unfold joint_register_update_860. solve_joint_register_ready.
Qed.
Definition joint_register_update_861 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1095)) (@Eref VarOrder.T (@Eid VarOrder.T 1031))).
Lemma joint_register_ready_861 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1031 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1095 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_861.
Proof.
 intros [g779 [b779 H779]].
 intros [g1031 [b1031 H1031]].
 intros [g1095 [b1095 H1095]].
 unfold joint_register_update_861. solve_joint_register_ready.
Qed.
Definition joint_register_update_862 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1096)) (@Eref VarOrder.T (@Eid VarOrder.T 1032))).
Lemma joint_register_ready_862 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1032 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1096 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_862.
Proof.
 intros [g779 [b779 H779]].
 intros [g1032 [b1032 H1032]].
 intros [g1096 [b1096 H1096]].
 unfold joint_register_update_862. solve_joint_register_ready.
Qed.
Definition joint_register_update_863 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1097)) (@Eref VarOrder.T (@Eid VarOrder.T 1033))).
Lemma joint_register_ready_863 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1033 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1097 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_863.
Proof.
 intros [g779 [b779 H779]].
 intros [g1033 [b1033 H1033]].
 intros [g1097 [b1097 H1097]].
 unfold joint_register_update_863. solve_joint_register_ready.
Qed.
Definition joint_register_update_864 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1098)) (@Eref VarOrder.T (@Eid VarOrder.T 1034))).
Lemma joint_register_ready_864 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1034 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1098 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_864.
Proof.
 intros [g779 [b779 H779]].
 intros [g1034 [b1034 H1034]].
 intros [g1098 [b1098 H1098]].
 unfold joint_register_update_864. solve_joint_register_ready.
Qed.
Definition joint_register_update_865 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1099)) (@Eref VarOrder.T (@Eid VarOrder.T 1035))).
Lemma joint_register_ready_865 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1035 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1099 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_865.
Proof.
 intros [g779 [b779 H779]].
 intros [g1035 [b1035 H1035]].
 intros [g1099 [b1099 H1099]].
 unfold joint_register_update_865. solve_joint_register_ready.
Qed.
Definition joint_register_update_866 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1100)) (@Eref VarOrder.T (@Eid VarOrder.T 1036))).
Lemma joint_register_ready_866 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1036 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1100 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_866.
Proof.
 intros [g779 [b779 H779]].
 intros [g1036 [b1036 H1036]].
 intros [g1100 [b1100 H1100]].
 unfold joint_register_update_866. solve_joint_register_ready.
Qed.
Definition joint_register_update_867 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1101)) (@Eref VarOrder.T (@Eid VarOrder.T 1037))).
Lemma joint_register_ready_867 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1037 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1101 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_867.
Proof.
 intros [g779 [b779 H779]].
 intros [g1037 [b1037 H1037]].
 intros [g1101 [b1101 H1101]].
 unfold joint_register_update_867. solve_joint_register_ready.
Qed.
Definition joint_register_update_868 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1102)) (@Eref VarOrder.T (@Eid VarOrder.T 1038))).
Lemma joint_register_ready_868 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1038 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1102 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_868.
Proof.
 intros [g779 [b779 H779]].
 intros [g1038 [b1038 H1038]].
 intros [g1102 [b1102 H1102]].
 unfold joint_register_update_868. solve_joint_register_ready.
Qed.
Definition joint_register_update_869 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1103)) (@Eref VarOrder.T (@Eid VarOrder.T 1039))).
Lemma joint_register_ready_869 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1039 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1103 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_869.
Proof.
 intros [g779 [b779 H779]].
 intros [g1039 [b1039 H1039]].
 intros [g1103 [b1103 H1103]].
 unfold joint_register_update_869. solve_joint_register_ready.
Qed.
Definition joint_register_update_870 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1104)) (@Eref VarOrder.T (@Eid VarOrder.T 1040))).
Lemma joint_register_ready_870 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1040 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1104 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_870.
Proof.
 intros [g779 [b779 H779]].
 intros [g1040 [b1040 H1040]].
 intros [g1104 [b1104 H1104]].
 unfold joint_register_update_870. solve_joint_register_ready.
Qed.
Definition joint_register_update_871 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1105)) (@Eref VarOrder.T (@Eid VarOrder.T 1041))).
Lemma joint_register_ready_871 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1041 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1105 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_871.
Proof.
 intros [g779 [b779 H779]].
 intros [g1041 [b1041 H1041]].
 intros [g1105 [b1105 H1105]].
 unfold joint_register_update_871. solve_joint_register_ready.
Qed.
Definition joint_register_update_872 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1106)) (@Eref VarOrder.T (@Eid VarOrder.T 1042))).
Lemma joint_register_ready_872 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1042 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1106 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_872.
Proof.
 intros [g779 [b779 H779]].
 intros [g1042 [b1042 H1042]].
 intros [g1106 [b1106 H1106]].
 unfold joint_register_update_872. solve_joint_register_ready.
Qed.
Definition joint_register_update_873 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1107)) (@Eref VarOrder.T (@Eid VarOrder.T 1043))).
Lemma joint_register_ready_873 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1043 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1107 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_873.
Proof.
 intros [g779 [b779 H779]].
 intros [g1043 [b1043 H1043]].
 intros [g1107 [b1107 H1107]].
 unfold joint_register_update_873. solve_joint_register_ready.
Qed.
Definition joint_register_update_874 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1108)) (@Eref VarOrder.T (@Eid VarOrder.T 1044))).
Lemma joint_register_ready_874 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1044 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1108 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_874.
Proof.
 intros [g779 [b779 H779]].
 intros [g1044 [b1044 H1044]].
 intros [g1108 [b1108 H1108]].
 unfold joint_register_update_874. solve_joint_register_ready.
Qed.
Definition joint_register_update_875 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1109)) (@Eref VarOrder.T (@Eid VarOrder.T 1045))).
Lemma joint_register_ready_875 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1045 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1109 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_875.
Proof.
 intros [g779 [b779 H779]].
 intros [g1045 [b1045 H1045]].
 intros [g1109 [b1109 H1109]].
 unfold joint_register_update_875. solve_joint_register_ready.
Qed.
Definition joint_register_update_876 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1110)) (@Eref VarOrder.T (@Eid VarOrder.T 1046))).
Lemma joint_register_ready_876 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1046 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1110 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_876.
Proof.
 intros [g779 [b779 H779]].
 intros [g1046 [b1046 H1046]].
 intros [g1110 [b1110 H1110]].
 unfold joint_register_update_876. solve_joint_register_ready.
Qed.
Definition joint_register_update_877 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1111)) (@Eref VarOrder.T (@Eid VarOrder.T 1047))).
Lemma joint_register_ready_877 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1047 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1111 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_877.
Proof.
 intros [g779 [b779 H779]].
 intros [g1047 [b1047 H1047]].
 intros [g1111 [b1111 H1111]].
 unfold joint_register_update_877. solve_joint_register_ready.
Qed.
Definition joint_register_update_878 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1112)) (@Eref VarOrder.T (@Eid VarOrder.T 1048))).
Lemma joint_register_ready_878 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1048 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1112 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_878.
Proof.
 intros [g779 [b779 H779]].
 intros [g1048 [b1048 H1048]].
 intros [g1112 [b1112 H1112]].
 unfold joint_register_update_878. solve_joint_register_ready.
Qed.
Definition joint_register_update_879 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1113)) (@Eref VarOrder.T (@Eid VarOrder.T 1049))).
Lemma joint_register_ready_879 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1049 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1113 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_879.
Proof.
 intros [g779 [b779 H779]].
 intros [g1049 [b1049 H1049]].
 intros [g1113 [b1113 H1113]].
 unfold joint_register_update_879. solve_joint_register_ready.
Qed.
Definition joint_register_update_880 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1114)) (@Eref VarOrder.T (@Eid VarOrder.T 1050))).
Lemma joint_register_ready_880 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1050 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1114 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_880.
Proof.
 intros [g779 [b779 H779]].
 intros [g1050 [b1050 H1050]].
 intros [g1114 [b1114 H1114]].
 unfold joint_register_update_880. solve_joint_register_ready.
Qed.
Definition joint_register_update_881 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1115)) (@Eref VarOrder.T (@Eid VarOrder.T 1051))).
Lemma joint_register_ready_881 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1051 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1115 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_881.
Proof.
 intros [g779 [b779 H779]].
 intros [g1051 [b1051 H1051]].
 intros [g1115 [b1115 H1115]].
 unfold joint_register_update_881. solve_joint_register_ready.
Qed.
Definition joint_register_update_882 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1116)) (@Eref VarOrder.T (@Eid VarOrder.T 1052))).
Lemma joint_register_ready_882 old :
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1052 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1116 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_882.
Proof.
 intros [g779 [b779 H779]].
 intros [g1052 [b1052 H1052]].
 intros [g1116 [b1116 H1116]].
 unfold joint_register_update_882. solve_joint_register_ready.
Qed.
Definition joint_register_update_7748 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8158)) (@Eref VarOrder.T (@Eid VarOrder.T 7801))).
Lemma joint_register_ready_7748 old :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7801 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8158 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7748.
Proof.
 intros [g65 [b65 H65]].
 intros [g7801 [b7801 H7801]].
 intros [g8158 [b8158 H8158]].
 unfold joint_register_update_7748. solve_joint_register_ready.
Qed.
Definition joint_register_update_7749 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 0) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8159)) (@Eref VarOrder.T (@Eid VarOrder.T 7800)))).
Lemma joint_register_ready_7749 old :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7800 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8159 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7749.
Proof.
 intros [g65 [b65 H65]].
 intros [g7800 [b7800 H7800]].
 intros [g8159 [b8159 H8159]].
 unfold joint_register_update_7749. solve_joint_register_ready.
Qed.
Definition joint_register_update_7750 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8160)) (@Eref VarOrder.T (@Eid VarOrder.T 7878))).
Lemma joint_register_ready_7750 old :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7878 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8160 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7750.
Proof.
 intros [g65 [b65 H65]].
 intros [g7878 [b7878 H7878]].
 intros [g8160 [b8160 H8160]].
 unfold joint_register_update_7750. solve_joint_register_ready.
Qed.
Definition joint_register_update_7751 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8161)) (@Eref VarOrder.T (@Eid VarOrder.T 7877))).
Lemma joint_register_ready_7751 old :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7877 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8161 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7751.
Proof.
 intros [g65 [b65 H65]].
 intros [g7877 [b7877 H7877]].
 intros [g8161 [b8161 H8161]].
 unfold joint_register_update_7751. solve_joint_register_ready.
Qed.
Definition joint_register_update_7752 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8162)) (@Eref VarOrder.T (@Eid VarOrder.T 7879))).
Lemma joint_register_ready_7752 old :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7879 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8162 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7752.
Proof.
 intros [g65 [b65 H65]].
 intros [g7879 [b7879 H7879]].
 intros [g8162 [b8162 H8162]].
 unfold joint_register_update_7752. solve_joint_register_ready.
Qed.
Definition joint_register_update_7753 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8163)) (@Eref VarOrder.T (@Eid VarOrder.T 7880))).
Lemma joint_register_ready_7753 old :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7880 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8163 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7753.
Proof.
 intros [g65 [b65 H65]].
 intros [g7880 [b7880 H7880]].
 intros [g8163 [b8163 H8163]].
 unfold joint_register_update_7753. solve_joint_register_ready.
Qed.
Definition joint_register_update_7754 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7871)).
Lemma joint_register_ready_7754 old :
 (exists ground bits, VM.find 7871 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7754.
Proof.
 intros [g7871 [b7871 H7871]].
 unfold joint_register_update_7754. solve_joint_register_ready.
Qed.
Definition joint_register_update_7755 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7872)).
Lemma joint_register_ready_7755 old :
 (exists ground bits, VM.find 7872 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7755.
Proof.
 intros [g7872 [b7872 H7872]].
 unfold joint_register_update_7755. solve_joint_register_ready.
Qed.
Definition joint_register_update_7756 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7881)).
Lemma joint_register_ready_7756 old :
 (exists ground bits, VM.find 7881 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7756.
Proof.
 intros [g7881 [b7881 H7881]].
 unfold joint_register_update_7756. solve_joint_register_ready.
Qed.
Definition joint_register_update_7757 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7873)).
Lemma joint_register_ready_7757 old :
 (exists ground bits, VM.find 7873 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7757.
Proof.
 intros [g7873 [b7873 H7873]].
 unfold joint_register_update_7757. solve_joint_register_ready.
Qed.
Definition joint_register_update_7758 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7874)).
Lemma joint_register_ready_7758 old :
 (exists ground bits, VM.find 7874 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7758.
Proof.
 intros [g7874 [b7874 H7874]].
 unfold joint_register_update_7758. solve_joint_register_ready.
Qed.
Definition joint_register_update_7759 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7875)).
Lemma joint_register_ready_7759 old :
 (exists ground bits, VM.find 7875 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7759.
Proof.
 intros [g7875 [b7875 H7875]].
 unfold joint_register_update_7759. solve_joint_register_ready.
Qed.
Definition joint_register_update_7760 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7876)).
Lemma joint_register_ready_7760 old :
 (exists ground bits, VM.find 7876 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7760.
Proof.
 intros [g7876 [b7876 H7876]].
 unfold joint_register_update_7760. solve_joint_register_ready.
Qed.
Definition joint_register_update_7762 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7761)).
Lemma joint_register_ready_7762 old :
 (exists ground bits, VM.find 7761 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7762.
Proof.
 intros [g7761 [b7761 H7761]].
 unfold joint_register_update_7762. solve_joint_register_ready.
Qed.
Definition joint_register_update_7768 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 7767)) (@Eref VarOrder.T (@Eid VarOrder.T 7781))).
Lemma joint_register_ready_7768 old :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7767 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7781 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_register_update_7768.
Proof.
 intros [g65 [b65 H65]].
 intros [g7767 [b7767 H7767]].
 intros [g7781 [b7781 H7781]].
 unfold joint_register_update_7768. solve_joint_register_ready.
Qed.
Print Assumptions joint_register_ready_7768.

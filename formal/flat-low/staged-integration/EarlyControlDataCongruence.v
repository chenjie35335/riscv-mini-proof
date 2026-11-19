Require Import CoreSocModel ComparisonNodes SelectedUIntNodeCongruenceGeneral SelectedNodeSafety DataAddressExpressionCertificates DataAddressUIntCertificates DataAddressPositionCertificate DataAddressSafetyCertificate.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma early_control_data_member_883 : List.In (883,address_expr_883) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 0%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_883_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 883 next_left = VM.find 883 next_right.
Proof.
 intros H780 E780 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 883 address_expr_883 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_883)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 883 address_expr_883 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_883 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_883 inputs path site flat_memories left value H780 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_884 : List.In (884,address_expr_884) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 1%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_884_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 851 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 851 left = VM.find 851 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 884 next_left = VM.find 884 next_right.
Proof.
 intros H780 H851 E780 E851 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 884 address_expr_884 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_884)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 884 address_expr_884 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_884 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E851.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_884 inputs path site flat_memories left value H780 H851 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_885 : List.In (885,address_expr_885) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 2%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_885_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 852 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 884 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 852 left = VM.find 852 right ->
 VM.find 884 left = VM.find 884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 885 next_left = VM.find 885 next_right.
Proof.
 intros H780 H852 H884 E780 E852 E884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 885 address_expr_885 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_885)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 885 address_expr_885 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_885 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E852.
   rewrite E884.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_885 inputs path site flat_memories left value H780 H852 H884 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_886 : List.In (886,address_expr_886) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 3%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_886_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 853 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 885 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 853 left = VM.find 853 right ->
 VM.find 885 left = VM.find 885 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 886 next_left = VM.find 886 next_right.
Proof.
 intros H780 H853 H885 E780 E853 E885 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 886 address_expr_886 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_886)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 886 address_expr_886 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_886 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E853.
   rewrite E885.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_886 inputs path site flat_memories left value H780 H853 H885 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_887 : List.In (887,address_expr_887) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 4%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_887_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 854 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 886 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 854 left = VM.find 854 right ->
 VM.find 886 left = VM.find 886 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 887 next_left = VM.find 887 next_right.
Proof.
 intros H780 H854 H886 E780 E854 E886 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 887 address_expr_887 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_887)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 887 address_expr_887 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_887 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E854.
   rewrite E886.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_887 inputs path site flat_memories left value H780 H854 H886 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_888 : List.In (888,address_expr_888) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 5%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_888_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 855 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 887 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 855 left = VM.find 855 right ->
 VM.find 887 left = VM.find 887 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 888 next_left = VM.find 888 next_right.
Proof.
 intros H780 H855 H887 E780 E855 E887 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 888 address_expr_888 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_888)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 888 address_expr_888 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_888 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E855.
   rewrite E887.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_888 inputs path site flat_memories left value H780 H855 H887 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_889 : List.In (889,address_expr_889) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 6%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_889_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 856 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 888 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 856 left = VM.find 856 right ->
 VM.find 888 left = VM.find 888 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 889 next_left = VM.find 889 next_right.
Proof.
 intros H780 H856 H888 E780 E856 E888 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 889 address_expr_889 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_889)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 889 address_expr_889 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_889 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E856.
   rewrite E888.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_889 inputs path site flat_memories left value H780 H856 H888 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_890 : List.In (890,address_expr_890) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 7%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_890_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 857 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 889 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 857 left = VM.find 857 right ->
 VM.find 889 left = VM.find 889 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 890 next_left = VM.find 890 next_right.
Proof.
 intros H780 H857 H889 E780 E857 E889 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 890 address_expr_890 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_890)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 890 address_expr_890 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_890 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E857.
   rewrite E889.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_890 inputs path site flat_memories left value H780 H857 H889 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_891 : List.In (891,address_expr_891) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 8%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_891_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 858 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 890 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 858 left = VM.find 858 right ->
 VM.find 890 left = VM.find 890 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 891 next_left = VM.find 891 next_right.
Proof.
 intros H780 H858 H890 E780 E858 E890 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 891 address_expr_891 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_891)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 891 address_expr_891 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_891 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E858.
   rewrite E890.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_891 inputs path site flat_memories left value H780 H858 H890 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_892 : List.In (892,address_expr_892) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 9%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_892_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 859 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 891 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 859 left = VM.find 859 right ->
 VM.find 891 left = VM.find 891 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 892 next_left = VM.find 892 next_right.
Proof.
 intros H780 H859 H891 E780 E859 E891 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 892 address_expr_892 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_892)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 892 address_expr_892 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_892 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E859.
   rewrite E891.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_892 inputs path site flat_memories left value H780 H859 H891 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_893 : List.In (893,address_expr_893) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 10%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_893_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 860 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 892 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 860 left = VM.find 860 right ->
 VM.find 892 left = VM.find 892 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 893 next_left = VM.find 893 next_right.
Proof.
 intros H780 H860 H892 E780 E860 E892 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 893 address_expr_893 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_893)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 893 address_expr_893 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_893 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E860.
   rewrite E892.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_893 inputs path site flat_memories left value H780 H860 H892 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_894 : List.In (894,address_expr_894) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 11%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_894_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 861 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 893 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 861 left = VM.find 861 right ->
 VM.find 893 left = VM.find 893 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 894 next_left = VM.find 894 next_right.
Proof.
 intros H780 H861 H893 E780 E861 E893 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 894 address_expr_894 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_894)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 894 address_expr_894 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_894 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E861.
   rewrite E893.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_894 inputs path site flat_memories left value H780 H861 H893 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_895 : List.In (895,address_expr_895) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 12%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_895_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 862 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 894 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 862 left = VM.find 862 right ->
 VM.find 894 left = VM.find 894 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 895 next_left = VM.find 895 next_right.
Proof.
 intros H780 H862 H894 E780 E862 E894 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 895 address_expr_895 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_895)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 895 address_expr_895 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_895 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E862.
   rewrite E894.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_895 inputs path site flat_memories left value H780 H862 H894 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_896 : List.In (896,address_expr_896) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 13%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_896_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 863 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 895 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 863 left = VM.find 863 right ->
 VM.find 895 left = VM.find 895 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 896 next_left = VM.find 896 next_right.
Proof.
 intros H780 H863 H895 E780 E863 E895 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 896 address_expr_896 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_896)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 896 address_expr_896 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_896 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E863.
   rewrite E895.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_896 inputs path site flat_memories left value H780 H863 H895 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_897 : List.In (897,address_expr_897) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 14%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_897_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 864 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 896 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 864 left = VM.find 864 right ->
 VM.find 896 left = VM.find 896 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 897 next_left = VM.find 897 next_right.
Proof.
 intros H780 H864 H896 E780 E864 E896 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 897 address_expr_897 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_897)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 897 address_expr_897 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_897 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E864.
   rewrite E896.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_897 inputs path site flat_memories left value H780 H864 H896 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_898 : List.In (898,address_expr_898) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 15%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_898_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 865 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 897 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 865 left = VM.find 865 right ->
 VM.find 897 left = VM.find 897 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 898 next_left = VM.find 898 next_right.
Proof.
 intros H780 H865 H897 E780 E865 E897 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 898 address_expr_898 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_898)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 898 address_expr_898 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_898 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E865.
   rewrite E897.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_898 inputs path site flat_memories left value H780 H865 H897 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_899 : List.In (899,address_expr_899) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 16%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_899_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 866 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 898 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 866 left = VM.find 866 right ->
 VM.find 898 left = VM.find 898 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 899 next_left = VM.find 899 next_right.
Proof.
 intros H780 H866 H898 E780 E866 E898 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 899 address_expr_899 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_899)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 899 address_expr_899 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_899 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E866.
   rewrite E898.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_899 inputs path site flat_memories left value H780 H866 H898 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_900 : List.In (900,address_expr_900) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 17%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_900_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 867 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 899 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 867 left = VM.find 867 right ->
 VM.find 899 left = VM.find 899 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 900 next_left = VM.find 900 next_right.
Proof.
 intros H780 H867 H899 E780 E867 E899 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 900 address_expr_900 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_900)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 900 address_expr_900 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_900 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E867.
   rewrite E899.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_900 inputs path site flat_memories left value H780 H867 H899 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_901 : List.In (901,address_expr_901) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 18%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_901_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 868 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 900 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 868 left = VM.find 868 right ->
 VM.find 900 left = VM.find 900 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 901 next_left = VM.find 901 next_right.
Proof.
 intros H780 H868 H900 E780 E868 E900 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 901 address_expr_901 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_901)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 901 address_expr_901 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_901 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E868.
   rewrite E900.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_901 inputs path site flat_memories left value H780 H868 H900 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_902 : List.In (902,address_expr_902) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 19%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_902_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 869 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 901 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 869 left = VM.find 869 right ->
 VM.find 901 left = VM.find 901 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 902 next_left = VM.find 902 next_right.
Proof.
 intros H780 H869 H901 E780 E869 E901 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 902 address_expr_902 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_902)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 902 address_expr_902 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_902 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E869.
   rewrite E901.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_902 inputs path site flat_memories left value H780 H869 H901 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_903 : List.In (903,address_expr_903) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 20%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_903_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 870 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 902 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 870 left = VM.find 870 right ->
 VM.find 902 left = VM.find 902 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 903 next_left = VM.find 903 next_right.
Proof.
 intros H780 H870 H902 E780 E870 E902 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 903 address_expr_903 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_903)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 903 address_expr_903 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_903 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E870.
   rewrite E902.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_903 inputs path site flat_memories left value H780 H870 H902 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_904 : List.In (904,address_expr_904) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 21%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_904_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 871 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 903 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 871 left = VM.find 871 right ->
 VM.find 903 left = VM.find 903 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 904 next_left = VM.find 904 next_right.
Proof.
 intros H780 H871 H903 E780 E871 E903 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 904 address_expr_904 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_904)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 904 address_expr_904 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_904 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E871.
   rewrite E903.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_904 inputs path site flat_memories left value H780 H871 H903 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_905 : List.In (905,address_expr_905) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 22%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_905_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 872 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 904 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 872 left = VM.find 872 right ->
 VM.find 904 left = VM.find 904 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 905 next_left = VM.find 905 next_right.
Proof.
 intros H780 H872 H904 E780 E872 E904 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 905 address_expr_905 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_905)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 905 address_expr_905 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_905 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E872.
   rewrite E904.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_905 inputs path site flat_memories left value H780 H872 H904 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_906 : List.In (906,address_expr_906) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 23%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_906_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 873 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 905 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 873 left = VM.find 873 right ->
 VM.find 905 left = VM.find 905 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 906 next_left = VM.find 906 next_right.
Proof.
 intros H780 H873 H905 E780 E873 E905 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 906 address_expr_906 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_906)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 906 address_expr_906 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_906 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E873.
   rewrite E905.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_906 inputs path site flat_memories left value H780 H873 H905 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_907 : List.In (907,address_expr_907) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 24%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_907_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 874 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 906 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 874 left = VM.find 874 right ->
 VM.find 906 left = VM.find 906 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 907 next_left = VM.find 907 next_right.
Proof.
 intros H780 H874 H906 E780 E874 E906 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 907 address_expr_907 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_907)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 907 address_expr_907 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_907 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E874.
   rewrite E906.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_907 inputs path site flat_memories left value H780 H874 H906 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_908 : List.In (908,address_expr_908) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 25%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_908_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 875 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 907 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 875 left = VM.find 875 right ->
 VM.find 907 left = VM.find 907 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 908 next_left = VM.find 908 next_right.
Proof.
 intros H780 H875 H907 E780 E875 E907 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 908 address_expr_908 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_908)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 908 address_expr_908 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_908 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E875.
   rewrite E907.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_908 inputs path site flat_memories left value H780 H875 H907 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_909 : List.In (909,address_expr_909) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 26%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_909_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 876 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 908 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 876 left = VM.find 876 right ->
 VM.find 908 left = VM.find 908 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 909 next_left = VM.find 909 next_right.
Proof.
 intros H780 H876 H908 E780 E876 E908 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 909 address_expr_909 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_909)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 909 address_expr_909 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_909 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E876.
   rewrite E908.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_909 inputs path site flat_memories left value H780 H876 H908 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_910 : List.In (910,address_expr_910) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 27%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_910_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 877 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 909 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 877 left = VM.find 877 right ->
 VM.find 909 left = VM.find 909 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 910 next_left = VM.find 910 next_right.
Proof.
 intros H780 H877 H909 E780 E877 E909 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 910 address_expr_910 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_910)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 910 address_expr_910 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_910 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E877.
   rewrite E909.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_910 inputs path site flat_memories left value H780 H877 H909 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_911 : List.In (911,address_expr_911) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 28%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_911_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 878 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 910 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 878 left = VM.find 878 right ->
 VM.find 910 left = VM.find 910 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 911 next_left = VM.find 911 next_right.
Proof.
 intros H780 H878 H910 E780 E878 E910 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 911 address_expr_911 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_911)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 911 address_expr_911 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_911 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E878.
   rewrite E910.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_911 inputs path site flat_memories left value H780 H878 H910 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_912 : List.In (912,address_expr_912) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 29%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_912_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 879 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 911 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 879 left = VM.find 879 right ->
 VM.find 911 left = VM.find 911 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 912 next_left = VM.find 912 next_right.
Proof.
 intros H780 H879 H911 E780 E879 E911 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 912 address_expr_912 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_912)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 912 address_expr_912 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_912 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E879.
   rewrite E911.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_912 inputs path site flat_memories left value H780 H879 H911 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_913 : List.In (913,address_expr_913) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 30%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_913_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 880 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 912 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 880 left = VM.find 880 right ->
 VM.find 912 left = VM.find 912 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 913 next_left = VM.find 913 next_right.
Proof.
 intros H780 H880 H912 E780 E880 E912 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 913 address_expr_913 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_913)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 913 address_expr_913 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_913 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E880.
   rewrite E912.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_913 inputs path site flat_memories left value H780 H880 H912 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_914 : List.In (914,address_expr_914) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 31%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_914_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 881 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 913 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 881 left = VM.find 881 right ->
 VM.find 913 left = VM.find 913 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 914 next_left = VM.find 914 next_right.
Proof.
 intros H780 H881 H913 E780 E881 E913 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 914 address_expr_914 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_914)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 914 address_expr_914 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_914 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E881.
   rewrite E913.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_914 inputs path site flat_memories left value H780 H881 H913 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_915 : List.In (915,address_expr_915) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 32%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_915_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 780 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 882 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 914 left = Some (Gval (Fuint width) bits)) ->
 VM.find 780 left = VM.find 780 right ->
 VM.find 882 left = VM.find 882 right ->
 VM.find 914 left = VM.find 914 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 915 next_left = VM.find 915 next_right.
Proof.
 intros H780 H882 H914 E780 E882 E914 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 915 address_expr_915 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_915)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 915 address_expr_915 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_915 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E780.
   rewrite E882.
   rewrite E914.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_915 inputs path site flat_memories left value H780 H882 H914 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_916 : List.In (916,address_expr_916) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 33%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_916_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 915 left = Some (Gval (Fuint width) bits)) ->
 VM.find 915 left = VM.find 915 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 916 next_left = VM.find 916 next_right.
Proof.
 intros H915 E915 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 916 address_expr_916 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_916)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 916 address_expr_916 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_916 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E915.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_916 inputs path site flat_memories left value H915 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_917 : List.In (917,address_expr_917) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 34%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_917_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 883 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 916 left = Some (Gval (Fuint width) bits)) ->
 VM.find 883 left = VM.find 883 right ->
 VM.find 916 left = VM.find 916 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 917 next_left = VM.find 917 next_right.
Proof.
 intros H883 H916 E883 E916 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 917 address_expr_917 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_917)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 917 address_expr_917 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_917 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E883.
   rewrite E916.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_917 inputs path site flat_memories left value H883 H916 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_918 : List.In (918,address_expr_918) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 35%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_918_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 918 next_left = VM.find 918 next_right.
Proof.
 intros H781 E781 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 918 address_expr_918 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_918)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 918 address_expr_918 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_918 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_918 inputs path site flat_memories left value H781 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_919 : List.In (919,address_expr_919) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 36%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_919_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 851 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 851 left = VM.find 851 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 919 next_left = VM.find 919 next_right.
Proof.
 intros H781 H851 E781 E851 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 919 address_expr_919 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_919)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 919 address_expr_919 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_919 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E851.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_919 inputs path site flat_memories left value H781 H851 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_920 : List.In (920,address_expr_920) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 37%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_920_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 852 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 919 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 852 left = VM.find 852 right ->
 VM.find 919 left = VM.find 919 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 920 next_left = VM.find 920 next_right.
Proof.
 intros H781 H852 H919 E781 E852 E919 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 920 address_expr_920 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_920)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 920 address_expr_920 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_920 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E852.
   rewrite E919.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_920 inputs path site flat_memories left value H781 H852 H919 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_921 : List.In (921,address_expr_921) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 38%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_921_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 853 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 920 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 853 left = VM.find 853 right ->
 VM.find 920 left = VM.find 920 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 921 next_left = VM.find 921 next_right.
Proof.
 intros H781 H853 H920 E781 E853 E920 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 921 address_expr_921 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_921)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 921 address_expr_921 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_921 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E853.
   rewrite E920.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_921 inputs path site flat_memories left value H781 H853 H920 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_922 : List.In (922,address_expr_922) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 39%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_922_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 854 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 921 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 854 left = VM.find 854 right ->
 VM.find 921 left = VM.find 921 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 922 next_left = VM.find 922 next_right.
Proof.
 intros H781 H854 H921 E781 E854 E921 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 922 address_expr_922 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_922)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 922 address_expr_922 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_922 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E854.
   rewrite E921.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_922 inputs path site flat_memories left value H781 H854 H921 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_923 : List.In (923,address_expr_923) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 40%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_923_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 855 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 922 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 855 left = VM.find 855 right ->
 VM.find 922 left = VM.find 922 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 923 next_left = VM.find 923 next_right.
Proof.
 intros H781 H855 H922 E781 E855 E922 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 923 address_expr_923 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_923)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 923 address_expr_923 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_923 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E855.
   rewrite E922.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_923 inputs path site flat_memories left value H781 H855 H922 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_924 : List.In (924,address_expr_924) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 41%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_924_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 856 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 923 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 856 left = VM.find 856 right ->
 VM.find 923 left = VM.find 923 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 924 next_left = VM.find 924 next_right.
Proof.
 intros H781 H856 H923 E781 E856 E923 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 924 address_expr_924 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_924)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 924 address_expr_924 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_924 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E856.
   rewrite E923.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_924 inputs path site flat_memories left value H781 H856 H923 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_925 : List.In (925,address_expr_925) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 42%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_925_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 857 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 924 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 857 left = VM.find 857 right ->
 VM.find 924 left = VM.find 924 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 925 next_left = VM.find 925 next_right.
Proof.
 intros H781 H857 H924 E781 E857 E924 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 925 address_expr_925 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_925)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 925 address_expr_925 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_925 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E857.
   rewrite E924.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_925 inputs path site flat_memories left value H781 H857 H924 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_926 : List.In (926,address_expr_926) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 43%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_926_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 858 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 925 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 858 left = VM.find 858 right ->
 VM.find 925 left = VM.find 925 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 926 next_left = VM.find 926 next_right.
Proof.
 intros H781 H858 H925 E781 E858 E925 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 926 address_expr_926 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_926)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 926 address_expr_926 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_926 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E858.
   rewrite E925.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_926 inputs path site flat_memories left value H781 H858 H925 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_927 : List.In (927,address_expr_927) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 44%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_927_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 859 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 926 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 859 left = VM.find 859 right ->
 VM.find 926 left = VM.find 926 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 927 next_left = VM.find 927 next_right.
Proof.
 intros H781 H859 H926 E781 E859 E926 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 927 address_expr_927 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_927)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 927 address_expr_927 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_927 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E859.
   rewrite E926.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_927 inputs path site flat_memories left value H781 H859 H926 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_928 : List.In (928,address_expr_928) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 45%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_928_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 860 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 927 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 860 left = VM.find 860 right ->
 VM.find 927 left = VM.find 927 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 928 next_left = VM.find 928 next_right.
Proof.
 intros H781 H860 H927 E781 E860 E927 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 928 address_expr_928 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_928)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 928 address_expr_928 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_928 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E860.
   rewrite E927.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_928 inputs path site flat_memories left value H781 H860 H927 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_929 : List.In (929,address_expr_929) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 46%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_929_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 861 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 928 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 861 left = VM.find 861 right ->
 VM.find 928 left = VM.find 928 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 929 next_left = VM.find 929 next_right.
Proof.
 intros H781 H861 H928 E781 E861 E928 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 929 address_expr_929 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_929)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 929 address_expr_929 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_929 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E861.
   rewrite E928.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_929 inputs path site flat_memories left value H781 H861 H928 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_930 : List.In (930,address_expr_930) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 47%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_930_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 862 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 929 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 862 left = VM.find 862 right ->
 VM.find 929 left = VM.find 929 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 930 next_left = VM.find 930 next_right.
Proof.
 intros H781 H862 H929 E781 E862 E929 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 930 address_expr_930 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_930)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 930 address_expr_930 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_930 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E862.
   rewrite E929.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_930 inputs path site flat_memories left value H781 H862 H929 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_931 : List.In (931,address_expr_931) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 48%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_931_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 863 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 930 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 863 left = VM.find 863 right ->
 VM.find 930 left = VM.find 930 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 931 next_left = VM.find 931 next_right.
Proof.
 intros H781 H863 H930 E781 E863 E930 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 931 address_expr_931 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_931)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 931 address_expr_931 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_931 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E863.
   rewrite E930.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_931 inputs path site flat_memories left value H781 H863 H930 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_932 : List.In (932,address_expr_932) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 49%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_932_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 864 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 931 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 864 left = VM.find 864 right ->
 VM.find 931 left = VM.find 931 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 932 next_left = VM.find 932 next_right.
Proof.
 intros H781 H864 H931 E781 E864 E931 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 932 address_expr_932 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_932)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 932 address_expr_932 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_932 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E864.
   rewrite E931.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_932 inputs path site flat_memories left value H781 H864 H931 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_933 : List.In (933,address_expr_933) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 50%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_933_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 865 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 932 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 865 left = VM.find 865 right ->
 VM.find 932 left = VM.find 932 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 933 next_left = VM.find 933 next_right.
Proof.
 intros H781 H865 H932 E781 E865 E932 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 933 address_expr_933 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_933)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 933 address_expr_933 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_933 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E865.
   rewrite E932.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_933 inputs path site flat_memories left value H781 H865 H932 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_934 : List.In (934,address_expr_934) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 51%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_934_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 866 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 933 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 866 left = VM.find 866 right ->
 VM.find 933 left = VM.find 933 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 934 next_left = VM.find 934 next_right.
Proof.
 intros H781 H866 H933 E781 E866 E933 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 934 address_expr_934 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_934)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 934 address_expr_934 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_934 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E866.
   rewrite E933.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_934 inputs path site flat_memories left value H781 H866 H933 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_935 : List.In (935,address_expr_935) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 52%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_935_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 867 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 934 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 867 left = VM.find 867 right ->
 VM.find 934 left = VM.find 934 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 935 next_left = VM.find 935 next_right.
Proof.
 intros H781 H867 H934 E781 E867 E934 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 935 address_expr_935 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_935)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 935 address_expr_935 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_935 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E867.
   rewrite E934.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_935 inputs path site flat_memories left value H781 H867 H934 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_936 : List.In (936,address_expr_936) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 53%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_936_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 868 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 935 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 868 left = VM.find 868 right ->
 VM.find 935 left = VM.find 935 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 936 next_left = VM.find 936 next_right.
Proof.
 intros H781 H868 H935 E781 E868 E935 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 936 address_expr_936 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_936)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 936 address_expr_936 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_936 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E868.
   rewrite E935.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_936 inputs path site flat_memories left value H781 H868 H935 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_937 : List.In (937,address_expr_937) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 54%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_937_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 869 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 936 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 869 left = VM.find 869 right ->
 VM.find 936 left = VM.find 936 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 937 next_left = VM.find 937 next_right.
Proof.
 intros H781 H869 H936 E781 E869 E936 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 937 address_expr_937 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_937)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 937 address_expr_937 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_937 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E869.
   rewrite E936.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_937 inputs path site flat_memories left value H781 H869 H936 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_938 : List.In (938,address_expr_938) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 55%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_938_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 870 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 937 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 870 left = VM.find 870 right ->
 VM.find 937 left = VM.find 937 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 938 next_left = VM.find 938 next_right.
Proof.
 intros H781 H870 H937 E781 E870 E937 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 938 address_expr_938 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_938)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 938 address_expr_938 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_938 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E870.
   rewrite E937.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_938 inputs path site flat_memories left value H781 H870 H937 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_939 : List.In (939,address_expr_939) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 56%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_939_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 871 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 938 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 871 left = VM.find 871 right ->
 VM.find 938 left = VM.find 938 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 939 next_left = VM.find 939 next_right.
Proof.
 intros H781 H871 H938 E781 E871 E938 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 939 address_expr_939 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_939)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 939 address_expr_939 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_939 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E871.
   rewrite E938.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_939 inputs path site flat_memories left value H781 H871 H938 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_940 : List.In (940,address_expr_940) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 57%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_940_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 872 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 939 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 872 left = VM.find 872 right ->
 VM.find 939 left = VM.find 939 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 940 next_left = VM.find 940 next_right.
Proof.
 intros H781 H872 H939 E781 E872 E939 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 940 address_expr_940 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_940)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 940 address_expr_940 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_940 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E872.
   rewrite E939.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_940 inputs path site flat_memories left value H781 H872 H939 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_941 : List.In (941,address_expr_941) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 58%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_941_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 873 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 940 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 873 left = VM.find 873 right ->
 VM.find 940 left = VM.find 940 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 941 next_left = VM.find 941 next_right.
Proof.
 intros H781 H873 H940 E781 E873 E940 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 941 address_expr_941 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_941)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 941 address_expr_941 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_941 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E873.
   rewrite E940.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_941 inputs path site flat_memories left value H781 H873 H940 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_942 : List.In (942,address_expr_942) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 59%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_942_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 874 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 941 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 874 left = VM.find 874 right ->
 VM.find 941 left = VM.find 941 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 942 next_left = VM.find 942 next_right.
Proof.
 intros H781 H874 H941 E781 E874 E941 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 942 address_expr_942 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_942)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 942 address_expr_942 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_942 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E874.
   rewrite E941.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_942 inputs path site flat_memories left value H781 H874 H941 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_943 : List.In (943,address_expr_943) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 60%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_943_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 875 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 942 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 875 left = VM.find 875 right ->
 VM.find 942 left = VM.find 942 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 943 next_left = VM.find 943 next_right.
Proof.
 intros H781 H875 H942 E781 E875 E942 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 943 address_expr_943 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_943)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 943 address_expr_943 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_943 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E875.
   rewrite E942.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_943 inputs path site flat_memories left value H781 H875 H942 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_944 : List.In (944,address_expr_944) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 61%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_944_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 876 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 943 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 876 left = VM.find 876 right ->
 VM.find 943 left = VM.find 943 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 944 next_left = VM.find 944 next_right.
Proof.
 intros H781 H876 H943 E781 E876 E943 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 944 address_expr_944 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_944)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 944 address_expr_944 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_944 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E876.
   rewrite E943.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_944 inputs path site flat_memories left value H781 H876 H943 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_945 : List.In (945,address_expr_945) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 62%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_945_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 877 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 944 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 877 left = VM.find 877 right ->
 VM.find 944 left = VM.find 944 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 945 next_left = VM.find 945 next_right.
Proof.
 intros H781 H877 H944 E781 E877 E944 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 945 address_expr_945 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_945)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 945 address_expr_945 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_945 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E877.
   rewrite E944.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_945 inputs path site flat_memories left value H781 H877 H944 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_946 : List.In (946,address_expr_946) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 63%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_946_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 878 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 945 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 878 left = VM.find 878 right ->
 VM.find 945 left = VM.find 945 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 946 next_left = VM.find 946 next_right.
Proof.
 intros H781 H878 H945 E781 E878 E945 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 946 address_expr_946 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_946)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 946 address_expr_946 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_946 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E878.
   rewrite E945.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_946 inputs path site flat_memories left value H781 H878 H945 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_947 : List.In (947,address_expr_947) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 64%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_947_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 879 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 946 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 879 left = VM.find 879 right ->
 VM.find 946 left = VM.find 946 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 947 next_left = VM.find 947 next_right.
Proof.
 intros H781 H879 H946 E781 E879 E946 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 947 address_expr_947 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_947)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 947 address_expr_947 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_947 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E879.
   rewrite E946.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_947 inputs path site flat_memories left value H781 H879 H946 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_948 : List.In (948,address_expr_948) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 65%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_948_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 880 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 947 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 880 left = VM.find 880 right ->
 VM.find 947 left = VM.find 947 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 948 next_left = VM.find 948 next_right.
Proof.
 intros H781 H880 H947 E781 E880 E947 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 948 address_expr_948 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_948)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 948 address_expr_948 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_948 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E880.
   rewrite E947.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_948 inputs path site flat_memories left value H781 H880 H947 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_949 : List.In (949,address_expr_949) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 66%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_949_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 881 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 948 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 881 left = VM.find 881 right ->
 VM.find 948 left = VM.find 948 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 949 next_left = VM.find 949 next_right.
Proof.
 intros H781 H881 H948 E781 E881 E948 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 949 address_expr_949 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_949)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 949 address_expr_949 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_949 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E881.
   rewrite E948.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_949 inputs path site flat_memories left value H781 H881 H948 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_950 : List.In (950,address_expr_950) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 67%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_950_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 781 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 882 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 949 left = Some (Gval (Fuint width) bits)) ->
 VM.find 781 left = VM.find 781 right ->
 VM.find 882 left = VM.find 882 right ->
 VM.find 949 left = VM.find 949 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 950 next_left = VM.find 950 next_right.
Proof.
 intros H781 H882 H949 E781 E882 E949 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 950 address_expr_950 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_950)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 950 address_expr_950 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_950 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E781.
   rewrite E882.
   rewrite E949.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_950 inputs path site flat_memories left value H781 H882 H949 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_951 : List.In (951,address_expr_951) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 68%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_951_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 950 left = Some (Gval (Fuint width) bits)) ->
 VM.find 950 left = VM.find 950 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 951 next_left = VM.find 951 next_right.
Proof.
 intros H950 E950 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 951 address_expr_951 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_951)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 951 address_expr_951 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_951 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E950.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_951 inputs path site flat_memories left value H950 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_952 : List.In (952,address_expr_952) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 69%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_952_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 918 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 951 left = Some (Gval (Fuint width) bits)) ->
 VM.find 918 left = VM.find 918 right ->
 VM.find 951 left = VM.find 951 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 952 next_left = VM.find 952 next_right.
Proof.
 intros H918 H951 E918 E951 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 952 address_expr_952 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_952)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 952 address_expr_952 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_952 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E918.
   rewrite E951.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_952 inputs path site flat_memories left value H918 H951 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7803 : List.In (7803,address_expr_7803) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 125%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7803_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7748 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7748 left = VM.find 7748 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7803 next_left = VM.find 7803 next_right.
Proof.
 intros H7748 E7748 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7803 address_expr_7803 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7803)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7803 address_expr_7803 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7803 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7748.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7803 inputs path site flat_memories left value H7748 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7804 : List.In (7804,address_expr_7804) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 126%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7804_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7748 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7748 left = VM.find 7748 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7804 next_left = VM.find 7804 next_right.
Proof.
 intros H7748 E7748 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7804 address_expr_7804 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7804)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7804 address_expr_7804 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7804 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7748.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7804 inputs path site flat_memories left value H7748 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7805 : List.In (7805,address_expr_7805) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 127%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7805_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7750 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7750 left = VM.find 7750 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7805 next_left = VM.find 7805 next_right.
Proof.
 intros H7750 E7750 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7805 address_expr_7805 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7805)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7805 address_expr_7805 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7805 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7750.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7805 inputs path site flat_memories left value H7750 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7806 : List.In (7806,address_expr_7806) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 128%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7806_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7803 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7803 left = VM.find 7803 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7806 next_left = VM.find 7806 next_right.
Proof.
 intros H7803 E7803 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7806 address_expr_7806 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7806)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7806 address_expr_7806 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7806 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7803.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7806 inputs path site flat_memories left value H7803 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7807 : List.In (7807,address_expr_7807) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 129%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7807_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7757 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7806 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7757 left = VM.find 7757 right ->
 VM.find 7806 left = VM.find 7806 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7807 next_left = VM.find 7807 next_right.
Proof.
 intros H7757 H7806 E7757 E7806 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7807 address_expr_7807 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7807)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7807 address_expr_7807 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7807 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7757.
   rewrite E7806.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7807 inputs path site flat_memories left value H7757 H7806 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7808 : List.In (7808,address_expr_7808) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 130%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7808_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7803 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7805 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7803 left = VM.find 7803 right ->
 VM.find 7805 left = VM.find 7805 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7808 next_left = VM.find 7808 next_right.
Proof.
 intros H7803 H7805 E7803 E7805 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7808 address_expr_7808 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7808)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7808 address_expr_7808 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7808 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7803.
   rewrite E7805.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7808 inputs path site flat_memories left value H7803 H7805 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7809 : List.In (7809,address_expr_7809) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 131%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7809_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7807 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7808 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7807 left = VM.find 7807 right ->
 VM.find 7808 left = VM.find 7808 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7809 next_left = VM.find 7809 next_right.
Proof.
 intros H7807 H7808 E7807 E7808 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7809 address_expr_7809 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7809)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7809 address_expr_7809 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7809 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7807.
   rewrite E7808.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7809 inputs path site flat_memories left value H7807 H7808 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7810 : List.In (7810,address_expr_7810) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 132%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7810_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7804 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7804 left = VM.find 7804 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7810 next_left = VM.find 7810 next_right.
Proof.
 intros H7804 E7804 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7810 address_expr_7810 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7810)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7810 address_expr_7810 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7810 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7804.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7810 inputs path site flat_memories left value H7804 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7811 : List.In (7811,address_expr_7811) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 133%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7811_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7757 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7810 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7757 left = VM.find 7757 right ->
 VM.find 7810 left = VM.find 7810 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7811 next_left = VM.find 7811 next_right.
Proof.
 intros H7757 H7810 E7757 E7810 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7811 address_expr_7811 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7811)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7811 address_expr_7811 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7811 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7757.
   rewrite E7810.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7811 inputs path site flat_memories left value H7757 H7810 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7812 : List.In (7812,address_expr_7812) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 134%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7812_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7804 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7805 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7804 left = VM.find 7804 right ->
 VM.find 7805 left = VM.find 7805 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7812 next_left = VM.find 7812 next_right.
Proof.
 intros H7804 H7805 E7804 E7805 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7812 address_expr_7812 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7812)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7812 address_expr_7812 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7812 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7804.
   rewrite E7805.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7812 inputs path site flat_memories left value H7804 H7805 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7813 : List.In (7813,address_expr_7813) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 135%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7813_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7811 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7812 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7811 left = VM.find 7811 right ->
 VM.find 7812 left = VM.find 7812 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7813 next_left = VM.find 7813 next_right.
Proof.
 intros H7811 H7812 E7811 E7812 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7813 address_expr_7813 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7813)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7813 address_expr_7813 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7813 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7811.
   rewrite E7812.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7813 inputs path site flat_memories left value H7811 H7812 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7814 : List.In (7814,address_expr_7814) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 136%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7814_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7756 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7756 left = VM.find 7756 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7814 next_left = VM.find 7814 next_right.
Proof.
 intros H7756 E7756 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7814 address_expr_7814 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7814)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7814 address_expr_7814 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7814 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7756.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7814 inputs path site flat_memories left value H7756 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7815 : List.In (7815,address_expr_7815) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 137%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7815_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7809 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7814 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7809 left = VM.find 7809 right ->
 VM.find 7814 left = VM.find 7814 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7815 next_left = VM.find 7815 next_right.
Proof.
 intros H7809 H7814 E7809 E7814 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7815 address_expr_7815 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7815)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7815 address_expr_7815 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7815 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7809.
   rewrite E7814.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7815 inputs path site flat_memories left value H7809 H7814 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7816 : List.In (7816,address_expr_7816) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 138%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7816_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 782 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7752 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7815 left = Some (Gval (Fuint width) bits)) ->
 VM.find 782 left = VM.find 782 right ->
 VM.find 7752 left = VM.find 7752 right ->
 VM.find 7815 left = VM.find 7815 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7816 next_left = VM.find 7816 next_right.
Proof.
 intros H782 H7752 H7815 E782 E7752 E7815 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7816 address_expr_7816 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7816)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7816 address_expr_7816 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7816 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E782.
   rewrite E7752.
   rewrite E7815.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7816 inputs path site flat_memories left value H782 H7752 H7815 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7817 : List.In (7817,address_expr_7817) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 139%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7817_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7756 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7756 left = VM.find 7756 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7817 next_left = VM.find 7817 next_right.
Proof.
 intros H7756 E7756 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7817 address_expr_7817 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7817)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7817 address_expr_7817 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7817 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7756.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7817 inputs path site flat_memories left value H7756 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7818 : List.In (7818,address_expr_7818) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 140%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7818_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7813 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7817 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7813 left = VM.find 7813 right ->
 VM.find 7817 left = VM.find 7817 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7818 next_left = VM.find 7818 next_right.
Proof.
 intros H7813 H7817 E7813 E7817 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7818 address_expr_7818 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7818)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7818 address_expr_7818 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7818 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E7813.
   rewrite E7817.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7818 inputs path site flat_memories left value H7813 H7817 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_7819 : List.In (7819,address_expr_7819) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 141%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_7819_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 783 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7752 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7818 left = Some (Gval (Fuint width) bits)) ->
 VM.find 783 left = VM.find 783 right ->
 VM.find 7752 left = VM.find 7752 right ->
 VM.find 7818 left = VM.find 7818 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7819 next_left = VM.find 7819 next_right.
Proof.
 intros H783 H7752 H7818 E783 E7752 E7818 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 7819 address_expr_7819 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_7819)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 7819 address_expr_7819 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_7819 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E783.
   rewrite E7752.
   rewrite E7818.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_7819 inputs path site flat_memories left value H783 H7752 H7818 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8263 : List.In (8263,address_expr_8263) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 149%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8263_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8263 next_left = VM.find 8263 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8263 address_expr_8263 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8263)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8263 address_expr_8263 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8263 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8263 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8264 : List.In (8264,address_expr_8264) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 150%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8264_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8263 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8263 left = VM.find 8263 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8264 next_left = VM.find 8264 next_right.
Proof.
 intros H8263 E8263 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8264 address_expr_8264 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8264)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8264 address_expr_8264 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8264 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8263.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8264 inputs path site flat_memories left value H8263 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8265 : List.In (8265,address_expr_8265) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 151%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8265_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8265 next_left = VM.find 8265 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8265 address_expr_8265 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8265)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8265 address_expr_8265 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8265 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8265 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8266 : List.In (8266,address_expr_8266) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 152%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8266_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8265 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8265 left = VM.find 8265 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8266 next_left = VM.find 8266 next_right.
Proof.
 intros H8265 E8265 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8266 address_expr_8266 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8266)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8266 address_expr_8266 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8266 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8265.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8266 inputs path site flat_memories left value H8265 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8267 : List.In (8267,address_expr_8267) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 153%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8267_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8267 next_left = VM.find 8267 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8267 address_expr_8267 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8267)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8267 address_expr_8267 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8267 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8267 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8268 : List.In (8268,address_expr_8268) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 154%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8268_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8267 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8267 left = VM.find 8267 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8268 next_left = VM.find 8268 next_right.
Proof.
 intros H8267 E8267 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8268 address_expr_8268 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8268)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8268 address_expr_8268 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8268 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8267.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8268 inputs path site flat_memories left value H8267 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8269 : List.In (8269,address_expr_8269) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 155%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8269_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8269 next_left = VM.find 8269 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8269 address_expr_8269 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8269)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8269 address_expr_8269 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8269 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8269 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8270 : List.In (8270,address_expr_8270) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 156%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8270_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8269 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8269 left = VM.find 8269 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8270 next_left = VM.find 8270 next_right.
Proof.
 intros H8269 E8269 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8270 address_expr_8270 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8270)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8270 address_expr_8270 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8270 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8269.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8270 inputs path site flat_memories left value H8269 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8271 : List.In (8271,address_expr_8271) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 157%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8271_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8271 next_left = VM.find 8271 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8271 address_expr_8271 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8271)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8271 address_expr_8271 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8271 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8271 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8272 : List.In (8272,address_expr_8272) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 158%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8272_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8271 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8271 left = VM.find 8271 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8272 next_left = VM.find 8272 next_right.
Proof.
 intros H8271 E8271 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8272 address_expr_8272 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8272)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8272 address_expr_8272 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8272 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8271.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8272 inputs path site flat_memories left value H8271 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8273 : List.In (8273,address_expr_8273) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 159%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8273_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8273 next_left = VM.find 8273 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8273 address_expr_8273 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8273)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8273 address_expr_8273 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8273 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8273 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8274 : List.In (8274,address_expr_8274) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 160%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8274_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8273 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8273 left = VM.find 8273 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8274 next_left = VM.find 8274 next_right.
Proof.
 intros H8273 E8273 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8274 address_expr_8274 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8274)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8274 address_expr_8274 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8274 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8273.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8274 inputs path site flat_memories left value H8273 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8275 : List.In (8275,address_expr_8275) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 161%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8275_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8275 next_left = VM.find 8275 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8275 address_expr_8275 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8275)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8275 address_expr_8275 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8275 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8275 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8276 : List.In (8276,address_expr_8276) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 162%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8276_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8275 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8275 left = VM.find 8275 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8276 next_left = VM.find 8276 next_right.
Proof.
 intros H8275 E8275 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8276 address_expr_8276 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8276)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8276 address_expr_8276 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8276 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8275.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8276 inputs path site flat_memories left value H8275 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8277 : List.In (8277,address_expr_8277) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 163%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8277_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8277 next_left = VM.find 8277 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8277 address_expr_8277 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8277)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8277 address_expr_8277 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8277 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8277 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8278 : List.In (8278,address_expr_8278) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 164%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8278_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8277 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8277 left = VM.find 8277 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8278 next_left = VM.find 8278 next_right.
Proof.
 intros H8277 E8277 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8278 address_expr_8278 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8278)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8278 address_expr_8278 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8278 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8277.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8278 inputs path site flat_memories left value H8277 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8279 : List.In (8279,address_expr_8279) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 165%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8279_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8279 next_left = VM.find 8279 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8279 address_expr_8279 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8279)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8279 address_expr_8279 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8279 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8279 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8280 : List.In (8280,address_expr_8280) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 166%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8280_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8279 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8279 left = VM.find 8279 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8280 next_left = VM.find 8280 next_right.
Proof.
 intros H8279 E8279 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8280 address_expr_8280 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8280)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8280 address_expr_8280 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8280 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8279.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8280 inputs path site flat_memories left value H8279 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8281 : List.In (8281,address_expr_8281) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 167%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8281_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8281 next_left = VM.find 8281 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8281 address_expr_8281 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8281)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8281 address_expr_8281 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8281 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8281 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8282 : List.In (8282,address_expr_8282) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 168%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8282_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8281 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8281 left = VM.find 8281 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8282 next_left = VM.find 8282 next_right.
Proof.
 intros H8281 E8281 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8282 address_expr_8282 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8282)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8282 address_expr_8282 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8282 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8281.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8282 inputs path site flat_memories left value H8281 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8283 : List.In (8283,address_expr_8283) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 169%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8283_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8283 next_left = VM.find 8283 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8283 address_expr_8283 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8283)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8283 address_expr_8283 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8283 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8283 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8284 : List.In (8284,address_expr_8284) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 170%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8284_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8283 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8283 left = VM.find 8283 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8284 next_left = VM.find 8284 next_right.
Proof.
 intros H8283 E8283 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8284 address_expr_8284 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8284)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8284 address_expr_8284 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8284 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8283.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8284 inputs path site flat_memories left value H8283 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8285 : List.In (8285,address_expr_8285) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 171%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8285_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8285 next_left = VM.find 8285 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8285 address_expr_8285 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8285)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8285 address_expr_8285 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8285 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8285 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8286 : List.In (8286,address_expr_8286) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 172%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8286_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8285 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8285 left = VM.find 8285 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8286 next_left = VM.find 8286 next_right.
Proof.
 intros H8285 E8285 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8286 address_expr_8286 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8286)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8286 address_expr_8286 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8286 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8285.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8286 inputs path site flat_memories left value H8285 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8287 : List.In (8287,address_expr_8287) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 173%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8287_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8287 next_left = VM.find 8287 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8287 address_expr_8287 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8287)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8287 address_expr_8287 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8287 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8287 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8288 : List.In (8288,address_expr_8288) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 174%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8288_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8287 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8287 left = VM.find 8287 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8288 next_left = VM.find 8288 next_right.
Proof.
 intros H8287 E8287 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8288 address_expr_8288 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8288)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8288 address_expr_8288 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8288 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8287.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8288 inputs path site flat_memories left value H8287 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8289 : List.In (8289,address_expr_8289) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 175%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8289_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8289 next_left = VM.find 8289 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8289 address_expr_8289 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8289)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8289 address_expr_8289 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8289 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8289 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8290 : List.In (8290,address_expr_8290) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 176%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8290_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8289 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8289 left = VM.find 8289 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8290 next_left = VM.find 8290 next_right.
Proof.
 intros H8289 E8289 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8290 address_expr_8290 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8290)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8290 address_expr_8290 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8290 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8289.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8290 inputs path site flat_memories left value H8289 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8291 : List.In (8291,address_expr_8291) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 177%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8291_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8291 next_left = VM.find 8291 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8291 address_expr_8291 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8291)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8291 address_expr_8291 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8291 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8291 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8292 : List.In (8292,address_expr_8292) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 178%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8292_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8291 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8291 left = VM.find 8291 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8292 next_left = VM.find 8292 next_right.
Proof.
 intros H8291 E8291 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8292 address_expr_8292 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8292)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8292 address_expr_8292 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8292 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8291.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8292 inputs path site flat_memories left value H8291 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8293 : List.In (8293,address_expr_8293) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 179%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8293_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8293 next_left = VM.find 8293 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8293 address_expr_8293 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8293)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8293 address_expr_8293 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8293 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8293 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8294 : List.In (8294,address_expr_8294) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 180%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8294_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8293 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8293 left = VM.find 8293 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8294 next_left = VM.find 8294 next_right.
Proof.
 intros H8293 E8293 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8294 address_expr_8294 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8294)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8294 address_expr_8294 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8294 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8293.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8294 inputs path site flat_memories left value H8293 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8295 : List.In (8295,address_expr_8295) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 181%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8295_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8295 next_left = VM.find 8295 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8295 address_expr_8295 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8295)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8295 address_expr_8295 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8295 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8295 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8296 : List.In (8296,address_expr_8296) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 182%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8296_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8295 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8295 left = VM.find 8295 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8296 next_left = VM.find 8296 next_right.
Proof.
 intros H8295 E8295 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8296 address_expr_8296 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8296)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8296 address_expr_8296 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8296 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8295.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8296 inputs path site flat_memories left value H8295 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8297 : List.In (8297,address_expr_8297) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 183%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8297_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8297 next_left = VM.find 8297 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8297 address_expr_8297 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8297)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8297 address_expr_8297 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8297 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8297 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8298 : List.In (8298,address_expr_8298) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 184%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8298_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8297 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8297 left = VM.find 8297 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8298 next_left = VM.find 8298 next_right.
Proof.
 intros H8297 E8297 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8298 address_expr_8298 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8298)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8298 address_expr_8298 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8298 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8297.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8298 inputs path site flat_memories left value H8297 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8299 : List.In (8299,address_expr_8299) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 185%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8299_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8299 next_left = VM.find 8299 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8299 address_expr_8299 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8299)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8299 address_expr_8299 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8299 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8299 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8300 : List.In (8300,address_expr_8300) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 186%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8300_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8299 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8299 left = VM.find 8299 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8300 next_left = VM.find 8300 next_right.
Proof.
 intros H8299 E8299 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8300 address_expr_8300 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8300)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8300 address_expr_8300 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8300 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8299.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8300 inputs path site flat_memories left value H8299 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8301 : List.In (8301,address_expr_8301) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 187%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8301_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8301 next_left = VM.find 8301 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8301 address_expr_8301 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8301)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8301 address_expr_8301 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8301 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8301 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8302 : List.In (8302,address_expr_8302) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 188%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8302_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8301 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8301 left = VM.find 8301 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8302 next_left = VM.find 8302 next_right.
Proof.
 intros H8301 E8301 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8302 address_expr_8302 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8302)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8302 address_expr_8302 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8302 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8301.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8302 inputs path site flat_memories left value H8301 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8303 : List.In (8303,address_expr_8303) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 189%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8303_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8303 next_left = VM.find 8303 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8303 address_expr_8303 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8303)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8303 address_expr_8303 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8303 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8303 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8304 : List.In (8304,address_expr_8304) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 190%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8304_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8303 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8303 left = VM.find 8303 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8304 next_left = VM.find 8304 next_right.
Proof.
 intros H8303 E8303 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8304 address_expr_8304 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8304)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8304 address_expr_8304 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8304 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8303.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8304 inputs path site flat_memories left value H8303 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8305 : List.In (8305,address_expr_8305) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 191%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8305_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8305 next_left = VM.find 8305 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8305 address_expr_8305 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8305)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8305 address_expr_8305 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8305 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8305 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8306 : List.In (8306,address_expr_8306) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 192%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8306_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8305 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8305 left = VM.find 8305 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8306 next_left = VM.find 8306 next_right.
Proof.
 intros H8305 E8305 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8306 address_expr_8306 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8306)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8306 address_expr_8306 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8306 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8305.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8306 inputs path site flat_memories left value H8305 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8307 : List.In (8307,address_expr_8307) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 193%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8307_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8307 next_left = VM.find 8307 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8307 address_expr_8307 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8307)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8307 address_expr_8307 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8307 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8307 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8308 : List.In (8308,address_expr_8308) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 194%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8308_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8307 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8307 left = VM.find 8307 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8308 next_left = VM.find 8308 next_right.
Proof.
 intros H8307 E8307 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8308 address_expr_8308 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8308)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8308 address_expr_8308 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8308 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8307.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8308 inputs path site flat_memories left value H8307 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8309 : List.In (8309,address_expr_8309) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 195%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8309_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8309 next_left = VM.find 8309 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8309 address_expr_8309 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8309)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8309 address_expr_8309 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8309 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8309 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8310 : List.In (8310,address_expr_8310) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 196%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8310_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8309 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8309 left = VM.find 8309 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8310 next_left = VM.find 8310 next_right.
Proof.
 intros H8309 E8309 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8310 address_expr_8310 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8310)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8310 address_expr_8310 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8310 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8309.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8310 inputs path site flat_memories left value H8309 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8311 : List.In (8311,address_expr_8311) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 197%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8311_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8311 next_left = VM.find 8311 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8311 address_expr_8311 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8311)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8311 address_expr_8311 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8311 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8311 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8312 : List.In (8312,address_expr_8312) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 198%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8312_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8311 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8311 left = VM.find 8311 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8312 next_left = VM.find 8312 next_right.
Proof.
 intros H8311 E8311 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8312 address_expr_8312 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8312)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8312 address_expr_8312 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8312 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8311.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8312 inputs path site flat_memories left value H8311 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8313 : List.In (8313,address_expr_8313) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 199%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8313_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8313 next_left = VM.find 8313 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8313 address_expr_8313 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8313)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8313 address_expr_8313 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8313 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8313 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8314 : List.In (8314,address_expr_8314) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 200%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8314_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8313 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8313 left = VM.find 8313 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8314 next_left = VM.find 8314 next_right.
Proof.
 intros H8313 E8313 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8314 address_expr_8314 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8314)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8314 address_expr_8314 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8314 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8313.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8314 inputs path site flat_memories left value H8313 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8315 : List.In (8315,address_expr_8315) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 201%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8315_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8315 next_left = VM.find 8315 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8315 address_expr_8315 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8315)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8315 address_expr_8315 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8315 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8315 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8316 : List.In (8316,address_expr_8316) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 202%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8316_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8315 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8315 left = VM.find 8315 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8316 next_left = VM.find 8316 next_right.
Proof.
 intros H8315 E8315 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8316 address_expr_8316 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8316)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8316 address_expr_8316 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8316 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8315.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8316 inputs path site flat_memories left value H8315 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8317 : List.In (8317,address_expr_8317) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 203%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8317_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8317 next_left = VM.find 8317 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8317 address_expr_8317 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8317)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8317 address_expr_8317 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8317 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8317 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8318 : List.In (8318,address_expr_8318) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 204%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8318_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8317 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8317 left = VM.find 8317 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8318 next_left = VM.find 8318 next_right.
Proof.
 intros H8317 E8317 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8318 address_expr_8318 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8318)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8318 address_expr_8318 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8318 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8317.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8318 inputs path site flat_memories left value H8317 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8319 : List.In (8319,address_expr_8319) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 205%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8319_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8319 next_left = VM.find 8319 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8319 address_expr_8319 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8319)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8319 address_expr_8319 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8319 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8319 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8320 : List.In (8320,address_expr_8320) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 206%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8320_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8319 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8319 left = VM.find 8319 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8320 next_left = VM.find 8320 next_right.
Proof.
 intros H8319 E8319 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8320 address_expr_8320 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8320)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8320 address_expr_8320 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8320 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8319.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8320 inputs path site flat_memories left value H8319 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8321 : List.In (8321,address_expr_8321) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 207%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8321_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8321 next_left = VM.find 8321 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8321 address_expr_8321 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8321)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8321 address_expr_8321 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8321 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8321 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8322 : List.In (8322,address_expr_8322) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 208%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8322_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8321 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8321 left = VM.find 8321 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8322 next_left = VM.find 8322 next_right.
Proof.
 intros H8321 E8321 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8322 address_expr_8322 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8322)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8322 address_expr_8322 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8322 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8321.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8322 inputs path site flat_memories left value H8321 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8323 : List.In (8323,address_expr_8323) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 209%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8323_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8323 next_left = VM.find 8323 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8323 address_expr_8323 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8323)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8323 address_expr_8323 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8323 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8323 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8324 : List.In (8324,address_expr_8324) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 210%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8324_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8323 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8323 left = VM.find 8323 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8324 next_left = VM.find 8324 next_right.
Proof.
 intros H8323 E8323 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8324 address_expr_8324 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8324)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8324 address_expr_8324 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8324 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8323.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8324 inputs path site flat_memories left value H8323 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8325 : List.In (8325,address_expr_8325) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 211%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8325_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8325 next_left = VM.find 8325 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8325 address_expr_8325 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8325)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8325 address_expr_8325 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8325 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8325 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8326 : List.In (8326,address_expr_8326) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 212%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8326_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8325 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8325 left = VM.find 8325 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8326 next_left = VM.find 8326 next_right.
Proof.
 intros H8325 E8325 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8326 address_expr_8326 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8326)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8326 address_expr_8326 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8326 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8325.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8326 inputs path site flat_memories left value H8325 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8327 : List.In (8327,address_expr_8327) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 213%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8327_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8327 next_left = VM.find 8327 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8327 address_expr_8327 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8327)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8327 address_expr_8327 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8327 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8327 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8328 : List.In (8328,address_expr_8328) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 214%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8328_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8327 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8327 left = VM.find 8327 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8328 next_left = VM.find 8328 next_right.
Proof.
 intros H8327 E8327 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8328 address_expr_8328 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8328)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8328 address_expr_8328 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8328 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8327.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8328 inputs path site flat_memories left value H8327 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8329 : List.In (8329,address_expr_8329) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 215%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8329_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8329 next_left = VM.find 8329 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8329 address_expr_8329 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8329)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8329 address_expr_8329 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8329 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8329 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8330 : List.In (8330,address_expr_8330) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 216%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8330_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8329 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8329 left = VM.find 8329 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8330 next_left = VM.find 8330 next_right.
Proof.
 intros H8329 E8329 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8330 address_expr_8330 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8330)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8330 address_expr_8330 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8330 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8329.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8330 inputs path site flat_memories left value H8329 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8331 : List.In (8331,address_expr_8331) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 217%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8331_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8331 next_left = VM.find 8331 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8331 address_expr_8331 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8331)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8331 address_expr_8331 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8331 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8331 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8332 : List.In (8332,address_expr_8332) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 218%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8332_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8331 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8331 left = VM.find 8331 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8332 next_left = VM.find 8332 next_right.
Proof.
 intros H8331 E8331 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8332 address_expr_8332 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8332)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8332 address_expr_8332 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8332 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8331.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8332 inputs path site flat_memories left value H8331 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8333 : List.In (8333,address_expr_8333) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 219%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8333_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8333 next_left = VM.find 8333 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8333 address_expr_8333 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8333)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8333 address_expr_8333 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8333 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8333 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8334 : List.In (8334,address_expr_8334) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 220%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8334_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8333 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8333 left = VM.find 8333 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8334 next_left = VM.find 8334 next_right.
Proof.
 intros H8333 E8333 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8334 address_expr_8334 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8334)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8334 address_expr_8334 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8334 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8333.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8334 inputs path site flat_memories left value H8333 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8335 : List.In (8335,address_expr_8335) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 221%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8335_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8335 next_left = VM.find 8335 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8335 address_expr_8335 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8335)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8335 address_expr_8335 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8335 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8335 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8336 : List.In (8336,address_expr_8336) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 222%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8336_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8335 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8335 left = VM.find 8335 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8336 next_left = VM.find 8336 next_right.
Proof.
 intros H8335 E8335 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8336 address_expr_8336 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8336)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8336 address_expr_8336 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8336 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8335.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8336 inputs path site flat_memories left value H8335 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8337 : List.In (8337,address_expr_8337) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 223%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8337_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8337 next_left = VM.find 8337 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8337 address_expr_8337 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8337)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8337 address_expr_8337 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8337 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8337 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8338 : List.In (8338,address_expr_8338) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 224%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8338_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8337 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8337 left = VM.find 8337 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8338 next_left = VM.find 8338 next_right.
Proof.
 intros H8337 E8337 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8338 address_expr_8338 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8338)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8338 address_expr_8338 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8338 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8337.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8338 inputs path site flat_memories left value H8337 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8339 : List.In (8339,address_expr_8339) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 225%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8339_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8339 next_left = VM.find 8339 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8339 address_expr_8339 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8339)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8339 address_expr_8339 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8339 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8339 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8340 : List.In (8340,address_expr_8340) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 226%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8340_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8339 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8339 left = VM.find 8339 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8340 next_left = VM.find 8340 next_right.
Proof.
 intros H8339 E8339 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8340 address_expr_8340 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8340)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8340 address_expr_8340 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8340 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8339.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8340 inputs path site flat_memories left value H8339 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8341 : List.In (8341,address_expr_8341) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 227%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8341_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8341 next_left = VM.find 8341 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8341 address_expr_8341 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8341)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8341 address_expr_8341 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8341 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8341 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8342 : List.In (8342,address_expr_8342) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 228%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8342_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8341 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8341 left = VM.find 8341 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8342 next_left = VM.find 8342 next_right.
Proof.
 intros H8341 E8341 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8342 address_expr_8342 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8342)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8342 address_expr_8342 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8342 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8341.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8342 inputs path site flat_memories left value H8341 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8343 : List.In (8343,address_expr_8343) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 229%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8343_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8343 next_left = VM.find 8343 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8343 address_expr_8343 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8343)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8343 address_expr_8343 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8343 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8343 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8344 : List.In (8344,address_expr_8344) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 230%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8344_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8343 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8343 left = VM.find 8343 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8344 next_left = VM.find 8344 next_right.
Proof.
 intros H8343 E8343 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8344 address_expr_8344 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8344)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8344 address_expr_8344 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8344 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8343.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8344 inputs path site flat_memories left value H8343 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8345 : List.In (8345,address_expr_8345) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 231%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8345_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8345 next_left = VM.find 8345 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8345 address_expr_8345 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8345)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8345 address_expr_8345 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8345 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8345 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8346 : List.In (8346,address_expr_8346) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 232%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8346_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8345 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8345 left = VM.find 8345 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8346 next_left = VM.find 8346 next_right.
Proof.
 intros H8345 E8345 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8346 address_expr_8346 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8346)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8346 address_expr_8346 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8346 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8345.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8346 inputs path site flat_memories left value H8345 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8347 : List.In (8347,address_expr_8347) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 233%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8347_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8347 next_left = VM.find 8347 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8347 address_expr_8347 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8347)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8347 address_expr_8347 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8347 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8347 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8348 : List.In (8348,address_expr_8348) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 234%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8348_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8347 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8347 left = VM.find 8347 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8348 next_left = VM.find 8348 next_right.
Proof.
 intros H8347 E8347 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8348 address_expr_8348 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8348)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8348 address_expr_8348 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8348 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8347.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8348 inputs path site flat_memories left value H8347 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8349 : List.In (8349,address_expr_8349) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 235%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8349_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8349 next_left = VM.find 8349 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8349 address_expr_8349 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8349)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8349 address_expr_8349 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8349 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8349 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8350 : List.In (8350,address_expr_8350) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 236%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8350_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8349 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8349 left = VM.find 8349 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8350 next_left = VM.find 8350 next_right.
Proof.
 intros H8349 E8349 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8350 address_expr_8350 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8350)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8350 address_expr_8350 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8350 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8349.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8350 inputs path site flat_memories left value H8349 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8351 : List.In (8351,address_expr_8351) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 237%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8351_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8351 next_left = VM.find 8351 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8351 address_expr_8351 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8351)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8351 address_expr_8351 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8351 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8351 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8352 : List.In (8352,address_expr_8352) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 238%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8352_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8351 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8351 left = VM.find 8351 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8352 next_left = VM.find 8352 next_right.
Proof.
 intros H8351 E8351 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8352 address_expr_8352 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8352)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8352 address_expr_8352 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8352 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8351.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8352 inputs path site flat_memories left value H8351 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8353 : List.In (8353,address_expr_8353) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 239%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8353_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8353 next_left = VM.find 8353 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8353 address_expr_8353 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8353)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8353 address_expr_8353 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8353 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8353 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8354 : List.In (8354,address_expr_8354) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 240%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8354_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8353 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8353 left = VM.find 8353 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8354 next_left = VM.find 8354 next_right.
Proof.
 intros H8353 E8353 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8354 address_expr_8354 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8354)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8354 address_expr_8354 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8354 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8353.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8354 inputs path site flat_memories left value H8353 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8355 : List.In (8355,address_expr_8355) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 241%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8355_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8355 next_left = VM.find 8355 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8355 address_expr_8355 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8355)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8355 address_expr_8355 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8355 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8355 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8356 : List.In (8356,address_expr_8356) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 242%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8356_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8355 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8355 left = VM.find 8355 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8356 next_left = VM.find 8356 next_right.
Proof.
 intros H8355 E8355 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8356 address_expr_8356 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8356)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8356 address_expr_8356 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8356 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8355.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8356 inputs path site flat_memories left value H8355 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8357 : List.In (8357,address_expr_8357) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 243%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8357_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8357 next_left = VM.find 8357 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8357 address_expr_8357 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8357)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8357 address_expr_8357 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8357 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8357 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8358 : List.In (8358,address_expr_8358) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 244%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8358_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8357 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8357 left = VM.find 8357 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8358 next_left = VM.find 8358 next_right.
Proof.
 intros H8357 E8357 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8358 address_expr_8358 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8358)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8358 address_expr_8358 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8358 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8357.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8358 inputs path site flat_memories left value H8357 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8359 : List.In (8359,address_expr_8359) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 245%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8359_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8249 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8249 left = VM.find 8249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8359 next_left = VM.find 8359 next_right.
Proof.
 intros H8249 E8249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8359 address_expr_8359 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8359)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8359 address_expr_8359 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8359 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8249.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8359 inputs path site flat_memories left value H8249 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_data_member_8360 : List.In (8360,address_expr_8360) data_address_expected_nodes.
Proof. apply (List.nth_error_In data_address_expected_nodes 246%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8360_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 8359 left = Some (Gval (Fuint width) bits)) ->
 VM.find 8359 left = VM.find 8359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8360 next_left = VM.find 8360 next_right.
Proof.
 intros H8359 E8359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8360 address_expr_8360 data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_8360)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail 8360 address_expr_8360 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [address_expr_8360 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8359.
   reflexivity.
 - intros site value Eval.
   destruct (address_uint_result_8360 inputs path site flat_memories left value H8359 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Print Assumptions early_control_node_884_congruent.
Print Assumptions early_control_node_919_congruent.

Require Import ReferenceLoadImmediate DUTRedirectSemantics FormalLocalHistory ObservedJointRegisterConcrete CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceLoadSemantics.
From Coq Require Import NArith ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_compare_expr_1162 := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1151))).
Definition rf_compare_expr_1163 := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Definition rf_compare_expr_1164 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1162)) (@Eref VarOrder.T (@Eid VarOrder.T 1163))).
Definition rf_compare_expr_1165 := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1161))).
Definition rf_compare_expr_1166 := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 1153))).
Definition rf_compare_expr_1167 := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Definition rf_compare_expr_1168 := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1151))).
Definition rf_compare_expr_1169 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1166)) (@Eref VarOrder.T (@Eid VarOrder.T 1167)) (@Eref VarOrder.T (@Eid VarOrder.T 1168))).
Definition rf_compare_expr_1170 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1164)) (@Eref VarOrder.T (@Eid VarOrder.T 1165)) (@Eref VarOrder.T (@Eid VarOrder.T 1169))).
Definition rf_compare_nodes := [::(1162,rf_compare_expr_1162);(1163,rf_compare_expr_1163);(1164,rf_compare_expr_1164);(1165,rf_compare_expr_1165);(1166,rf_compare_expr_1166);(1167,rf_compare_expr_1167);(1168,rf_compare_expr_1168);(1169,rf_compare_expr_1169);(1170,rf_compare_expr_1170)].
Definition rf_compare_offsets := [::1237%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_compare_positions :select_node_offsets rf_compare_offsets flat_statements=Some rf_compare_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_compare_safety :selected_node_safety flat_memories flat_statements rf_compare_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.

(* Handwritten semantic composition. *)
Definition rf_compare_bit unsigned left right :=if unsigned then N.ltb(to_N left)(to_N right)else Z.ltb(to_Z left)(to_Z right).
Lemma rf_compare_signs unsigned left right :size left=32%nat ->size right=32%nat ->
 (if msb left==msb right then msb(dut_branch_difference left right)else if unsigned then msb right else msb left)=rf_compare_bit unsigned left right.
Proof. intros Left Right. rewrite(dut_branch_difference_subB left right Left Right). unfold rf_compare_bit.
 destruct unsigned;[apply dut_unsigned_compare|apply dut_signed_compare];lia.
Qed.
Theorem rf_compare_sign_history unsigned invalid s0 s1 s2 s3 left right :
 size left=32%nat ->size right=32%nat ->
 VM.find 1151 s0=Some(Gval(Fuint 32)left) ->VM.find 1152 s0=Some(Gval(Fuint 32)right) ->
 VM.find 1153 s0=Some(Gval(Fuint 4)[::true;unsigned;true;false]) ->
 VM.find 1161 s1=Some(Gval(Fuint 32)(dut_branch_difference left right)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 VM.find 1170 s3=Some(Gval(Fuint 1)[::rf_compare_bit unsigned left right]).
Proof.
 intros LeftSize RightSize Left Right Mode Sum S1 S2 S3.
assert(V1162:VM.find 1162 s1=Some(Gval(Fuint 1)[::msb left])).
{eapply(reference_redirect_ground_step rf_compare_offsets rf_compare_nodes 1162 rf_compare_expr_1162);[exact rf_compare_positions|exact rf_compare_safety|apply(List.nth_error_In rf_compare_nodes 0%nat);reflexivity| |exact S1].
intro site. cbn[rf_compare_expr_1162 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left. cbn[eval_unop]. rewrite(dut_sign_extract left LeftSize);reflexivity. }
assert(V1163:VM.find 1163 s1=Some(Gval(Fuint 1)[::msb right])).
{eapply(reference_redirect_ground_step rf_compare_offsets rf_compare_nodes 1163 rf_compare_expr_1163);[exact rf_compare_positions|exact rf_compare_safety|apply(List.nth_error_In rf_compare_nodes 1%nat);reflexivity| |exact S1].
intro site. cbn[rf_compare_expr_1163 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Right. cbn[eval_unop]. rewrite(dut_sign_extract right RightSize);reflexivity. }
assert(V1167:VM.find 1167 s1=Some(Gval(Fuint 1)[::msb right])).
{eapply(reference_redirect_ground_step rf_compare_offsets rf_compare_nodes 1167 rf_compare_expr_1167);[exact rf_compare_positions|exact rf_compare_safety|apply(List.nth_error_In rf_compare_nodes 5%nat);reflexivity| |exact S1].
intro site. cbn[rf_compare_expr_1167 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Right. cbn[eval_unop]. rewrite(dut_sign_extract right RightSize);reflexivity. }
assert(V1168:VM.find 1168 s1=Some(Gval(Fuint 1)[::msb left])).
{eapply(reference_redirect_ground_step rf_compare_offsets rf_compare_nodes 1168 rf_compare_expr_1168);[exact rf_compare_positions|exact rf_compare_safety|apply(List.nth_error_In rf_compare_nodes 6%nat);reflexivity| |exact S1].
intro site. cbn[rf_compare_expr_1168 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left. cbn[eval_unop]. rewrite(dut_sign_extract left LeftSize);reflexivity. }
assert(V1166:VM.find 1166 s1=Some(Gval(Fuint 1)[::unsigned])).
{eapply(reference_redirect_ground_step rf_compare_offsets rf_compare_nodes 1166 rf_compare_expr_1166);[exact rf_compare_positions|exact rf_compare_safety|apply(List.nth_error_In rf_compare_nodes 4%nat);reflexivity| |exact S1].
intro site. cbn[rf_compare_expr_1166 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct unsigned;reflexivity. }
assert(V1164:VM.find 1164 s2=Some(Gval(Fuint 1)[::msb left==msb right])).
{eapply(reference_redirect_ground_step rf_compare_offsets rf_compare_nodes 1164 rf_compare_expr_1164);[exact rf_compare_positions|exact rf_compare_safety|apply(List.nth_error_In rf_compare_nodes 2%nat);reflexivity| |exact S2].
intro site. cbn[rf_compare_expr_1164 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1162 V1163. apply dut_boolean_binop. }
assert(V1165:VM.find 1165 s2=Some(Gval(Fuint 1)[::msb(dut_branch_difference left right)])).
{eapply(reference_redirect_ground_step rf_compare_offsets rf_compare_nodes 1165 rf_compare_expr_1165);[exact rf_compare_positions|exact rf_compare_safety|apply(List.nth_error_In rf_compare_nodes 3%nat);reflexivity| |exact S2].
intro site. cbn[rf_compare_expr_1165 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Sum. cbn[eval_unop]. rewrite(dut_sign_extract (dut_branch_difference left right) ltac:(unfold dut_branch_difference;rewrite size_take size_from_Z;reflexivity));reflexivity. }
assert(V1169:VM.find 1169 s2=Some(Gval(Fuint 1)[::if unsigned then msb right else msb left])).
{eapply(reference_redirect_ground_step rf_compare_offsets rf_compare_nodes 1169 rf_compare_expr_1169);[exact rf_compare_positions|exact rf_compare_safety|apply(List.nth_error_In rf_compare_nodes 7%nat);reflexivity| |exact S2].
intro site. cbn[rf_compare_expr_1169 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1166. destruct unsigned;cbn;rewrite ?V1167 ?V1168;cbn;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V1167 ?V1168;destruct(msb left),(msb right);reflexivity. }
eapply(reference_redirect_ground_step rf_compare_offsets rf_compare_nodes 1170 rf_compare_expr_1170);[exact rf_compare_positions|exact rf_compare_safety|apply(List.nth_error_In rf_compare_nodes 8%nat);reflexivity| |exact S3].
intro site. cbn[rf_compare_expr_1170 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1164. rewrite<-(rf_compare_signs unsigned left right LeftSize RightSize). destruct(msb left==msb right);cbn;rewrite ?V1165 ?V1169;cbn;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V1165 ?V1169;destruct unsigned, (msb left),(msb right),(msb(dut_branch_difference left right));reflexivity.
Qed.

Require Import RFShiftNodes RFShiftNodeStep RFShiftReverseHistory RFWritebackSelection CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_shift_center_word arithmetic word right :=
 take 32(sext_to 33(drop(minn(to_nat(take 5 right))32)
 (word++andB [::arithmetic](drop 31(take 32 word))))).
Theorem rf_shift_center_history invalid history limit arithmetic b1 b2 direction word right :
 (forall t,(t<=limit)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)[::arithmetic;b1;b2;direction])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1152(history t)=Some(Gval(Fuint 32)right)) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1222(history t)=Some(Gval(Fuint 32)word)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1229(history t)=Some(Gval(Fuint 32)(rf_shift_center_word arithmetic word right)).
Proof.
 intros Modes Rights Words Steps.
 assert(V1171:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1171(history t)=Some(Gval(Fuint 5)(take 5 right))).
 { intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1171 rf_shift_expr_1171);
 [apply(List.nth_error_In rf_shift_nodes 0%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1171 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Rights t ltac:(lia)).
 cbn[eval_unop]. rewrite ?drop0. unfold eval_binop,refine_boolean_result. cbn[eval_binop_basic]. destruct arithmetic;try destruct(absorbing_bit _ _ _);reflexivity. }
 assert(V1223:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1223(history t)=Some(Gval(Fuint 1)([::arithmetic]))).
 { intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1223 rf_shift_expr_1223);
 [apply(List.nth_error_In rf_shift_nodes 52%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1223 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Modes t ltac:(lia)).
 cbn[eval_unop]. rewrite ?drop0. unfold eval_binop,refine_boolean_result. cbn[eval_binop_basic]. destruct arithmetic;try destruct(absorbing_bit _ _ _);reflexivity. }
 assert(V1224:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1224(history t)=Some(Gval(Fuint 1)(drop 31(take 32 word)))).
 { intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1224 rf_shift_expr_1224);
 [apply(List.nth_error_In rf_shift_nodes 53%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1224 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Words t ltac:(lia)).
 cbn[eval_unop]. rewrite ?drop0. unfold eval_binop,refine_boolean_result. cbn[eval_binop_basic]. destruct arithmetic;try destruct(absorbing_bit _ _ _);reflexivity. }
 assert(V1225:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1225(history t)=Some(Gval(Fuint 1)(andB [::arithmetic](drop 31(take 32 word))))).
 { intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1225 rf_shift_expr_1225);
 [apply(List.nth_error_In rf_shift_nodes 54%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1225 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V1223 t ltac:(lia)ltac:(lia)).
 rewrite(V1224 t ltac:(lia)ltac:(lia)).
 cbn[eval_unop]. rewrite ?drop0. unfold eval_binop,refine_boolean_result. cbn[eval_binop_basic]. destruct arithmetic;try destruct(absorbing_bit _ _ _);reflexivity. }
 assert(V1226:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1226(history t)=Some(Gval(Fuint 33)(word++andB [::arithmetic](drop 31(take 32 word))))).
 { intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1226 rf_shift_expr_1226);
 [apply(List.nth_error_In rf_shift_nodes 55%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1226 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V1225 t ltac:(lia)ltac:(lia)).
 rewrite(Words t ltac:(lia)).
 cbn[eval_unop]. rewrite ?drop0. unfold eval_binop,refine_boolean_result. cbn[eval_binop_basic]. destruct arithmetic;try destruct(absorbing_bit _ _ _);reflexivity. }
 assert(V1227:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1227(history t)=Some(Gval(Fsint 33)(word++andB [::arithmetic](drop 31(take 32 word))))).
 { intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1227 rf_shift_expr_1227);
 [apply(List.nth_error_In rf_shift_nodes 56%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1227 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V1226 t ltac:(lia)ltac:(lia)).
 cbn[eval_unop]. rewrite ?drop0. unfold eval_binop,refine_boolean_result. cbn[eval_binop_basic]. destruct arithmetic;try destruct(absorbing_bit _ _ _);reflexivity. }
 assert(V1228:forall t,(5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1228(history t)=Some(Gval(Fsint 33)(sext_to 33(drop(minn(to_nat(take 5 right))32)(word++andB [::arithmetic](drop 31(take 32 word))))))).
 { intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1228 rf_shift_expr_1228);
 [apply(List.nth_error_In rf_shift_nodes 57%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1228 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V1227 t ltac:(lia)ltac:(lia)).
 rewrite(V1171 t ltac:(lia)ltac:(lia)).
 cbn[eval_unop]. rewrite ?drop0. unfold eval_binop,refine_boolean_result. cbn[eval_binop_basic]. destruct arithmetic;try destruct(absorbing_bit _ _ _);reflexivity. }
 assert(V1229:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1229(history t)=Some(Gval(Fuint 32)(rf_shift_center_word arithmetic word right))).
 { intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1229 rf_shift_expr_1229);
 [apply(List.nth_error_In rf_shift_nodes 58%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1229 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V1228 t ltac:(lia)ltac:(lia)).
 cbn[eval_unop]. rewrite ?drop0. unfold eval_binop,refine_boolean_result. cbn[eval_binop_basic]. destruct arithmetic;try destruct(absorbing_bit _ _ _);reflexivity. }
intros t Lower Upper. exact(V1229 t Lower Upper).
Qed.

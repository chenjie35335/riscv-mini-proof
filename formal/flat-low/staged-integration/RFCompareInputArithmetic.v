Require Import RFSubtractArithmetic DUTRedirectSemantics ALUAddressSemantics ReferenceLoadImmediate ReferenceRedirectSpine CoreSocModel ComparisonNodes.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_compare_select_sub unsigned invalid s0 s1 s2 right :
 VM.find 1153 s0=Some(Gval(Fuint 4)[::true;unsigned;true;false]) ->
 VM.find 1152 s1=Some(Gval(Fuint 32)right) ->VM.find 1158 s1=Some(Gval(Fuint 32)(rf_negated_word right)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find 1159 s2=Some(Gval(Fuint 32)(rf_negated_word right)).
Proof.
 intros Mode Right Neg S1 S2.
 assert(Guard:VM.find 1156 s1=Some(Gval(Fuint 1)[::true])).
 { eapply(reference_redirect_ground_step alu_address_offsets alu_address_nodes 1156 alu_address_expr_1156);
 [exact alu_address_positions|exact alu_address_safety|apply(List.nth_error_In alu_address_nodes 0%nat);reflexivity| |exact S1].
 intro site. cbn[alu_address_expr_1156 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode;destruct unsigned;reflexivity. }
 eapply(reference_redirect_ground_step alu_address_offsets alu_address_nodes 1159 alu_address_expr_1159);
 [exact alu_address_positions|exact alu_address_safety|apply(List.nth_error_In alu_address_nodes 3%nat);reflexivity| |exact S2].
 intro site. unfold alu_address_expr_1159.
 exact(immediate_selected_mux _ site s1 1156 1158 1152 32(rf_negated_word right)(Gval(Fuint 32)right)true(rf_negated_word_size right)Guard Neg Right(Logic.eq_refl _)).
Qed.
Theorem rf_compare_subtract_from_inputs unsigned invalid history left right :
 size left=32%nat ->size right=32%nat ->
 VM.find 1152(history 0%nat)=Some(Gval(Fuint 32)right) ->
 VM.find 1153(history 1%nat)=Some(Gval(Fuint 4)[::true;unsigned;true;false]) ->
 VM.find 1152(history 2%nat)=Some(Gval(Fuint 32)right) ->
 VM.find 1151(history 3%nat)=Some(Gval(Fuint 32)left) ->
 (forall i,(i<5)%coq_nat ->formal_value_iter invalid flat_memories(history i)false(history i)flat_statements=Some(history(S i))) ->
 VM.find 1161(history 5%nat)=Some(Gval(Fuint 32)(dut_branch_difference left right)).
Proof.
 intros LeftSize RightSize Right0 Mode Right2 Left Steps.
 pose proof(rf_alu_negated_value invalid(history 0%nat)(history 1%nat)(history 2%nat)right Right0(Steps 0%nat ltac:(lia))(Steps 1%nat ltac:(lia)))as Neg.
 pose proof(rf_compare_select_sub unsigned invalid(history 1%nat)(history 2%nat)(history 3%nat)right Mode Right2 Neg(Steps 1%nat ltac:(lia))(Steps 2%nat ltac:(lia)))as Selected.
 pose proof(alu_address_add_history invalid(history 3%nat)(history 4%nat)(history 5%nat)left(rf_negated_word right)Left Selected(Steps 3%nat ltac:(lia))(Steps 4%nat ltac:(lia)))as Sum.
 rewrite(rf_subtract_sum left right LeftSize RightSize)in Sum;exact Sum.
Qed.

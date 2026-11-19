Require Import RFShiftNodes RFShiftNodeStep RFShiftReverseHistory ReferenceLoadImmediate CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_shift_selected_history invalid history limit arithmetic b1 b2 direction word :
 size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)[::arithmetic;b1;b2;direction])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1151(history t)=Some(Gval(Fuint 32)word)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(22<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 1222(history t)=Some(Gval(Fuint 32)(if direction then word else rev word)).
Proof.
 intros Size Modes Words Steps.
 pose proof(rf_shift_reverse_history_1221 invalid history limit word Size Words Steps)as Reversed.
 assert(Direction:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1172(history t)=Some(Gval(Fuint 1)[::direction])).
 { intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1172 rf_shift_expr_1172);
 [apply(List.nth_error_In rf_shift_nodes 1%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1172 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Modes t ltac:(lia));reflexivity. }
 intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step 1222 rf_shift_expr_1222);
 [apply(List.nth_error_In rf_shift_nodes 51%nat);reflexivity| |apply Steps;lia].
 intro site. unfold rf_shift_expr_1222.
 destruct direction.
 - exact(immediate_selected_mux _ site(history t)1172 1151 1221 32 word(Gval(Fuint 32)(rev word))true Size (Direction t ltac:(lia)ltac:(lia))(Words t ltac:(lia))(Reversed t ltac:(lia)ltac:(lia))(Logic.eq_refl _)).
 - exact(immediate_selected_mux _ site(history t)1172 1151 1221 32 (rev word)(Gval(Fuint 32)word)false ltac:(rewrite size_rev;exact Size)(Direction t ltac:(lia)ltac:(lia))(Reversed t ltac:(lia)ltac:(lia))(Words t ltac:(lia))(Logic.eq_refl _)).
Qed.

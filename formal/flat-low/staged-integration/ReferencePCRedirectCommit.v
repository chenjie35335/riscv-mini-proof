Require Import ReferencePCSequentialSteps CoreSocModel ComparisonNodes ReferencePCSequentialNodes ReferencePCSequentialValues ReferencePCUpdateNodes ExceptionPCPayloadNodes ExceptionPCPayloadConnections ReferencePCNextConnections ReferencePCNormalCommit ExceptionPCSourceRegisters StagedRegisterHold FormalRFResetPropagation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Lemma reference_pc_redirect_mux_6810 invalid old current result base input :
 reference_pc_seq_extension base input ->
 VM.find 6807 old = Some (Gval (Fuint 1) [::false]) -> VM.find 6508 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 6810 result = Some value /\ reference_pc_seq_extension base value.
Proof.
 intros Ext Cond Input Step.
 destruct (reference_pc_sequential_6810_evaluation invalid old current result Step) as [value Eval].
 assert (Extended : reference_pc_seq_extension base value).
 { eapply (reference_pc_seq_mux flat_memories old 6807 _ _ false base input value Ext Cond); [|exact Eval]. exact Input. }
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 exact (reference_pc_sequential_6810_value invalid old current result width _ Eval Step).
Qed.
Theorem reference_pc_redirect_payload_after_five invalid s0 s1 s2 s3 s4 s5 target :
 size target = 32%nat ->
 VM.find 6508 s0 = Some (Gval (Fuint 32) target) ->
 VM.find 6807 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6780 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1707 s2 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 1819 s5 = Some (Gval (Fuint 32) target).
Proof.
 intros Size Target Redirect Exception Enabled S1 S2 S3 S4 S5.
 assert (Base : reference_pc_seq_extension target (Gval (Fuint 32) target)).
 { pose proof (reference_pc_seq_base target) as Base. rewrite Size in Base. exact Base. }
 destruct (reference_pc_redirect_mux_6810 invalid s0 s0 s1 _ _ Base Redirect Target S1) as [v1 [V1 E1]].
 destruct (reference_pc_seq_mux_7094 invalid s1 s1 s2 _ _ E1 Exception V1 S2) as [v2 [V2 E2]].
 destruct (reference_pc_seq_mux_7109 invalid s2 s2 s3 _ _ E2 Enabled V2 S3) as [v3 [V3 [width [Bound Shape]]]]. subst v3.
 assert (V4 : VM.find 7149 s4 = Some (Gval (Fuint 32) target)).
 { apply (reference_pc_update_7149_value invalid s3 s3 s4 32 _); [|exact S4].
   cbn [reference_pc_update_7149_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite V3.
   exact (reference_pc_seq_low_extract _ width Size Bound). }
 exact (exception_pc_1819_value invalid s4 s4 s5 _ _ V4 (sized_uint_adapt_identity 32 _ Size) S5).
Qed.
Theorem reference_pc_redirect_commit_after_five invalid s0 s1 s2 s3 s4 s5 result target old_value :
 size target = 32%nat ->
 VM.find 6508 s0 = Some (Gval (Fuint 32) target) ->
 VM.find 6807 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6780 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1707 s2 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7331 s5 = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 s5 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 true s5 flat_statements = Some result ->
 VM.find 7331 result = Some (Gval (Fuint 32) target).
Proof.
 intros Size Target Redirect Exception Enabled Old Typed Reset S1 S2 S3 S4 S5 Commit.
 pose proof (reference_pc_redirect_payload_after_five invalid s0 s1 s2 s3 s4 s5 target
 Size Target Redirect Exception Enabled S1 S2 S3 S4 S5) as Payload.
 exact (reference_pc_formal_normal_commit invalid s5 s5 result old_value target Old Typed Reset Payload Size Commit).
Qed.
Lemma reference_pc_redirect_nonzero_test invalid old current result input :
 reference_pc_seq_extension [::true] input -> VM.find 6806 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6807 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros [width [Width Value]] Input Step. subst input.
 apply (reference_pc_sequential_6807_value invalid old current result 1 [::false]); [|exact Step].
 cbn [reference_pc_sequential_6807_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Input.
 change (eval_binop (Bcomp Beq) (Gval (Fuint width) (zext_to width [::true])) (Gval (Fuint 1) [::false]) = Some (Gval (Fuint 1) [::false])).
 assert (One : to_N (zext_to width [::true]) = 1).
 { rewrite to_N_nat. unfold zext_to. rewrite to_nat_zext. reflexivity. }
 unfold eval_binop, absorbing_bit, refine_boolean_result. cbn [eval_binop_basic]. rewrite One.
 repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.
Theorem reference_pc_redirect_flag_after_four invalid s0 s1 s2 s3 s4 :
 VM.find 6507 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 6780 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1707 s1 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 6807 s4 = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Redirect Exception Enabled S1 S2 S3 S4.
 destruct (reference_pc_seq_mux_6804 invalid s0 s0 s1 [::true] _ (reference_pc_seq_base [::true]) Exception Redirect S1) as [v1 [V1 E1]].
 destruct (reference_pc_seq_mux_6805 invalid s1 s1 s2 [::true] _ E1 Enabled V1 S2) as [v2 [V2 E2]].
 pose proof (reference_pc_seq_alias_6806 invalid s2 s2 s3 [::true] v2 E2 V2 S3) as V3.
 exact (reference_pc_redirect_nonzero_test invalid s3 s3 s4 v2 E2 V3 S4).
Qed.

Require Import RFUpperSemantics ReferenceLoadSemantics ReferenceControlStabilityHistory CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ExceptionPCPayloadNodes ExceptionPCPayloadConnections ExceptionPCSourceRegisters FormalRFResetPropagation FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_upper_reference_expr_3501:=(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition rf_upper_reference_expr_3502:=(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3501))).
Definition rf_upper_reference_expr_3503:=(@Eref VarOrder.T (@Eid VarOrder.T 3502)).
Definition rf_upper_reference_expr_3504:=(@Eref VarOrder.T (@Eid VarOrder.T 2552)).
Definition rf_upper_reference_nodes:=[::(3501,rf_upper_reference_expr_3501);(3502,rf_upper_reference_expr_3502);(3503,rf_upper_reference_expr_3503);(3504,rf_upper_reference_expr_3504)].
Definition rf_upper_reference_offsets:=[::3580%nat;0%nat;0%nat;0%nat].
Lemma rf_upper_reference_positions:select_node_offsets rf_upper_reference_offsets flat_statements=Some rf_upper_reference_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_upper_reference_safety:selected_node_safety flat_memories flat_statements rf_upper_reference_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_upper_reference_output auipc :=if auipc then 3503 else 3504.
Theorem rf_upper_reference_data_three auipc invalid s0 s1 s2 s3 pc immediate :
 VM.find 2812 s0=Some(Gval(Fuint 32)pc) ->
 VM.find 2552 s0=Some(Gval(Fuint 32)immediate) ->
 VM.find 2552 s2=Some(Gval(Fuint 32)immediate) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 VM.find(rf_upper_reference_output auipc)s3=Some(Gval(Fuint 32)(if auipc then reference_load_address pc immediate else immediate)).
Proof.
 intros PC Imm0 Imm2 S1 S2 S3. destruct auipc.
 - assert(V1:VM.find 3501 s1=Some(Gval(Fuint 33)(from_N 33(to_N pc+to_N immediate)))).
   { eapply(reference_redirect_ground_step rf_upper_reference_offsets rf_upper_reference_nodes 3501 rf_upper_reference_expr_3501);
     [exact rf_upper_reference_positions|exact rf_upper_reference_safety|apply(List.nth_error_In rf_upper_reference_nodes 0%nat);reflexivity| |exact S1].
     intro site. cbn[rf_upper_reference_expr_3501 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite PC Imm0;reflexivity. }
   assert(V2:VM.find 3502 s2=Some(Gval(Fuint 32)(reference_load_address pc immediate))).
   { eapply(reference_redirect_ground_step rf_upper_reference_offsets rf_upper_reference_nodes 3502 rf_upper_reference_expr_3502);
     [exact rf_upper_reference_positions|exact rf_upper_reference_safety|apply(List.nth_error_In rf_upper_reference_nodes 1%nat);reflexivity| |exact S2].
     intro site. cbn[rf_upper_reference_expr_3502 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }
   eapply(reference_redirect_ground_step rf_upper_reference_offsets rf_upper_reference_nodes 3503 rf_upper_reference_expr_3503);
   [exact rf_upper_reference_positions|exact rf_upper_reference_safety|apply(List.nth_error_In rf_upper_reference_nodes 2%nat);reflexivity| |exact S3].
   intro site;exact V2.
 - eapply(reference_redirect_ground_step rf_upper_reference_offsets rf_upper_reference_nodes 3504 rf_upper_reference_expr_3504);
   [exact rf_upper_reference_positions|exact rf_upper_reference_safety|apply(List.nth_error_In rf_upper_reference_nodes 3%nat);reflexivity| |exact S3].
   intro site;exact Imm2.
Qed.
Theorem rf_upper_reference_data_observed memory inputs k observed auipc pc immediate :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 size pc=32%nat ->VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find(rf_upper_reference_output auipc)(top_environment observed)=Some(Gval(Fuint 32)(if auipc then reference_load_address pc immediate else immediate)).
Proof.
 intros Observe Legal Size PC Immediate.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(PC0:VM.find 7331(history 9254%nat)=Some(Gval(Fuint 32)pc)).
 { rewrite(proj2(exception_pc_sources_history_stable _ history 9259 9254 Steps ltac:(vm_compute;lia)))Last. exact PC. }
 pose proof(exception_pc_1749_value _ (history 9254%nat)(history 9254%nat)(history 9255%nat) _ _ PC0 (sized_uint_adapt_identity 32 pc Size)(Steps 9254%nat ltac:(vm_compute;lia)))as P1.
 pose proof(exception_pc_2812_value _ (history 9255%nat)(history 9255%nat)(history 9256%nat) pc P1 (Steps 9255%nat ltac:(vm_compute;lia)))as P2.
 assert(Imm:forall t,(500<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 2552(history t)=Some(Gval(Fuint 32)immediate)).
 { intros t Lower Upper. rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last. exact Immediate. }
 rewrite <-Last. exact(rf_upper_reference_data_three auipc _ (history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)pc immediate P2
 (Imm 9256%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))(Imm 9258%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))
 (Steps 9256%nat ltac:(vm_compute;lia))(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.

Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferencePCSequentialValues ExceptionPCPayloadNodes ExceptionPCPayloadConnections ExceptionPCSourceRegisters FormalRFResetPropagation FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_link_expr_3444 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Definition rf_link_expr_3445 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3444))).
Definition rf_link_expr_3446 := (@Eref VarOrder.T (@Eid VarOrder.T 3445)).
Definition rf_link_expr_3447 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Definition rf_link_expr_3448 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3447))).
Definition rf_link_expr_3449 := (@Eref VarOrder.T (@Eid VarOrder.T 3448)).
Definition rf_link_nodes := [::(3444,rf_link_expr_3444);(3445,rf_link_expr_3445);(3446,rf_link_expr_3446);(3447,rf_link_expr_3447);(3448,rf_link_expr_3448);(3449,rf_link_expr_3449)].
Definition rf_link_offsets := [::3523%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_link_positions :select_node_offsets rf_link_offsets flat_statements=Some rf_link_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_link_safety :selected_node_safety flat_memories flat_statements rf_link_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_link_output lane :=if Nat.eqb lane 0 then 3449 else 3446.
Theorem rf_link_data_three lane invalid s0 s1 s2 s3 pc :
 (lane<2)%coq_nat -> VM.find 2812 s0=Some(Gval(Fuint 32)pc) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 VM.find(rf_link_output lane)s3=Some(Gval(Fuint 32)(reference_pc_plus_four pc)).
Proof.
 intros Bound PC S1 S2 S3. destruct lane as[|[|lane]];[| |lia].
 {
 assert(V0:VM.find 3447 s1=Some(Gval(Fuint 33)(from_N 33(to_N pc+4)))).
 {eapply(reference_redirect_ground_step rf_link_offsets rf_link_nodes 3447 rf_link_expr_3447);[exact rf_link_positions|exact rf_link_safety|apply(List.nth_error_In rf_link_nodes 3%nat);reflexivity| |exact S1].
 intros site. cbn[rf_link_expr_3447 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite PC. reflexivity. }
 assert(V1:VM.find 3448 s2=Some(Gval(Fuint 32)(reference_pc_plus_four pc))).
 {eapply(reference_redirect_ground_step rf_link_offsets rf_link_nodes 3448 rf_link_expr_3448);[exact rf_link_positions|exact rf_link_safety|apply(List.nth_error_In rf_link_nodes 4%nat);reflexivity| |exact S2].
 intros site. cbn[rf_link_expr_3448 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0. reflexivity. }
 assert(V2:VM.find 3449 s3=Some(Gval(Fuint 32)(reference_pc_plus_four pc))).
 {eapply(reference_redirect_ground_step rf_link_offsets rf_link_nodes 3449 rf_link_expr_3449);[exact rf_link_positions|exact rf_link_safety|apply(List.nth_error_In rf_link_nodes 5%nat);reflexivity| |exact S3].
 intros site. cbn[rf_link_expr_3449 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1. reflexivity. }
 exact V2. }
 {
 assert(V0:VM.find 3444 s1=Some(Gval(Fuint 33)(from_N 33(to_N pc+4)))).
 {eapply(reference_redirect_ground_step rf_link_offsets rf_link_nodes 3444 rf_link_expr_3444);[exact rf_link_positions|exact rf_link_safety|apply(List.nth_error_In rf_link_nodes 0%nat);reflexivity| |exact S1].
 intros site. cbn[rf_link_expr_3444 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite PC. reflexivity. }
 assert(V1:VM.find 3445 s2=Some(Gval(Fuint 32)(reference_pc_plus_four pc))).
 {eapply(reference_redirect_ground_step rf_link_offsets rf_link_nodes 3445 rf_link_expr_3445);[exact rf_link_positions|exact rf_link_safety|apply(List.nth_error_In rf_link_nodes 1%nat);reflexivity| |exact S2].
 intros site. cbn[rf_link_expr_3445 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0. reflexivity. }
 assert(V2:VM.find 3446 s3=Some(Gval(Fuint 32)(reference_pc_plus_four pc))).
 {eapply(reference_redirect_ground_step rf_link_offsets rf_link_nodes 3446 rf_link_expr_3446);[exact rf_link_positions|exact rf_link_safety|apply(List.nth_error_In rf_link_nodes 2%nat);reflexivity| |exact S3].
 intros site. cbn[rf_link_expr_3446 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1. reflexivity. }
 exact V2. }
Qed.
Theorem rf_link_data_observed memory inputs k observed lane pc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<2)%coq_nat ->size pc=32%nat ->
 VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find(rf_link_output lane)(top_environment observed)=Some(Gval(Fuint 32)(reference_pc_plus_four pc)).
Proof.
 intros Observe Legal Lane Size PC.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(PC0:VM.find 7331(history 9254%nat)=Some(Gval(Fuint 32)pc)).
 { rewrite(proj2(exception_pc_sources_history_stable _ history 9259 9254 Steps ltac:(vm_compute;lia)))Last. exact PC. }
 pose proof(exception_pc_1749_value _ (history 9254%nat)(history 9254%nat)(history 9255%nat) _ _ PC0 (sized_uint_adapt_identity 32 pc Size)(Steps 9254%nat ltac:(vm_compute;lia)))as P1.
 pose proof(exception_pc_2812_value _ (history 9255%nat)(history 9255%nat)(history 9256%nat) pc P1 (Steps 9255%nat ltac:(vm_compute;lia)))as P2.
 rewrite <-Last. exact(rf_link_data_three lane _ (history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat) pc Lane P2
 (Steps 9256%nat ltac:(vm_compute;lia))(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.

Require Import CoreSocModel ComparisonNodes ReferenceStoreRs2 StoreTypeCorrespondence RFReadPorts RFReferenceNopHistory ReferenceRedirectSpine ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_store_data_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(6634,(@Eref VarOrder.T (@Eid VarOrder.T 2804)));(6635,(@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 6634))));(6654,(@Eref VarOrder.T (@Eid VarOrder.T 2804)));(6655,(@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 6654))));(6678,(@Eref VarOrder.T (@Eid VarOrder.T 2804)));(6679,(@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 6678))))].
Definition reference_store_data_offsets := [::6713%nat;0%nat;18%nat;0%nat;22%nat;0%nat].
Lemma reference_store_data_positions : select_node_offsets reference_store_data_offsets flat_statements = Some reference_store_data_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_store_data_safety : selected_node_safety flat_memories flat_statements reference_store_data_offsets flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_store_data_base lane : VarOrder.T := nth 0 [::6678;6654;6634] lane.
Definition reference_store_data_width lane := nth 0%nat [::32%nat;16%nat;8%nat] lane.
Theorem reference_store_data_steps lane invalid s0 s1 s2 word : (lane<3)%coq_nat ->
 VM.find 2804 s0=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find (reference_store_data_base lane+1) s2=Some(Gval(Fuint(reference_store_data_width lane))(take(reference_store_data_width lane)word)).
Proof.
 intros Lane Source Step1 Step2.
 destruct lane as [|lane]. {
 assert (Alias:VM.find 6678 s1=Some(Gval(Fuint 32)word)). {
 eapply (reference_redirect_ground_step reference_store_data_offsets reference_store_data_nodes 6678 (@Eref VarOrder.T (@Eid VarOrder.T 2804)) (Fuint 32) (word) invalid s0 s0 s1);
 [exact reference_store_data_positions|exact reference_store_data_safety|
 apply (List.nth_error_In reference_store_data_nodes 4%nat);vm_compute;reflexivity|
 intro site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];exact Source|exact Step1]. }
 change (VM.find 6679 s2=Some(Gval(Fuint 32)(take 32 word))).
 eapply (reference_redirect_ground_step reference_store_data_offsets reference_store_data_nodes 6679 (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 6678))) (Fuint 32) (take 32 word) invalid s1 s1 s2);
 [exact reference_store_data_positions|exact reference_store_data_safety|
 apply (List.nth_error_In reference_store_data_nodes 5%nat);vm_compute;reflexivity|
 intro site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Alias;cbn;rewrite drop0;reflexivity|exact Step2]. }
 destruct lane as [|lane]. {
 assert (Alias:VM.find 6654 s1=Some(Gval(Fuint 32)word)). {
 eapply (reference_redirect_ground_step reference_store_data_offsets reference_store_data_nodes 6654 (@Eref VarOrder.T (@Eid VarOrder.T 2804)) (Fuint 32) (word) invalid s0 s0 s1);
 [exact reference_store_data_positions|exact reference_store_data_safety|
 apply (List.nth_error_In reference_store_data_nodes 2%nat);vm_compute;reflexivity|
 intro site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];exact Source|exact Step1]. }
 change (VM.find 6655 s2=Some(Gval(Fuint 16)(take 16 word))).
 eapply (reference_redirect_ground_step reference_store_data_offsets reference_store_data_nodes 6655 (@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 6654))) (Fuint 16) (take 16 word) invalid s1 s1 s2);
 [exact reference_store_data_positions|exact reference_store_data_safety|
 apply (List.nth_error_In reference_store_data_nodes 3%nat);vm_compute;reflexivity|
 intro site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Alias;cbn;rewrite drop0;reflexivity|exact Step2]. }
 destruct lane as [|lane]. {
 assert (Alias:VM.find 6634 s1=Some(Gval(Fuint 32)word)). {
 eapply (reference_redirect_ground_step reference_store_data_offsets reference_store_data_nodes 6634 (@Eref VarOrder.T (@Eid VarOrder.T 2804)) (Fuint 32) (word) invalid s0 s0 s1);
 [exact reference_store_data_positions|exact reference_store_data_safety|
 apply (List.nth_error_In reference_store_data_nodes 0%nat);vm_compute;reflexivity|
 intro site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];exact Source|exact Step1]. }
 change (VM.find 6635 s2=Some(Gval(Fuint 8)(take 8 word))).
 eapply (reference_redirect_ground_step reference_store_data_offsets reference_store_data_nodes 6635 (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 6634))) (Fuint 8) (take 8 word) invalid s1 s1 s2);
 [exact reference_store_data_positions|exact reference_store_data_safety|
 apply (List.nth_error_In reference_store_data_nodes 1%nat);vm_compute;reflexivity|
 intro site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Alias;cbn;rewrite drop0;reflexivity|exact Step2]. }
 lia. Qed.
Theorem reference_store_data_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(reference_store_data_base lane+1)(top_environment observed)=Some(Gval(Fuint(reference_store_data_width lane))(take(reference_store_data_width lane)(bank(to_nat(rf_instruction_address true instruction))))).
Proof.
 intros Observe Legal Reset Lane Instruction Store Bank.
 pose proof(reference_store_rs2_bank_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Store Bank)as Data.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Source:VM.find 2804(history 9257%nat)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address true instruction))))).
 { rewrite(reference_control_stable_2804_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9257 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last;exact Data. }
 rewrite <-Last. eapply(reference_store_data_steps lane _ (history 9257%nat)(history 9258%nat)(history 9259%nat));[exact Lane|exact Source|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia].
Qed.

Require Import DUTRedirectDecode DUTRedirectSemantics LoadExecuteControl.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Lemma redirect_decode_add_row n left right : (n < 49)%coq_nat ->
 dut_redirect_function
 (to_N (from_N 2 (dut_decode_output false (dut_decode_row n))))
 (to_N (from_N 3 (dut_decode_output true (dut_decode_row n)))) left right = true ->
 from_N 4 (load_execute_row 3 n) = [::false;false;false;false].
Proof.
 intro Bound. do 49 (destruct n as [|n];[first [reflexivity|intro Taken;vm_compute in Taken;discriminate]|]);lia.
Qed.
Theorem redirect_decode_is_add instruction count left right : (count <= 49)%coq_nat ->
 dut_redirect_function (to_N (dut_decode_mux_value false instruction count))
 (to_N (dut_decode_mux_value true instruction count)) left right = true ->
 load_execute_decode 3 instruction count = [::false;false;false;false].
Proof.
 induction count as [|n IH];intros Bound Taken.
 - vm_compute in Taken;discriminate.
 - cbn [dut_decode_mux_value load_execute_decode] in *.
   destruct (dut_decode_test instruction (Nat.sub 48 n)) eqn:Selected.
   + apply (redirect_decode_add_row (Nat.sub 48 n) left right ltac:(lia));exact Taken.
   + apply IH;[lia|exact Taken].
Qed.
Lemma redirect_decode_non_eret_row n left right : (n < 49)%coq_nat ->
 dut_redirect_function
 (to_N (from_N 2 (dut_decode_output false (dut_decode_row n))))
 (to_N (from_N 3 (dut_decode_output true (dut_decode_row n)))) left right = true ->
 N.eqb (to_N (from_N 2 (dut_decode_output false (dut_decode_row n)))) 3 = false.
Proof.
 intro Bound. do 49 (destruct n as [|n];[first [reflexivity|intro Taken;vm_compute in Taken;discriminate]|]);lia.
Qed.
Theorem redirect_decode_non_eret instruction count left right : (count <= 49)%coq_nat ->
 dut_redirect_function (to_N (dut_decode_mux_value false instruction count))
 (to_N (dut_decode_mux_value true instruction count)) left right = true ->
 N.eqb (to_N (dut_decode_mux_value false instruction count)) 3 = false.
Proof.
 induction count as [|n IH];intros Bound Taken.
 - reflexivity.
 - cbn [dut_decode_mux_value] in *.
   destruct (dut_decode_test instruction (Nat.sub 48 n)) eqn:Selected.
   + apply (redirect_decode_non_eret_row (Nat.sub 48 n) left right ltac:(lia));exact Taken.
   + apply IH;[lia|exact Taken].
Qed.
Require Import CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory
 DataAddressConnectionCertificates FormalDeclaredConnection FormalPCControlNodes ReferenceRedirectSpine.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem pipeline_redirect_controls_observed memory inputs k observed instruction left right :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 VM.find 1357 (top_environment observed) = Some (Gval (Fuint 32) left) -> size left = 32%nat ->
 VM.find 1358 (top_environment observed) = Some (Gval (Fuint 32) right) -> size right = 32%nat ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 89 (top_environment observed) = Some (Gval (Fuint 4) [::false;false;false;false]) /\
 VM.find 1153 (top_environment observed) = Some (Gval (Fuint 4) [::false;false;false;false]) /\
 VM.find 7771 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Front Size Left LeftSize Right RightSize Taken.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (F : VM.find 7748 (history 9259%nat) = Some (Gval (Fuint 32) instruction)) by (rewrite Last;exact Front).
 destruct (dut_decode_history (generated_observation_input inputs k) nil history 9259 instruction Steps F Size 9259 ltac:(vm_compute;lia) (le_n _)) as [Selector Kind].
 rewrite Last in Selector, Kind.
 pose proof (dut_redirect_observed memory inputs k observed left right _ _ Observe Legal Left Right Kind Selector LeftSize RightSize) as Redirect.
 assert (Decision : dut_redirect_function (to_N (dut_decode_mux_value false (to_N instruction) 49))
 (to_N (dut_decode_mux_value true (to_N instruction) 49)) (to_N left) (to_N right) = true).
 { rewrite Taken in Redirect.
   pose proof (f_equal (fun value => match value with Some (Gval _ (bit::_)) => bit | _ => false end) Redirect) as Bits.
   change (true = dut_redirect_function (to_N (dut_decode_mux_value false (to_N instruction) 49))
     (to_N (dut_decode_mux_value true (to_N instruction) 49)) (to_N left) (to_N right)) in Bits.
   exact (Logic.eq_sym Bits). }
 pose proof (redirect_decode_is_add (to_N instruction) 49 (to_N left) (to_N right) ltac:(lia) Decision) as Mode.
 assert (ModeValue : forall time, (55 <= time)%coq_nat -> (time <= 9259)%coq_nat ->
 VM.find 89 (history time) = Some (Gval (Fuint 4) [::false;false;false;false])).
 { intros time Lower Upper. pose proof (load_execute_decode_history (generated_observation_input inputs k) nil history 9259 instruction 3 ltac:(lia) Steps F Size time Lower Upper) as Value.
   change (VM.find 89 (history time) = Some (Gval (Fuint 4) (load_execute_decode 3 (to_N instruction) 49))) in Value.
   rewrite Mode in Value;exact Value. }
 split.
 - rewrite <- Last;apply ModeValue;vm_compute;lia.
 - split.
   + rewrite <- Last.
     eapply (declared_connection_value 1228 flat_statements data_address_connection_1153_decl data_address_connection_1153_mid data_address_connection_1153_tail 1153 89 4 (Gval (Fuint 4) [::false;false;false;false]));
   [exact data_address_connection_1153_position|exact data_address_connection_1153_split|exact data_address_connection_1153_straight|exact data_address_connection_1153_mid_safe|exact data_address_connection_1153_tail_safe|exact data_address_connection_1153_nonregister|reflexivity| |reflexivity|exact (Steps 9258%nat ltac:(vm_compute;lia))].
     apply ModeValue;vm_compute;lia.
   + pose proof (redirect_decode_non_eret (to_N instruction) 49 (to_N left) (to_N right) ltac:(lia) Decision) as NonEret.
     destruct (dut_decode_history (generated_observation_input inputs k) nil history 9259 instruction Steps F Size 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [BeforeSelector _].
     rewrite <- Last. eapply (pc_control_node_7771 _ (history 9258%nat) (history 9258%nat));[|reflexivity|exact (Steps 9258%nat ltac:(vm_compute;lia))].
     cbn [pc_control_expr_7771 eval_hfexpr_with_memory eval_href_with_memory]. rewrite BeforeSelector.
     change (Some (Gval (Fuint 1) [::(to_N (dut_decode_mux_value false (to_N instruction) 49) == 3)]) = Some (Gval (Fuint 1) [::false])).
     rewrite redirect_N_eqb NonEret;reflexivity.
Qed.
Require Import ALUInputStability ReferenceLoadSemantics PipelinePCSuccessor.
Theorem pipeline_redirect_targets_observed memory inputs k observed next instruction branch_left branch_right alu_left alu_right :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 VM.find 1357 (top_environment observed) = Some (Gval (Fuint 32) branch_left) -> size branch_left = 32%nat ->
 VM.find 1358 (top_environment observed) = Some (Gval (Fuint 32) branch_right) -> size branch_right = 32%nat ->
 VM.find 1151 (top_environment observed) = Some (Gval (Fuint 32) alu_left) ->
 VM.find 1152 (top_environment observed) = Some (Gval (Fuint 32) alu_right) -> size alu_right = 32%nat ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7752 (top_environment next) = Some (Gval (Fuint 32) (reference_load_address alu_left alu_right)) /\
 VM.find 7768 (top_environment next) = Some (Gval (Fuint 33) (pipeline_redirect_target (reference_load_address alu_left alu_right))).
Proof.
 intros Observe Legal Next Reset Front InstSize BL BLS BR BRS AL AR ARS Taken.
 destruct (pipeline_redirect_controls_observed memory inputs k observed instruction branch_left branch_right Observe Legal Front InstSize BL BLS BR BRS Taken) as [Decode [Mode NonEret]].
 exact (alu_taken_pc_commit_observed memory inputs k observed next alu_left alu_right Observe Legal Next Reset ARS AL AR Mode Taken NonEret).
Qed.
Require Import DelayedRedirectObserved DelayedDUTRedirectSemantics DUTRedirectReachability
 JointBoundaryRegisters FetchPCArithmetic.
Lemma pipeline_alu_sum_bit1 left right :
 N.testbit (to_N (reference_load_address left right)) 1 = N.testbit (to_N left + to_N right) 1.
Proof.
 unfold reference_load_address. rewrite (fetch_pc_take_from_N 33 32 _ ltac:(reflexivity)) to_N_from_N.
 apply N.mod_pow2_bits_low;lia.
Qed.
Theorem pipeline_delayed_target_bit1 memory inputs k observed committed next_observed target :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs (S k) ->
 generated_run memory inputs (S k) = Some committed ->
 generated_observe memory inputs (S k) = Some next_observed ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs (S k))) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7752 (top_environment committed) = Some (Gval (Fuint 32) target) -> size target = 32%nat ->
 N.testbit (to_N target) 1 = false.
Proof.
 intros Observe Legal RunNext ObserveNext Reset ResetNext Taken Target Size.
 assert (LegalNow : generated_legal_trace memory inputs k).
 { destruct Legal as [Defined Cycles]. split;[exact Defined|]. intros j Bound;apply Cycles;lia. }
 pose proof (delayed_redirect_observed_step memory inputs k observed committed true Observe LegalNow RunNext Reset Taken) as Delayed.
 assert (R : VM.find 7760 (top_environment next_observed) = Some (Gval (Fuint 1) [::true])).
 { rewrite (delayed_joint_observed_copy memory inputs (S k) committed next_observed 7760 1 ltac:(apply (List.nth_error_In joint_boundary_registers 65%nat);vm_compute;reflexivity) RunNext ObserveNext). exact Delayed. }
 assert (T : VM.find 7752 (top_environment next_observed) = Some (Gval (Fuint 32) target)).
 { rewrite (delayed_joint_observed_copy memory inputs (S k) committed next_observed 7752 32 ltac:(apply (List.nth_error_In joint_boundary_registers 57%nat);vm_compute;reflexivity) RunNext ObserveNext). exact Target. }
 exact (dut_no_trap_target_bit_observed memory inputs (S k) next_observed target ObserveNext Legal ResetNext R T Size).
Qed.
Theorem pipeline_redirect_sum_bit1 memory inputs k observed committed next_observed instruction branch_left branch_right alu_left alu_right :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs (S k) ->
 generated_run memory inputs (S k) = Some committed -> generated_observe memory inputs (S k) = Some next_observed ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs (S k))) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 VM.find 1357 (top_environment observed) = Some (Gval (Fuint 32) branch_left) -> size branch_left = 32%nat ->
 VM.find 1358 (top_environment observed) = Some (Gval (Fuint 32) branch_right) -> size branch_right = 32%nat ->
 VM.find 1151 (top_environment observed) = Some (Gval (Fuint 32) alu_left) ->
 VM.find 1152 (top_environment observed) = Some (Gval (Fuint 32) alu_right) -> size alu_right = 32%nat ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 N.testbit (to_N alu_left + to_N alu_right) 1 = false.
Proof.
 intros Observe Legal Next ObserveNext Reset ResetNext Front InstSize BL BLS BR BRS AL AR ARS Taken.
 assert (LegalNow : generated_legal_trace memory inputs k).
 { destruct Legal as [Defined Cycles]. split;[exact Defined|]. intros j Bound;apply Cycles;lia. }
 destruct (pipeline_redirect_targets_observed memory inputs k observed committed instruction branch_left branch_right alu_left alu_right Observe LegalNow Next Reset Front InstSize BL BLS BR BRS AL AR ARS Taken) as [Target Fetch].
 rewrite <- pipeline_alu_sum_bit1.
 apply (pipeline_delayed_target_bit1 memory inputs k observed committed next_observed _ Observe Legal Next ObserveNext Reset ResetNext Taken Target).
 unfold reference_load_address;rewrite size_take size_from_N;reflexivity.
Qed.

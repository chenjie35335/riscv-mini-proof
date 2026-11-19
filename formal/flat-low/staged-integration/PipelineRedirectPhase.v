Require Import CoreSocModel ComparisonNodes DUTRedirectDecode ReferenceRedirectSpine
 JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates FormalDeclaredConnection.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition pipeline_kill_rows : seq bool := [::false;false;true;true;false;false;false;false;false;false;true;true;true;true;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true;false;false;true;false].
Definition pipeline_kill_indices : seq nat := [::1144%nat;1145%nat;1146%nat;1147%nat;1148%nat;1149%nat;1150%nat;1151%nat;1152%nat;1153%nat;1154%nat;1155%nat;1156%nat;1157%nat;1158%nat;1159%nat;1160%nat;1161%nat;1162%nat;1163%nat;1164%nat;1165%nat;1166%nat;1167%nat;1168%nat;1169%nat;1170%nat;1171%nat;1172%nat;1173%nat;1174%nat;1175%nat;1176%nat;1177%nat;1178%nat;1179%nat;1180%nat;1181%nat;1182%nat;1183%nat;1184%nat;1185%nat;1186%nat;1187%nat;1188%nat;1189%nat;1190%nat;1191%nat;1192%nat].
Definition pipeline_kill_extract_index : nat := 1389%nat.
(* Parametric kill/redirect phase proofs. *)
Definition pipeline_kill_node n := 8655 + N.of_nat n.
Definition pipeline_kill_expression n := @Emux VarOrder.T
 (@Eref VarOrder.T (@Eid VarOrder.T (dut_decode_guard_node (Nat.sub 48 n))))
 (@Econst VarOrder.T (Fuint 1) [::nth false pipeline_kill_rows (Nat.sub 48 n)])
 (match n with O => @Econst VarOrder.T (Fuint 1) [::false]
 | S before => @Eref VarOrder.T (@Eid VarOrder.T (pipeline_kill_node before)) end).
Fixpoint pipeline_kill_decode instruction count := match count with
 | O => false
 | S n => if dut_decode_test instruction (Nat.sub 48 n) then nth false pipeline_kill_rows (Nat.sub 48 n)
   else pipeline_kill_decode instruction n end.
Lemma pipeline_kill_certificate n : (n < 49)%coq_nat ->
 nth_error joint_update_expected_nodes (nth 0%nat pipeline_kill_indices n) = Some (pipeline_kill_node n,pipeline_kill_expression n).
Proof. intro Bound;do 49 (destruct n as [|n];[vm_compute;reflexivity|]);lia. Qed.
Lemma pipeline_kill_decode_S instruction n : pipeline_kill_decode instruction (S n) =
 if dut_decode_test instruction (Nat.sub 48 n) then nth false pipeline_kill_rows (Nat.sub 48 n) else pipeline_kill_decode instruction n.
Proof. reflexivity. Qed.
Lemma pipeline_bit_if (bit yes no : bool) : [::if bit then yes else no] = if bit then [::yes] else [::no].
Proof. destruct bit;reflexivity. Qed.
Theorem pipeline_kill_mux_history inputs path history limit instruction :
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)) ->
 forall n time, (n < 49)%coq_nat -> (Nat.add 5 n <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (pipeline_kill_node n) (history time) = Some (Gval (Fuint 1) [::pipeline_kill_decode (to_N instruction) (S n)]).
Proof.
 intros Steps Instruction n. induction n as [|n IH];intros time Bound Lower Upper;destruct time as [|time];try lia.
 - rewrite (pipeline_kill_decode_S _ 0) pipeline_bit_if.
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes _ (pipeline_kill_expression 0));
   [exact joint_update_node_positions|exact joint_update_node_safety|eapply List.nth_error_In;apply pipeline_kill_certificate;lia| |apply Steps;lia].
   intros site. unfold pipeline_kill_expression. eapply dut_decode_mux_eval.
   + intros inner;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction 48 ltac:(lia) Steps Instruction time);split;lia.
   + intros inner;reflexivity.
   + intros inner;reflexivity.
   + reflexivity.
   + reflexivity.
   + reflexivity.
   + reflexivity.
 - pose proof (IH time ltac:(lia) ltac:(lia) ltac:(lia)) as Previous.
   rewrite (pipeline_kill_decode_S _ (S n)) pipeline_bit_if.
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes _ (pipeline_kill_expression (S n)));
   [exact joint_update_node_positions|exact joint_update_node_safety|eapply List.nth_error_In;apply pipeline_kill_certificate;lia| |apply Steps;lia].
   intros site. unfold pipeline_kill_expression. eapply dut_decode_mux_eval.
   + intros inner;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction (Nat.sub 48 (S n)) ltac:(lia) Steps Instruction time);split;lia.
   + intros inner. destruct (nth false pipeline_kill_rows (Nat.sub 48 (S n)));reflexivity.
   + intros inner;exact Previous.
   + reflexivity.
   + unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite Previous;reflexivity.
   + reflexivity.
   + reflexivity.

Qed.
Lemma pipeline_jump_kill_row n : (n < 49)%coq_nat ->
 N.eqb (to_N (from_N 2 (dut_decode_output false (dut_decode_row n)))) 1 = true -> nth false pipeline_kill_rows n = true.
Proof.
 intro Bound. do 49 (destruct n as [|n];[first [reflexivity|intro Taken;vm_compute in Taken;discriminate]|]);lia.
Qed.
Theorem pipeline_jump_implies_kill instruction count : (count <= 49)%coq_nat ->
 N.eqb (to_N (dut_decode_mux_value false instruction count)) 1 = true -> pipeline_kill_decode instruction count = true.
Proof.
 induction count as [|n IH];intros Bound Jump;[vm_compute in Jump;discriminate|].
 cbn [dut_decode_mux_value pipeline_kill_decode] in *.
 destruct (dut_decode_test instruction (Nat.sub 48 n)).
 - apply (pipeline_jump_kill_row (Nat.sub 48 n) ltac:(lia));exact Jump.
 - apply IH;[lia|exact Jump].
Qed.
Require Import JointUpdateBoundaryHistory JointBoundaryRegisters FormalPCDecodeInputConnections.
Theorem pipeline_kill_history inputs path history limit instruction :
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 85 (history time) = Some (Gval (Fuint 1) [::pipeline_kill_decode (to_N instruction) 49]).
Proof.
 intros Steps Front Size time Lower Upper.
 assert (Source : forall i, (i <= limit)%coq_nat -> VM.find 7748 (history i) = Some (Gval (Fuint 32) instruction)).
 { intros i Bound.
   pose proof (joint_update_register_history_same (formal_invalid_policy inputs path) history limit 7748 32
     ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity) Steps) as Hold.
   rewrite (Hold i Bound). rewrite <- (Hold limit ltac:(lia));exact Front. }
 assert (Instruction : forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)).
 { intros [|[|i]] Bound;try lia.
   eapply decode_input_connection_8249;[|apply dut_decode_adapt;exact Size|apply Steps;lia].
   eapply decode_input_connection_83;[|apply dut_decode_adapt;exact Size|apply Steps;lia]. apply Source;lia. }
 destruct time as [|[|[|time]]];try lia.
 pose proof (pipeline_kill_mux_history inputs path history limit instruction Steps Instruction 48 time ltac:(lia) ltac:(lia) ltac:(lia)) as Mux.
 change (VM.find 8703 (history time) = Some (Gval (Fuint 1) [::pipeline_kill_decode (to_N instruction) 49])) in Mux.
 assert (Extract : VM.find 8998 (history (S time)) = Some (Gval (Fuint 1) [::pipeline_kill_decode (to_N instruction) 49])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 8998 joint_update_expr_8998);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes pipeline_kill_extract_index);vm_compute;reflexivity| |apply Steps;lia].
   intros site;cbn [joint_update_expr_8998 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mux.
   destruct (pipeline_kill_decode (to_N instruction) 49);reflexivity. }
 assert (Inner : VM.find 8251 (history (S (S time))) = Some (Gval (Fuint 1) [::pipeline_kill_decode (to_N instruction) 49])).
 { eapply (declared_connection_value 9011 flat_statements joint_update_connection_8251_decl joint_update_connection_8251_mid joint_update_connection_8251_tail 8251 8998 1 (Gval (Fuint 1) [::pipeline_kill_decode (to_N instruction) 49]));
   [exact joint_update_connection_8251_position|exact joint_update_connection_8251_split|exact joint_update_connection_8251_straight|exact joint_update_connection_8251_mid_safe|exact joint_update_connection_8251_tail_safe|exact joint_update_connection_8251_nonregister|reflexivity|exact Extract|apply dut_decode_adapt;reflexivity|apply Steps;lia]. }
 eapply (declared_connection_value 62 flat_statements joint_update_connection_85_decl joint_update_connection_85_mid joint_update_connection_85_tail 85 8251 1 (Gval (Fuint 1) [::pipeline_kill_decode (to_N instruction) 49]));
 [exact joint_update_connection_85_position|exact joint_update_connection_85_split|exact joint_update_connection_85_straight|exact joint_update_connection_85_mid_safe|exact joint_update_connection_85_tail_safe|exact joint_update_connection_85_nonregister|reflexivity|exact Inner|apply dut_decode_adapt;reflexivity|apply Steps;lia].
Qed.
Require Import EarlyBubbleValues EarlyBubbleNopControlKnown EarlyControlWireBitNormalization
 EarlyControlStabilityHistory ExceptionStabilityHistory ExceptionEventHistory StartupFlagInitialization
 ConcreteRegisterInitialization FormalPCControlNodes.
Theorem pipeline_taken_bubble_source_history inputs path history instruction :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7748 (history 9259%nat) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 VM.find 7773 (history 9259%nat) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7944 (history 9259%nat) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Boundary Steps Front Size Taken.
 destruct (joint_update_register_history_concrete _ history 9259 7762 1 startup_register_member
 (Boundary _ _ startup_register_member) Steps 9256 ltac:(vm_compute;lia)) as [started [StartedSize Started]].
 destruct started as [|start tail];[discriminate StartedSize|]. destruct tail as [|extra tail];[|discriminate StartedSize].
 pose proof (pipeline_kill_history inputs path history 9259 instruction Steps Front Size 9256 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Kill.
 destruct (early_control_wire_1360_normalized _ (history 9256%nat) (history 9256%nat) (history 9257%nat)
 (Steps 9256%nat ltac:(vm_compute;lia))) as [branchValue [BranchValue BranchNormal]].
 destruct (early_bubble_normalized_concrete _ 1360 branchValue BranchValue BranchNormal
 (early_control_concrete_1360_history inputs path history 9259 Boundary Steps 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [branch Branch].
 destruct (exception_source128_normalized _ (history 9257%nat) (history 9257%nat) (history 9258%nat)
 (Steps 9257%nat ltac:(vm_compute;lia))) as [exceptionValue [ExceptionValue ExceptionNormal]].
 destruct (early_bubble_normalized_concrete _ 128 exceptionValue ExceptionValue ExceptionNormal
 (exception_concrete_128_history inputs path history 9259 Boundary Steps 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [exception Exception].
 assert (Branch8 : VM.find 1360 (history 9258%nat) = Some (Gval (Fuint 1) [::branch])).
 { rewrite (early_control_stable_1360_history inputs path history 9259 Boundary Steps 9258 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia));exact Branch. }
 destruct (dut_decode_history inputs path history 9259 instruction Steps Front Size 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [Selector _].
 assert (Jump : VM.find 7772 (history 9258%nat) = Some (Gval (Fuint 1) [::N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1])).
 { eapply (pc_control_node_7772 _ (history 9257%nat) (history 9257%nat));[|reflexivity|exact (Steps 9257%nat ltac:(vm_compute;lia))].
   cbn [pc_control_expr_7772 eval_hfexpr_with_memory eval_href_with_memory];rewrite Selector.
   change (Some (Gval (Fuint 1) [::(to_N (dut_decode_mux_value false (to_N instruction) 49) == 1)]) = Some (Gval (Fuint 1) [::N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1])).
   rewrite redirect_N_eqb;reflexivity. }
 assert (Raw : VM.find 7773 (history 9259%nat) = Some (Gval (Fuint 1) [::N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1 || branch])).
 { eapply (pc_control_node_7773 _ (history 9258%nat) (history 9258%nat));[|reflexivity|exact (Steps 9258%nat ltac:(vm_compute;lia))].
   cbn [pc_control_expr_7773 eval_hfexpr_with_memory eval_href_with_memory];rewrite Jump Branch8.
   destruct (N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1),branch;reflexivity. }
 rewrite Taken in Raw.
 pose proof (f_equal (fun value => match value with Some (Gval _ (bit::_)) => bit | _ => false end) Raw) as Decision.
 change (true = (N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1 || branch)) in Decision.
 assert (KillBranch : pipeline_kill_decode (to_N instruction) 49 || branch = true).
 { destruct branch.
   - apply Bool.orb_true_r.
   - rewrite Bool.orb_false_r in Decision. rewrite Bool.orb_false_r.
     apply (pipeline_jump_implies_kill (to_N instruction) 49 ltac:(lia));exact (Logic.eq_sym Decision). }
 pose proof (early_bubble_value_after_three (formal_invalid_policy inputs path) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat)
 start (pipeline_kill_decode (to_N instruction) 49) branch exception Started Kill Branch Exception
 (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia))) as Source.
 assert (Overall : ((start || pipeline_kill_decode (to_N instruction) 49) || branch) || exception = true).
 { destruct start, (pipeline_kill_decode (to_N instruction) 49), branch, exception;cbn in KillBranch |- *;congruence. }
 rewrite Overall in Source;exact Source.
Qed.
Require Import ALUOutputTransfer FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration
 PipelineBubbleNormalCommit Bubble7945Type FormalCheckerResetConnections.
Theorem pipeline_taken_bubble_observed memory inputs k observed next instruction :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7945 (top_environment next) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Observe Legal Next Reset Front Size Taken.
 destruct (alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)
 as [history [Last [Boundary [Steps [Resets ALU]]]]].
 pose proof (pipeline_taken_bubble_source_history (generated_observation_input inputs k) nil history instruction Boundary Steps ltac:(rewrite Last;exact Front) Size ltac:(rewrite Last;exact Taken)) as Source.
 destruct (bubble7945_observe_type memory inputs k observed Observe) as [old [Old Typed]].
 assert (Root : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
   - apply (reset_connection_24_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9257%nat) (history 9257%nat) (history 9258%nat) false);[apply Resets|apply Steps];vm_compute;lia.
   - apply Steps;vm_compute;lia. }
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 rewrite <- Top in Step. rewrite <- Last in Step.
 unfold top_environment;rewrite After.
 apply (pipeline_bubble_7945_normal_commit (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9259%nat) (history 9259%nat) after old true);try assumption.
 rewrite Last;exact Old.
Qed.
Require Import PipelinePCRedirectControl PipelinePCSuccessor ReferenceLoadSemantics DelayedRedirectObserved.
Definition pipeline_late_redirect_phase env : Prop :=
 VM.find 7760 env = Some (Gval (Fuint 1) [::true]) ->
 exists word, size word = 32%nat /\ VM.find 7752 env = Some (Gval (Fuint 32) word) /\
 VM.find 7768 env = Some (Gval (Fuint 33) (pipeline_redirect_target word)) /\
 VM.find 7945 env = Some (Gval (Fuint 1) [::true]).
Theorem pipeline_taken_phase_observed memory inputs k observed next instruction branch_left branch_right alu_left alu_right :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 VM.find 1357 (top_environment observed) = Some (Gval (Fuint 32) branch_left) -> size branch_left = 32%nat ->
 VM.find 1358 (top_environment observed) = Some (Gval (Fuint 32) branch_right) -> size branch_right = 32%nat ->
 VM.find 1151 (top_environment observed) = Some (Gval (Fuint 32) alu_left) ->
 VM.find 1152 (top_environment observed) = Some (Gval (Fuint 32) alu_right) -> size alu_right = 32%nat ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7760 (top_environment next) = Some (Gval (Fuint 1) [::true]) /\
 pipeline_late_redirect_phase (top_environment next).
Proof.
 intros Observe Legal Next Reset Front InstSize BL BLS BR BRS AL AR ARS Taken.
 destruct (pipeline_redirect_targets_observed memory inputs k observed next instruction branch_left branch_right alu_left alu_right Observe Legal Next Reset Front InstSize BL BLS BR BRS AL AR ARS Taken) as [Target Fetch].
 pose proof (pipeline_taken_bubble_observed memory inputs k observed next instruction Observe Legal Next Reset Front InstSize Taken) as Bubble.
 split.
 - exact (delayed_redirect_observed_step memory inputs k observed next true Observe Legal Next Reset Taken).
 - intro Delayed. exists (reference_load_address alu_left alu_right). split.
   + unfold reference_load_address;rewrite size_take size_from_N;reflexivity.
   + repeat split;assumption.
Qed.
Require Import FormalDeclaredConnectionObservation ALUInputStability DataAddressConnectionCertificates ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames RegisterInvariants.
Lemma pipeline_declared_uint_concrete_size count stmts decl middle tail node source width invalid memories old current result :
 straight_drop count stmts = Some (Qcons (Swire node (Gtyp (Fuint width))) decl) ->
 decl = statement_append middle (Qcons (Sfcnct (Eid node) (Eref (Eid source))) tail) ->
 straight_statements middle -> formal_typed_suffix_safe memories node middle -> formal_typed_suffix_safe memories node tail ->
 has_register node stmts = false -> node != source ->
 (exists ground bits, VM.find source old = Some (Gval ground bits)) ->
 formal_value_iter invalid memories old false current stmts = Some result ->
 map_uint_concrete node width result.
Proof.
 intros Position Split Straight MidSafe TailSafe Nonreg Different [ground [bits Known]] Step.
 destruct (declared_connection_observation count stmts decl middle tail node source width invalid memories old current result
 Position Split Straight MidSafe TailSafe Nonreg Different Step) as [sv [value [Source [Adapt Value]]]].
 rewrite Known in Source. inversion Source;subst sv.
 destruct ground;cbn [adapt_hvalue_as_type] in Adapt;try discriminate Adapt.
 inversion Adapt;subst value. exists (zext_to width (take width bits)). split;[|exact Value].
 unfold zext_to. rewrite size_zext size_take. apply subnKC;apply geq_minl.
Qed.
Definition pipeline_operand_node which : VarOrder.T := nth 0 [::1357;1358;1151;1152] which.
Definition pipeline_operand_source which : VarOrder.T := nth 0 [::7816;7819;7821;7823] which.
Lemma pipeline_operand_wire_sized which invalid old current result :
 (which < 4)%coq_nat ->
 (exists ground bits, VM.find (pipeline_operand_source which) old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 map_uint_concrete (pipeline_operand_node which) 32 result.
Proof.
 intros Which Ground Step. destruct which as [|[|[|[|which]]]];cbn [pipeline_operand_node pipeline_operand_source nth] in *;try lia.
 - exact (pipeline_declared_uint_concrete_size 1435 flat_statements joint_update_connection_1357_decl joint_update_connection_1357_mid joint_update_connection_1357_tail 1357 7816 32 invalid flat_memories old current result
 joint_update_connection_1357_position joint_update_connection_1357_split joint_update_connection_1357_straight joint_update_connection_1357_mid_safe joint_update_connection_1357_tail_safe joint_update_connection_1357_nonregister (Logic.eq_refl _) Ground Step).
 - exact (pipeline_declared_uint_concrete_size 1436 flat_statements joint_update_connection_1358_decl joint_update_connection_1358_mid joint_update_connection_1358_tail 1358 7819 32 invalid flat_memories old current result
 joint_update_connection_1358_position joint_update_connection_1358_split joint_update_connection_1358_straight joint_update_connection_1358_mid_safe joint_update_connection_1358_tail_safe joint_update_connection_1358_nonregister (Logic.eq_refl _) Ground Step).
 - exact (pipeline_declared_uint_concrete_size 1226 flat_statements data_address_connection_1151_decl data_address_connection_1151_mid data_address_connection_1151_tail 1151 7821 32 invalid flat_memories old current result
 data_address_connection_1151_position data_address_connection_1151_split data_address_connection_1151_straight data_address_connection_1151_mid_safe data_address_connection_1151_tail_safe data_address_connection_1151_nonregister (Logic.eq_refl _) Ground Step).
 - exact (pipeline_declared_uint_concrete_size 1227 flat_statements data_address_connection_1152_decl data_address_connection_1152_mid data_address_connection_1152_tail 1152 7823 32 invalid flat_memories old current result
 data_address_connection_1152_position data_address_connection_1152_split data_address_connection_1152_straight data_address_connection_1152_mid_safe data_address_connection_1152_tail_safe data_address_connection_1152_nonregister (Logic.eq_refl _) Ground Step).
Qed.
Theorem pipeline_operands_sized_history inputs path history :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall which, (which < 4)%coq_nat -> map_uint_concrete (pipeline_operand_node which) 32 (history 9259%nat).
Proof.
 intros Boundary Steps which Which.
 apply (pipeline_operand_wire_sized which (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat) (history 9259%nat) Which);[|apply Steps;vm_compute;lia].
 destruct which as [|[|[|[|which]]]];cbn [pipeline_operand_source nth];try lia.
 - destruct (early_control_concrete_7816_history inputs path history 9259 Boundary Steps 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [width [bits Value]]. exists (Fuint width),bits;exact Value.
 - destruct (early_control_concrete_7819_history inputs path history 9259 Boundary Steps 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [width [bits Value]]. exists (Fuint width),bits;exact Value.
 - exact (proj1 (alu_stability_from_roots inputs path history 9259 Steps (alu_stability_roots_history inputs path history 9259 Boundary Steps) 57 7821 [::7749%nat;7816%nat;7820%nat]
 ltac:(apply (List.nth_error_In alu_stability_table 53%nat);vm_compute;reflexivity) 9258 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia))).
 - exact (proj1 (alu_stability_from_roots inputs path history 9259 Steps (alu_stability_roots_history inputs path history 9259 Boundary Steps) 66 7823 [::1308%nat;7819%nat;7822%nat]
 ltac:(apply (List.nth_error_In alu_stability_table 63%nat);vm_compute;reflexivity) 9258 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia))).
Qed.
Require Import DUTRedirectSemantics.
Theorem pipeline_normal_redirect_phase memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_late_redirect_phase (top_environment next).
Proof.
 intros Observe Legal Next Reset.
 destruct (alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)
 as [history [Last [Boundary [Steps [Resets ALU]]]]].
 assert (Member : List.In (7748%nat,32%nat) joint_boundary_registers).
 { apply (List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity. }
 destruct (joint_update_register_history_concrete _ history 9259 7748 32 Member (Boundary _ _ Member) Steps 9259 (le_n _)) as [instruction [InstSize Front]].
 destruct (pipeline_operands_sized_history _ _ history Boundary Steps 0 ltac:(lia)) as [branch_left [BLS BL]].
 destruct (pipeline_operands_sized_history _ _ history Boundary Steps 1 ltac:(lia)) as [branch_right [BRS BR]].
 destruct (pipeline_operands_sized_history _ _ history Boundary Steps 2 ltac:(lia)) as [alu_left [ALS AL]].
 destruct (pipeline_operands_sized_history _ _ history Boundary Steps 3 ltac:(lia)) as [alu_right [ARS AR]].
 cbn [pipeline_operand_node nth] in BL,BR,AL,AR.
 destruct (dut_decode_history (generated_observation_input inputs k) nil history 9259 instruction Steps Front InstSize 9259 ltac:(vm_compute;lia) (le_n _)) as [Selector Kind].
 rewrite Last in Front,BL,BR,AL,AR,Selector,Kind.
 pose proof (dut_redirect_observed memory inputs k observed branch_left branch_right _ _ Observe Legal BL BR Kind Selector BLS BRS) as Raw.
 remember (dut_redirect_function (to_N (dut_decode_mux_value false (to_N instruction) 49)) (to_N (dut_decode_mux_value true (to_N instruction) 49)) (to_N branch_left) (to_N branch_right)) as bit eqn:Bit in Raw.
 destruct bit.
 - exact (proj2 (pipeline_taken_phase_observed memory inputs k observed next instruction branch_left branch_right alu_left alu_right Observe Legal Next Reset Front InstSize BL BLS BR BRS AL AR ARS Raw)).
 - pose proof (delayed_redirect_observed_step memory inputs k observed next false Observe Legal Next Reset Raw) as Clear.
   intro Flag. rewrite Clear in Flag;discriminate Flag.
Qed.

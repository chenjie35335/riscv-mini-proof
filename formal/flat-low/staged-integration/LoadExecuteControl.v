Require Import LoadTypeCorrespondence DUTRedirectDecode CoreSocModel ComparisonNodes DataAddressPositionCertificate DataAddressSafetyCertificate FormalDeclaredWireCheck ReferenceRedirectSpine JointBoundaryRegisters JointUpdateBoundaryHistory FormalPCDecodeInputConnections ObservedJointRegisterConcrete FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition load_execute_values : seq (seq N) := [::[::0;0;0;1;0;0;0;0;0;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;0;0;0;0;0;0;0];[::0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1;1;1;1;1;1;1;1;1;1;0;0;0;0;0;0;0;0;0;0;0;0];[::3;3;4;1;5;5;5;5;5;5;1;1;1;1;1;2;2;2;1;1;1;1;1;1;1;1;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;6;6;6;0;0;0;0];[::11;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;5;7;4;3;2;6;8;9;0;1;6;5;7;4;8;9;3;2;15;15;10;10;10;15;15;15;15;15;15;15]].
Definition load_execute_indices : seq (seq nat) := [::[::295%nat;294%nat;293%nat;292%nat;291%nat;290%nat;289%nat;288%nat;287%nat;286%nat;285%nat;284%nat;283%nat;282%nat;281%nat;280%nat;279%nat;278%nat;277%nat;276%nat;275%nat;274%nat;273%nat;272%nat;271%nat;270%nat;269%nat;268%nat;267%nat;266%nat;265%nat;264%nat;263%nat;262%nat;261%nat;260%nat;259%nat;258%nat;257%nat;256%nat;255%nat;254%nat;253%nat;252%nat;251%nat;250%nat;249%nat;248%nat;247%nat];[::344%nat;343%nat;342%nat;341%nat;340%nat;339%nat;338%nat;337%nat;336%nat;335%nat;334%nat;333%nat;332%nat;331%nat;330%nat;329%nat;328%nat;327%nat;326%nat;325%nat;324%nat;323%nat;322%nat;321%nat;320%nat;319%nat;318%nat;317%nat;316%nat;315%nat;314%nat;313%nat;312%nat;311%nat;310%nat;309%nat;308%nat;307%nat;306%nat;305%nat;304%nat;303%nat;302%nat;301%nat;300%nat;299%nat;298%nat;297%nat;296%nat];[::393%nat;392%nat;391%nat;390%nat;389%nat;388%nat;387%nat;386%nat;385%nat;384%nat;383%nat;382%nat;381%nat;380%nat;379%nat;378%nat;377%nat;376%nat;375%nat;374%nat;373%nat;372%nat;371%nat;370%nat;369%nat;368%nat;367%nat;366%nat;365%nat;364%nat;363%nat;362%nat;361%nat;360%nat;359%nat;358%nat;357%nat;356%nat;355%nat;354%nat;353%nat;352%nat;351%nat;350%nat;349%nat;348%nat;347%nat;346%nat;345%nat];[::442%nat;441%nat;440%nat;439%nat;438%nat;437%nat;436%nat;435%nat;434%nat;433%nat;432%nat;431%nat;430%nat;429%nat;428%nat;427%nat;426%nat;425%nat;424%nat;423%nat;422%nat;421%nat;420%nat;419%nat;418%nat;417%nat;416%nat;415%nat;414%nat;413%nat;412%nat;411%nat;410%nat;409%nat;408%nat;407%nat;406%nat;405%nat;404%nat;403%nat;402%nat;401%nat;400%nat;399%nat;398%nat;397%nat;396%nat;395%nat;394%nat]].
Definition load_execute_wire_positions : seq nat := [::9012%nat;63%nat;9013%nat;64%nat;9014%nat;65%nat;9015%nat;66%nat].
Definition load_execute_wire_distances : seq nat := [::749%nat;9928%nat;749%nat;9928%nat;749%nat;9928%nat;749%nat;9928%nat].
Definition load_execute_width which := nth 0%nat [::1%nat;1%nat;3%nat;4%nat] which.
Definition load_execute_default which : N := if Nat.eqb which 3 then 15 else 0.
Definition load_execute_expected which : N := nth 0 [::1;0;1;0] which.
Definition load_execute_wire_target which outer : VarOrder.T := (if outer then 86 else 8252) + N.of_nat which.
Definition load_execute_wire_source which outer : VarOrder.T := if outer then 8252 + N.of_nat which else 8458 + 49 * N.of_nat which.
Definition load_execute_wire_index which outer := Nat.add (Nat.mul 2 which) (if outer then 1%nat else 0%nat).
Lemma load_execute_wire_certificate which outer : (which < 4)%coq_nat ->
 declared_wire_check flat_memories flat_statements (nth 0%nat load_execute_wire_positions (load_execute_wire_index which outer))
 (nth 0%nat load_execute_wire_distances (load_execute_wire_index which outer))
 (load_execute_wire_target which outer) (load_execute_wire_source which outer) (load_execute_width which) = true.
Proof. intro Bound. destruct outer;do 4 (destruct which as [|which];[vm_compute;reflexivity|]);lia. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Parametric execute-control semantics. *)
Definition load_execute_row which n := nth 0 (nth [::] load_execute_values which) n.
Definition load_execute_mux_node which n := 8410 + 49 * N.of_nat which + N.of_nat n.
Definition load_execute_mux_expression which n :=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (dut_decode_guard_node (Nat.sub 48 n))))
 (@Econst VarOrder.T (Fuint (load_execute_width which)) (from_N (load_execute_width which) (load_execute_row which (Nat.sub 48 n))))
 (match n with O => @Econst VarOrder.T (Fuint (load_execute_width which)) (from_N (load_execute_width which) (load_execute_default which))
 | S before => @Eref VarOrder.T (@Eid VarOrder.T (load_execute_mux_node which before)) end).
Fixpoint load_execute_decode which instruction count :=
 match count with O => from_N (load_execute_width which) (load_execute_default which)
 | S n => if dut_decode_test instruction (Nat.sub 48 n) then
  from_N (load_execute_width which) (load_execute_row which (Nat.sub 48 n)) else load_execute_decode which instruction n end.
Lemma load_execute_mux_certificates which n : (which < 4)%coq_nat -> (n < 49)%coq_nat ->
 nth_error data_address_expected_nodes (nth 0%nat (nth [::] load_execute_indices which) (Nat.sub 48 n)) =
 Some (load_execute_mux_node which n,load_execute_mux_expression which n).
Proof.
 intros Which Bound. do 4 (destruct which as [|which];[do 49 (destruct n as [|n];[vm_compute;reflexivity|]);lia|]). lia.
Qed.
Lemma load_execute_decode_size which instruction count : size (load_execute_decode which instruction count) = load_execute_width which.
Proof.
 induction count as [|count IH];cbn [load_execute_decode];[apply size_from_N|].
 destruct (dut_decode_test instruction (Nat.sub 48 count));[apply size_from_N|exact IH].
Qed.
Theorem load_execute_mux_history inputs path history limit instruction which :
 (which < 4)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)) ->
 forall n time, (n < 49)%coq_nat -> (Nat.add 5 n <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (load_execute_mux_node which n) (history time) = Some (Gval (Fuint (load_execute_width which)) (load_execute_decode which (to_N instruction) (S n))).
Proof.
 intros Which Steps Instruction n. induction n as [|n IH]; intros time Bound Lower Upper; destruct time as [|time]; try lia.
 - eapply (reference_redirect_ground_step data_address_node_offsets data_address_expected_nodes _ (load_execute_mux_expression which 0));
   [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|eapply List.nth_error_In; apply load_execute_mux_certificates; lia| |apply Steps; lia].
   intros site. unfold load_execute_mux_expression. change (48-0)%nat with 48%nat.
   cbn [load_execute_decode]. eapply dut_decode_mux_eval.
   + intros inner. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction 48 ltac:(lia) Steps Instruction time); lia.
   + intro inner. apply dut_decode_constant.
   + intro inner. apply dut_decode_constant.
   + apply dut_decode_constant_type.
   + apply dut_decode_constant_type.
   + apply size_from_N.
   + apply size_from_N.
 - pose proof (IH time ltac:(lia) ltac:(lia) ltac:(lia)) as Previous.
   eapply (reference_redirect_ground_step data_address_node_offsets data_address_expected_nodes _ (load_execute_mux_expression which (S n)));
   [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|eapply List.nth_error_In; apply load_execute_mux_certificates; lia| |apply Steps; lia].
   intros site. unfold load_execute_mux_expression. cbn [load_execute_decode]. eapply dut_decode_mux_eval.
   + intros inner. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction (Nat.sub 48 (S n)) ltac:(lia) Steps Instruction time); lia.
   + intro inner. apply dut_decode_constant.
   + intro inner. exact Previous.
   + apply dut_decode_constant_type.
   + unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Previous. reflexivity.
   + apply size_from_N.
   + exact (load_execute_decode_size which (to_N instruction) (S n)).
Qed.
Theorem load_execute_wire_step which outer invalid old current result word :
 (which < 4)%coq_nat -> size word = load_execute_width which ->
 VM.find (load_execute_wire_source which outer) old = Some (Gval (Fuint (load_execute_width which)) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (load_execute_wire_target which outer) result = Some (Gval (Fuint (load_execute_width which)) word).
Proof.
 intros Which Size Source Step.
 eapply declared_wire_checked_value;
 [exact (load_execute_wire_certificate which outer Which)|exact Source|apply dut_decode_adapt;exact Size|exact Step].
Qed.
Theorem load_execute_decode_history inputs path history limit instruction which :
 (which < 4)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (load_execute_wire_target which true) (history time) = Some (Gval (Fuint (load_execute_width which)) (load_execute_decode which (to_N instruction) 49)).
Proof.
 intros Which Steps Front Size time Lower Upper.
 assert (Source : forall i, (i <= limit)%coq_nat -> VM.find 7748 (history i) = Some (Gval (Fuint 32) instruction)).
 { intros i Bound.
   pose proof (joint_update_register_history_same (formal_invalid_policy inputs path) history limit 7748 32
     ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat); vm_compute; reflexivity) Steps) as Hold.
   rewrite (Hold i Bound). rewrite <- (Hold limit ltac:(lia)). exact Front. }
 assert (Instruction : forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)).
 { intros [|[|i]] Bound; try lia.
   eapply decode_input_connection_8249; [|apply dut_decode_adapt; exact Size|apply Steps; lia].
   eapply decode_input_connection_83; [|apply dut_decode_adapt; exact Size|apply Steps; lia]. apply Source; lia. }
 destruct time as [|[|time]]; try lia.
 eapply (load_execute_wire_step which true);[exact Which|apply load_execute_decode_size| |apply Steps;lia].
 change (VM.find (load_execute_wire_target which false) (history (S time)) = Some (Gval (Fuint (load_execute_width which)) (load_execute_decode which (to_N instruction) 49))).
 eapply (load_execute_wire_step which false);[exact Which|apply load_execute_decode_size| |apply Steps;lia].
 assert (Node : load_execute_wire_source which false = load_execute_mux_node which 48).
 { do 4 (destruct which as [|which];[reflexivity|]). lia. }
 rewrite Node.
 exact (load_execute_mux_history inputs path history limit instruction which Which Steps Instruction 48 time ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Theorem load_execute_decode_load which instruction lane : (which < 4)%coq_nat -> (lane < 5)%coq_nat ->
 N.land instruction 28799 = load_type_lane_code lane ->
 load_execute_decode which instruction 49 = from_N (load_execute_width which) (load_execute_expected which).
Proof.
 intros Which Lane Code. cbn [load_execute_decode].
 repeat match goal with |- context[dut_decode_test instruction ?index] =>
 rewrite (load_type_load_guard instruction lane index Lane ltac:(vm_compute;lia) Code) end.
 do 4 (destruct which as [|which];[do 5 (destruct lane as [|lane];[reflexivity|]);lia|]). lia.
Qed.
Theorem load_execute_control_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (lane < 5)%coq_nat -> VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 VM.find 86 (top_environment observed) = Some (Gval (Fuint 1) [::true]) /\
 VM.find 87 (top_environment observed) = Some (Gval (Fuint 1) [::false]) /\
 VM.find 88 (top_environment observed) = Some (Gval (Fuint 3) [::true;false;false]) /\
 VM.find 89 (top_environment observed) = Some (Gval (Fuint 4) [::false;false;false;false]).
Proof.
 intros Observe Legal Lane Instruction Load.
 destruct (observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal
 ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity)) as [front [Size Front]].
 rewrite Instruction in Front. inversion Front;subst front.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (All : forall which, (which < 4)%coq_nat ->
 VM.find (load_execute_wire_target which true) (top_environment observed) =
 Some (Gval (Fuint (load_execute_width which)) (from_N (load_execute_width which) (load_execute_expected which)))).
 { intros which Which.
   pose proof (load_execute_decode_history (generated_observation_input inputs k) nil history 9259 instruction which Which Steps
   ltac:(rewrite Last;exact Instruction) Size 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as E.
   rewrite Last (load_execute_decode_load which (to_N instruction) lane Which Lane Load) in E. exact E. }
 split;[exact (All 0%nat ltac:(lia))|]. split;[exact (All 1%nat ltac:(lia))|].
 split;[exact (All 2%nat ltac:(lia))|exact (All 3%nat ltac:(lia))].
Qed.

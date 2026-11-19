Require Import FormalLocalHistory ConcreteRegisterInitialization JointBoundaryInitialization ReferenceImmediateTypes DUTRedirectDecode CoreSocModel ComparisonNodes LoadExecuteControl LoadImmediateSemantics LoadTypeCorrespondence ReferenceLoadSemantics ReferenceLoadImmediate RFReadPorts RFReadForwarding ALUInputStability ALUOutputTransfer EarlyControlStabilityHistory JointBoundaryRegisters JointUpdateBoundaryHistory FormalDeclaredConnection FormalDeclaredConnectionObservation DataAddressConnectionCertificates DataAddressExpressionCertificates DataAddressPositionCertificate DataAddressSafetyCertificate SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation UIntMuxResultType ScalarSinkTypes ReferenceRedirectSpine.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition load_operand_wire which :VarOrder.T:=nth 0[::1151;1152;1153]which.
Definition load_operand_source which :VarOrder.T:=nth 0[::7821;7823;89]which.
Definition load_operand_width which :nat:=if Nat.eqb which 2 then 4%nat else 32%nat.
Lemma load_operand_wire_value which invalid old current result word :(which<3)%coq_nat ->size word=load_operand_width which ->
 VM.find(load_operand_source which)old=Some(Gval(Fuint(load_operand_width which))word) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find(load_operand_wire which)result=Some(Gval(Fuint(load_operand_width which))word).
Proof. intros Bound Size Source Step.
 destruct which as[|which]. { eapply(declared_connection_value 1226 flat_statements data_address_connection_1151_decl data_address_connection_1151_mid data_address_connection_1151_tail 1151 7821);
 [exact data_address_connection_1151_position|exact data_address_connection_1151_split|exact data_address_connection_1151_straight|exact data_address_connection_1151_mid_safe|exact data_address_connection_1151_tail_safe|exact data_address_connection_1151_nonregister|reflexivity|exact Source|apply dut_decode_adapt;exact Size|exact Step]. }
 destruct which as[|which]. { eapply(declared_connection_value 1227 flat_statements data_address_connection_1152_decl data_address_connection_1152_mid data_address_connection_1152_tail 1152 7823);
 [exact data_address_connection_1152_position|exact data_address_connection_1152_split|exact data_address_connection_1152_straight|exact data_address_connection_1152_mid_safe|exact data_address_connection_1152_tail_safe|exact data_address_connection_1152_nonregister|reflexivity|exact Source|apply dut_decode_adapt;exact Size|exact Step]. }
 destruct which as[|which]. { eapply(declared_connection_value 1228 flat_statements data_address_connection_1153_decl data_address_connection_1153_mid data_address_connection_1153_tail 1153 89);
 [exact data_address_connection_1153_position|exact data_address_connection_1153_split|exact data_address_connection_1153_straight|exact data_address_connection_1153_mid_safe|exact data_address_connection_1153_tail_safe|exact data_address_connection_1153_nonregister|reflexivity|exact Source|apply dut_decode_adapt;exact Size|exact Step]. }
 lia. Qed.
Lemma load_operand_raw_type invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 exists v,VM.find 783 result=Some v /\type_of_val v=Gtyp(Fuint 32).
Proof. intro Step.
 destruct(declared_connection_observation 792 flat_statements data_address_connection_783_decl data_address_connection_783_mid data_address_connection_783_tail 783 952 32 invalid flat_memories old current result data_address_connection_783_position data_address_connection_783_split data_address_connection_783_straight data_address_connection_783_mid_safe data_address_connection_783_tail_safe data_address_connection_783_nonregister (Logic.eq_refl _) Step)as[source[value[Source[Adapt Value]]]].
 exists value;split;[exact Value|eapply adapted_uint_result_type;exact Adapt]. Qed.
Lemma load_operand_forward_type invalid old result alu raw :
 VM.find 7752 old=Some(Gval(Fuint 32)alu) ->VM.find 783 old=Some raw ->type_of_val raw=Gtyp(Fuint 32) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists v,VM.find 7819 result=Some v /\type_of_val v=Gtyp(Fuint 32).
Proof. intros Alu Raw Typed Step.
 destruct(selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe (rf_forward_members true))as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Position Step)as[value Eval].
 assert(Shape:type_of_val value=Gtyp(Fuint 32)).
 { change(type_of_val value=Gtyp(Fuint(maxn 32 32))).
   eapply immediate_mux_type;[eapply immediate_ref;[exact Alu|reflexivity]|eapply immediate_ref;[exact Raw|exact Typed]|exact Eval]. }
 exists value;split;[|exact Shape]. eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact Shape|exact Step].
Qed.
Definition load_operand_condition second : VarOrder.T:=if second then 7822 else 7820.
Definition load_operand_mux second : VarOrder.T:=if second then 7823 else 7821.
Definition load_operand_selected second : VarOrder.T:=if second then 1308 else 7816.
Definition load_operand_other second : VarOrder.T:=if second then 7819 else 7749.
Lemma load_operand_condition_step second invalid old result :
 VM.find(if second then 87 else 86)old=Some(Gval(Fuint 1)[::negb second]) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(load_operand_condition second)result=Some(Gval(Fuint 1)[::negb second]).
Proof. intros Control Step.
 eapply(reference_redirect_ground_step data_address_node_offsets data_address_expected_nodes _ (if second then address_expr_7822 else address_expr_7820));
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe| | |exact Step].
 - destruct second;[apply(List.nth_error_In data_address_expected_nodes 144%nat)|apply(List.nth_error_In data_address_expected_nodes 142%nat)];vm_compute;reflexivity.
 - intro site. destruct second;cbn [address_expr_7822 address_expr_7820 eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Control;reflexivity.
Qed.
Lemma load_operand_mux_step second invalid old result word other :size word=32%nat ->
 VM.find(load_operand_condition second)old=Some(Gval(Fuint 1)[::negb second]) ->
 VM.find(load_operand_selected second)old=Some(Gval(Fuint 32)word) ->
 VM.find(load_operand_other second)old=Some other ->type_of_val other=Gtyp(Fuint 32) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(load_operand_mux second)result=Some(Gval(Fuint 32)word).
Proof. intros Size Control Selected Other Typed Step.
 eapply(reference_redirect_ground_step data_address_node_offsets data_address_expected_nodes _ (if second then address_expr_7823 else address_expr_7821));
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe| | |exact Step].
 - destruct second;[apply(List.nth_error_In data_address_expected_nodes 145%nat)|apply(List.nth_error_In data_address_expected_nodes 143%nat)];vm_compute;reflexivity.
 - intro site. destruct second; [eapply(immediate_selected_mux _ _ _ _ _ _ 32 word other false)|eapply(immediate_selected_mux _ _ _ _ _ _ 32 word other true)];try exact Size;try exact Control;try exact Selected;try exact Other;exact Typed.
Qed.
(* Actual FE load address transfer. *)
Theorem load_operand_inputs_history inputs path history limit instruction lane left :
 (lane<5)%coq_nat ->load_type_is_load instruction lane ->size instruction=32%nat ->size left=32%nat ->
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 7748(history limit)=Some(Gval(Fuint 32)instruction) ->
 (forall t,(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)) ->
 forall time,(100<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1151(history time)=Some(Gval(Fuint 32)left) /\
 VM.find 1152(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction)) /\
 VM.find 1153(history time)=Some(Gval(Fuint 4)[::false;false;false;false]).
Proof.
 intros Lane Load Size LeftSize Boundary Steps Front Left.
 assert(Control:forall which t,(which<4)%coq_nat ->(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(load_execute_wire_target which true)(history t)=Some(Gval(Fuint(load_execute_width which))(from_N(load_execute_width which)(load_execute_expected which)))).
 { intros which t Which Lower Upper. rewrite(load_execute_decode_history inputs path history limit instruction which Which Steps Front Size t Lower Upper) (load_execute_decode_load which (to_N instruction)lane Which Lane Load);reflexivity. }
 assert(Imm:forall t,(68<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1308(history t)=Some(Gval(Fuint 32)(load_i_immediate instruction))).
 { intros t Lower Upper. eapply(load_imm_front_register_history _ history limit 55 instruction Size);[| |exact Steps|exact Lower|exact Upper].
 - pose proof(joint_update_register_history_same _ history limit 7748 32 load_imm_front_member Steps limit (Nat.le_refl _))as Hold. change(VM.find 7748(history limit)=VM.find 7748(history 0%nat))in Hold. rewrite<-Hold;exact Front.
 - intros u L U. exact(Control 2%nat u ltac:(lia)L U). }
 assert(Registers:forall node width,List.In(node,width)joint_boundary_registers ->forall t,(t<=limit)%coq_nat ->exists word,VM.find(N.of_nat node)(history t)=Some(Gval(Fuint width)word)).
 { intros node width Member t Upper. destruct(joint_update_register_history_concrete _ history limit node width Member (Boundary node width Member) Steps t Upper)as[word[W V]]. exists word;exact V. }
 assert(Other:forall second t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find(load_operand_other second)(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros second t Lower Upper. destruct second.
 - destruct t as[|[|t]];try lia. destruct(load_operand_raw_type _ (history t)(history t)(history(S t))(Steps t ltac:(lia)))as[raw[Raw Typed]].
   destruct(Registers 7752%nat 32%nat rf_read_alu_member (S t)ltac:(lia))as[alu Alu].
   exact(load_operand_forward_type _ (history(S t))(history(S(S t)))alu raw Alu Raw Typed (Steps(S t)ltac:(lia))).
 - destruct(Registers 7749%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity) t Upper)as[word Word]. exists(Gval(Fuint 32)word);split;[exact Word|reflexivity]. }
 assert(Condition:forall second t,(56<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(load_operand_condition second)(history t)=Some(Gval(Fuint 1)[::negb second])).
 { intros second [|t] Lower Upper;try lia. apply(load_operand_condition_step second (formal_invalid_policy inputs path) (history t)(history(S t)));[destruct second;[exact(Control 1%nat t ltac:(lia)ltac:(lia)ltac:(lia))|exact(Control 0%nat t ltac:(lia)ltac:(lia)ltac:(lia))]|apply Steps;lia]. }
 assert(Mux:forall second t,(70<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(load_operand_mux second)(history t)=Some(Gval(Fuint 32)(if second then load_i_immediate instruction else left))).
 { intros second [|t] Lower Upper;try lia. destruct(Other second t ltac:(lia)ltac:(lia))as[other[Value Typed]].
 eapply(load_operand_mux_step second _ (history t)(history(S t)) _ other);[destruct second;[exact(load_i_immediate_size instruction Size)|exact LeftSize]|apply Condition;lia|destruct second;[apply Imm;lia|apply Left;lia]|exact Value|exact Typed|apply Steps;lia]. }
 intros [|time] Lower Upper;try lia. split.
 - exact(load_operand_wire_value 0%nat _ (history time)(history time)(history(S time)) left ltac:(lia) LeftSize (Mux false time ltac:(lia)ltac:(lia))(Steps time ltac:(lia))).
 - split.
 + exact(load_operand_wire_value 1%nat _ (history time)(history time)(history(S time))(load_i_immediate instruction)ltac:(lia)(load_i_immediate_size instruction Size)(Mux true time ltac:(lia)ltac:(lia))(Steps time ltac:(lia))).
 + exact(load_operand_wire_value 2%nat _ (history time)(history time)(history(S time))[::false;false;false;false]ltac:(lia)(Logic.eq_refl _)(Control 3%nat time ltac:(lia)ltac:(lia)ltac:(lia))(Steps time ltac:(lia))).
Qed.
Require Import ObservedJointRegisterConcrete.
Theorem load_effective_address_commit memory inputs k observed next instruction lane left :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<5)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->load_type_is_load instruction lane ->
 size left=32%nat ->VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(reference_load_address left(load_i_immediate instruction))).
Proof.
 intros Observe Legal Next Reset Lane Instruction Load LeftSize Left.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 assert(Forward:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)).
 { intros t Lower Upper. rewrite(early_control_stable_7816_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 pose proof(load_operand_inputs_history (generated_observation_input inputs k)nil history 9259 instruction lane left Lane Load Size LeftSize Boundary Steps ltac:(rewrite Last;exact Instruction)Forward)as Inputs.
 apply(Transfer left(load_i_immediate instruction)(load_i_immediate_size instruction Size)).
 - exact(proj1(proj2(Inputs 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj2(proj2(Inputs 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(proj2(Inputs 9252%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(Inputs 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))).
 - exact(proj2(proj2(Inputs 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
Qed.
Require Import RFEffectState RFWriteEffect RFArchitecturalNormalRelation RFReferenceNopHistory.
Theorem load_effective_address_forwarded memory inputs k observed next instruction lane bank reference destination enabled low high alu_data write_data :
 let index:=to_nat(rf_instruction_address false instruction) in
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<5)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->load_type_is_load instruction lane ->
 rf_dut_bank_at(top_environment observed)bank ->rf_reference_bank_at(top_environment observed)reference ->
 VM.find 7805(top_environment observed)=Some(Gval(Fuint 5)destination) ->VM.find 7757(top_environment observed)=Some(Gval(Fuint 1)[::enabled]) ->
 VM.find 7756(top_environment observed)=Some(Gval(Fuint 2)[::low;high]) ->size alu_data=32%nat ->VM.find 7752(top_environment observed)=Some(Gval(Fuint 32)alu_data) ->
 size write_data=32%nat ->bank index=rf_apply_effect reference RFNoWrite index ->((~~low && ~~high)=true ->alu_data=write_data) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(reference_load_address (rf_apply_effect reference(if enabled then RFWrite(to_nat destination)write_data else RFNoWrite)index)(load_i_immediate instruction))).
Proof.
 cbn zeta. intros Observe Legal Next Reset Lane Instruction Load Bank Reference Destination Enabled Mode AluSize Alu WriteSize Paired AluData.
 assert(Size:size instruction=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[W V]]. rewrite Instruction in V;inversion V;subst;exact W. }
 assert(Index:(to_nat(rf_instruction_address false instruction)<32)%coq_nat).
 { pose proof(to_nat_bounded(rf_instruction_address false instruction))as B. rewrite(rf_instruction_address_size false instruction Size)in B. exact(elimT ltP B). }
 eapply(load_effective_address_commit memory inputs k observed next instruction lane);[exact Observe|exact Legal|exact Next|exact Reset|exact Lane|exact Instruction|exact Load| |].
 - apply rf_apply_effect_size;[exact(proj1(Reference _ Index))|destruct enabled;[exact WriteSize|exact I]].
 - exact(rf_actual_forwarding_observed memory inputs k observed false bank reference instruction destination enabled low high alu_data write_data Observe Legal Bank Size Instruction Destination Enabled Mode AluSize Alu Paired AluData).
Qed.

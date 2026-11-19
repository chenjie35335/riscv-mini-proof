"""Reuse the checked actual connections for the three ALU input wires."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
s='''Require Import FormalLocalHistory ConcreteRegisterInitialization JointBoundaryInitialization ReferenceImmediateTypes DUTRedirectDecode CoreSocModel ComparisonNodes LoadExecuteControl LoadImmediateSemantics LoadTypeCorrespondence ReferenceLoadSemantics ReferenceLoadImmediate RFReadPorts RFReadForwarding ALUInputStability ALUOutputTransfer EarlyControlStabilityHistory JointBoundaryRegisters JointUpdateBoundaryHistory FormalDeclaredConnection FormalDeclaredConnectionObservation DataAddressConnectionCertificates DataAddressExpressionCertificates DataAddressPositionCertificate DataAddressSafetyCertificate SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation UIntMuxResultType ScalarSinkTypes ReferenceRedirectSpine.
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
'''
for n,source,pos in [(1151,7821,1226),(1152,7823,1227),(1153,89,1228)]:
 s+=f''' destruct which as[|which]. {{ eapply(declared_connection_value {pos} flat_statements data_address_connection_{n}_decl data_address_connection_{n}_mid data_address_connection_{n}_tail {n} {source});
 [exact data_address_connection_{n}_position|exact data_address_connection_{n}_split|exact data_address_connection_{n}_straight|exact data_address_connection_{n}_mid_safe|exact data_address_connection_{n}_tail_safe|exact data_address_connection_{n}_nonregister|reflexivity|exact Source|apply dut_decode_adapt;exact Size|exact Step]. }}
'''
s+=' lia. Qed.\n'
s+=r'''Lemma load_operand_raw_type invalid old current result :
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
'''
p=base/'LoadEffectiveAddress.v';mark='(* Actual FE load address transfer. *)';tail=p.read_text().split(mark,1)[1] if p.exists()and mark in p.read_text()else'\n';p.write_text(s+mark+tail)

Require Import CoreSocModel ComparisonNodes LoadEffectiveAddress ReferenceLoadImmediate ReferenceRedirectSpine DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition alu_operand_yes second :VarOrder.T:=if second then 7819 else 7816.
Definition alu_operand_no second :VarOrder.T:=if second then 1308 else 7749.
Lemma alu_operand_condition_step second bit invalid old result :
 VM.find(if second then 87 else 86)old=Some(Gval(Fuint 1)[::bit]) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(load_operand_condition second)result=Some(Gval(Fuint 1)[::bit]).
Proof. intros Control Step.
 eapply(reference_redirect_ground_step data_address_node_offsets data_address_expected_nodes _ (if second then address_expr_7822 else address_expr_7820));
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe| | |exact Step].
 - destruct second;[apply(List.nth_error_In data_address_expected_nodes 144%nat)|apply(List.nth_error_In data_address_expected_nodes 142%nat)];vm_compute;reflexivity.
 - intro site. destruct second;cbn [address_expr_7822 address_expr_7820 eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Control;destruct bit;reflexivity.
Qed.
Lemma alu_operand_mux_step second bit invalid old result word other :size word=32%nat ->
 VM.find(load_operand_condition second)old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find(if bit then alu_operand_yes second else alu_operand_no second)old=Some(Gval(Fuint 32)word) ->
 VM.find(if bit then alu_operand_no second else alu_operand_yes second)old=Some other ->type_of_val other=Gtyp(Fuint 32) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(load_operand_mux second)result=Some(Gval(Fuint 32)word).
Proof. intros Size Control Selected Other Typed Step.
 eapply(reference_redirect_ground_step data_address_node_offsets data_address_expected_nodes _ (if second then address_expr_7823 else address_expr_7821));
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe| | |exact Step].
 - destruct second;[apply(List.nth_error_In data_address_expected_nodes 145%nat)|apply(List.nth_error_In data_address_expected_nodes 143%nat)];vm_compute;reflexivity.
 - intro site. destruct second; eapply(immediate_selected_mux _ _ _ _ _ _ 32 word other bit);try exact Size;try exact Control;try exact Selected;try exact Other;exact Typed.
Qed.
Theorem alu_operand_selected_history invalid history limit start choose word :
 size word=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall second,
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(if second then 87 else 86)(history t)=Some(Gval(Fuint 1)[::choose])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(if choose then alu_operand_yes second else alu_operand_no second)(history t)=Some(Gval(Fuint 32)word)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find(if choose then alu_operand_no second else alu_operand_yes second)(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 forall time,(Nat.add start 3<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find(if second then 1152 else 1151)(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Steps second Control Selected Other [|[|[|time]]] Lower Upper;try lia.
 pose proof(alu_operand_condition_step second choose invalid(history time)(history(S time))(Control time ltac:(lia)ltac:(lia))(Steps time ltac:(lia)))as Cond.
 destruct(Other(S time)ltac:(lia)ltac:(lia))as[other[Lookup Typed]].
 pose proof(alu_operand_mux_step second choose invalid(history(S time))(history(S(S time)))word other Size Cond(Selected(S time)ltac:(lia)ltac:(lia))Lookup Typed(Steps(S time)ltac:(lia)))as Mux.
 destruct second;[exact(load_operand_wire_value 1%nat invalid _ _ _ word ltac:(lia)Size Mux(Steps(S(S time))ltac:(lia)))|exact(load_operand_wire_value 0%nat invalid _ _ _ word ltac:(lia)Size Mux(Steps(S(S time))ltac:(lia)))].
Qed.
Require Import FormalDeclaredConnectionObservation DataAddressConnectionCertificates ScalarSinkTypes.
Lemma alu_immediate_wire_type invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 exists v,VM.find 1308 result=Some v /\type_of_val v=Gtyp(Fuint 32).
Proof. intro Step.
 destruct(declared_connection_observation 1385 flat_statements data_address_connection_1308_decl data_address_connection_1308_mid data_address_connection_1308_tail 1308 1354 32 invalid flat_memories old current result data_address_connection_1308_position data_address_connection_1308_split data_address_connection_1308_straight data_address_connection_1308_mid_safe data_address_connection_1308_tail_safe data_address_connection_1308_nonregister (Logic.eq_refl _) Step)as[source[value[Source[Adapt Value]]]].
 exists value;split;[exact Value|eapply adapted_uint_result_type;exact Adapt].
Qed.

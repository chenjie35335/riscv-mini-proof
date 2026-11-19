Require Import CoreSocModel ComparisonNodes ALUOperandTransfer LoadEffectiveAddress JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization RFReadPorts.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem memory_address_inputs_history inputs path history limit start left immediate :
 size left=32%nat ->size immediate=32%nat ->(2<=start)%coq_nat ->
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 86(history t)=Some(Gval(Fuint 1)[::true]) /\VM.find 87(history t)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 89(history t)=Some(Gval(Fuint 4)[::false;false;false;false]) /\
 VM.find 7816(history t)=Some(Gval(Fuint 32)left) /\VM.find 1308(history t)=Some(Gval(Fuint 32)immediate)) ->
 forall time,(Nat.add start 3<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1151(history time)=Some(Gval(Fuint 32)left) /\VM.find 1152(history time)=Some(Gval(Fuint 32)immediate) /\VM.find 1153(history time)=Some(Gval(Fuint 4)[::false;false;false;false]).
Proof.
 intros LeftSize ImmSize Start Boundary Steps Inputs time Lower Upper.
 assert(Registers:forall node width,List.In(node,width)joint_boundary_registers ->forall t,(t<=limit)%coq_nat ->exists word,VM.find(N.of_nat node)(history t)=Some(Gval(Fuint width)word)).
 { intros node width Member t Bound. destruct(joint_update_register_history_concrete _ history limit node width Member (Boundary node width Member) Steps t Bound)as[word[W V]]. exists word;exact V. }
 assert(Other:forall second t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find(load_operand_other second)(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros second t Lo Hi. destruct second.
 - destruct t as[|[|t]];try lia. destruct(load_operand_raw_type _ (history t)(history t)(history(S t))(Steps t ltac:(lia)))as[raw[Raw Typed]].
   destruct(Registers 7752%nat 32%nat rf_read_alu_member (S t)ltac:(lia))as[alu Alu].
   exact(load_operand_forward_type _ (history(S t))(history(S(S t)))alu raw Alu Raw Typed(Steps(S t)ltac:(lia))).
 - destruct(Registers 7749%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity)t Hi)as[word Word]. exists(Gval(Fuint 32)word);split;[exact Word|reflexivity]. }
 split.
 - eapply(alu_operand_selected_history _ history limit start true left LeftSize Steps false);[| |exact(Other false)|exact Lower|exact Upper].
 + intros t Lo Hi;exact(proj1(Inputs t Lo Hi)).
 + intros t Lo Hi;exact(proj1(proj2(proj2(proj2(Inputs t Lo Hi))))).
 - split.
 + eapply(alu_operand_selected_history _ history limit start false immediate ImmSize Steps true);[| |exact(Other true)|exact Lower|exact Upper].
 * intros t Lo Hi;exact(proj1(proj2(Inputs t Lo Hi))).
 * intros t Lo Hi;exact(proj2(proj2(proj2(proj2(Inputs t Lo Hi))))).
 + destruct time as[|time];[lia|]. exact(load_operand_wire_value 2%nat _ (history time)(history time)(history(S time))[::false;false;false;false]ltac:(lia)(Logic.eq_refl _)(proj1(proj2(proj2(Inputs time ltac:(lia)ltac:(lia)))))(Steps time ltac:(lia))).
Qed.
Require Import ALUInputStability ALUOutputTransfer FormalLocalHistory.
Theorem memory_effective_address_commit_observed memory inputs k observed next left immediate :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 size left=32%nat ->size immediate=32%nat ->
 VM.find 86(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->VM.find 87(top_environment observed)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 89(top_environment observed)=Some(Gval(Fuint 4)[::false;false;false;false]) ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->VM.find 1308(top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(ReferenceLoadSemantics.reference_load_address left immediate)).
Proof.
 intros Observe Legal Next Reset LeftSize ImmSize A B Mode Left Imm.
 destruct(alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 assert(Root:forall node value t,List.In node alu_stability_roots ->VM.find(N.of_nat node)(top_environment observed)=Some value ->(128<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find(N.of_nat node)(history t)=Some value).
 { intros node value t Member Value Lower Upper.
 rewrite(proj2(alu_stability_roots_history (generated_observation_input inputs k)nil history 9259 Boundary Steps node Member t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia)))Last;exact Value. }
 assert(Inputs:forall t,(128<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 86(history t)=Some(Gval(Fuint 1)[::true]) /\VM.find 87(history t)=Some(Gval(Fuint 1)[::false]) /\VM.find 89(history t)=Some(Gval(Fuint 4)[::false;false;false;false]) /\VM.find 7816(history t)=Some(Gval(Fuint 32)left) /\VM.find 1308(history t)=Some(Gval(Fuint 32)immediate)).
 { intros t Lower Upper. split;[exact(Root 86%nat _ t ltac:(cbn;tauto)A Lower Upper)|].
 split;[exact(Root 87%nat _ t ltac:(cbn;tauto)B Lower Upper)|].
 split;[exact(Root 89%nat _ t ltac:(cbn;tauto)Mode Lower Upper)|].
 split;[exact(Root 7816%nat _ t ltac:(cbn;tauto)Left Lower Upper)|].
 exact(alu_stable_value_at (generated_observation_input inputs k)nil history 1308 _ t Boundary Steps ltac:(cbn;tauto)Lower Upper ltac:(rewrite Last;exact Imm)). }
 pose proof(memory_address_inputs_history (generated_observation_input inputs k)nil history 9259 128 left immediate LeftSize ImmSize ltac:(lia)Boundary Steps Inputs)as Values.
 apply(Transfer left immediate ImmSize).
 - exact(proj1(proj2(Values 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj2(proj2(Values 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(proj2(Values 9252%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(Values 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))).
 - exact(proj2(proj2(Values 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
Qed.

Require Import StoreRequestDataObserved StoreEffectiveAddress StoreExecuteControl StoreTypeCorrespondence ReferenceStoreParts MemoryAddressInputs ALUInputStability FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete ObservedRFPortsConcrete JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization CoreSocModel ComparisonNodes ReferenceLoadSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem memory_effective_address_sum_observed memory inputs k observed left immediate :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 size left=32%nat ->size immediate=32%nat ->
 VM.find 86(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->VM.find 87(top_environment observed)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 89(top_environment observed)=Some(Gval(Fuint 4)[::false;false;false;false]) ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->VM.find 1308(top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find 1155(top_environment observed)=Some(Gval(Fuint 32)(reference_load_address left immediate)).
Proof.
 intros Observe Legal LeftSize ImmSize A B Mode Left Imm.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member.
 destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[bits[BitsSize Value]].
 exists bits. split;[exact BitsSize|].
 rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)).
 rewrite Last. exact Value. }
 assert(Root:forall node value t,List.In node alu_stability_roots ->VM.find(N.of_nat node)(top_environment observed)=Some value ->(128<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find(N.of_nat node)(history t)=Some value).
 { intros node value t Member Value Lower Upper.
 rewrite(proj2(alu_stability_roots_history (generated_observation_input inputs k)nil history 9259 Boundary Steps node Member t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia)))Last;exact Value. }
 assert(Inputs:forall t,(128<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 86(history t)=Some(Gval(Fuint 1)[::true]) /\VM.find 87(history t)=Some(Gval(Fuint 1)[::false]) /\VM.find 89(history t)=Some(Gval(Fuint 4)[::false;false;false;false]) /\VM.find 7816(history t)=Some(Gval(Fuint 32)left) /\VM.find 1308(history t)=Some(Gval(Fuint 32)immediate)).
 { intros t Lower Upper. split;[exact(Root 86%nat _ t ltac:(unfold alu_stability_roots;left;reflexivity)A Lower Upper)|].
 split;[exact(Root 87%nat _ t ltac:(unfold alu_stability_roots;do 1 right;left;reflexivity)B Lower Upper)|].
 split;[exact(Root 89%nat _ t ltac:(unfold alu_stability_roots;do 3 right;left;reflexivity)Mode Lower Upper)|].
 split;[exact(Root 7816%nat _ t ltac:(unfold alu_stability_roots;do 6 right;left;reflexivity)Left Lower Upper)|].
 exact(alu_stable_value_at (generated_observation_input inputs k)nil history 1308 _ t Boundary Steps ltac:(unfold alu_stability_targets;do 5 right;left;reflexivity)Lower Upper ltac:(rewrite Last;exact Imm)). }
 pose proof(memory_address_inputs_history (generated_observation_input inputs k)nil history 9259 128 left immediate LeftSize ImmSize ltac:(lia)Boundary Steps Inputs)as Values.
 pose proof(Values 9259%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))as[OperandLeft[OperandRight OperandMode]].
 pose proof(alu_sum_to_taken_history (generated_observation_input inputs k)nil history left immediate Boundary Steps ImmSize OperandLeft OperandRight OperandMode)as Sum.
 rewrite(proj2(alu_inputs_stable_history (generated_observation_input inputs k)nil history 9259 Boundary Steps 1155 ltac:(unfold alu_stability_targets;do 3 right;left;reflexivity) 9253 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)))Last in Sum.
 exact Sum.
Qed.
Theorem store_address_observed memory inputs k observed instruction lane left :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 1155(top_environment observed)=Some(Gval(Fuint 32)(reference_load_address left(store_s_immediate instruction))).
Proof.
 intros Observe Legal Lane Instruction Store Left.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[insn[IS IV]].
 rewrite Instruction in IV;inversion IV;subst insn.
 destruct(proj1(observed_rf_ports_concrete memory inputs k observed Observe Legal))as[word[WS WV]].
 rewrite Left in WV;inversion WV;subst word.
 destruct(store_execute_control_observed memory inputs k observed instruction lane Observe Legal Lane Instruction Store)as[A[B[Select Mode]]].
 exact(memory_effective_address_sum_observed memory inputs k observed left(store_s_immediate instruction)Observe Legal WS(store_s_immediate_size instruction IS)A B Mode Left
   (store_immediate_dut_observed memory inputs k observed instruction lane Observe Legal Lane Instruction Store)).
Qed.

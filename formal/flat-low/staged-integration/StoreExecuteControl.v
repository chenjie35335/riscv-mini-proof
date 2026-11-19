Require Import CoreSocModel ComparisonNodes LoadExecuteControl StoreTypeCorrespondence DUTRedirectDecode FormalObservedHistory ObservedJointRegisterConcrete FormalLocalHistory JointBoundaryRegisters.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition store_execute_expected which :N:=nth 0[::1;0;2;0]which.
Theorem store_execute_decode_store which instruction lane :(which<4)%coq_nat ->(lane<3)%coq_nat ->
 N.land instruction 28799=store_type_lane_code lane ->
 load_execute_decode which instruction 49=from_N(load_execute_width which)(store_execute_expected which).
Proof.
 intros Which Lane Code. cbn [load_execute_decode].
 repeat match goal with |-context[dut_decode_test instruction ?index]=>rewrite(store_type_store_guard instruction lane index Lane ltac:(vm_compute;lia)Code)end.
 do 4(destruct which as[|which];[do 3(destruct lane as[|lane];[reflexivity|]);lia|]);lia.
Qed.
Theorem store_execute_control_history inputs path history limit instruction lane :
 (lane<3)%coq_nat ->size instruction=32%nat ->store_type_is_store instruction lane ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 7748(history limit)=Some(Gval(Fuint 32)instruction) ->
 forall which time,(which<4)%coq_nat ->(55<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find(load_execute_wire_target which true)(history time)=Some(Gval(Fuint(load_execute_width which))(from_N(load_execute_width which)(store_execute_expected which))).
Proof.
 intros Lane Size Store Steps Front which time Which Lower Upper.
 rewrite(load_execute_decode_history inputs path history limit instruction which Which Steps Front Size time Lower Upper)(store_execute_decode_store which(to_N instruction)lane Which Lane Store);reflexivity.
Qed.
Theorem store_execute_control_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 VM.find 86(top_environment observed)=Some(Gval(Fuint 1)[::true]) /\
 VM.find 87(top_environment observed)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 88(top_environment observed)=Some(Gval(Fuint 3)[::false;true;false]) /\
 VM.find 89(top_environment observed)=Some(Gval(Fuint 4)[::false;false;false;false]).
Proof.
 intros Observe Legal Lane Instruction Store.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[word[Size Word]].
 rewrite Instruction in Word;inversion Word;subst word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 pose proof(store_execute_control_history (generated_observation_input inputs k)nil history 9259 instruction lane Lane Size Store Steps ltac:(rewrite Last;exact Instruction))as Control.
 rewrite<-Last. split;[exact(Control 0%nat 9259%nat ltac:(lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))|].
 split;[exact(Control 1%nat 9259%nat ltac:(lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))|].
 split;[exact(Control 2%nat 9259%nat ltac:(lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))|exact(Control 3%nat 9259%nat ltac:(lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))].
Qed.

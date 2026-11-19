Require Import StagedFlatCircuitIteration RFArchitecturalResetRelation RFArchitecturalNormalRelation RFReferenceNopCycle RFReferenceNopHistory ReferenceBankObservation ReferenceBankGuardedObserved ReferenceBankSelectedData ReferenceBankCycleInputs RFReferenceWriteEffect RFWriteEffect FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Definition reference_bank_concrete_zero env : Prop :=
 exists bank, rf_reference_bank_at env bank /\ bank 0%nat=nseq 32 false.
Theorem reference_bank_run_zero_concrete memory inputs states :
 generated_run memory inputs 0=Some states ->reference_bank_concrete_zero(top_environment states).
Proof.
 intro Run.
 destruct(rf_architectural_run_zero memory inputs states Run)as[env[Env Relation]].
 destruct(rf_storage_x0_run_zero memory inputs states Run)as[zeroenv[ZeroEnv Zero]].
 rewrite Env in ZeroEnv;inversion ZeroEnv;subst zeroenv.
 exists(rf_architectural_bank env). split.
 - unfold top_environment;rewrite Env. exact(proj2(rf_architectural_relation_banks env Relation)).
 - unfold rf_architectural_bank. change(match VM.find 851 env with Some(Gval _ word)=>word|_=>nseq 32 false end=nseq 32 false).
   rewrite Zero;reflexivity.
Qed.
Theorem reference_bank_observed_zero_concrete memory inputs observed :
 generated_observe memory inputs 0=Some observed ->reference_bank_concrete_zero(top_environment observed).
Proof.
 intro Observe. pose proof Observe as Expanded. unfold generated_observe in Expanded.
 destruct(generated_run memory inputs 0)as[states|]eqn:Run;[|discriminate Expanded].
 destruct(reference_bank_run_zero_concrete memory inputs states Run)as[bank[Bank Zero]].
 exists bank;split;[exact(reference_bank_run_observed memory inputs 0 states observed bank Run Observe Bank)|exact Zero].
Qed.
Definition reference_bank_step_inputs env :Prop :=
 ref_bank_guarded_controls env /\ref_write_selected_data_concrete env /\
 VM.find 3221 env=Some(Gval(Fuint 5)(ref_write_destination env)).
Theorem reference_bank_normal_concrete_next memory inputs k observed committed next :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some committed ->generated_observe memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 reference_bank_concrete_zero(top_environment observed) ->reference_bank_step_inputs(top_environment observed) ->
 reference_bank_concrete_zero(top_environment next).
Proof.
 intros Observe Legal Run Next Reset[bank[Bank Zero]][Controls[Data Destination]].
 exists(rf_apply_effect bank(ref_write_effect(top_environment observed)));split.
 - exact(reference_bank_guarded_effect_next memory inputs k observed committed next bank Observe Legal Run Next Reset Bank Zero Controls Data Destination).
 - apply rf_apply_effect_x0.
Qed.
Require Import JointBoundaryRegisters JointBoundaryReachable JointBoundaryInduction JointBoundaryInitialization ConcreteRegisterInitialization FormalObservationCommit ExternalReset RFArchitecturalRelation.
Lemma reference_bank_dut_joint_member index : (index<32)%coq_nat ->
 List.In((Nat.add 851 index),32%nat)joint_boundary_registers.
Proof.
 intro Bound. apply(List.nth_error_In joint_boundary_registers(Nat.add 21 index)).
 do 32(destruct index as[|index];[vm_compute;reflexivity|]);lia.
Qed.
Lemma reference_bank_architectural_concrete env bank :
 joint_registers_concrete env ->rf_reference_bank_at env bank ->rf_architectural_registers_concrete env.
Proof.
 intros Joint Reference node Member.
 assert(Ids:rf_architectural_register_ids=List.flat_map(fun index=>[::Nat.add 851 index;Nat.add 7299 index])(List.seq 0 32))by reflexivity.
 rewrite Ids in Member. apply List.in_flat_map in Member.
 destruct Member as[index[Bound Member]]. apply List.in_seq in Bound.
 cbn in Member. destruct Member as[Equal|[Equal|Impossible]];try contradiction;subst node.
 - exact(Joint _ _ (reference_bank_dut_joint_member index ltac:(lia))).
 - exists(bank index). exact(Reference index ltac:(lia)).
Qed.
Theorem reference_bank_reset_run_next memory inputs k previous next :
 generated_run memory inputs k=Some previous ->generated_legal_trace memory inputs(S k) ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::true]) ->
 reference_bank_concrete_zero(top_environment previous) ->reference_bank_concrete_zero(top_environment next).
Proof.
 intros Run Legal Next Reset[bank[Bank BankZero]].
 pose proof(joint_legal_trace_prefix memory inputs(S k)k Legal(Nat.le_succ_diag_r k))as PriorLegal.
 destruct(joint_boundary_reachable memory inputs k previous Run PriorLegal)as[Joint Storage].
 destruct(rf_storage_x0_reachable memory inputs k previous Run PriorLegal)as[old[Old Zero]].
 assert(Concrete:rf_architectural_registers_concrete old).
 { unfold top_environment in Joint,Bank. rewrite Old in Joint,Bank. exact(reference_bank_architectural_concrete old bank Joint Bank). }
 pose proof Next as Cycle. rewrite generated_run_successor Run in Cycle.
 destruct(rf_architectural_real_reset_cycle _ previous old next Old Concrete Reset Cycle)as[env[Env Relation]].
 destruct(rf_storage_x0_reachable memory inputs(S k)next Next Legal)as[zeroenv[ZeroEnv NextZero]].
 rewrite Env in ZeroEnv;inversion ZeroEnv;subst zeroenv.
 exists(rf_architectural_bank env);split.
 - unfold top_environment;rewrite Env. exact(proj2(rf_architectural_relation_banks env Relation)).
 - unfold rf_architectural_bank. change(match VM.find 851 env with Some(Gval _ word)=>word|_=>nseq 32 false end=nseq 32 false).
   rewrite NextZero;reflexivity.
Qed.
Theorem reference_bank_normal_run_next memory inputs k observed next :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 reference_bank_concrete_zero(top_environment observed) ->reference_bank_step_inputs(top_environment observed) ->
 reference_bank_concrete_zero(top_environment next).
Proof.
 intros Observe Legal Run Reset[bank[Bank Zero]][Controls[Data Destination]].
 rewrite(observation_then_commit memory inputs k observed Observe)in Run.
 destruct(flat_iteration_projection _ observed true next Run)as[before[after[Before[Commit After]]]].
 assert(Top:top_environment observed=before)by(unfold top_environment;rewrite Before;reflexivity).
 exists(rf_apply_effect bank(ref_write_effect(top_environment observed)));split;[|apply rf_apply_effect_x0].
 unfold top_environment;rewrite After.
 apply(reference_bank_guarded_effect_commit memory inputs k observed bank after Observe Legal Reset Bank Zero Controls Data Destination).
 rewrite Top;exact Commit.
Qed.
Require Import ReferenceBankNopObserved FormalInstructionResetConstants.
Definition reference_bank_normal_inputs env :Prop :=
 VM.find 7750 env=Some(Gval(Fuint 32)instruction_nop) \/ reference_bank_step_inputs env.
Theorem reference_bank_normal_or_nop_run_next memory inputs k observed next :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 reference_bank_concrete_zero(top_environment observed) ->reference_bank_normal_inputs(top_environment observed) ->
 reference_bank_concrete_zero(top_environment next).
Proof.
 intros Observe Legal Run Reset Bank[Nop|Inputs].
 - destruct Bank as[bank[Bank Zero]].
   rewrite(observation_then_commit memory inputs k observed Observe)in Run.
   destruct(flat_iteration_projection _ observed true next Run)as[before[after[Before[Commit After]]]].
   assert(Top:top_environment observed=before)by(unfold top_environment;rewrite Before;reflexivity).
   exists bank;split;[|exact Zero]. unfold top_environment;rewrite After.
   apply(reference_bank_nop_observed_commit memory inputs k observed bank after Observe Legal Reset Bank Zero Nop).
   rewrite Top;exact Commit.
 - exact(reference_bank_normal_run_next memory inputs k observed next Observe Legal Run Reset Bank Inputs).
Qed.
Theorem reference_bank_run_reachable_given_inputs memory inputs k states :
 generated_run memory inputs k=Some states ->generated_legal_trace memory inputs k ->
 (forall j observed,(j<k)%coq_nat ->generated_observe memory inputs j=Some observed ->
  VM.find 1(formal_external_inputs(generated_observation_input inputs j))=Some(Gval(Fuint 1)[::false]) ->
  reference_bank_concrete_zero(top_environment observed) ->reference_bank_normal_inputs(top_environment observed)) ->
 reference_bank_concrete_zero(top_environment states).
Proof.
 revert states. induction k as[|k IH];intros states Run Legal Inputs.
 - exact(reference_bank_run_zero_concrete memory inputs states Run).
 - pose proof Run as Expanded. rewrite generated_run_successor in Expanded.
   destruct(generated_run memory inputs k)as[previous|]eqn:Previous;[|discriminate Expanded].
   pose proof(joint_legal_trace_prefix memory inputs(S k)k Legal(Nat.le_succ_diag_r k))as PriorLegal.
   assert(Prior:reference_bank_concrete_zero(top_environment previous)).
   { apply(IH previous(Logic.eq_refl _)PriorLegal). intros j observed Bound Observe Reset Bank. exact(Inputs j observed ltac:(lia)Observe Reset Bank). }
   destruct(legal_observation_reset memory inputs k PriorLegal)as[reset Reset].
   destruct reset.
   + exact(reference_bank_reset_run_next memory inputs k previous states Previous Legal Run Reset Prior).
   + destruct(generated_successful_commit memory inputs k states Run)as[observed[Observe Commit]].
     assert(Bank:reference_bank_concrete_zero(top_environment observed)).
     { destruct Prior as[bank[Bank Zero]]. exists bank;split;[exact(reference_bank_run_observed memory inputs k previous observed bank Previous Observe Bank)|exact Zero]. }
     exact(reference_bank_normal_or_nop_run_next memory inputs k observed states Observe PriorLegal Run Reset Bank(Inputs k observed ltac:(lia)Observe Reset Bank)).
Qed.
Theorem reference_bank_observed_reachable_given_inputs memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (forall j current,(j<k)%coq_nat ->generated_observe memory inputs j=Some current ->
  VM.find 1(formal_external_inputs(generated_observation_input inputs j))=Some(Gval(Fuint 1)[::false]) ->
  reference_bank_concrete_zero(top_environment current) ->reference_bank_normal_inputs(top_environment current)) ->
 reference_bank_concrete_zero(top_environment observed).
Proof.
 intros Observe Legal Inputs. pose proof Observe as Expanded. unfold generated_observe in Expanded.
 destruct(generated_run memory inputs k)as[states|]eqn:Run;[|discriminate Expanded].
 destruct(reference_bank_run_reachable_given_inputs memory inputs k states Run Legal Inputs)as[bank[Bank Zero]].
 exists bank;split;[exact(reference_bank_run_observed memory inputs k states observed bank Run Observe Bank)|exact Zero].
Qed.

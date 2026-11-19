Require Import JointUpdateBoundaryHistory ReferenceLoadImmediate ReferenceStoreParts StoreTypeCorrespondence RFScalarControl ReferenceInstructionDecode ReferenceIllegalObserved CoreSocModel ComparisonNodes ReferenceImmediateTypes ReferenceControlExpressions ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceRedirectSpine ReferenceLoadSemantics MemoryRequestObservedSemantics ReferenceMemoryRequest LoadPipelineClassification LoadImmediateSemantics DUTRedirectDecode LoadTypeCorrespondence FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete ReferenceSystemDecode.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma store_reference_enabled_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 3)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 store_type_is_store instruction lane ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Observe Legal Reset Lane Instruction Store.
 destruct (load_pipeline_late_observed memory inputs k observed Observe Legal) as [bit [Late Nop]].
 destruct bit.
 - specialize (Nop (Logic.eq_refl _)). rewrite Nop in Instruction. inversion Instruction;subst instruction.
   exfalso. exact (store_type_nop_not_store lane Lane Store).
 - exact (reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late).
Qed.
Definition store_upper_decoder n := nth 0%nat [::29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat] n.
Lemma store_upper_guard n : (n < 11)%coq_nat -> load_imm_mux_guard true n = reference_instruction_guard (store_upper_decoder n).
Proof. intro Bound. do 11 (destruct n as [|n];[reflexivity|]);lia. Qed.
Lemma store_upper_decode instruction lane n :
 (lane < 3)%coq_nat -> (n < 11)%coq_nat -> store_type_is_store instruction lane ->
 N.eqb (reference_instruction_code (store_upper_decoder n)) (N.land (to_N instruction) (reference_instruction_mask (store_upper_decoder n))) = Nat.eqb n (Nat.sub 7 lane).
Proof.
 intros Lane Bound Store.
 assert (Row : (Nat.sub 36 lane < 37)%coq_nat) by lia.
 assert (Match : N.land (to_N instruction) (reference_instruction_mask (Nat.sub 36 lane)) = reference_instruction_code (Nat.sub 36 lane)).
 { unfold store_type_is_store in Store. do 3 (destruct lane as [|lane];[exact Store|]);lia. }
 rewrite (rf_reference_decode_onehot instruction (Nat.sub 36 lane) (store_upper_decoder n) Row ltac:(do 11 (destruct n as [|n];[cbn [store_upper_decoder nth];lia|]);lia) Match).
 do 3 (destruct lane as [|lane];[do 11 (destruct n as [|n];[reflexivity|]);lia|]);lia.
Qed.
Theorem reference_store_immediate_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 3)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 store_type_is_store instruction lane ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) (store_s_immediate instruction)).
Proof.
 intros Observe Legal Reset Lane Instruction Load.
 pose proof (store_reference_enabled_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load) as Enabled.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (195 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert (Source : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Lower Upper. exact (memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert (Guards : forall n, (n < load_imm_mux_count true)%coq_nat -> VM.find (load_imm_mux_guard true n) (history 9250%nat) = Some (Gval (Fuint 1) [::Nat.eqb n (Nat.sub 7 lane)])).
 { intros n Bound. cbn [load_imm_mux_count] in Bound. rewrite (store_upper_guard n Bound).
   pose proof (reference_instruction_decode_history (formal_invalid_policy (generated_observation_input inputs k) nil) (fun t => history (Nat.add 9248 t)) 2 instruction (store_upper_decoder n)
      ltac:(do 11 (destruct n as [|n];[cbn [store_upper_decoder nth];lia|]);lia)
      ltac:(intros i I;destruct i as [|[|i]];[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia])
      ltac:(intros i I;destruct i as [|[|[|i]]];[apply Source;vm_compute;lia|apply Source;vm_compute;lia|apply Source;vm_compute;lia|lia])
      2 ltac:(lia) ltac:(lia)) as Decode.
   change (VM.find (reference_instruction_guard (store_upper_decoder n)) (history 9250%nat) = Some (Gval (Fuint 1) [::N.eqb (reference_instruction_code (store_upper_decoder n)) (N.land (to_N instruction) (reference_instruction_mask (store_upper_decoder n)))])) in Decode.
   rewrite (store_upper_decode instruction lane n Lane Bound Load) in Decode. exact Decode. }
 pose proof (reference_store_immediate_history (generated_observation_input inputs k) nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia) ltac:(vm_compute;lia) (Enable 9250%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Guards) as Value.
 rewrite (reference_control_stable_2552_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last in Value. exact Value.
Qed.

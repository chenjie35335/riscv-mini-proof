Require Import CoreSocModel ComparisonNodes FormalLocalHistory ReferencePCStutterCommit ReferencePCResetHistory ExceptionPCSourceRegisters FormalCheckerValidStability FormalReferenceValid.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem reference_pc_disabled_full_history invalid history result bits :
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 size bits = 32%nat ->
 VM.find 7331 (history 9259%nat) = Some (Gval (Fuint 32) bits) ->
 VM.find 1395 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7331 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Steps Resets Size Source Disabled Commit.
 assert (SourceEarly : VM.find 7331 (history 9254%nat) = Some (Gval (Fuint 32) bits)).
 { rewrite (proj2 (exception_pc_sources_history_stable invalid history 9259 9254 Steps ltac:(vm_compute; lia))). exact Source. }
 assert (DisabledEarly : VM.find 1395 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { pose proof (checker_valid_history_stable invalid history 9259 9242 9247 false Steps Resets
   ltac:(vm_compute; lia) ltac:(vm_compute; lia)) as Same.
   change (VM.find 1395 (history 9254%nat) = VM.find 1395 (history 9259%nat)) in Same.
   rewrite Same. exact Disabled. }
 pose proof (reference_valid_after_two invalid (history 9254%nat) (history 9255%nat) (history 9256%nat) false
 DisabledEarly (Steps 9254%nat ltac:(vm_compute; lia)) (Steps 9255%nat ltac:(vm_compute; lia))) as RefDisabled.
 pose proof (reference_pc_reset_after_four invalid (history 9255%nat) (history 9256%nat) (history 9257%nat)
 (history 9258%nat) (history 9259%nat) false
 (Resets 9255%nat ltac:(vm_compute; lia))
 (Steps 9255%nat ltac:(vm_compute; lia)) (Steps 9256%nat ltac:(vm_compute; lia))
 (Steps 9257%nat ltac:(vm_compute; lia)) (Steps 9258%nat ltac:(vm_compute; lia))) as Reset.
 exact (reference_pc_disabled_commit_after_five invalid (history 9254%nat) (history 9255%nat)
 (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) result bits
 Size SourceEarly RefDisabled Reset
 (Steps 9254%nat ltac:(vm_compute; lia)) (Steps 9255%nat ltac:(vm_compute; lia))
 (Steps 9256%nat ltac:(vm_compute; lia)) (Steps 9257%nat ltac:(vm_compute; lia))
 (Steps 9258%nat ltac:(vm_compute; lia)) Commit).
Qed.
Print Assumptions reference_pc_disabled_full_history.

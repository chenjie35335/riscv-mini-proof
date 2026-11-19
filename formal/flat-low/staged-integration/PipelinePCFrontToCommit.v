Require Import CoreSocModel FormalLocalHistory PipelinePCRelation ObservedCommitPCTransfer ObservedLateBubbleTransfer ObservedCheckerBubbleValue ObservedReferencePCStutter.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pipeline_pc_front_to_commit memory inputs k observed next bits :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size bits = 32%nat -> take 2 bits = [::false;false] ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) bits) ->
 VM.find 7749 (top_environment observed) = Some (Gval (Fuint 32) bits) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Size Aligned Reference Front Late Early.
 destruct (observed_checker_bubble_value memory inputs k observed true Observe Legal Reset Late)
 as [ObservedReset Disabled].
 pose proof (observed_reference_pc_disabled_step memory inputs k observed next bits
 Observe Legal Next ObservedReset Disabled Size Reference) as ReferenceNext.
 pose proof (observed_commit_pc_transfer memory inputs k observed next bits
 Observe Legal Next Reset Size Front) as CommitNext.
 pose proof (observed_late_bubble_normal_step memory inputs k observed next false (Gval (Fuint 1) [::true])
 Observe Legal Next Reset Early Late (Logic.eq_refl _)) as LateNext.
 exists bits. split; [exact Size|]. split; [exact Aligned|]. split; [exact ReferenceNext|].
 left. split; assumption.
Qed.
(* Audited separately: PipelinePCFrontToCommitAssumptions.v. *)

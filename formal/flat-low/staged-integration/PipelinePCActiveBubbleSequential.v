Require Import CoreSocModel FormalLocalHistory PipelinePCRelation PipelinePCAdjacentTransfer PipelinePCAdjacentArithmetic ReferencePCSequentialObserved ReferencePCSequentialValues ObservedFrontPCTransfer ObservedLateBubbleTransfer ObservedCheckerBubbleValue ObservedEarlyBubbleClear EarlyBubbleNopReachable PipelineBubbleInstructionInvariant ObservedNopControls StartupLateBubbleInvariant.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top generated_run.
Definition pipeline_commit_fetch_adjacent env : Prop :=
 exists commit fetch, size fetch = 33%nat /\
 VM.find 7751 env = Some (Gval (Fuint 32) commit) /\
 VM.find 7768 env = Some (Gval (Fuint 33) fetch) /\
 pc_adjacent commit (take 32 fetch).
Theorem pipeline_pc_active_bubble_sequential_window memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 reference_pc_sequential_control_window (formal_invalid_policy (generated_observation_input inputs k) nil) (top_environment observed) ->
 pipeline_pc_relation (top_environment observed) ->
 pipeline_commit_fetch_adjacent (top_environment observed) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Window [bits [Size [Aligned [Reference Phase]]]]
 [commit [fetch [FetchSize [Commit [Fetch Adjacent]]]]] Late Early.
 assert (CommitPC : VM.find 7751 (top_environment observed) = Some (Gval (Fuint 32) bits)).
 { destruct Phase as [[Flag Value]|[[Flag Rest]|[Flag Rest]]];
   [exact Value|rewrite Late in Flag; discriminate Flag|rewrite Late in Flag; discriminate Flag]. }
 rewrite CommitPC in Commit. inversion Commit; subst commit.
 pose proof Adjacent as [OldSize [LowSize Numeric]].
 destruct (observed_checker_bubble_value memory inputs k observed false Observe Legal Reset Late) as [Root Valid].
 pose proof (reference_pc_sequential_observed_window memory inputs k observed next bits Observe Legal Next Window Size Reference Valid) as NewReference.
 unfold reference_pc_plus_four in NewReference.
 rewrite (pc_adjacent_sequential_result bits (take 32 fetch) Adjacent) in NewReference.
 pose proof (observed_front_pc_transfer memory inputs k observed next fetch Observe Legal Next Root FetchSize Fetch) as NewFront.
 pose proof (observed_late_bubble_normal_step memory inputs k observed next true (Gval (Fuint 1) [::false])
 Observe Legal Next Reset Early Late (Logic.eq_refl _)) as NewLate.
 pose proof (active_observation_startup_false memory inputs k observed Observe Legal Late) as Started.
 pose proof (early_bubble_nop_all_observations memory inputs k observed Observe Legal Early) as Nop.
 destruct (observed_nop_controls_false memory inputs k observed Observe Legal Nop) as [Kill Branch].
 pose proof (observed_early_bubble_clear_step memory inputs k observed next (Gval (Fuint 1) [::true])
 Observe Legal Next Reset Started Kill Branch Early (Logic.eq_refl _)) as NewEarly.
 exists (take 32 fetch). split; [exact LowSize|].
 split; [exact (pc_adjacent_preserves_alignment bits (take 32 fetch) Adjacent Aligned)|].
 split; [exact NewReference|]. right. left. split; [exact NewLate|]. split; assumption.
Qed.
(* Conditional active case; reachable address adjacency and reference control
   values still need the strengthened architectural invariant. *)

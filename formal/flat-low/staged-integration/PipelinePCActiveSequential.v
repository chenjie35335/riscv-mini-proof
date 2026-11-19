Require Import CoreSocModel FormalLocalHistory PipelinePCRelation PipelinePCAdjacentTransfer PipelinePCAdjacentArithmetic ReferencePCSequentialObserved ReferencePCSequentialValues ObservedCommitPCTransfer ObservedLateBubbleTransfer ObservedCheckerBubbleValue.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pipeline_pc_active_sequential_window memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 reference_pc_sequential_control_window (formal_invalid_policy (generated_observation_input inputs k) nil) (top_environment observed) ->
 pipeline_pc_relation (top_environment observed) ->
 pipeline_commit_front_adjacent (top_environment observed) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Window [bits [Size [Aligned [Reference Phase]]]]
 [commit [front [Commit [Front Adjacent]]]] Late Early.
 assert (CommitPC : VM.find 7751 (top_environment observed) = Some (Gval (Fuint 32) bits)).
 { destruct Phase as [[Flag Value]|[[Flag Rest]|[Flag Rest]]];
   [exact Value|rewrite Late in Flag; discriminate Flag|rewrite Late in Flag; discriminate Flag]. }
 rewrite CommitPC in Commit. inversion Commit; subst commit.
 pose proof Adjacent as [OldSize [FrontSize Numeric]].
 destruct (observed_checker_bubble_value memory inputs k observed false Observe Legal Reset Late) as [Root Valid].
 pose proof (reference_pc_sequential_observed_window memory inputs k observed next bits Observe Legal Next Window Size Reference Valid) as NewReference.
 unfold reference_pc_plus_four in NewReference.
 rewrite (pc_adjacent_sequential_result bits front Adjacent) in NewReference.
 pose proof (observed_commit_pc_transfer memory inputs k observed next front Observe Legal Next Reset FrontSize Front) as NewCommit.
 pose proof (observed_late_bubble_normal_step memory inputs k observed next false (Gval (Fuint 1) [::false])
 Observe Legal Next Reset Early Late (Logic.eq_refl _)) as NewLate.
 exists front. split; [exact FrontSize|]. split; [exact (pc_adjacent_preserves_alignment bits front Adjacent Aligned)|].
 split; [exact NewReference|]. left. split; assumption.
Qed.
(* This is one actual active-step case. Reachable adjacency and the reference
   control window are explicit outstanding premises, not new design assumes. *)

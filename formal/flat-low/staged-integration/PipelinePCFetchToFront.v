Require Import CoreSocModel FormalLocalHistory PipelinePCRelation ObservedFrontPCTransfer ObservedEarlyBubbleClear ObservedLateBubbleTransfer ObservedCheckerBubbleValue ObservedReferencePCStutter.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pipeline_pc_fetch_to_front_controlled memory inputs k observed next fetch :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size fetch = 33%nat -> take 2 (take 32 fetch) = [::false;false] ->
 VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) fetch) ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) (take 32 fetch)) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7762 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 85 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1360 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Size Aligned Fetch Reference Late Early Started Kill Branch.
 assert (LowSize : size (take 32 fetch) = 32%nat) by (rewrite size_take Size; reflexivity).
 destruct (observed_checker_bubble_value memory inputs k observed true Observe Legal Reset Late)
 as [ObservedReset Disabled].
 pose proof (observed_reference_pc_disabled_step memory inputs k observed next (take 32 fetch)
 Observe Legal Next ObservedReset Disabled LowSize Reference) as ReferenceNext.
 pose proof (observed_front_pc_transfer memory inputs k observed next fetch
 Observe Legal Next ObservedReset Size Fetch) as FrontNext.
 pose proof (observed_late_bubble_normal_step memory inputs k observed next true (Gval (Fuint 1) [::true])
 Observe Legal Next Reset Early Late (Logic.eq_refl _)) as LateNext.
 pose proof (observed_early_bubble_clear_step memory inputs k observed next (Gval (Fuint 1) [::true])
 Observe Legal Next Reset Started Kill Branch Early (Logic.eq_refl _)) as EarlyNext.
 exists (take 32 fetch). split; [exact LowSize|]. split; [exact Aligned|]. split; [exact ReferenceNext|].
 right. left. split; [exact LateNext|]. split; assumption.
Qed.
(* Independent transitive assumption audit follows after NOP controls are discharged. *)

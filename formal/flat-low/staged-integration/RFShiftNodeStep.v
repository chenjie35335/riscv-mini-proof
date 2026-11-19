Require Import RFShiftNodes ReferenceRedirectSpine CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_shift_node_step node expr invalid old current result ground bits :
 List.In(node,expr)rf_shift_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step.
 eapply(reference_redirect_ground_step rf_shift_offsets rf_shift_nodes node expr);
 [exact rf_shift_positions|exact rf_shift_safety|exact Member|exact Eval|exact Step].
Qed.

Require Import CoreSocModel ComparisonNodes FormalPCAddressConnections FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma pc_extract_connection_ground invalid old current result ground pc :
 VM.find 7781 old = Some (Gval ground pc) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find 71 result = Some (Gval (Fuint 32) word).
Proof.
 intros PC Step.
 destruct (pc_71_observation invalid old current result Step) as [source [value [Source [Adapt Value]]]].
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Source. rewrite PC in Source.
 destruct ground; cbn [eval_unop] in Source; try discriminate Source;

 match type of Source with context [if ?b then _ else _] => destruct b eqn:Bound end; try discriminate Source;
 inversion Source; subst source; cbn [adapt_hvalue_as_type] in Adapt; inversion Adapt; subst value;
 eexists; exact Value.
Qed.
Theorem pc_address_ground_after_two invalid s0 s1 s2 ground pc :
 VM.find 7781 s0 = Some (Gval ground pc) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 exists word, VM.find 30 s2 = Some (Gval (Fuint 32) word).
Proof.
 intros PC First Second.
 destruct (pc_extract_connection_ground invalid s0 s0 s1 ground pc PC First) as [bits Bits].
 eexists. eapply (pc_30_connection invalid s1 s1 s2 (Gval (Fuint 32) bits));
 [exact Bits|reflexivity|exact Second].
Qed.
Print Assumptions pc_address_ground_after_two.

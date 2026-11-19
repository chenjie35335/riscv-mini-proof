Require Import RegisterInvariants ScalarNodeFrames ScalarSinkTypes FormalTypedNodeFrames FormalStatementSegments.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma formal_uint_observation invalid site mm phase node rhs old current result previous width :
 VM.find node current = Some previous -> type_of_val previous = Gtyp (Fuint width) ->
 formal_connect invalid site mm phase (@Eid VarOrder.T node) rhs old current = Some result ->
 exists source value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site mm rhs old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint width)) = Some value /\ VM.find node result = Some value.
Proof.
 intros Lookup Typed Step.
 unfold formal_connect, formal_connect_bundle in Step.
 cbn [HiF.base_ref eval_type_of_ref] in Step.
 rewrite Lookup in Step. cbn [option_map] in Step. rewrite Typed in Step.
 destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid) site mm rhs old old) as [source|] eqn:Source; [|discriminate Step].
 destruct (adapt_hvalue_as_type source (Gtyp (Fuint width))) as [value|] eqn:Adapt; [|discriminate Step].
 cbn [repl_val_part option_map] in Step. inversion Step; subst result.
 exists source, value. split; [reflexivity|]. split; [exact Adapt|].
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.

Require Import ScalarNodeFrames ScalarSinkTypes RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem bidirectional_uint_sink_observation mm node rhs old current result previous width :
 node != HiF.base_ref rhs ->
 VM.find node current = Some previous ->
 type_of_val previous = Gtyp (Fuint width) ->
 bidirectional_connect_with_memory mm (@Eid VarOrder.T node) rhs old current = Some result ->
 exists source value, eval_href_with_memory mm rhs old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint width)) = Some value /\ VM.find node result = Some value.
Proof.
 move/negP => Different. intros Lookup Typed Step.
 unfold bidirectional_connect_with_memory in Step.
 cbn [HiF.base_ref eval_type_of_ref] in Step.
 rewrite Lookup in Step. cbn [option_map] in Step. rewrite Typed in Step.
 destruct (eval_href_with_memory mm rhs old old) as [source|] eqn:Source; [|discriminate Step].
 destruct (adapt_hvalue_as_type source (Gtyp (Fuint width))) as [adapted|] eqn:Adapt;
   [|discriminate Step].
 pose proof (adapted_uint_is_passive source width adapted Adapt) as Passive.
 cbn [repl_val_part] in Step.
 rewrite (passive_sink_replaced previous adapted Passive) in Step.
 cbn [option_map] in Step.
 destruct (VM.find (HiF.base_ref rhs) (VM.add node adapted current)); [|discriminate Step].
 destruct (eval_type_of_ref rhs (VM.add node adapted current)); [|discriminate Step].
 destruct (eval_href_with_memory mm (Eid node) old old); [|discriminate Step].
 match type of Step with context [adapt_hvalue_as_type ?v ?t] => destruct (adapt_hvalue_as_type v t) end; [|discriminate Step].
 destruct (repl_val_part rhs _ _ _ _); [|discriminate Step].
 inversion Step; subst result. exists source, adapted. split; [reflexivity|]. split; [exact Adapt|].
 rewrite (RegisterMapFacts.find_add_neq Different).
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.


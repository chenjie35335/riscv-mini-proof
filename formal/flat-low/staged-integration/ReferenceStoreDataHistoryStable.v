Require Import ReferenceStoreRequestObserved ReferenceStoreRequestData CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_store_data_history_stable invalid history limit guards word :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2804(history t)=Some(Gval(Fuint 32)word)) ->
 (forall node t,List.In node reference_store_request_data_guards ->(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::guards node])) ->
 forall t u,(211<=t)%coq_nat ->(t<=limit)%coq_nat ->(211<=u)%coq_nat ->(u<=limit)%coq_nat ->
 VM.find 1526(history t)=VM.find 1526(history u).
Proof.
 intros Steps Source Guards.
 assert(Value:forall t,(211<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 1526(history t)=Some(Gval(Fuint 32)(reference_store_request_word guards word))).
 { intros t Lower Upper.
 eapply(reference_store_request_alias_history _ history limit 208);[apply reference_store_request_word_size|exact Steps| |exact Lower|exact Upper].
 intros i Lo Hi. exact(reference_store_request_data_history _ history limit 200 guards word Steps Source Guards i Lo Hi). }
 intros t u LT UT LU UU. rewrite(Value t LT UT)(Value u LU UU). reflexivity.
Qed.

Require Import ReferenceControlStabilityHistory.
Theorem reference_store_data_stable_from_last inputs path history limit reset guards word :
 (200<=limit)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 2804(history limit)=Some(Gval(Fuint 32)word) ->
 (forall node,List.In node reference_store_request_data_guards ->VM.find node(history limit)=Some(Gval(Fuint 1)[::guards node])) ->
 forall t u,(211<=t)%coq_nat ->(t<=limit)%coq_nat ->(211<=u)%coq_nat ->(u<=limit)%coq_nat ->
 VM.find 1526(history t)=VM.find 1526(history u).
Proof.
 intros Limit Resets Steps Source Guards.
 apply(reference_store_data_history_stable _ history limit guards word Steps).
 - intros t Lower Upper.
   rewrite(reference_control_stable_2804_history inputs path history limit reset Resets Steps t limit ltac:(lia)ltac:(lia)Upper ltac:(lia)). exact Source.
 - intros node t Member Lower Upper.
   assert(Same:VM.find node(history t)=VM.find node(history limit)).
   { cbn[reference_store_request_data_guards List.In]in Member.
     repeat destruct Member as[<-|Member];try contradiction.
     - apply(reference_control_stable_1951_history inputs path history limit reset Resets Steps t limit);lia.
     - apply(reference_control_stable_2723_history inputs path history limit reset Resets Steps t limit);lia.
     - apply(reference_control_stable_1946_history inputs path history limit reset Resets Steps t limit);lia.
     - apply(reference_control_stable_2708_history inputs path history limit reset Resets Steps t limit);lia.
     - apply(reference_control_stable_1941_history inputs path history limit reset Resets Steps t limit);lia.
     - apply(reference_control_stable_1707_history inputs path history limit reset Resets Steps t limit);lia.
   }
   rewrite Same. apply Guards;exact Member.
Qed.

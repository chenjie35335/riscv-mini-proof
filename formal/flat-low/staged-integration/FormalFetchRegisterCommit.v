Require Import FormalTypedNodeEquation FormalDeclaredConnection FormalRegisterReferenceObservation FormalRegisterCommitIdentity RegisterCommitCertificate ScalarNodeFrames CoreSocModel ComparisonNodes FormalStatementSegments FormalTypedNodeFrames.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition fetch_register_reg := @mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 0)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 9220))).
Definition fetch_register_reference := @Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 4.
Definition fetch_register_declared := match straight_drop 10050 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition fetch_register_middle := take_statements 74 fetch_register_declared.
Definition fetch_register_tail := match straight_drop 10125 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma fetch_register_position : straight_drop 10049 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 9220 fetch_register_reg) fetch_register_declared).
Proof. vm_compute. reflexivity. Qed.
Lemma fetch_register_split : fetch_register_declared = statement_append fetch_register_middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 9220) (@Eref VarOrder.T fetch_register_reference)) fetch_register_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma fetch_register_straight : straight_statements fetch_register_middle.
Proof. vm_compute. exact I. Qed.
Lemma fetch_register_middle_safe : formal_typed_suffix_safe flat_memories 9220 fetch_register_middle.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma fetch_register_tail_safe : formal_typed_suffix_safe flat_memories 9220 fetch_register_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma fetch_register_identity : register_identity_b 9220 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem fetch_register_formal_commit_source invalid old current result old_value :
 VM.find 9220 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists source value,
 eval_href_with_memory flat_memories fetch_register_reference old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value /\ VM.find 9220 result = Some value.
Proof.
 intros Old Typed Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_reference_observation 10049 flat_statements fetch_register_declared fetch_register_middle fetch_register_tail
 9220 fetch_register_reg fetch_register_reference invalid flat_memories old true current proposed old_value 32
 fetch_register_position fetch_register_split (Logic.eq_refl _) fetch_register_straight fetch_register_middle_safe fetch_register_tail_safe Old Typed Statements)
 as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 rewrite (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result
 9220 fetch_register_identity Step). exact Value.
Qed.
Print Assumptions fetch_register_formal_commit_source.

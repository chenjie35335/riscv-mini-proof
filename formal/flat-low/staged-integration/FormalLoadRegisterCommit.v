Require Import FormalTypedNodeEquation FormalDeclaredConnection FormalRegisterReferenceObservation FormalRegisterCommitIdentity RegisterCommitCertificate ScalarNodeFrames CoreSocModel ComparisonNodes FormalStatementSegments FormalTypedNodeFrames.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition load_register_reg := @mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 0)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 9222))).
Definition load_register_reference := @Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 4.
Definition load_register_declared := match straight_drop 10052 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition load_register_middle := take_statements 73 load_register_declared.
Definition load_register_tail := match straight_drop 10126 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma load_register_position : straight_drop 10051 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 9222 load_register_reg) load_register_declared).
Proof. vm_compute. reflexivity. Qed.
Lemma load_register_split : load_register_declared = statement_append load_register_middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 9222) (@Eref VarOrder.T load_register_reference)) load_register_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma load_register_straight : straight_statements load_register_middle.
Proof. vm_compute. exact I. Qed.
Lemma load_register_middle_safe : formal_typed_suffix_safe flat_memories 9222 load_register_middle.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma load_register_tail_safe : formal_typed_suffix_safe flat_memories 9222 load_register_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma load_register_identity : register_identity_b 9222 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem load_register_formal_commit_source invalid old current result old_value :
 VM.find 9222 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists source value,
 eval_href_with_memory flat_memories load_register_reference old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value /\ VM.find 9222 result = Some value.
Proof.
 intros Old Typed Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_reference_observation 10051 flat_statements load_register_declared load_register_middle load_register_tail
 9222 load_register_reg load_register_reference invalid flat_memories old true current proposed old_value 32
 load_register_position load_register_split (Logic.eq_refl _) load_register_straight load_register_middle_safe load_register_tail_safe Old Typed Statements)
 as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 rewrite (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result
 9222 load_register_identity Step). exact Value.
Qed.
Print Assumptions load_register_formal_commit_source.

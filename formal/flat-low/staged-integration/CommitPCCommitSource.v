Require Import FormalRegisterMuxObservation FormalRegisterCommitIdentity RegisterCommitCertificate ScalarNodeFrames CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition commit_pc_reg := @mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7751))).
Definition commit_pc_cond := @Eref VarOrder.T (@Eid VarOrder.T 65).
Definition commit_pc_yes := @Eref VarOrder.T (@Eid VarOrder.T 8161).
Definition commit_pc_no := @Eref VarOrder.T (@Eid VarOrder.T 7877).
Definition commit_pc_declared := match straight_drop 8258 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition commit_pc_middle := take_statements 595 commit_pc_declared.
Definition commit_pc_tail := match straight_drop 8854 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma commit_pc_position : straight_drop 8257 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7751 commit_pc_reg) commit_pc_declared).
Proof. vm_compute. reflexivity. Qed.
Lemma commit_pc_split : commit_pc_declared = statement_append commit_pc_middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7751) (@Emux VarOrder.T commit_pc_cond commit_pc_yes commit_pc_no)) commit_pc_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma commit_pc_straight : straight_statements commit_pc_middle.
Proof. vm_compute. exact I. Qed.
Lemma commit_pc_middle_safe : formal_typed_suffix_safe flat_memories 7751 commit_pc_middle.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma commit_pc_tail_safe : formal_typed_suffix_safe flat_memories 7751 commit_pc_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma commit_pc_identity : register_identity_b 7751 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem commit_pc_formal_commit_source invalid old current result old_value :
 VM.find 7751 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists source value,
 eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T commit_pc_cond commit_pc_yes commit_pc_no) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value /\ VM.find 7751 result = Some value.
Proof.
 intros Old Typed Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_mux_observation 8257 flat_statements commit_pc_declared commit_pc_middle commit_pc_tail
 7751 commit_pc_reg commit_pc_cond commit_pc_yes commit_pc_no invalid flat_memories old true current proposed old_value 32
 commit_pc_position commit_pc_split commit_pc_straight commit_pc_middle_safe commit_pc_tail_safe Old Typed Statements)
 as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 rewrite (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result
 7751 commit_pc_identity Step). exact Value.
Qed.
Print Assumptions commit_pc_formal_commit_source.

Require Import FormalRegisterMuxObservation FormalRegisterCommitIdentity RegisterCommitCertificate ScalarNodeFrames CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition fetch_pc_reg := @mk_freg VarOrder.T (Gtyp (Fuint 33)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7768))).
Definition fetch_pc_cond := @Eref VarOrder.T (@Eid VarOrder.T 65).
Definition fetch_pc_yes := @Eref VarOrder.T (@Eid VarOrder.T 7767).
Definition fetch_pc_no := @Eref VarOrder.T (@Eid VarOrder.T 7781).
Definition fetch_pc_declared := match straight_drop 8275 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition fetch_pc_middle := take_statements 589 fetch_pc_declared.
Definition fetch_pc_tail := match straight_drop 8865 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma fetch_pc_position : straight_drop 8274 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7768 fetch_pc_reg) fetch_pc_declared).
Proof. vm_compute. reflexivity. Qed.
Lemma fetch_pc_split : fetch_pc_declared = statement_append fetch_pc_middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7768) (@Emux VarOrder.T fetch_pc_cond fetch_pc_yes fetch_pc_no)) fetch_pc_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma fetch_pc_straight : straight_statements fetch_pc_middle.
Proof. vm_compute. exact I. Qed.
Lemma fetch_pc_middle_safe : formal_typed_suffix_safe flat_memories 7768 fetch_pc_middle.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma fetch_pc_tail_safe : formal_typed_suffix_safe flat_memories 7768 fetch_pc_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma fetch_pc_identity : register_identity_b 7768 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem fetch_pc_formal_commit_source invalid old current result old_value :
 VM.find 7768 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 33) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists source value,
 eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T fetch_pc_cond fetch_pc_yes fetch_pc_no) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 33)) = Some value /\ VM.find 7768 result = Some value.
Proof.
 intros Old Typed Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_mux_observation 8274 flat_statements fetch_pc_declared fetch_pc_middle fetch_pc_tail
 7768 fetch_pc_reg fetch_pc_cond fetch_pc_yes fetch_pc_no invalid flat_memories old true current proposed old_value 33
 fetch_pc_position fetch_pc_split fetch_pc_straight fetch_pc_middle_safe fetch_pc_tail_safe Old Typed Statements)
 as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 rewrite (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result
 7768 fetch_pc_identity Step). exact Value.
Qed.
Print Assumptions fetch_pc_formal_commit_source.

Require Import FormalRegisterMuxObservation FormalRegisterCommitIdentity RegisterCommitCertificate ScalarNodeFrames CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_pc_reg := @mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7331))).
Definition reference_pc_cond := @Eref VarOrder.T (@Eid VarOrder.T 1515).
Definition reference_pc_yes := @Eref VarOrder.T (@Eid VarOrder.T 7433).
Definition reference_pc_no := @Eref VarOrder.T (@Eid VarOrder.T 1819).
Definition reference_pc_declared := match straight_drop 7503 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_pc_middle := take_statements 418 reference_pc_declared.
Definition reference_pc_tail := match straight_drop 7922 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_position : straight_drop 7502 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7331 reference_pc_reg) reference_pc_declared).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_split : reference_pc_declared = statement_append reference_pc_middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7331) (@Emux VarOrder.T reference_pc_cond reference_pc_yes reference_pc_no)) reference_pc_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_straight : straight_statements reference_pc_middle.
Proof. vm_compute. exact I. Qed.
Lemma reference_pc_middle_safe : formal_typed_suffix_safe flat_memories 7331 reference_pc_middle.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_tail_safe : formal_typed_suffix_safe flat_memories 7331 reference_pc_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_identity : register_identity_b 7331 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_formal_commit_source invalid old current result old_value :
 VM.find 7331 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists source value,
 eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T reference_pc_cond reference_pc_yes reference_pc_no) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value /\ VM.find 7331 result = Some value.
Proof.
 intros Old Typed Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_mux_observation 7502 flat_statements reference_pc_declared reference_pc_middle reference_pc_tail
 7331 reference_pc_reg reference_pc_cond reference_pc_yes reference_pc_no invalid flat_memories old true current proposed old_value 32
 reference_pc_position reference_pc_split reference_pc_straight reference_pc_middle_safe reference_pc_tail_safe Old Typed Statements)
 as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 rewrite (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result
 7331 reference_pc_identity Step). exact Value.
Qed.
Print Assumptions reference_pc_formal_commit_source.

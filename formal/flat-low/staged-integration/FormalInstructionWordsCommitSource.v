Require Import FormalUIntRegisterCommitSource RegisterCommitCertificate ScalarNodeFrames CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition instruction_7748_reg := @mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7748))).
Definition instruction_7748_cond := @Eref VarOrder.T (@Eid VarOrder.T 65).
Definition instruction_7748_yes := @Eref VarOrder.T (@Eid VarOrder.T 8158).
Definition instruction_7748_no := @Eref VarOrder.T (@Eid VarOrder.T 7801).
Definition instruction_7748_declared := match straight_drop 8255 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition instruction_7748_middle := take_statements 595 instruction_7748_declared.
Definition instruction_7748_tail := match straight_drop 8851 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma instruction_7748_position : straight_drop 8254 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7748 instruction_7748_reg) instruction_7748_declared).
Proof. vm_compute. reflexivity. Qed.
Lemma instruction_7748_split : instruction_7748_declared = statement_append instruction_7748_middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7748) (@Emux VarOrder.T instruction_7748_cond instruction_7748_yes instruction_7748_no)) instruction_7748_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma instruction_7748_straight : straight_statements instruction_7748_middle.
Proof. vm_compute. exact I. Qed.
Lemma instruction_7748_middle_safe : formal_typed_suffix_safe flat_memories 7748 instruction_7748_middle.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma instruction_7748_tail_safe : formal_typed_suffix_safe flat_memories 7748 instruction_7748_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma instruction_7748_identity : register_identity_b 7748 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem instruction_7748_commit_source invalid old current result old_value :
 VM.find 7748 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists source value,
 eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T instruction_7748_cond instruction_7748_yes instruction_7748_no) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value /\ VM.find 7748 result = Some value.
Proof.
 intros Old Typed Step.
 eapply (formal_committed_uint_register_mux_observation 8254 flat_statements instruction_7748_declared instruction_7748_middle instruction_7748_tail
 7748 instruction_7748_reg instruction_7748_cond instruction_7748_yes instruction_7748_no invalid flat_memories old current result old_value 32);
 [exact instruction_7748_position|exact instruction_7748_split|exact instruction_7748_straight|exact instruction_7748_middle_safe|exact instruction_7748_tail_safe|
 exact Old|exact Typed|exact instruction_7748_identity|exact Step].
Qed.
Definition instruction_7750_reg := @mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7750))).
Definition instruction_7750_cond := @Eref VarOrder.T (@Eid VarOrder.T 65).
Definition instruction_7750_yes := @Eref VarOrder.T (@Eid VarOrder.T 8160).
Definition instruction_7750_no := @Eref VarOrder.T (@Eid VarOrder.T 7878).
Definition instruction_7750_declared := match straight_drop 8257 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition instruction_7750_middle := take_statements 595 instruction_7750_declared.
Definition instruction_7750_tail := match straight_drop 8853 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma instruction_7750_position : straight_drop 8256 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7750 instruction_7750_reg) instruction_7750_declared).
Proof. vm_compute. reflexivity. Qed.
Lemma instruction_7750_split : instruction_7750_declared = statement_append instruction_7750_middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7750) (@Emux VarOrder.T instruction_7750_cond instruction_7750_yes instruction_7750_no)) instruction_7750_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma instruction_7750_straight : straight_statements instruction_7750_middle.
Proof. vm_compute. exact I. Qed.
Lemma instruction_7750_middle_safe : formal_typed_suffix_safe flat_memories 7750 instruction_7750_middle.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma instruction_7750_tail_safe : formal_typed_suffix_safe flat_memories 7750 instruction_7750_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma instruction_7750_identity : register_identity_b 7750 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem instruction_7750_commit_source invalid old current result old_value :
 VM.find 7750 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists source value,
 eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T instruction_7750_cond instruction_7750_yes instruction_7750_no) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value /\ VM.find 7750 result = Some value.
Proof.
 intros Old Typed Step.
 eapply (formal_committed_uint_register_mux_observation 8256 flat_statements instruction_7750_declared instruction_7750_middle instruction_7750_tail
 7750 instruction_7750_reg instruction_7750_cond instruction_7750_yes instruction_7750_no invalid flat_memories old current result old_value 32);
 [exact instruction_7750_position|exact instruction_7750_split|exact instruction_7750_straight|exact instruction_7750_middle_safe|exact instruction_7750_tail_safe|
 exact Old|exact Typed|exact instruction_7750_identity|exact Step].
Qed.
Print Assumptions instruction_7750_commit_source.

Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConnectionObservation FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_event_connection_1857_decl := match straight_drop 1937 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_event_connection_1857_tail := match straight_drop 7428 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_event_connection_1857_mid := take_statements 5490 reference_event_connection_1857_decl.
Lemma reference_event_connection_1857_position : straight_drop 1936 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1857 (Gtyp (Fuint 1))) reference_event_connection_1857_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_connection_1857_split : reference_event_connection_1857_decl = statement_append reference_event_connection_1857_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1857) (@Eref VarOrder.T (@Eid VarOrder.T 7202))) reference_event_connection_1857_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_connection_1857_straight : straight_statements reference_event_connection_1857_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_event_connection_1857_mid_safe : formal_typed_suffix_safe flat_memories 1857 reference_event_connection_1857_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_connection_1857_tail_safe : formal_typed_suffix_safe flat_memories 1857 reference_event_connection_1857_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_connection_1857_nonregister : has_register 1857 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_connection_1857_observation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists source_value value, VM.find 7202 old = Some source_value /\
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value /\ VM.find 1857 result = Some value.
Proof.
 intro Step. exact (declared_connection_observation 1936 flat_statements reference_event_connection_1857_decl reference_event_connection_1857_mid reference_event_connection_1857_tail
 1857 7202 1 invalid flat_memories old current result
 reference_event_connection_1857_position reference_event_connection_1857_split reference_event_connection_1857_straight reference_event_connection_1857_mid_safe reference_event_connection_1857_tail_safe reference_event_connection_1857_nonregister
 (Logic.eq_refl _) Step).
Qed.
Theorem reference_event_connection_1857_value invalid old current result source_value value :
 VM.find 7202 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1857 result = Some value.
Proof.
 intros Source Adapt Step. exact (declared_connection_value 1936 flat_statements reference_event_connection_1857_decl reference_event_connection_1857_mid reference_event_connection_1857_tail
 1857 7202 1 source_value value invalid flat_memories old current result
 reference_event_connection_1857_position reference_event_connection_1857_split reference_event_connection_1857_straight reference_event_connection_1857_mid_safe reference_event_connection_1857_tail_safe reference_event_connection_1857_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition reference_event_connection_1667_decl := match straight_drop 1747 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_event_connection_1667_tail := match straight_drop 7885 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_event_connection_1667_mid := take_statements 6137 reference_event_connection_1667_decl.
Lemma reference_event_connection_1667_position : straight_drop 1746 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1667 (Gtyp (Fuint 1))) reference_event_connection_1667_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_connection_1667_split : reference_event_connection_1667_decl = statement_append reference_event_connection_1667_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1667) (@Eref VarOrder.T (@Eid VarOrder.T 1857))) reference_event_connection_1667_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_connection_1667_straight : straight_statements reference_event_connection_1667_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_event_connection_1667_mid_safe : formal_typed_suffix_safe flat_memories 1667 reference_event_connection_1667_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_connection_1667_tail_safe : formal_typed_suffix_safe flat_memories 1667 reference_event_connection_1667_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_connection_1667_nonregister : has_register 1667 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_connection_1667_observation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists source_value value, VM.find 1857 old = Some source_value /\
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value /\ VM.find 1667 result = Some value.
Proof.
 intro Step. exact (declared_connection_observation 1746 flat_statements reference_event_connection_1667_decl reference_event_connection_1667_mid reference_event_connection_1667_tail
 1667 1857 1 invalid flat_memories old current result
 reference_event_connection_1667_position reference_event_connection_1667_split reference_event_connection_1667_straight reference_event_connection_1667_mid_safe reference_event_connection_1667_tail_safe reference_event_connection_1667_nonregister
 (Logic.eq_refl _) Step).
Qed.
Theorem reference_event_connection_1667_value invalid old current result source_value value :
 VM.find 1857 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1667 result = Some value.
Proof.
 intros Source Adapt Step. exact (declared_connection_value 1746 flat_statements reference_event_connection_1667_decl reference_event_connection_1667_mid reference_event_connection_1667_tail
 1667 1857 1 source_value value invalid flat_memories old current result
 reference_event_connection_1667_position reference_event_connection_1667_split reference_event_connection_1667_straight reference_event_connection_1667_mid_safe reference_event_connection_1667_tail_safe reference_event_connection_1667_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions reference_event_connection_1667_observation.

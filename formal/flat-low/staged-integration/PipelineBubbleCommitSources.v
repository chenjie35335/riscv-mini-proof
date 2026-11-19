Require Import FormalRegisterMuxObservation FormalRegisterCommitIdentity RegisterCommitCertificate ScalarNodeFrames CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition pipeline_bubble_7945_reg := @mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7945))).
Definition pipeline_bubble_7945_cond := @Eref VarOrder.T (@Eid VarOrder.T 65).
Definition pipeline_bubble_7945_yes := @Econst VarOrder.T (Fuint 1) [::true].
Definition pipeline_bubble_7945_no := @Eref VarOrder.T (@Eid VarOrder.T 7944).
Definition pipeline_bubble_7945_declared := match straight_drop 8452 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pipeline_bubble_7945_middle := take_statements 418 pipeline_bubble_7945_declared.
Definition pipeline_bubble_7945_tail := match straight_drop 8871 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pipeline_bubble_7945_position : straight_drop 8451 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7945 pipeline_bubble_7945_reg) pipeline_bubble_7945_declared).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_bubble_7945_split : pipeline_bubble_7945_declared = statement_append pipeline_bubble_7945_middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7945) (@Emux VarOrder.T pipeline_bubble_7945_cond pipeline_bubble_7945_yes pipeline_bubble_7945_no)) pipeline_bubble_7945_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_bubble_7945_straight : straight_statements pipeline_bubble_7945_middle.
Proof. vm_compute. exact I. Qed.
Lemma pipeline_bubble_7945_middle_safe : formal_typed_suffix_safe flat_memories 7945 pipeline_bubble_7945_middle.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_bubble_7945_tail_safe : formal_typed_suffix_safe flat_memories 7945 pipeline_bubble_7945_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_bubble_7945_identity : register_identity_b 7945 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_bubble_7945_formal_commit_source invalid old current result old_value :
 VM.find 7945 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists source value,
 eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T pipeline_bubble_7945_cond pipeline_bubble_7945_yes pipeline_bubble_7945_no) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 1)) = Some value /\ VM.find 7945 result = Some value.
Proof.
 intros Old Typed Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_mux_observation 8451 flat_statements pipeline_bubble_7945_declared pipeline_bubble_7945_middle pipeline_bubble_7945_tail
 7945 pipeline_bubble_7945_reg pipeline_bubble_7945_cond pipeline_bubble_7945_yes pipeline_bubble_7945_no invalid flat_memories old true current proposed old_value 1
 pipeline_bubble_7945_position pipeline_bubble_7945_split pipeline_bubble_7945_straight pipeline_bubble_7945_middle_safe pipeline_bubble_7945_tail_safe Old Typed Statements)
 as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 rewrite (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result
 7945 pipeline_bubble_7945_identity Step). exact Value.
Qed.
Print Assumptions pipeline_bubble_7945_formal_commit_source.

Definition pipeline_bubble_7947_reg := @mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7947))).
Definition pipeline_bubble_7947_cond := @Eref VarOrder.T (@Eid VarOrder.T 65).
Definition pipeline_bubble_7947_yes := @Econst VarOrder.T (Fuint 1) [::true].
Definition pipeline_bubble_7947_no := @Eref VarOrder.T (@Eid VarOrder.T 7946).
Definition pipeline_bubble_7947_declared := match straight_drop 8454 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pipeline_bubble_7947_middle := take_statements 417 pipeline_bubble_7947_declared.
Definition pipeline_bubble_7947_tail := match straight_drop 8872 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pipeline_bubble_7947_position : straight_drop 8453 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7947 pipeline_bubble_7947_reg) pipeline_bubble_7947_declared).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_bubble_7947_split : pipeline_bubble_7947_declared = statement_append pipeline_bubble_7947_middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7947) (@Emux VarOrder.T pipeline_bubble_7947_cond pipeline_bubble_7947_yes pipeline_bubble_7947_no)) pipeline_bubble_7947_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_bubble_7947_straight : straight_statements pipeline_bubble_7947_middle.
Proof. vm_compute. exact I. Qed.
Lemma pipeline_bubble_7947_middle_safe : formal_typed_suffix_safe flat_memories 7947 pipeline_bubble_7947_middle.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_bubble_7947_tail_safe : formal_typed_suffix_safe flat_memories 7947 pipeline_bubble_7947_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_bubble_7947_identity : register_identity_b 7947 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_bubble_7947_formal_commit_source invalid old current result old_value :
 VM.find 7947 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists source value,
 eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T pipeline_bubble_7947_cond pipeline_bubble_7947_yes pipeline_bubble_7947_no) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 1)) = Some value /\ VM.find 7947 result = Some value.
Proof.
 intros Old Typed Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_mux_observation 8453 flat_statements pipeline_bubble_7947_declared pipeline_bubble_7947_middle pipeline_bubble_7947_tail
 7947 pipeline_bubble_7947_reg pipeline_bubble_7947_cond pipeline_bubble_7947_yes pipeline_bubble_7947_no invalid flat_memories old true current proposed old_value 1
 pipeline_bubble_7947_position pipeline_bubble_7947_split pipeline_bubble_7947_straight pipeline_bubble_7947_middle_safe pipeline_bubble_7947_tail_safe Old Typed Statements)
 as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 rewrite (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result
 7947 pipeline_bubble_7947_identity Step). exact Value.
Qed.
Print Assumptions pipeline_bubble_7947_formal_commit_source.


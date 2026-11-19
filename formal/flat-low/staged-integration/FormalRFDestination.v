Require Import FormalRFInputConcrete.
Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_source_expr_7805 := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 7750))).
Definition rf_source_tail_7805 := match straight_drop 8312 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_7805 : straight_drop 8311 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7805 rf_source_expr_7805) rf_source_tail_7805).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_7805 : formal_typed_suffix_safe flat_memories 7805 rf_source_tail_7805.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_7805 : has_register 7805 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_7805 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_7805 old old = Some value ->
 type_of_val value = Gtyp (Fuint 5) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7805 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_7805|exact rf_source_suffix_7805|exact rf_source_nonregister_7805|exact Eval|exact Typed|exact Step]. Qed.

Lemma rf_destination_width (instruction : seq bool) :
 size instruction = 32%nat -> size (drop 7 (take 12 instruction)) = 5%nat.
Proof. intro Size. rewrite size_drop size_take Size. reflexivity. Qed.
Theorem rf_destination_node invalid old current result instruction :
 VM.find 7750 old = Some (Gval (Fuint 32) instruction) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7805 result = Some (Gval (Fuint 5) (drop 7 (take 12 instruction))).
Proof.
 intros Instruction Step.
 apply (rf_source_node_7805 invalid old current result (Gval (Fuint 5) (drop 7 (take 12 instruction))));
 [|reflexivity|exact Step].
 unfold rf_source_expr_7805. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Instruction. reflexivity.
Qed.
Theorem rf_destination_port_after_two invalid old middle result instruction :
 size instruction = 32%nat ->
 VM.find 7750 old = Some (Gval (Fuint 32) instruction) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some middle ->
 formal_value_iter invalid flat_memories middle false middle flat_statements = Some result ->
 VM.find 785 result = Some (Gval (Fuint 5) (drop 7 (take 12 instruction))).
Proof.
 intros Size Instruction First Second.
 apply (rf_input_address_concrete invalid middle middle result (drop 7 (take 12 instruction)));
 [apply rf_destination_width; exact Size|exact (rf_destination_node invalid old old middle instruction Instruction First)|exact Second].
Qed.
Print Assumptions rf_destination_port_after_two.

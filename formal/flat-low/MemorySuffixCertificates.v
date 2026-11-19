Require Import MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.
Fixpoint memory_suffix_safe_b mm node stmts : bool :=
 match stmts with
 | Qnil => true
 | Qcons st tail =>
 (match st with
 | Sskip | Sinst _ _ => true
 | Swire name _ | Sreg name _ | Smem name _ | Snode name _ => node != name
 | Sfcnct lhs rhs => (node != HiF.base_ref lhs) &&
   memory_storage_disjoint mm node (HiF.base_ref lhs) &&
   (match rhs with Eref r => node != HiF.base_ref r | _ => true end)
 | Sinvalid r => (node != HiF.base_ref r) && (is_memory_writer_ref mm r == false)
 | Swhen _ _ _ => false end) && memory_suffix_safe_b mm node tail
 end.
Lemma memory_suffix_safe_b_sound : forall mm node stmts,
 memory_suffix_safe_b mm node stmts -> memory_suffix_safe mm node stmts.
Proof.
 fix IH 3. intros mm node stmts. destruct stmts as [|st tail]; [intros _; exact I|].
 cbn [memory_suffix_safe_b memory_suffix_safe]. move/andP => [Head Tail].
 split; [|exact (IH mm node tail Tail)].
 destruct st as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no];
 try exact Head; try exact I; try discriminate Head.
 - move/andP: Head => [/andP [Different Storage] Source].
   split; [exact Different|]. split; [exact Storage|]. destruct rhs; try exact I; exact Source.
 - move/andP: Head => [Different /eqP Memory]. split; assumption.
Qed.
Theorem full_iteration_memory_node_equation count stmts tail node expression
 invalid mm old set_regs current result :
 straight_drop count stmts = Some (Qcons (Snode node expression) tail) ->
 memory_suffix_safe mm node tail -> has_register node stmts = false ->
 value_iter_with_memory_policy invalid mm old set_regs current stmts = Some result ->
 VM.find node result = eval_hfexpr_with_memory mm expression old old.
Proof.
 intros Position Safe Nonregister Step.
 destruct (policy_iteration_nonregister_projection invalid mm old set_regs current result stmts node Nonregister Step)
   as [proposed [Statements Projection]].
 destruct (successful_straight_prefix count stmts (Qcons (Snode node expression) tail)
   invalid [::] 0 mm old set_regs current proposed Position Statements) as [at_node NodeStep].
 rewrite Projection.
 eapply node_statement_evaluation_projection; [|exact NodeStep].
 intros value Eval Rest.
 eapply memory_suffix_preserves_value; [exact Safe| |exact Rest].
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.
Print Assumptions full_iteration_memory_node_equation.

Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation StagedRegisterHold.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma top_reset_safe : formal_typed_suffix_safe flat_memories 1 flat_statements.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma top_reset_nonregister : has_register 1 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem top_reset_iteration invalid old current result bit :
 VM.find 1 current = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Reset Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old false current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 rewrite (staged_finish_false_equal flat_statements invalid nil 0 flat_memories old proposed
   (fun e => eval_hfexpr_with_memory flat_memories e old old)) in Step.
 pose proof (finish_registers_preserves_nonregister flat_statements _ old false proposed result
   1 top_reset_nonregister Step) as Projection.
 rewrite Projection.
 eapply formal_typed_suffix_preserves_value;
 [exact top_reset_safe|reflexivity|exact Reset|exact Statements].
Qed.
Print Assumptions top_reset_iteration.

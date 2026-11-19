Require Import ScalarNodeFrames.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_memory.
Fixpoint statement_append (prefix suffix : HiF.hfstmt_seq) : HiF.hfstmt_seq :=
 match prefix with
 | Qnil => suffix
 | Qcons head tail => Qcons head (statement_append tail suffix) end.
Fixpoint statement_count (stmts : HiF.hfstmt_seq) : nat :=
 match stmts with Qnil => 0 | Qcons _ tail => S (statement_count tail) end.
Fixpoint straight_statements (stmts : HiF.hfstmt_seq) : Prop :=
 match stmts with
 | Qnil => True
 | Qcons (Swhen _ _ _) _ => False
 | Qcons _ tail => straight_statements tail end.

Theorem straight_append_evaluation : forall prefix suffix invalid scope position mm old set_regs current,
 straight_statements prefix ->
 formal_statements invalid scope position mm old set_regs current
   (statement_append prefix suffix) =
 match formal_statements invalid scope position mm old set_regs current prefix with
 | Some middle => formal_statements invalid scope (position + statement_count prefix)
     mm old set_regs middle suffix
 | None => None end.
Proof.
 fix IH 1. intros prefix suffix invalid scope position mm old set_regs current Straight.
 destruct prefix as [|head tail].
 - cbn [statement_append statement_count formal_statements]. rewrite addn0. reflexivity.
 - destruct head as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no];
   try contradiction;
   cbn [statement_append statement_count formal_statements];
   rewrite addnS;
   try (rewrite (IH tail suffix invalid scope (S position) mm old set_regs _ Straight) addSn; reflexivity).
   all: try (match goal with
   | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
   end; [rewrite (IH tail suffix invalid scope (S position) mm old set_regs _ Straight) addSn; reflexivity|reflexivity]).
   destruct rhs;
   repeat match goal with
   | |- context [match ?x with Some _ => _ | None => _ end] =>
       first [rewrite (IH tail suffix invalid scope (S position) mm old set_regs _ Straight) addSn; reflexivity
             | destruct x]
   end; try reflexivity.
Qed.
Print Assumptions straight_append_evaluation.

Corollary successful_straight_segment prefix suffix invalid scope position mm old set_regs current result :
 straight_statements prefix ->
 formal_statements invalid scope position mm old set_regs current
   (statement_append prefix suffix) = Some result ->
 exists middle,
   formal_statements invalid scope position mm old set_regs current prefix = Some middle /\
   formal_statements invalid scope (position + statement_count prefix)
     mm old set_regs middle suffix = Some result.
Proof.
 intros Straight Step.
 rewrite (straight_append_evaluation prefix suffix invalid scope position mm old set_regs current Straight) in Step.
 destruct (formal_statements invalid scope position mm old set_regs current prefix)
   as [middle|] eqn:Prefix; [|discriminate Step].
 exists middle. split; [reflexivity|exact Step].
Qed.

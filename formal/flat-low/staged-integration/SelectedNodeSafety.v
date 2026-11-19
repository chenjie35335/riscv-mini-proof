Require Import ScalarNodeFrames RegisterInvariants FormalTypedNodeFrames FormalTypedNodeEquation X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeEvaluation.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_memory.
Theorem selected_node_safe_position mm full offsets stmts entries node expression :
 select_node_offsets offsets stmts = Some entries ->
 selected_node_safety mm full offsets stmts ->
 List.In (node, expression) entries ->
 exists count tail,
 straight_drop count stmts = Some (Qcons (Snode node expression) tail) /\
 formal_typed_suffix_safe mm node tail /\ has_register node full = false.
Proof.
 revert stmts entries. induction offsets as [|offset rest IH]; intros stmts entries Selected Safe Member.
 - inversion Selected; subst. contradiction.
 - cbn [select_node_offsets] in Selected. cbn [selected_node_safety] in Safe.
   destruct (straight_drop offset stmts) as [suffix|] eqn:Drop; [|discriminate Selected].
   destruct suffix as [|st tail]; [discriminate Selected|].
   destruct st as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no]; try discriminate Selected.
   move/andP: Safe => [/andP [Suffix Nonregister] RestSafe].
   destruct (select_node_offsets rest tail) as [remaining|] eqn:Rest; [|discriminate Selected].
   inversion Selected; subst entries. simpl in Member.
   destruct Member as [Equal|Member].
   + inversion Equal; subst. exists offset, tail. split; [exact Drop|]. split.
     * exact (formal_typed_suffix_safe_b_sound mm node tail Suffix).
     * exact (elimT negPf Nonregister).
   + destruct (IH tail remaining Rest RestSafe Member) as [count [last [Position [SuffixSafe Nonreg]]]].
     exists (offset + S count), last. split.
     * eapply straight_drop_compose; [exact Drop|]. cbn [straight_drop]. exact Position.
     * split; assumption.
Qed.
Print Assumptions selected_node_safe_position.

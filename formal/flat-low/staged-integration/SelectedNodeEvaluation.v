Require Import CoreSocModel ComparisonNodes ScalarNodeFrames X0ConcretePositionCertificate FormalSuccessfulNodeEvaluation ConcreteExpressionClosure ConcreteGroundOperations.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements generated_modules generated_top.
Lemma straight_drop_compose first second stmts middle final :
 straight_drop first stmts = Some middle ->
 straight_drop second middle = Some final ->
 straight_drop (first + second) stmts = Some final.
Proof.
 revert stmts. induction first as [|first IH]; intros stmts A B.
 - inversion A; subst. exact B.
 - destruct stmts as [|st tail]; [discriminate A|].
   destruct st; try discriminate A; rewrite addSn; cbn [straight_drop] in *;
   exact (IH tail A B).
Qed.
Theorem selected_node_position offsets stmts entries node expression :
 select_node_offsets offsets stmts = Some entries ->
 List.In (node, expression) entries ->
 exists count tail, straight_drop count stmts = Some (Qcons (Snode node expression) tail).
Proof.
 revert stmts entries. induction offsets as [|offset rest IH]; intros stmts entries Selected Member.
 - inversion Selected; subst. contradiction.
 - cbn [select_node_offsets] in Selected.
   destruct (straight_drop offset stmts) as [suffix|] eqn:Drop; [|discriminate Selected].
   destruct suffix as [|st tail]; [discriminate Selected|].
   destruct st as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no]; try discriminate Selected.
   destruct (select_node_offsets rest tail) as [remaining|] eqn:Rest; [|discriminate Selected].
   inversion Selected; subst entries. simpl in Member.
   destruct Member as [Equal|Member].
   + inversion Equal; subst. exists offset, tail. exact Drop.
   + destruct (IH tail remaining Rest Member) as [count [last Position]].
     exists (offset + S count), last.
     eapply straight_drop_compose; [exact Drop|].
     cbn [straight_drop]. exact Position.
Qed.
Theorem selected_node_successful_concrete offsets stmts entries node expression inputs path mm old phase current result :
 select_node_offsets offsets stmts = Some entries ->
 List.In (node, expression) entries ->
 concrete_expression_ready old expression ->
 formal_value_iter (formal_invalid_policy inputs path) mm old phase current stmts = Some result ->
 exists site value,
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm expression old old = Some value /\
 concrete_ground_value value.
Proof.
 intros Selected Member Ready Step.
 destruct (selected_node_position offsets stmts entries node expression Selected Member) as [count [tail Position]].
 destruct (formal_successful_node_evaluation count stmts tail node expression _ mm old phase current result Position Step) as [value Eval].
 eexists; exists value. split; [exact Eval|].
 exact (concrete_expression_closure inputs path mm old expression Ready _ value Eval).
Qed.
Print Assumptions selected_node_successful_concrete.

Require Import CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence3 FormalGroundNodeEquation SelectedNodeSafety.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.


Lemma reference_redirect_mux_step node expression condition yes no invalid old current result c y n :
 List.In (node, expression) reference_control_3_nodes ->
 expression = @Emux VarOrder.T condition yes no ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories condition old old = Some (Gval (Fuint 1) [::c])) ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories yes old old = Some (Gval (Fuint 1) [::y])) ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories no old old = Some (Gval (Fuint 1) [::n])) ->
 eval_type_of_expr yes old = Some (Gtyp (Fuint 1)) ->
 eval_type_of_expr no old = Some (Gtyp (Fuint 1)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find node result = Some (Gval (Fuint 1) [::if c then y else n]).
Proof.
 intros Member Expression Condition Yes No YesType NoType Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes node expression reference_control_3_positions reference_control_3_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply (formal_combinational_known_ground_node count flat_statements tail node expression (Fuint 1)); [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 rewrite Expression. cbn [eval_hfexpr_validif_policy]. rewrite Condition.
 destruct c; cbn; [rewrite Yes NoType|rewrite No YesType]; destruct y, n; reflexivity.
Qed.

From Coq Require Import Lia.
From nbits Require Import NBitsDef NBitsOp.

Lemma redirect_to_N_cons bit rest :
 to_N (bit :: rest) = 2 * to_N rest + (if bit then 1 else 0).
Proof. unfold to_N. destruct bit; cbn [foldr N.b2n]; lia. Qed.
Lemma redirect_to_N_and_nil right : to_N (andB [::] right) = 0.
Proof.
 induction right as [|b right IH]; [reflexivity|].
 unfold andB, lift0 in *. rewrite lift_nil_cons.
 rewrite redirect_to_N_cons. change (2 * to_N (lift b0 andb [::] right) + 0 = 0). rewrite IH. reflexivity.
Qed.
Lemma redirect_to_N_and left right :
 to_N (andB left right) = N.land (to_N left) (to_N right).
Proof.
 revert right. induction left as [|a left IH]; intros [|b right].
 - reflexivity.
 - rewrite redirect_to_N_and_nil. reflexivity.
 - unfold andB, lift0. rewrite lift_cons_nil.
   rewrite redirect_to_N_cons. change (2 * to_N (andB left [::]) + (if a && false then 1 else 0) = N.land (to_N (a :: left)) 0).
   rewrite IH !N.land_0_r. destruct a; reflexivity.
 - rewrite andB_cons !redirect_to_N_cons IH.
   destruct a, b; cbn [andb]; rewrite ?N.add_0_r;
   rewrite ?N.land_even_even ?N.land_odd_even ?N.land_even_odd ?N.land_odd_odd; reflexivity.
Qed.

Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
Lemma reference_redirect_ground_step offsets nodes node expression ground bits invalid old current result :
 select_node_offsets offsets flat_statements = Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements = true ->
 List.In (node, expression) nodes ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories expression old old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find node result = Some (Gval ground bits).
Proof.
 intros Positions Safety Member Eval Step.
 destruct (selected_node_safe_position flat_memories flat_statements offsets flat_statements
 nodes node expression Positions Safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply (formal_combinational_known_ground_node count flat_statements tail node expression ground);
 [exact Position|exact Safe|exact Nonreg|apply Eval|reflexivity|exact Step].
Qed.

From firrtl Require Import Firrtl_with_implicit_widths.
Lemma redirect_N_eqb x y : (x == y) = N.eqb x y.
Proof.
 destruct (eqP : reflect (x = y) (x == y)) as [H|H].
 - subst y. rewrite N.eqb_refl. reflexivity.
 - symmetry. apply N.eqb_neq. exact H.
Qed.
Lemma redirect_mask_decode instruction mask code iw mw cw :
 eval_binop (Bcomp Beq) (Gval (Fuint cw) code)
  (Gval (Fuint (maxn iw mw)) (andB instruction mask)) =
 Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) (to_N mask)) (to_N code)]).
Proof.
 unfold eval_binop. cbn [eval_binop_basic].
 destruct (absorbing_bit (Bcomp Beq) (Gval (Fuint cw) code)
 (Gval (Fuint (maxn iw mw)) (andB instruction mask))); cbn [refine_boolean_result];
 rewrite redirect_to_N_and redirect_N_eqb N.eqb_sym; reflexivity.
Qed.

From Coq Require Import NArith.
Lemma redirect_to_N_testbit bits index :
 N.testbit (to_N bits) (N.of_nat index) = nth false bits index.
Proof.
 revert bits. induction index as [|index IH]; intros [|b bits].
 - reflexivity.
 - rewrite redirect_to_N_cons. change (N.testbit (2 * to_N bits + N.b2n b) 0 = b). apply N.testbit_0_r.
 - rewrite N.bits_0. reflexivity.
 - rewrite redirect_to_N_cons Nat2N.inj_succ.
   change (N.testbit (2 * to_N bits + N.b2n b) (N.succ (N.of_nat index)) = nth false bits index).
   rewrite N.testbit_succ_r. apply IH.
Qed.
Lemma redirect_msb_nth bits : msb bits = nth false bits (size bits).-1.
Proof.
 rewrite nth_last. unfold msb, splitmsb, split_last, lastd.
 destruct bits; reflexivity.
Qed.

Lemma reference_redirect_csr_compressed bits :
 size bits = 32%nat ->
 eval_unop (Uextr 2 2) (Gval (Fuint 32) bits) =
 Some (Gval (Fuint 1) [::N.testbit (to_N bits) 2]).
Proof.
 intro Size. rewrite (redirect_to_N_testbit bits 2).
 change (Some (Gval (Fuint 1) (drop 2 (take 3 bits))) = Some (Gval (Fuint 1) [::nth false bits 2])).
 destruct bits as [|a [|b [|c rest]]]; try discriminate Size.
 cbn [drop take nth]. rewrite take0. reflexivity.
Qed.

Require Import ReferenceControlGroundExpressions FormalSuccessfulNodeEvaluation.
Lemma reference_redirect_node_equation offsets nodes node expression inputs path old result :
 select_node_offsets offsets flat_statements = Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements = true ->
 List.In (node, expression) nodes ->
 reference_control_ready old expression ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false old flat_statements = Some result ->
 VM.find node old = VM.find node result ->
 exists site, VM.find node old =
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories expression old old.
Proof.
 intros Positions Safety Member Ready Step Stable.
 destruct (selected_node_safe_position flat_memories flat_statements offsets flat_statements
 nodes node expression Positions Safety Member) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node expression
 (formal_invalid_policy inputs path) flat_memories old false old result Position Step) as [value Eval].
 rewrite add0n in Eval.
 destruct (reference_control_expression_ground inputs path flat_memories old expression Ready _ value Eval) as [ground Typed].
 exists (validif_raw_address nil count 0 nil).
 rewrite Stable Eval.
 exact (formal_combinational_known_ground_node count flat_statements tail node expression ground value (formal_invalid_policy inputs path)
 flat_memories old old result Position Safe Nonreg Eval Typed Step).
Qed.

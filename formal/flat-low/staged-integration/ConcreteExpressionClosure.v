Require Import ConcreteGroundOperations ConcreteBinaryOperations ConcreteGroundAdapt ConcreteScalarExpressions FormalConcreteScalarExpressions ConcreteFormalValidIf.
From nbits Require Import NBits.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

(* Recursive closure permits operators above muxes and validifs, without
   assuming a particular value for any symbolic invalid source. *)
Inductive concrete_expression_ready (old : VM.t hvalue) : hfexpr VarOrder.T -> Prop :=
| closure_scalar e : scalar_expression_ready old e -> concrete_expression_ready old e
| closure_unary op e : concrete_expression_ready old e -> concrete_expression_ready old (Eprim_unop op e)
| closure_binary op a b : concrete_expression_ready old a -> concrete_expression_ready old b -> concrete_expression_ready old (Eprim_binop op a b)
| closure_mux c a b : concrete_expression_ready old c -> concrete_expression_ready old a -> concrete_expression_ready old b -> concrete_expression_ready old (Emux c a b)
| closure_validif c b width : concrete_expression_ready old c -> concrete_expression_ready old b -> eval_type_of_expr b old = Some (Gtyp (Fuint width)) -> concrete_expression_ready old (Evalidif c b).

Theorem concrete_expression_closure inputs path mm old expression :
 concrete_expression_ready old expression ->
 forall site result,
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm expression old old = Some result ->
 concrete_ground_value result.
Proof.
 intro Ready. induction Ready as [e Scalar|op e Ready IH|op a b A IHA B IHB|c a b C IHC A IHA B IHB|c b width C IHC B IHB Typed]; intros site result Eval.
 - exact (formal_concrete_scalar_expression _ _ mm old e result Scalar Eval).
 - cbn [eval_hfexpr_validif_policy] in Eval.
   destruct (eval_hfexpr_validif_policy _ _ mm e old old) as [v|] eqn:E; [|discriminate Eval].
   destruct (IH _ _ E) as [g [bits V]]. subst v.
   exact (concrete_unary_result op g bits result Eval).
 - cbn [eval_hfexpr_validif_policy] in Eval.
   destruct (eval_hfexpr_validif_policy _ _ mm a old old) as [va|] eqn:EA; [|discriminate Eval].
   destruct (eval_hfexpr_validif_policy _ _ mm b old old) as [vb|] eqn:EB; [|discriminate Eval].
   destruct (IHA _ _ EA) as [ga [ba VA]].
   destruct (IHB _ _ EB) as [gb [bb VB]]. subst va vb.
   exact (concrete_binary_result op ga ba gb bb result Eval).
 - cbn [eval_hfexpr_validif_policy] in Eval.
   destruct (eval_hfexpr_validif_policy _ _ mm c old old) as [v|] eqn:EC; [|discriminate Eval].
   destruct (IHC _ _ EC) as [g [bits V]]. subst v.
   destruct g; try discriminate Eval. destruct (is_zero bits).
   + destruct (eval_hfexpr_validif_policy _ _ mm b old old) as [v|] eqn:EB; [|discriminate Eval].
     destruct (eval_type_of_expr a old) as [typ|]; [|discriminate Eval].
     destruct (IHB _ _ EB) as [gb [bb VB]]. subst v.
     exact (concrete_ground_extend gb bb typ result Eval).
   + destruct (eval_hfexpr_validif_policy _ _ mm a old old) as [v|] eqn:EA; [|discriminate Eval].
     destruct (eval_type_of_expr b old) as [typ|]; [|discriminate Eval].
     destruct (IHA _ _ EA) as [ga [ba VA]]. subst v.
     exact (concrete_ground_extend ga ba typ result Eval).
 - cbn [eval_hfexpr_validif_policy] in Eval. rewrite Typed in Eval.
   destruct (eval_hfexpr_validif_policy _ _ mm c old old) as [v|] eqn:EC; [|discriminate Eval].
   destruct (IHC _ _ EC) as [g [bits V]]. subst v.
   destruct g; try discriminate Eval.
   eapply formal_validif_result_concrete; [|exact Eval].
   intros value Body. exact (IHB _ _ Body).
Qed.
Print Assumptions concrete_expression_closure.

Require Import RegisterInvariants ScalarNodeFrames.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
Fixpoint register_update_identity (id : VarOrder.T) (eval : HiF.hfexpr -> option hvalue)
 (stmts : HiF.hfstmt_seq) : Prop :=
 match stmts with
 | Qnil => True
 | Qcons st tl =>
 (match st with
 | Sreg name reg => id = name -> forall proposed, register_next_value eval reg proposed = Some proposed
 | Swhen _ yes no => register_update_identity id eval yes /\ register_update_identity id eval no
 | _ => True end) /\ register_update_identity id eval tl end.
Theorem finish_identity_preserves_candidate : forall (stmts : HiF.hfstmt_seq)
 eval old current result id,
 register_update_identity id eval stmts ->
 finish_registers eval old true current stmts = Some result ->
 VM.find id result = VM.find id current.
Proof.
 fix IH 1. intros stmts eval old current result id Identity Step.
 destruct stmts as [|st tl].
 - cbn [finish_registers] in Step. inversion Step; subst result. reflexivity.
 - destruct Identity as [Head Tail].
   destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
   cbn [finish_registers] in Step; try (eapply IH; [exact Tail|exact Step]).
   + destruct (VM.find r old); [|discriminate Step].
     destruct (VM.find r current) as [proposed|] eqn:Proposed; [|discriminate Step].
     destruct (register_next_value eval reg proposed) as [value|] eqn:Next; [|discriminate Step].
     rewrite (IH tl eval old _ result id Tail Step).
     case Same: (id == r).
     * move/eqP: Same => Same. subst id.
       rewrite (Head (Logic.eq_refl _) proposed) in Next. inversion Next; subst value.
       rewrite (RegisterMapFacts.find_add_eq (eqxx r)). symmetry. exact Proposed.
     * rewrite RegisterMapFacts.find_add_neq; [reflexivity|].
       change (~ (id == r)). rewrite Same. discriminate.
   + destruct Head as [Yes No].
     destruct (finish_registers eval old true current yes) as [after_yes|] eqn:SY; [|discriminate Step].
     destruct (finish_registers eval old true after_yes no) as [after_no|] eqn:SN; [|discriminate Step].
     rewrite (IH tl eval old after_no result id Tail Step).
     rewrite (IH no eval old after_yes after_no id No SN).
     exact (IH yes eval old current after_yes id Yes SY).
Qed.
Print Assumptions finish_identity_preserves_candidate.

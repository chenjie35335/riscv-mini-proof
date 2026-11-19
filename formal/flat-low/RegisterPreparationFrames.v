Require Import RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Fixpoint initial_register_safe (id : VarOrder.T) (stmts : HiF.hfstmt_seq) : bool :=
 match stmts with
 | Qnil => true
 | Qcons st tl =>
 (match st with
 | Swire name _ | Snode name _ | Sinst name _ => id != name
 | Smem name mem => (id != name) && (id != storage_id mem)
 | Swhen _ yes no => initial_register_safe id yes && initial_register_safe id no
 | _ => true end) && initial_register_safe id tl end.
Lemma initial_register_preserves : forall (stmts : HiF.hfstmt_seq) modules old current result id,
 initial_register_safe id stmts -> VM.find id current = VM.find id old ->
 statements_initial_map_with_memory modules stmts (Some old) current = Some result ->
 VM.find id result = VM.find id old.
Proof.
 fix IH 1. intros stmts modules old current result id Safe Agree Step.
 destruct stmts as [|st tl].
 - cbn [statements_initial_map_with_memory] in Step. inversion Step; subst result. exact Agree.
 - move/andP: Safe => [Head Tail].
   destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
   cbn [statements_initial_map_with_memory] in Step;
   try (eapply IH; [exact Tail|exact Agree|exact Step]).
   + eapply IH; [exact Tail| |exact Step]. rewrite RegisterMapFacts.find_add_neq; [exact Agree|].
     exact (elimT negP Head).
   + destruct (VM.find r old) as [value|] eqn:Value; [|discriminate Step].
     eapply IH; [exact Tail| |exact Step]. eapply restore_preserves_agreement; eassumption.
   + move/andP: Head => [Port Storage].
     destruct (VM.find (storage_id mem) old) as [value|] eqn:Value; [|discriminate Step].
     eapply IH; [exact Tail| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [|exact (elimT negP Storage)].
     rewrite RegisterMapFacts.find_add_neq; [exact Agree|exact (elimT negP Port)].
   + destruct (module_type modules target); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step]. rewrite RegisterMapFacts.find_add_neq;
     [exact Agree|exact (elimT negP Head)].
   + destruct (eval_type_of_expr expr current); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step]. rewrite RegisterMapFacts.find_add_neq;
     [exact Agree|exact (elimT negP Head)].
   + move/andP: Head => [Yes No].
     destruct (statements_initial_map_with_memory modules yes (Some old) current) as [after_yes|] eqn:SY;
     [|discriminate Step].
     destruct (statements_initial_map_with_memory modules no (Some old) after_yes) as [after_no|] eqn:SN;
     [|discriminate Step].
     eapply IH; [exact Tail| |exact Step]. eapply IH; [exact No| |exact SN].
     eapply IH; [exact Yes|exact Agree|exact SY].
Qed.
Print Assumptions initial_register_preserves.
Lemma initial_register_copies : forall (stmts : HiF.hfstmt_seq) modules old current result id,
 initial_register_safe id stmts -> has_register id stmts = true ->
 statements_initial_map_with_memory modules stmts (Some old) current = Some result ->
 VM.find id result = VM.find id old.
Proof.
 fix IH 1. intros stmts modules old current result id Safe Present Step.
 destruct stmts as [|st tl]; [discriminate Present|].
 move/andP: Safe => [Head Tail].
 destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
 cbn [statements_initial_map_with_memory] in Step; cbn [has_register] in Present;
 try (eapply IH; [exact Tail|exact Present|exact Step]).
 - destruct (VM.find r old) as [value|] eqn:Value; [|discriminate Step].
   move/orP: Present => [Same|InTail].
   + move/eqP: Same => Same. subst id.
     eapply initial_register_preserves; [exact Tail| |exact Step].
     rewrite (RegisterMapFacts.find_add_eq (eqxx r)). symmetry. exact Value.
   + eapply IH; [exact Tail|exact InTail|exact Step].
 - destruct (VM.find (storage_id mem) old); [|discriminate Step].
   eapply IH; [exact Tail|exact Present|exact Step].
 - destruct (module_type modules target); [|discriminate Step].
   eapply IH; [exact Tail|exact Present|exact Step].
 - destruct (eval_type_of_expr expr current); [|discriminate Step].
   eapply IH; [exact Tail|exact Present|exact Step].
 - move/andP: Head => [Yes No].
   destruct (statements_initial_map_with_memory modules yes (Some old) current) as [after_yes|] eqn:SY;
   [|discriminate Step].
   destruct (statements_initial_map_with_memory modules no (Some old) after_yes) as [after_no|] eqn:SN;
   [|discriminate Step].
   move/orP: Present => [InBranches|InTail].
   + eapply initial_register_preserves; [exact Tail| |exact Step].
     move/orP: InBranches => [InYes|InNo].
     * eapply initial_register_preserves; [exact No| |exact SN].
       eapply IH; [exact Yes|exact InYes|exact SY].
     * eapply IH; [exact No|exact InNo|exact SN].
   + eapply IH; [exact Tail|exact InTail|exact Step].
Qed.
Print Assumptions initial_register_copies.

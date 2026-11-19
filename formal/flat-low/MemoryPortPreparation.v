Require Import RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Fixpoint initial_port_safe (id : VarOrder.T) (stmts : HiF.hfstmt_seq) : bool :=
 match stmts with
 | Qnil => true
 | Qcons st tl => (match st with
   | Swire name _ | Sreg name _ | Snode name _ | Sinst name _ => id != name
   | Smem _ mem => id != storage_id mem
   | Swhen _ yes no => initial_port_safe id yes && initial_port_safe id no
   | _ => true end) && initial_port_safe id tl
 end.
Fixpoint port_seed_description (id : VarOrder.T) (stmts : HiF.hfstmt_seq) (prior : option HiF.hfmem) : option HiF.hfmem :=
 match stmts with
 | Qnil => prior
 | Qcons st tl => port_seed_description id tl
   (match st with
   | Smem name mem => if id == name then Some mem else prior
   | Swhen _ yes no => port_seed_description id no (port_seed_description id yes prior)
   | _ => prior end)
 end.
Definition port_seed_value description fallback :=
 match description with Some mem => Some (memory_bundle_initial mem) | None => fallback end.
Lemma initial_port_projection : forall stmts modules previous current result id prior fallback,
 initial_port_safe id stmts -> VM.find id current = port_seed_value prior fallback ->
 statements_initial_map_with_memory modules stmts previous current = Some result ->
 VM.find id result = port_seed_value (port_seed_description id stmts prior) fallback.
Proof.
 fix IH 1. intros stmts modules previous current result id prior fallback Safe Agree Step.
 destruct stmts as [|st tl]; [inversion Step; subst result; exact Agree|].
 move/andP: Safe => [Head Tail].
 destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
 cbn [statements_initial_map_with_memory] in Step; cbn [port_seed_description];
 try (eapply IH; [exact Tail|exact Agree|exact Step]).
 - eapply IH; [exact Tail| |exact Step].
   rewrite RegisterMapFacts.find_add_neq; [exact Agree|exact (elimT negP Head)].
 - destruct previous as [old|].
   + destruct (VM.find r old); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step]. rewrite RegisterMapFacts.find_add_neq; [exact Agree|exact (elimT negP Head)].
   + eapply IH; [exact Tail| |exact Step]. rewrite RegisterMapFacts.find_add_neq; [exact Agree|exact (elimT negP Head)].
 - assert (Port : VM.find id (VM.add m (memory_bundle_initial mem) current) =
     port_seed_value (if id == m then Some mem else prior) fallback).
   { case Same: (id == m).
     - move/eqP: Same => Same. subst id. rewrite (RegisterMapFacts.find_add_eq (eqxx m)). reflexivity.
     - rewrite RegisterMapFacts.find_add_neq; [exact Agree|]. change (~ (id == m)). rewrite Same. discriminate. }
   destruct previous as [old|].
   + destruct (VM.find (storage_id mem) old); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step]. rewrite RegisterMapFacts.find_add_neq; [exact Port|exact (elimT negP Head)].
   + eapply IH; [exact Tail| |exact Step]. rewrite RegisterMapFacts.find_add_neq; [exact Port|exact (elimT negP Head)].
 - destruct (module_type modules target); [|discriminate Step].
   eapply IH; [exact Tail| |exact Step]. rewrite RegisterMapFacts.find_add_neq; [exact Agree|exact (elimT negP Head)].
 - destruct (eval_type_of_expr expr current); [|discriminate Step].
   eapply IH; [exact Tail| |exact Step]. rewrite RegisterMapFacts.find_add_neq; [exact Agree|exact (elimT negP Head)].
 - move/andP: Head => [Yes No].
   destruct (statements_initial_map_with_memory modules yes previous current) as [after_yes|] eqn:YesStep; [|discriminate Step].
   destruct (statements_initial_map_with_memory modules no previous after_yes) as [after_no|] eqn:NoStep; [|discriminate Step].
   eapply IH; [exact Tail| |exact Step]. eapply IH; [exact No| |exact NoStep].
   eapply IH; [exact Yes|exact Agree|exact YesStep].
Qed.
Print Assumptions initial_port_projection.

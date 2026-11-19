Require Import FormalCombStorageFrames ScalarNodeFrames RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.
Fixpoint comb_storage_suffix_safe_b mm node stmts : bool :=
 match stmts with
 | Qnil => true
 | Qcons st tail =>
 (match st with
 | Sskip | Sinst _ _ => true
 | Swire name _ | Sreg name _ | Smem name _ | Snode name _ => node != name
 | Sfcnct lhs rhs => (node != HiF.base_ref lhs) &&
   comb_storage_storage_safe mm node (HiF.base_ref lhs) &&
   (match rhs with Eref r => node != HiF.base_ref r | _ => true end)
 | Sinvalid r => (node != HiF.base_ref r) && (is_memory_writer_ref mm r == false)
 | Swhen _ _ _ => false end) && comb_storage_suffix_safe_b mm node tail
 end.
Lemma comb_storage_suffix_safe_b_sound : forall mm node stmts,
 comb_storage_suffix_safe_b mm node stmts -> comb_storage_suffix_safe mm node stmts.
Proof.
 fix IH 3. intros mm node stmts. destruct stmts as [|st tail]; [intros _; exact I|].
 cbn [comb_storage_suffix_safe_b comb_storage_suffix_safe]. move/andP => [Head Tail].
 split; [|exact (IH mm node tail Tail)].
 destruct st as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no];
 try exact Head; try exact I; try discriminate Head.
 - move/andP: Head => [/andP [Different Storage] Source].
   split; [exact Different|]. split; [exact Storage|]. destruct rhs; try exact I; exact Source.
 - move/andP: Head => [Different /eqP Memory]. split; assumption.
Qed.

Require Import ConcreteRegisterInitialization.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths.
Fixpoint uint_register_declarations_b (id : VarOrder.T) width (stmts : HiF.hfstmt_seq) : bool :=
 match stmts with
 | Qnil => true
 | Qcons st tl =>
 (match st with
 | Sreg name reg => (id != name) || (type reg == Gtyp (Fuint width))
 | Swhen _ yes no => uint_register_declarations_b id width yes && uint_register_declarations_b id width no
 | _ => true end) && uint_register_declarations_b id width tl end.
Lemma uint_register_declarations_b_sound : forall stmts id width,
 uint_register_declarations_b id width stmts -> uint_register_declarations id width stmts.
Proof.
 fix IH 1. intros stmts id width Check. destruct stmts as [|st tl]; [exact I|].
 move/andP: Check => [Head Tail]. split; [|apply IH; exact Tail].
 destruct st; try exact I.
 - move/orP: Head => [Different|Typed]; intro Same.
   + subst. rewrite eqxx in Different. discriminate Different.
   + move/eqP: Typed => Typed. exact Typed.
 - move/andP: Head => [Yes No]. split; apply IH; assumption.
Qed.

Require Import RegisterCommitIdentity.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Definition literal_false (expression : HiF.hfexpr) : bool :=
 match expression with Econst (Fuint 1) [::false] => true | _ => false end.
Lemma literal_false_sound expression : literal_false expression ->
 expression = @Econst VarOrder.T (Fuint 1) [::false].
Proof.
 unfold literal_false. intro Check.
 repeat match type of Check with
 | context [match ?x with _ => _ end] => destruct x; cbn in Check; try discriminate Check
 end; reflexivity.
Qed.
Fixpoint register_identity_b (id : VarOrder.T) (stmts : HiF.hfstmt_seq) : bool :=
 match stmts with
 | Qnil => true
 | Qcons st tl =>
 (match st with
 | Sreg name reg => (id != name) ||
   match reset reg with NRst => true | Rst condition _ => literal_false condition end
 | Swhen _ yes no => register_identity_b id yes && register_identity_b id no
 | _ => true end) && register_identity_b id tl end.
Theorem register_identity_b_sound : forall stmts id mm old,
 register_identity_b id stmts ->
 register_update_identity id (fun e => eval_hfexpr_with_memory mm e old old) stmts.
Proof.
 fix IH 1. intros stmts id mm old Check. destruct stmts as [|st tl]; [exact I|].
 move/andP: Check => [Head Tail]. split; [|apply IH; exact Tail].
 destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no]; try exact I.
 - move/orP: Head => [Different|ResetShape]; intros Same proposed.
   + subst id. rewrite eqxx in Different. discriminate Different.
   + unfold register_next_value. destruct (reset reg) as [|condition initial] eqn:Reset.
     * reflexivity.
     * apply literal_false_sound in ResetShape. rewrite ResetShape. reflexivity.
 - move/andP: Head => [Yes No]. split; apply IH; assumption.
Qed.
Print Assumptions register_identity_b_sound.

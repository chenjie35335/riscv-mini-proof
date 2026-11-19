Require Import RegisterInvariants RegisterCommitCertificate.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem formal_finish_identity_preserves : forall stmts invalid scope position mm old current result id,
 register_identity_b id stmts ->
 formal_finish_registers invalid scope position mm old true current stmts = Some result ->
 VM.find id result = VM.find id current.
Proof.
 fix IH 1. intros stmts invalid scope position mm old current result id Identity Step.
 destruct stmts as [|st tail].
 - cbn [formal_finish_registers] in Step. inversion Step; reflexivity.
 - move/andP: Identity => [Head Tail].
   destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
   cbn [formal_finish_registers] in Step; try (eapply IH; [exact Tail|exact Step]).
   + destruct (VM.find r old); [|discriminate Step].
     destruct (VM.find r current) as [proposed|] eqn:Proposed; [|discriminate Step].
     set (eval := fun context e => eval_hfexpr_validif_policy (isolated_validif_policy invalid)
       (validif_raw_address scope position context [::]) mm e old old) in *.
     destruct (formal_register_next_value eval reg proposed) as [value|] eqn:Next; [|discriminate Step].
     rewrite (IH tail invalid scope (S position) mm old _ result id Tail Step).
     case Same: (id == r).
     * move/eqP: Same => Same. subst id. rewrite eqxx /= in Head.
       assert (Keep : formal_register_next_value eval reg proposed = Some proposed).
       { unfold formal_register_next_value.
         destruct (reset reg) as [|condition initial] eqn:Reset; [reflexivity|].
         apply literal_false_sound in Head. rewrite Head. reflexivity. }
       rewrite Keep in Next. inversion Next; subst value.
       rewrite (RegisterMapFacts.find_add_eq (eqxx r)). symmetry. exact Proposed.
     * rewrite RegisterMapFacts.find_add_neq; [reflexivity|].
       change (~ (id == r)). rewrite Same. discriminate.
   + move/andP: Head => [Yes No].
     destruct (formal_finish_registers invalid (scope ++ [::position;0]) 0 mm old true current yes)
       as [after_yes|] eqn:SY; [|discriminate Step].
     destruct (formal_finish_registers invalid (scope ++ [::position;1]) 0 mm old true after_yes no)
       as [after_no|] eqn:SN; [|discriminate Step].
     rewrite (IH tail invalid scope (S position) mm old after_no result id Tail Step).
     rewrite (IH no invalid (scope ++ [::position;1]) 0 mm old after_yes after_no id No SN).
     exact (IH yes invalid (scope ++ [::position;0]) 0 mm old current after_yes id Yes SY).
Qed.
Print Assumptions formal_finish_identity_preserves.

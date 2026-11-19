Require Import ReadonlyStorageFrames FormalConnectionFrames RegisterInvariants ScalarNodeFrames.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Definition comb_storage_storage_safe (mm : memory_map) (node mem : VarOrder.T) := true.
Fixpoint comb_storage_suffix_safe (mm : memory_map) (node : VarOrder.T)
 (stmts : HiF.hfstmt_seq) : Prop :=
 match stmts with
 | Qnil => True
 | Qcons st tail =>
   (match st with
    | Sskip | Sinst _ _ => True
    | Swire name _ | Sreg name _ | Smem name _ | Snode name _ => node != name
    | Sfcnct lhs rhs => node != HiF.base_ref lhs /\
        comb_storage_storage_safe mm node (HiF.base_ref lhs) /\ (match rhs with Eref reference => node != HiF.base_ref reference | _ => True end)
    | Sinvalid reference => node != HiF.base_ref reference /\ is_memory_writer_ref mm reference = false
    | Swhen _ _ _ => False
    end) /\ comb_storage_suffix_safe mm node tail
 end.

Lemma formal_comb_storage_connection_preserves_other invalid site mm node lhs rhs old current result :
 node != HiF.base_ref lhs -> comb_storage_storage_safe mm node (HiF.base_ref lhs) ->
 formal_connect invalid site mm false lhs rhs old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 intros Different Storage Step. unfold formal_connect in Step.
 destruct lhs as [id|parent field|parent index|parent expr];
 try (exact (formal_bundle_preserves_other invalid site mm node _ rhs old current result Different Step)).
 destruct parent as [id|base port|base index|base expr];
 try (exact (formal_bundle_preserves_other invalid site mm node _ rhs old current result Different Step)).
 destruct base as [mem|r id|r index|r expr]; try (exact (formal_bundle_preserves_other invalid site mm node _ rhs old current result Different Step)).
 destruct (is_memory_data_port true mm mem port field);
 [|exact (formal_bundle_preserves_other invalid site mm node _ rhs old current result Different Step)].
 destruct (formal_connect_bundle invalid site mm _ rhs old current) as [middle|] eqn:Connect; [|discriminate Step].
 destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid) site mm rhs old old) as [source|]; [|discriminate Step].
 unfold write_memory_data in Step. cbn in Step. inversion Step; subst result.
 exact (formal_bundle_preserves_other invalid site mm node _ rhs old current middle Different Connect).
Qed.

Lemma formal_selected_comb_storage_connection_preserves_other invalid site mm node lhs rhs value old current result :
 VM.find node current = Some value -> node != HiF.base_ref lhs ->
 comb_storage_storage_safe mm node (HiF.base_ref lhs) ->
 (match rhs with Eref r => node != HiF.base_ref r | _ => True end) ->
 (match rhs with Eref r => if is_memory_writer_ref mm lhs then
   formal_connect invalid site mm false lhs rhs old current
   else bidirectional_connect_with_memory mm lhs r old current
 | _ => formal_connect invalid site mm false lhs rhs old current end) = Some result ->
 VM.find node result = Some value.
Proof.
 intros Current Different Storage Other Step.
 destruct rhs; try (rewrite (formal_comb_storage_connection_preserves_other invalid site mm node lhs _ old current result Different Storage Step); exact Current).
 destruct (is_memory_writer_ref mm lhs).
 - rewrite (formal_comb_storage_connection_preserves_other invalid site mm node lhs _ old current result Different Storage Step). exact Current.
 - rewrite (bidirectional_connect_with_memory_preserves_other mm node lhs _ old current result Different Other Step). exact Current.
Qed.

Lemma formal_comb_storage_suffix_preserves_value : forall stmts mm node value invalid scope position
 old current result,
 comb_storage_suffix_safe mm node stmts ->
 VM.find node current = Some value ->
 formal_statements invalid scope position mm old false current stmts = Some result ->
 VM.find node result = Some value.
Proof.
 fix IH 1. intros stmts mm node value invalid scope position old current result Safe Current Step.
 destruct stmts as [|st tail].
 - inversion Step; subst; exact Current.
 - destruct Safe as [Head Tail].
   destruct st as [|name t|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no];
     cbn [formal_statements] in Step.
   + eapply IH; eassumption.
   + eapply IH; [exact Tail| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + destruct (VM.find name old); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + destruct (VM.find name old); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + eapply IH; eassumption.
   + destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address scope position 0 [::]) mm expr old old); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + destruct Head as [Different [Nonmemory Source]].
     set (connection := match rhs with
       | Eref r => if is_memory_writer_ref mm lhs then
           formal_connect invalid (validif_raw_address scope position 0 [::]) mm false lhs rhs old current
         else bidirectional_connect_with_memory mm lhs r old current
       | _ => formal_connect invalid (validif_raw_address scope position 0 [::]) mm false lhs rhs old current end).
     assert (Dispatch : match connection with
       | Some next => formal_statements invalid scope (S position)
            mm old false next tail
       | None => None end = Some result).
     { unfold connection. destruct rhs; exact Step. }
     destruct connection as [next|] eqn:Connect; [|discriminate Dispatch].
     eapply IH; [exact Tail| |exact Dispatch].
     eapply (formal_selected_comb_storage_connection_preserves_other invalid (validif_raw_address scope position 0 [::]) mm node lhs rhs value old current next);
       eassumption.
   + destruct Head as [Different Nonmemory].
     destruct (invalidate_ref_with_memory mm false reference (invalid (rcons scope position)) old current)
       as [next|] eqn:Invalidate; [|discriminate Step].
     eapply IH; [exact Tail| |exact Step].
     rewrite (nonmemory_invalidation_preserves_other mm false node reference
       (invalid (rcons scope position)) old current next Different _ Invalidate); [exact Current|].
     destruct reference as [id|parent field|parent index|parent expr]; try exact I.
     destruct parent as [id|base port|base index|base expr]; try exact I.
     destruct base; try exact I. exact Nonmemory.
   + contradiction.
Qed.
Print Assumptions formal_comb_storage_suffix_preserves_value.

Require Import RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Fixpoint memory_seed_description (id : VarOrder.T) (stmts : HiF.hfstmt_seq)
 (previous : option (VarOrder.T * ftype * nat)) : option (VarOrder.T * ftype * nat) :=
 match stmts with
 | Qnil => previous
 | Qcons st tl => memory_seed_description id tl
   (match st with
    | Smem name mem => if id == storage_id mem then Some (name, data_type mem, depth mem) else previous
    | Swhen _ yes no => memory_seed_description id no (memory_seed_description id yes previous)
    | _ => previous end)
 end.
Definition seed_value (contents : memory_initialization) (path : seq VarOrder.T) (description : option (VarOrder.T * ftype * nat)) (fallback : option hvalue) :=
 match description with
 | Some (name, typ, count) => Some (memory_initial_value (contents path name) (Atyp typ count) [::])
 | None => fallback end.
Lemma memory_seed_projection : forall stmts contents path state id previous fallback,
 VM.find id state = seed_value contents path previous fallback ->
 VM.find id (initialize_module_memories contents path stmts state) =
 seed_value contents path (memory_seed_description id stmts previous) fallback.
Proof.
 fix IH 1. intros stmts contents path state id previous fallback Current.
 destruct stmts as [|st tl]; [exact Current|].
 destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
 cbn [initialize_module_memories memory_seed_description];
 try (apply IH; exact Current).
 - case Same: (id == storage_id mem).
   + apply IH. move/eqP: Same => Same. subst id.
     rewrite (RegisterMapFacts.find_add_eq (eqxx (storage_id mem))). reflexivity.
   + apply IH. rewrite RegisterMapFacts.find_add_neq; [exact Current|].
     change (~ (id == storage_id mem)). rewrite Same. discriminate.
 - apply IH. apply IH. apply IH. exact Current.
Qed.
Lemma symbolic_initialization_preserves_nonregister : forall stmts inputs path state id,
 has_register id stmts = false ->
 VM.find id (initialize_symbolic_registers inputs path stmts state) = VM.find id state.
Proof.
 fix IH 1. intros stmts inputs path state id Absent.
 destruct stmts as [|st tl]; [reflexivity|].
 destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
 cbn [initialize_symbolic_registers]; cbn [has_register] in Absent;
 try (apply IH; exact Absent).
 - apply Bool.orb_false_iff in Absent as [Different Tail].
   rewrite (IH tl inputs path _ id Tail).
   rewrite RegisterMapFacts.find_add_neq; [reflexivity|].
   change (~ (id == r)). rewrite Different. discriminate.
 - apply Bool.orb_false_iff in Absent as [Branches Tail].
   apply Bool.orb_false_iff in Branches as [Yes No].
   rewrite (IH tl inputs path _ id Tail) (IH no inputs path _ id No) (IH yes inputs path state id Yes).
   reflexivity.
Qed.
Print Assumptions memory_seed_projection.
Print Assumptions symbolic_initialization_preserves_nonregister.

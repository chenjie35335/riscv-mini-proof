Require Import RegisterInvariants SymbolicUInt.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths FormalInitialization.
Definition map_uint_concrete (id : VarOrder.T) width (state : VM.t hvalue) :=
 exists bits, size bits = width /\ VM.find id state = Some (Gval (Fuint width) bits).
Fixpoint uint_register_declarations (id : VarOrder.T) width (stmts : HiF.hfstmt_seq) : Prop :=
 match stmts with
 | Qnil => True
 | Qcons st tl =>
 (match st with
 | Sreg name reg => id = name -> type reg = Gtyp (Fuint width)
 | Swhen _ yes no => uint_register_declarations id width yes /\ uint_register_declarations id width no
 | _ => True end) /\ uint_register_declarations id width tl end.
Lemma symbolic_add_uint_concrete inputs path state id name width (reg : HiF.hfreg) :
 (id = name -> type reg = Gtyp (Fuint width)) -> map_uint_concrete id width state ->
 map_uint_concrete id width (VM.add name (symbolic_register_value inputs path name (type reg)) state).
Proof.
 intros Typed Current. case Same: (id == name).
 - move/eqP: Same => Same. subst id. rewrite (Typed (Logic.eq_refl _)).
   destruct (symbolic_uint_concrete inputs path name width) as [bits [Width Value]].
   exists bits. split; [exact Width|]. rewrite (RegisterMapFacts.find_add_eq (eqxx name)) Value. reflexivity.
 - destruct Current as [bits [Width Value]]. exists bits. split; [exact Width|].
   rewrite RegisterMapFacts.find_add_neq; [exact Value|]. change (~ (id == name)). rewrite Same. discriminate.
Qed.
Theorem initialize_preserves_uint_concrete : forall (stmts : HiF.hfstmt_seq) inputs path state id width,
 uint_register_declarations id width stmts -> map_uint_concrete id width state ->
 map_uint_concrete id width (initialize_symbolic_registers inputs path stmts state).
Proof.
 fix IH 1. intros stmts inputs path state id width Declarations Current.
 destruct stmts as [|st tl]; [exact Current|]. destruct Declarations as [Head Tail].
 destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
 cbn [initialize_symbolic_registers]; try (apply IH; [exact Tail|exact Current]).
 - apply IH; [exact Tail|]. apply symbolic_add_uint_concrete; assumption.
 - destruct Head as [Yes No]. apply IH; [exact Tail|]. apply IH; [exact No|]. apply IH; [exact Yes|exact Current].
Qed.
Theorem initialize_establishes_uint_concrete : forall (stmts : HiF.hfstmt_seq) inputs path state id width,
 uint_register_declarations id width stmts -> has_register id stmts = true ->
 map_uint_concrete id width (initialize_symbolic_registers inputs path stmts state).
Proof.
 fix IH 1. intros stmts inputs path state id width Declarations Present.
 destruct stmts as [|st tl]; [discriminate Present|]. destruct Declarations as [Head Tail].
 destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
 cbn [initialize_symbolic_registers]; cbn [has_register] in Present;
 try (apply IH; [exact Tail|exact Present]).
 - move/orP: Present => [Same|InTail].
   + move/eqP: Same => Same. subst id. apply initialize_preserves_uint_concrete; [exact Tail|].
     rewrite (Head (Logic.eq_refl _)).
     destruct (symbolic_uint_concrete inputs path r width) as [bits [Width Value]].
     exists bits. split; [exact Width|]. rewrite (RegisterMapFacts.find_add_eq (eqxx r)) Value. reflexivity.
   + apply IH; [exact Tail|exact InTail].
 - destruct Head as [Yes No]. move/orP: Present => [InBranches|InTail].
   + apply initialize_preserves_uint_concrete; [exact Tail|]. move/orP: InBranches => [InYes|InNo].
     * apply initialize_preserves_uint_concrete; [exact No|]. apply IH; [exact Yes|exact InYes].
     * apply IH; [exact No|exact InNo].
   + apply IH; [exact Tail|exact InTail].
Qed.
Print Assumptions initialize_establishes_uint_concrete.

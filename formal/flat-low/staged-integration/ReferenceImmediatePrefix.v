Require Import ReferenceLoadImmediate CoreSocModel ComparisonNodes DUTRedirectDecode.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem immediate_stable_mux_prefix invalid old count width word prefix (node guard yes:nat->VarOrder.T) :
 size word=width ->
 (forall n,(n<count)%coq_nat ->forall value,
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories
 (@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T(guard n)))
 (@Eref VarOrder.T(@Eid VarOrder.T(yes n)))
 (@Eref VarOrder.T(@Eid VarOrder.T(match n with O=>prefix|S before=>node before end))))old old=Some(Gval(Fuint width)value)) ->
 VM.find(node n)old=Some(Gval(Fuint width)value)) ->
 (forall n,(n<count)%coq_nat ->VM.find(guard n)old=Some(Gval(Fuint 1)[::false])) ->
 (forall n,(n<count)%coq_nat ->exists value,VM.find(yes n)old=Some value /\type_of_val value=Gtyp(Fuint width)) ->
 VM.find prefix old=Some(Gval(Fuint width)word) ->
 forall n,(n<count)%coq_nat ->VM.find(node n)old=Some(Gval(Fuint width)word).
Proof.
 intros Size Node Guard Typed Prefix n. induction n as[|n IH];intro Bound;
 apply(Node _ Bound word);intro site;
 destruct(Typed _ Bound)as[other[Other Shape]];
 eapply(immediate_selected_mux _ _ _ _ _ _ _ word other false);
 try exact Size;try exact(Guard _ Bound);try exact Other;try exact Shape.
 - exact Prefix.
 - exact(IH ltac:(lia)).
Qed.

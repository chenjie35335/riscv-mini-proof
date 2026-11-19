Require Import StoreWriteValidCommitCertificate FormalUIntRegisterCommitSource CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem store_write_valid_commit invalid old current result old_value bit reset :
 VM.find 8028 old=Some old_value ->type_of_val old_value=Gtyp(Fuint 1) ->
 VM.find 65 old=Some(Gval(Fuint 1)[::reset]) ->
 VM.find 8027 old=Some(Gval(Fuint 1)[::bit]) ->
 formal_value_iter invalid flat_memories old true current flat_statements=Some result ->
 VM.find 8028 result=Some(Gval(Fuint 1)[::if reset then false else bit]).
Proof.
 intros Old Typed Reset Data Step.
 destruct(formal_committed_uint_register_mux_observation 8534 flat_statements joint_register_8028_decl joint_register_8028_mid joint_register_8028_tail
 8028 joint_register_8028_reg (@Eref VarOrder.T(@Eid VarOrder.T 65)) (@Econst VarOrder.T(Fuint 1)[::false]) (@Eref VarOrder.T(@Eid VarOrder.T 8027)) invalid flat_memories old current result old_value 1
 joint_register_8028_position joint_register_8028_split joint_register_8028_straight joint_register_8028_mid_safe joint_register_8028_tail_safe Old Typed joint_register_8028_identity Step)as[source[value[Eval[Adapt Value]]]].
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]in Eval. rewrite Reset in Eval.
 destruct reset;cbn in Eval.
 - unfold eval_type_of_expr in Eval. cbn[type_of_expr' eval_type_of_ref]in Eval.
   rewrite Data in Eval. inversion Eval;subst source.
   vm_compute in Adapt. inversion Adapt;subst value. exact Value.
 - rewrite Data in Eval. destruct bit;inversion Eval;subst source;
   vm_compute in Adapt;inversion Adapt;subst value;exact Value.
Qed.

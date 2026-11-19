Require Import StoreWidthCommitCertificate FormalUIntRegisterCommitSource CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem store_width_commit_reset invalid old current result old_value word :
 VM.find 8040 old=Some old_value ->type_of_val old_value=Gtyp(Fuint 6) ->
 VM.find 65 old=Some(Gval(Fuint 1)[::true]) ->
 VM.find 8002 old=Some(Gval(Fuint 6)word) ->size word=6%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements=Some result ->
 VM.find 8040 result=Some(Gval(Fuint 6)(zeros 6)).
Proof.
 intros Old Typed Reset Data Size Step.
 destruct(formal_committed_uint_register_mux_observation 8546 flat_statements joint_register_8040_decl joint_register_8040_mid joint_register_8040_tail
 8040 joint_register_8040_reg (@Eref VarOrder.T(@Eid VarOrder.T 65)) (@Econst VarOrder.T(Fuint 1)[::false]) (@Eref VarOrder.T(@Eid VarOrder.T 8002)) invalid flat_memories old current result old_value 6
 joint_register_8040_position joint_register_8040_split joint_register_8040_straight joint_register_8040_mid_safe joint_register_8040_tail_safe Old Typed joint_register_8040_identity Step)as[source[value[Eval[Adapt Value]]]].
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]in Eval. rewrite Reset in Eval. cbn in Eval.
 cbn[eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type adapt_hvalue_as_type]in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval. rewrite Data in Eval. cbn [type_of_val make_ftype_explicit extend_hvalue_as_type adapt_hvalue_as_type] in Eval.
 inversion Eval;subst source.
 vm_compute in Adapt. inversion Adapt;subst value. exact Value.
Qed.

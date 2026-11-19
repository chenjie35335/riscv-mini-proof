Require Import StoreMaskCommitCertificate FormalUIntRegisterCommitSource CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem store_mask_commit_reset invalid old current result old_value word :
 VM.find 7924 old=Some old_value ->type_of_val old_value=Gtyp(Fuint 4) ->
 VM.find 65 old=Some(Gval(Fuint 1)[::true]) ->
 VM.find 80 old=Some(Gval(Fuint 4)word) ->size word=4%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements=Some result ->
 VM.find 7924 result=Some(Gval(Fuint 4)(zeros 4)).
Proof.
 intros Old Typed Reset Data Size Step.
 destruct(formal_committed_uint_register_mux_observation 8430 flat_statements joint_register_7924_decl joint_register_7924_mid joint_register_7924_tail
 7924 joint_register_7924_reg (@Eref VarOrder.T(@Eid VarOrder.T 65)) (@Econst VarOrder.T(Fuint 1)[::false]) (@Eref VarOrder.T(@Eid VarOrder.T 80)) invalid flat_memories old current result old_value 4
 joint_register_7924_position joint_register_7924_split joint_register_7924_straight joint_register_7924_mid_safe joint_register_7924_tail_safe Old Typed joint_register_7924_identity Step)as[source[value[Eval[Adapt Value]]]].
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]in Eval. rewrite Reset in Eval. cbn in Eval.
 cbn[eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type adapt_hvalue_as_type]in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval. rewrite Data in Eval. cbn [type_of_val make_ftype_explicit extend_hvalue_as_type adapt_hvalue_as_type] in Eval.
 inversion Eval;subst source.
 vm_compute in Adapt. inversion Adapt;subst value. exact Value.
Qed.

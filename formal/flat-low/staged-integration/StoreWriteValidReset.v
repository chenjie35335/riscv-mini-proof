Require Import StoreWriteValidCommitCertificate FormalUIntRegisterCommitSource CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem store_write_valid_reset_commit invalid old current result old_value request_value :
 VM.find 8028 old=Some old_value ->type_of_val old_value=Gtyp(Fuint 1) ->
 VM.find 65 old=Some(Gval(Fuint 1)[::true]) ->
 VM.find 8027 old=Some request_value ->type_of_val request_value=Gtyp(Fuint 1) ->
 formal_value_iter invalid flat_memories old true current flat_statements=Some result ->
 VM.find 8028 result=Some(Gval(Fuint 1)(zeros 1)).
Proof.
 intros Old Typed Reset Data RequestType Step.
 destruct(formal_committed_uint_register_mux_observation 8534 flat_statements joint_register_8028_decl joint_register_8028_mid joint_register_8028_tail
 8028 joint_register_8028_reg (@Eref VarOrder.T(@Eid VarOrder.T 65)) (@Econst VarOrder.T(Fuint 1)[::false]) (@Eref VarOrder.T(@Eid VarOrder.T 8027)) invalid flat_memories old current result old_value 1
 joint_register_8028_position joint_register_8028_split joint_register_8028_straight joint_register_8028_mid_safe joint_register_8028_tail_safe Old Typed joint_register_8028_identity Step)as[source[value[Eval[Adapt Value]]]].
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]in Eval. rewrite Reset in Eval. cbn in Eval.
 cbn[eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type adapt_hvalue_as_type]in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval. rewrite Data in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval. cbn [option_map] in Eval. rewrite RequestType in Eval. cbn [type_of_val make_ftype_explicit extend_hvalue_as_type adapt_hvalue_as_type] in Eval.
 inversion Eval;subst source.
 vm_compute in Adapt. inversion Adapt;subst value. exact Value.
Qed.
Require Import StoreWriteCompareType StoreWriteValidReachableType StoreDataCycleCommit FormalObservationCommit StagedFlatCircuitIteration FormalLocalHistory.
Local Opaque generated_modules generated_top.
Theorem store_write_valid_reset_cycle memory inputs k observed next :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::true]) ->
 VM.find 8028(top_environment next)=Some(Gval(Fuint 1)(zeros 1)).
Proof.
 intros Observe Legal Next Reset.
 destruct(store_write_valid_observed_type memory inputs k observed Observe)as[value[Old Typed]].
 destruct(store_write_compare_observed_type memory inputs k observed Observe Legal)as[request_value[Request RequestType]].
 pose proof(store_observed_core_reset memory inputs k observed true Reset Observe)as Control.
 rewrite(observation_then_commit memory inputs k observed Observe)in Next.
 destruct(flat_iteration_projection _ observed true next Next)as[before[after[Before[Step After]]]].
 assert(Top:top_environment observed=before)by(unfold top_environment;rewrite Before;reflexivity).
 rewrite <-Top in Step. unfold top_environment. rewrite After.
 exact(store_write_valid_reset_commit _ _ _ _ value request_value Old Typed Control Request RequestType Step).
Qed.

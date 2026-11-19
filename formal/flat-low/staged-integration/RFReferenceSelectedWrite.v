Require Import RFReferenceNopStorageCertificates RFSelectedLowMux RFReferenceWriteEffect RFReferenceNopHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_reference_selected_write_step index stage slot invalid old result bit selected word :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->(stage<36)%coq_nat ->(slot<rf_reference_write_depth stage)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(rf_reference_write_condition index stage slot)old old=Some(Gval(Fuint 1)[::bit])) ->
 VM.find(if bit then rf_reference_write_input index stage slot else rf_reference_write_prior index stage)old=Some selected ->
 rf_reference_low_word word selected ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find(rf_reference_write_selector index stage slot)result=Some value /\rf_reference_low_word word value.
Proof.
 intros Lower Upper Stage Slot Condition Selected Low Step.
 exact(rf_selected_low_mux rf_reference_write_offsets rf_reference_write_nodes
 (rf_reference_write_selector index stage slot)(rf_reference_write_condition index stage slot)
 (rf_reference_write_input index stage slot)(rf_reference_write_prior index stage)
 invalid old result bit selected word rf_reference_write_positions rf_reference_write_safety
 (rf_reference_write_member index stage slot Lower Upper Stage Slot)Condition Selected Low Step).
Qed.
Theorem rf_reference_selected_gate_step index stage invalid old result bit selected word :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->(stage<36)%coq_nat ->
 VM.find(rf_reference_chain_guard stage)old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find(if bit then rf_reference_write_selector index stage(rf_reference_write_depth stage-1) else rf_reference_write_prior index stage)old=Some selected ->
 rf_reference_low_word word selected ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find(rf_reference_chain_node index stage)result=Some value /\rf_reference_low_word word value.
Proof.
 intros Lower Upper Stage Guard Selected Low Step.
 eapply(rf_selected_low_mux rf_reference_chain_offsets rf_reference_chain_nodes
 (rf_reference_chain_node index stage)(@Eref VarOrder.T(@Eid VarOrder.T(rf_reference_chain_guard stage)))
 (rf_reference_write_selector index stage(rf_reference_write_depth stage-1))(rf_reference_write_prior index stage)
 invalid old result bit selected word);[exact rf_reference_chain_positions|exact rf_reference_chain_safety| | |exact Selected|exact Low|exact Step].
 - rewrite <-(rf_reference_gate_expression index stage Stage).
   exact(rf_reference_chain_member index stage(conj Lower Upper)Stage).
 - intro site;exact Guard.
Qed.
Theorem rf_reference_selected_stage_three_steps index stage invalid s0 s1 s2 s3 rd opcode permitted data_word prior_word :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->(stage<36)%coq_nat ->
 VM.find 3221 s0=Some(Gval(Fuint 5)rd) ->VM.find 3221 s1=Some(Gval(Fuint 5)rd) ->
 (opcode=true ->exists value,VM.find(rf_reference_write_data stage)s0=Some value /\rf_reference_low_word data_word value) ->
 (opcode=true ->exists value,VM.find(rf_reference_write_data stage)s1=Some value /\rf_reference_low_word data_word value) ->
 (exists value,VM.find(rf_reference_write_prior index stage)s0=Some value /\rf_reference_low_word prior_word value) ->
 (exists value,VM.find(rf_reference_write_prior index stage)s1=Some value /\rf_reference_low_word prior_word value) ->
 (exists value,VM.find(rf_reference_write_prior index stage)s2=Some value /\rf_reference_low_word prior_word value) ->
 (rf_reference_write_depth stage=2%nat ->VM.find(rf_reference_permission_node stage)s1=Some(Gval(Fuint 1)[::permitted])) ->
 VM.find(rf_reference_chain_guard stage)s2=Some(Gval(Fuint 1)[::opcode]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 exists value,VM.find(rf_reference_chain_node index stage)s3=Some value /\
 rf_reference_low_word(if opcode && rf_reference_permission_value stage permitted && (index==to_nat rd) then data_word else prior_word)value.
Proof.
 intros Lower Upper Stage Rd0 Rd1 Data0 Data1 Prior0 Prior1 Prior2 Permission Opcode S1 S2 S3.
 destruct opcode.
 - exact(rf_reference_write_stage_three_steps index stage invalid s0 s1 s2 s3 rd true permitted data_word prior_word Lower Upper Stage Rd0 Rd1(Data0(Logic.eq_refl true))(Data1(Logic.eq_refl true))Prior0 Prior1 Prior2 Permission Opcode S1 S2 S3).
 - destruct Prior2 as[value[Value Low]].
   exact(rf_reference_selected_gate_step index stage invalid s2 s3 false value prior_word Lower Upper Stage Opcode Value Low S3).
Qed.

Theorem rf_reference_selected_effect_history invalid history (limit start:nat) index rd initial guards permissions words :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(N.of_nat(2177-index)%nat)(history t)=Some value /\rf_reference_low_word initial value) ->
 (forall stage t,(stage<36)%coq_nat ->guards stage=true ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall count time,(count<=36)%coq_nat ->(Nat.add start(Nat.mul 3 count)<=time)%coq_nat ->(time<=limit)%coq_nat ->
 exists value,VM.find(rf_reference_fold_node index count)(history time)=Some value /\
 rf_reference_low_word(rf_reference_fold_word guards permissions words(to_nat rd)index initial count)value.
Proof.
 intros Lower Upper Rd Initial Data Guards Permissions Steps count. induction count as[|count IH];intros time Bound Ready Within.
 - apply Initial;lia.
 - destruct time as[|[|[|time]]];try lia.
   cbn [rf_reference_fold_node rf_reference_fold_word].
   eapply(rf_reference_selected_stage_three_steps index count invalid(history time)(history(S time))(history(S(S time)))(history(S(S(S time))))rd(guards count)(permissions count)(words count)(rf_reference_fold_word guards permissions words(to_nat rd)index initial count)Lower Upper ltac:(lia)).
   + apply Rd;lia.
   + apply Rd;lia.
   + intro Selected. apply Data;try exact Selected;lia.
   + intro Selected. apply Data;try exact Selected;lia.
   + rewrite rf_reference_prior_fold. apply IH;lia.
   + rewrite rf_reference_prior_fold. apply IH;lia.
   + rewrite rf_reference_prior_fold. apply IH;lia.
   + intro Depth. apply Permissions;try assumption;lia.
   + apply Guards;lia.
   + apply Steps;lia.
   + apply Steps;lia.
   + apply Steps;lia.
Qed.

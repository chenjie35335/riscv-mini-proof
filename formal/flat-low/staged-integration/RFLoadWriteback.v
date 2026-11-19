Require Import FormalGroundNodeEquation RFAluWritebackObserved RFWritebackSelection RFPreviewEffect JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation CoreSocModel ComparisonNodes RFReadForwarding.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_load_writeback_signed_selected node condition yes no invalid old result bit selected word :
 List.In(node,@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T condition))(@Eref VarOrder.T(@Eid VarOrder.T yes))(@Eref VarOrder.T(@Eid VarOrder.T no)))joint_update_expected_nodes ->
 VM.find condition old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find(if bit then yes else no)old=Some selected ->rf_signed_low_word word selected ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find node result=Some value /\rf_signed_low_word word value.
Proof.
 intros Member Condition Selected [width[raw[Value[Size[Wide Low]]]]] Step. subst selected.
 destruct(selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes node _ joint_update_node_positions joint_update_node_safety Member)as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail node _ invalid flat_memories old false old result Position Step)as[value Eval].
 pose proof Eval as Original.
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]in Eval. rewrite Condition in Eval.
 destruct bit;cbn in Eval;rewrite Selected in Eval;
 destruct(eval_type_of_expr _)as[typ|]eqn:Branch;try discriminate;
 unfold extend_hvalue_as_type in Eval;destruct typ as[ground|elt length|fields];try discriminate;
 destruct ground;cbn[type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type]in Eval;try discriminate;
 inversion Eval;subst value.
 all: eexists;split;[eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg|exact Original|reflexivity|exact Step]|].
 all: destruct(rf_signed_low_resize word (Gval(Fsint width)raw) (maxn width n))as[adapted[Adapt Result]].
 all: try (exists width,raw;repeat split;assumption).
 all: try (intros source bits Equal;inversion Equal;subst;apply leq_maxl).
 all: cbn[adapt_hvalue_as_type]in Adapt;inversion Adapt;subst;exact Result.
Qed.
Theorem rf_load_writeback_history invalid history limit result :
 size result=33%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 7756(history t)=Some(Gval(Fuint 2)[::true;false])) ->
 (forall t,(12<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7904(history t)=Some(Gval(Fsint 33)result)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(17<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 786(history t)=Some(Gval(Fuint 32)(take 32 result)).
Proof.
 intros Size Modes Loads Steps t Lower Upper.
 assert (Guards:forall u,(1<=u)%coq_nat ->(u<=limit)%coq_nat ->
 VM.find 7931(history u)=Some(Gval(Fuint 1)[::true]) /\
 VM.find 7933(history u)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 7935(history u)=Some(Gval(Fuint 1)[::false])).
 { intros [|u] Lo Hi;[lia|]. exact(rf_writeback_decode_step invalid(history u)(history u)(history(S u))true false(Modes u ltac:(lia))(Steps u ltac:(lia))). }
 assert(A:VM.find 7904(history(Nat.sub t 5)%nat)=Some(Gval(Fsint 33)result)).
 { apply Loads;lia. }
 assert(L:rf_signed_low_word (take 32 result)(Gval(Fsint 33)result)).
 { exists 33%nat,result;repeat split;try reflexivity;exact Size. }
 destruct(Guards(Nat.sub t 5)%nat ltac:(lia)ltac:(lia))as[G1 _].
 destruct(rf_load_writeback_signed_selected 7932 7931 7904 7926 invalid(history(Nat.sub t 5)%nat)(history(S(Nat.sub t 5)))true _ (take 32 result) ltac:(exact(rf_writeback_member 1 ltac:(lia)))G1 A L(Steps(Nat.sub t 5)%nat ltac:(lia)))as[v1[V1 L1]].
 replace(S(Nat.sub t 5))with(Nat.sub t 4)%nat in V1 by lia.
 destruct(Guards(Nat.sub t 4)%nat ltac:(lia)ltac:(lia))as[_[G2 _]].
 destruct(rf_writeback_signed_selected 7934 7933 7929 7932 invalid(history(Nat.sub t 4)%nat)(history(S(Nat.sub t 4)))_ (take 32 result) ltac:(exact(rf_writeback_member 3 ltac:(lia)))G2 V1 L1(Steps(Nat.sub t 4)%nat ltac:(lia)))as[v2[V2 L2]].
 replace(S(Nat.sub t 4))with(Nat.sub t 3)%nat in V2 by lia.
 destruct(Guards(Nat.sub t 3)%nat ltac:(lia)ltac:(lia))as[_[_ G3]].
 destruct(rf_writeback_signed_selected 7936 7935 7930 7934 invalid(history(Nat.sub t 3)%nat)(history(S(Nat.sub t 3)))_ (take 32 result) ltac:(exact(rf_writeback_member 5 ltac:(lia)))G3 V2 L2(Steps(Nat.sub t 3)%nat ltac:(lia)))as[v3[V3[width[raw[Value[RawSize[Wide Low]]]]]]].
 subst v3. replace(S(Nat.sub t 3))with(Nat.sub t 2)%nat in V3 by lia.
 assert(Cast:VM.find 7937(history(Nat.sub t 1)%nat)=Some(Gval(Fuint width)raw)).
 { replace(Nat.sub t 1)%nat with(S(Nat.sub t 2))by lia.
 apply(rf_writeback_node_step invalid(history(Nat.sub t 2)%nat)(history(Nat.sub t 2)%nat)(history(S(Nat.sub t 2)))6 _ (Fuint width));[lia| |reflexivity|apply Steps;lia].
 cbn[rf_writeback_nodes nth snd joint_update_expr_7937 eval_hfexpr_with_memory eval_href_with_memory]. rewrite V3. reflexivity. }
 replace t with(S(Nat.sub t 1))at 1 by lia. rewrite -Low.
 apply(rf_preview_data_port_exact invalid(history(Nat.sub t 1)%nat)(history(Nat.sub t 1)%nat)(history(S(Nat.sub t 1)))width raw);[exact/leP|exact RawSize|exact Cast|apply Steps;lia].
Qed.
Lemma rf_load_result_size low middle high raw b0 b1 :
 size raw=32%nat -> size(rf_load_result low middle high raw b0 b1)=33%nat.
Proof.
 intro Size. unfold rf_load_result,rf_load_selected.
 destruct low,middle,high;cbn[negb andb];
 unfold sext_to;rewrite ?size_sext ?size_zext ?size_take ?(rf_load_shift_size raw b0 b1 Size) ?Size;reflexivity.
Qed.
Theorem rf_load_result_history_stable invalid history limit low middle high b0 b1 rest raw :
 size raw=32%nat ->
 (forall t,(t<=limit)%coq_nat -> VM.find 7755(history t)=Some(Gval(Fuint 3)[::low;middle;high])) ->
 (forall t,(t<=limit)%coq_nat -> VM.find 7752(history t)=Some(Gval(Fuint 32)(b0::b1::rest))) ->
 (forall t,(t<=limit)%coq_nat -> VM.find 9222(history t)=Some(Gval(Fuint 32)raw)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(12<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 7904(history t)=Some(Gval(Fsint 33)(rf_load_result low middle high raw b0 b1)).
Proof.
 intros Size Modes Addresses Raws Steps t Lower Upper.
 pose proof(rf_load_from_register_history invalid (fun i=>history(Nat.add(Nat.sub t 12)i)) low middle high b0 b1 rest raw Size)as Load.
 assert(Start:(Nat.add(Nat.sub t 12)0<=limit)%coq_nat)by lia.
 specialize(Load(Modes _ Start)(Addresses _ Start)(Raws _ Start)).
 assert(ShiftSteps:forall i,(i<12)%coq_nat ->
 formal_value_iter invalid flat_memories(history(Nat.add(Nat.sub t 12)i))false(history(Nat.add(Nat.sub t 12)i))flat_statements=Some(history(Nat.add(Nat.sub t 12)(S i)))).
 { intros i Bound. replace(Nat.add(Nat.sub t 12)(S i))with(S(Nat.add(Nat.sub t 12)i))by lia. apply Steps;lia. }
 specialize(Load ShiftSteps). cbn beta in Load. replace(Nat.add(Nat.sub t 12)12)with t in Load by lia. exact Load.
Qed.
Theorem rf_load_writeback_register_history invalid history limit low middle high b0 b1 rest raw :
 size raw=32%nat ->
 (forall t,(t<=limit)%coq_nat -> VM.find 7756(history t)=Some(Gval(Fuint 2)[::true;false])) ->
 (forall t,(t<=limit)%coq_nat -> VM.find 7755(history t)=Some(Gval(Fuint 3)[::low;middle;high])) ->
 (forall t,(t<=limit)%coq_nat -> VM.find 7752(history t)=Some(Gval(Fuint 32)(b0::b1::rest))) ->
 (forall t,(t<=limit)%coq_nat -> VM.find 9222(history t)=Some(Gval(Fuint 32)raw)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(17<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 786(history t)=Some(Gval(Fuint 32)(take 32(rf_load_result low middle high raw b0 b1))).
Proof.
 intros Size Select Modes Addresses Raws Steps.
 apply(rf_load_writeback_history invalid history limit _ (rf_load_result_size low middle high raw b0 b1 Size) Select).
 - exact(rf_load_result_history_stable invalid history limit low middle high b0 b1 rest raw Size Modes Addresses Raws Steps).
 - exact Steps.
Qed.

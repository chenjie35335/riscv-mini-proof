Require Import ReferenceControlNodeCertificates2 ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence2 ReferenceControlNodeCongruence3 ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants ReferenceControlExpressions ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCertificates1 RFReferenceNopIngress RFReferenceNopHistory RFReadPorts ReferenceRedirectSpine ConcreteDecodeOperations CoreSocModel ComparisonNodes RFPreviewEffect RFArchitecturalNormalRelation RFWriteEffect DataAddressExpressionCertificates DataAddressPositionCertificate DataAddressSafetyCertificate SelectedNodeSafety FormalTypedNodeEquation FormalSuccessfulNodeEvaluation UIntMuxResultType ConcreteFormalValidIf FormalDeclaredWireCheck RFReadForwarding.
From Coq Require Import ZArith List Lia NArith.Nnat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_second_bank_read_address_port : VarOrder.T := 2622.
Definition reference_second_bank_read_stage (index:nat) : VarOrder.T := N.of_nat (Nat.add 2773 index).
Definition reference_second_bank_read_condition index : hfexpr VarOrder.T :=
 @Eprim_binop VarOrder.T (Bcomp Beq)
 (@Econst VarOrder.T (Fuint (rf_preview_index_width index)) (from_N (rf_preview_index_width index) (N.of_nat index)))
 (@Eref VarOrder.T (@Eid VarOrder.T (reference_second_bank_read_address_port))).
Definition reference_second_bank_read_stage_expr (index:nat) : hfexpr VarOrder.T :=
 if index is O then @Evalidif VarOrder.T (reference_second_bank_read_condition 0) (@Eref VarOrder.T (@Eid VarOrder.T 2177))
 else @Emux VarOrder.T (reference_second_bank_read_condition index)
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (Nat.sub 2177 index))))
 (@Eref VarOrder.T (@Eid VarOrder.T (reference_second_bank_read_stage (index-1)))).
Lemma reference_second_bank_read_stage_member (index:nat) : (index < 32)%coq_nat ->
 List.In (reference_second_bank_read_stage index,reference_second_bank_read_stage_expr index) (if Nat.ltb index 10 then reference_control_2_nodes else reference_control_2_nodes).
Proof. intro Bound.
 destruct index as [|index];[exact reference_control_member_2773|].
 destruct index as [|index];[exact reference_control_member_2774|].
 destruct index as [|index];[exact reference_control_member_2775|].
 destruct index as [|index];[exact reference_control_member_2776|].
 destruct index as [|index];[exact reference_control_member_2777|].
 destruct index as [|index];[exact reference_control_member_2778|].
 destruct index as [|index];[exact reference_control_member_2779|].
 destruct index as [|index];[exact reference_control_member_2780|].
 destruct index as [|index];[exact reference_control_member_2781|].
 destruct index as [|index];[exact reference_control_member_2782|].
 destruct index as [|index];[exact reference_control_member_2783|].
 destruct index as [|index];[exact reference_control_member_2784|].
 destruct index as [|index];[exact reference_control_member_2785|].
 destruct index as [|index];[exact reference_control_member_2786|].
 destruct index as [|index];[exact reference_control_member_2787|].
 destruct index as [|index];[exact reference_control_member_2788|].
 destruct index as [|index];[exact reference_control_member_2789|].
 destruct index as [|index];[exact reference_control_member_2790|].
 destruct index as [|index];[exact reference_control_member_2791|].
 destruct index as [|index];[exact reference_control_member_2792|].
 destruct index as [|index];[exact reference_control_member_2793|].
 destruct index as [|index];[exact reference_control_member_2794|].
 destruct index as [|index];[exact reference_control_member_2795|].
 destruct index as [|index];[exact reference_control_member_2796|].
 destruct index as [|index];[exact reference_control_member_2797|].
 destruct index as [|index];[exact reference_control_member_2798|].
 destruct index as [|index];[exact reference_control_member_2799|].
 destruct index as [|index];[exact reference_control_member_2800|].
 destruct index as [|index];[exact reference_control_member_2801|].
 destruct index as [|index];[exact reference_control_member_2802|].
 destruct index as [|index];[exact reference_control_member_2803|].
 destruct index as [|index];[exact reference_control_member_2804|].
 lia. Qed.

Lemma reference_second_bank_read_safe_position index : (index<32)%coq_nat -> exists count tail,
 straight_drop count flat_statements = Some (Qcons (Snode (reference_second_bank_read_stage index) (reference_second_bank_read_stage_expr index)) tail) /\
 formal_typed_suffix_safe flat_memories (reference_second_bank_read_stage index) tail /\ has_register (reference_second_bank_read_stage index) flat_statements = false.
Proof.
 intro Bound. pose proof (reference_second_bank_read_stage_member index Bound) as Member.
 destruct (Nat.ltb index 10).
 - exact (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements reference_control_2_nodes _ _ reference_control_2_positions reference_control_2_safety Member).
 - exact (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements reference_control_2_nodes _ _ reference_control_2_positions reference_control_2_safety Member).
Qed.
Lemma reference_second_bank_read_condition_value index invalid site mm old address :
 (index < 32)%coq_nat -> VM.find (reference_second_bank_read_address_port) old = Some (Gval (Fuint 5) address) ->
 eval_hfexpr_validif_policy (isolated_validif_policy invalid) site mm (reference_second_bank_read_condition index) old old =
 Some (Gval (Fuint 1) [::index == to_nat address]).
Proof.
 intros Bound Address. cbn [reference_second_bank_read_condition eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Address size_from_N ltnn.
 assert (Constant : zext_to (rf_preview_index_width index) (from_N (rf_preview_index_width index) (N.of_nat index)) = from_N (rf_preview_index_width index) (N.of_nat index)).
 { unfold zext_to,zext. rewrite size_from_N subnn cats0. reflexivity. }
 rewrite Constant. unfold eval_binop. cbn [eval_binop_basic]. rewrite refine_concrete_uint.
 rewrite (rf_preview_index_exact index Bound) rf_preview_rd_match. reflexivity.
Qed.
Lemma reference_second_bank_read_base_type inputs path site mm old address word value :
 VM.find (reference_second_bank_read_address_port) old = Some (Gval (Fuint 5) address) ->
 VM.find 2177 old = Some (Gval (Fuint 32) word) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm (reference_second_bank_read_stage_expr 0) old old = Some value ->
 type_of_val value = Gtyp (Fuint 32).
Proof.
 intros Address Word Eval.
 change (eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm
 (@Evalidif VarOrder.T (reference_second_bank_read_condition 0) (@Eref VarOrder.T (@Eid VarOrder.T 2177))) old old = Some value) in Eval.
 cbn [eval_hfexpr_validif_policy] in Eval.
 rewrite (reference_second_bank_read_condition_value 0 _ _ _ _ address ltac:(lia) Address) in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref eval_hfexpr_validif_policy eval_href_validif_policy] in Eval. rewrite Word in Eval.
 destruct (0%nat == to_nat address);cbn [validif_policy_result is_zero] in Eval;
 unfold isolated_validif_policy,formal_invalid_policy in Eval;cbn [input_value_of_type] in Eval;
 inversion Eval;reflexivity.
Qed.
Lemma reference_second_bank_read_base_step_type inputs path old result address word :
 VM.find (reference_second_bank_read_address_port) old = Some (Gval (Fuint 5) address) ->
 VM.find 2177 old = Some (Gval (Fuint 32) word) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (reference_second_bank_read_stage 0) result = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros Address Word Step.
 destruct (reference_second_bank_read_safe_position 0 ltac:(lia)) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ _ flat_memories old false old result Position Step) as [value Eval].
 assert (Typed : type_of_val value = Gtyp (Fuint 32)) by (eapply reference_second_bank_read_base_type;[exact Address|exact Word|exact Eval]).
 exists value. split;[|exact Typed]. eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma reference_second_bank_read_base_step_zero invalid old result address word :
 VM.find (reference_second_bank_read_address_port) old = Some (Gval (Fuint 5) address) -> to_nat address = 0%nat ->
 VM.find 2177 old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (reference_second_bank_read_stage 0) result = Some (Gval (Fuint 32) word).
Proof.
 intros Address Zero Word Step.
 destruct (reference_second_bank_read_safe_position 0 ltac:(lia)) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories (@Evalidif VarOrder.T (reference_second_bank_read_condition 0) (@Eref VarOrder.T (@Eid VarOrder.T 2177))) old old = Some (Gval (Fuint 32) word)).
 cbn [eval_hfexpr_validif_policy]. rewrite (reference_second_bank_read_condition_value 0 _ _ _ _ address ltac:(lia) Address) Zero.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Word. reflexivity.
Qed.
Lemma reference_second_bank_read_successor_step_type index invalid old result left right :
 (S index < 32)%coq_nat ->
 VM.find (N.of_nat (Nat.sub 2177 (S index))) old = Some left -> type_of_val left = Gtyp (Fuint 32) ->
 VM.find (reference_second_bank_read_stage index) old = Some right -> type_of_val right = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (reference_second_bank_read_stage (S index)) result = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros Bound Left LeftType Right RightType Step.
 destruct (reference_second_bank_read_safe_position (S index) Bound) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Position Step) as [value Eval].
 pose proof Eval as RawEval.
 cbn [reference_second_bank_read_stage_expr] in Eval. rewrite subn1 in Eval; cbn [predn] in Eval.
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (reference_second_bank_read_condition (S index))
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (Nat.sub 2177 (S index))))) (@Eref VarOrder.T (@Eid VarOrder.T (reference_second_bank_read_stage index)))) old old = Some value) in Eval.
 assert (Typed : type_of_val value = Gtyp (Fuint 32)) by (eapply uint_mux_result_type;[exact Left|exact LeftType|exact Right|exact RightType|exact Eval]).
 exists value. split;[|exact Typed]. eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact RawEval|exact Typed|exact Step].
Qed.
Lemma reference_second_bank_read_successor_step_exact index invalid old result address left right word :
 (S index < 32)%coq_nat ->
 VM.find (reference_second_bank_read_address_port) old = Some (Gval (Fuint 5) address) ->
 VM.find (N.of_nat (Nat.sub 2177 (S index))) old = Some left -> type_of_val left = Gtyp (Fuint 32) ->
 VM.find (reference_second_bank_read_stage index) old = Some right -> type_of_val right = Gtyp (Fuint 32) ->
 (if S index == to_nat address then left else right) = Gval (Fuint 32) word -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (reference_second_bank_read_stage (S index)) result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Address Left LeftType Right RightType Selected Size Step.
 destruct (reference_second_bank_read_safe_position (S index) Bound) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [reference_second_bank_read_stage_expr]. rewrite subn1. cbn [predn].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories (@Emux VarOrder.T (reference_second_bank_read_condition (S index))
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (Nat.sub 2177 (S index))))) (@Eref VarOrder.T (@Eid VarOrder.T (reference_second_bank_read_stage index)))) old old = Some (Gval (Fuint 32) word)).
 eapply rf_read_mux_exact;[intros site;exact (reference_second_bank_read_condition_value (S index) invalid site flat_memories old address Bound Address)|exact Left|exact LeftType|exact Right|exact RightType|exact Selected|exact Size].
Qed.
Lemma reference_second_bank_read_stage_history_type inputs path history (limit start:nat) bank address :
 (forall t index, (start <= t)%coq_nat -> (t <= limit)%coq_nat -> (index < 32)%coq_nat -> size (bank index)=32%nat /\ VM.find (N.of_nat (Nat.sub 2177 index)) (history t)=Some(Gval(Fuint 32)(bank index))) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (start <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_second_bank_read_address_port) (history time) = Some (Gval (Fuint 5) address)) ->
 forall index time, (index < 32)%coq_nat -> (Nat.add (Nat.add start index) 1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find (reference_second_bank_read_stage index) (history time) = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros Bank Steps Address index. induction index as [|index IH];intros time Bound Lower Upper;destruct time as [|time];[lia| |lia|].
 - eapply reference_second_bank_read_base_step_type with (old:=history time) (address:=address) (word:=bank 0%nat);[apply Address;lia| |apply Steps;lia].
   exact (proj2 (Bank time 0%nat ltac:(lia) ltac:(lia) ltac:(lia))).
 - destruct (IH time ltac:(lia) ltac:(lia) ltac:(lia)) as [right [Right Typed]].
   pose proof (Bank time (S index) ltac:(lia) ltac:(lia) Bound) as [Size Left].
   eapply reference_second_bank_read_successor_step_type with (old:=history time);[exact Bound|exact Left|reflexivity|exact Right|exact Typed|apply Steps;lia].
Qed.
Lemma reference_second_bank_read_stage_history_exact inputs path history (limit start:nat) bank address :
 (forall t index, (start <= t)%coq_nat -> (t <= limit)%coq_nat -> (index < 32)%coq_nat -> size (bank index)=32%nat /\ VM.find (N.of_nat (Nat.sub 2177 index)) (history t)=Some(Gval(Fuint 32)(bank index))) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (start <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_second_bank_read_address_port) (history time) = Some (Gval (Fuint 5) address)) ->
 forall index time, (index < 32)%coq_nat -> (to_nat address <= index)%coq_nat -> (Nat.add (Nat.add start index) 1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (reference_second_bank_read_stage index) (history time) = Some (Gval (Fuint 32) (bank (to_nat address))).
Proof.
 intros Bank Steps Address index. induction index as [|index IH];intros time Bound AddrBound Lower Upper;destruct time as [|time];[lia| |lia|].
 - assert (Zero:to_nat address=0%nat) by lia.
   eapply reference_second_bank_read_base_step_zero with (old:=history time) (address:=address);[apply Address;lia|exact Zero| |apply Steps;lia].
   rewrite Zero. exact (proj2 (Bank time 0%nat ltac:(lia) ltac:(lia) ltac:(lia))).
 - pose proof (Bank time (S index) ltac:(lia) ltac:(lia) Bound) as [Size Left].
   destruct (S index == to_nat address) eqn:Equal.
   + move/eqP: Equal => Equal.
     destruct (reference_second_bank_read_stage_history_type inputs path history limit start bank address Bank Steps Address index time ltac:(lia) ltac:(lia) ltac:(lia)) as [right [Right Typed]].
     eapply reference_second_bank_read_successor_step_exact with (old:=history time) (address:=address);[exact Bound|apply Address;lia|exact Left|reflexivity|exact Right|exact Typed| | |apply Steps;lia].
     * rewrite Equal eqxx. reflexivity.
     * rewrite -Equal. exact Size.
   + assert (Smaller:(to_nat address<=index)%coq_nat) by (move/eqP: Equal => Equal;lia).
     pose proof (IH time ltac:(lia) Smaller ltac:(lia) ltac:(lia)) as Right.
     eapply reference_second_bank_read_successor_step_exact with (old:=history time) (address:=address);[exact Bound|apply Address;lia|exact Left|reflexivity|exact Right|reflexivity|rewrite Equal;reflexivity| |apply Steps;lia].
     exact (proj1 (Bank time (to_nat address) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.
(* Reference bank and instruction bridge. *)
Theorem reference_second_register_read_history inputs path history limit start bank address :
 rf_reference_bank_at (history 0%nat) bank -> size address=5%nat -> (2<=start)%coq_nat ->
 (forall t,(t<limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2622(history t)=Some(Gval(Fuint 5)address)) ->
 forall t,(Nat.add start 32<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 2804(history t)=Some(Gval(Fuint 32)(bank(to_nat address))).
Proof.
 intros Bank Size Start Steps Address t Lower Upper.
 assert (Bound : (to_nat address<32)%coq_nat).
 { pose proof(to_nat_bounded address)as B. rewrite Size in B. exact(elimT ltP B). }
 assert (Aliases : forall time index,(start<=time)%coq_nat ->(time<=limit)%coq_nat ->(index<32)%coq_nat ->size(bank index)=32%nat /\ VM.find(N.of_nat(Nat.sub 2177 index))(history time)=Some(Gval(Fuint 32)(bank index))).
 { intros [|[|time]] index Lo Hi Index;try lia. split;[exact(proj1(Bank index Index))|].
   eapply (rf_reference_old_word_ingress index _ (history time) (history(S time)) (history(S(S time))) (bank index) Index (proj1(Bank index Index)));[|apply Steps;lia|apply Steps;lia].
   exact(proj2(rf_reference_bank_history_hold _ history limit bank Bank Steps time ltac:(lia) index Index)). }
 exact(reference_second_bank_read_stage_history_exact inputs path history limit start bank address Aliases Steps Address 31 t ltac:(lia) ltac:(lia) ltac:(lia) Upper).
Qed.
(* Second read observed bridge. *)
Require Import FormalLocalHistory FormalObservedHistory RFArchitecturalRelation StagedRegisterHold ReferenceControlStabilityHistory.
Theorem reference_second_register_read_observed memory inputs k observed bank address :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 rf_reference_bank_at(top_environment observed)bank ->size address=5%nat ->
 VM.find 2622(top_environment observed)=Some(Gval(Fuint 5)address) ->
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat address))).
Proof.
 intros Observe Legal Bank Size Address.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Hold:forall t index,(t<=9259)%coq_nat ->(index<32)%coq_nat ->VM.find(N.of_nat(7299+index)%nat)(history t)=VM.find(N.of_nat(7299+index)%nat)(history 0%nat)).
 { intros t. induction t as[|t IH];intros index Time Index;[reflexivity|].
   destruct(rf_architectural_register_properties _ (rf_reference_register_member index Index))as[Present Rest].
   rewrite(staged_combinational_holds_registers _ flat_memories(history t)(history t)(history(S t))flat_statements _ Present (Steps t ltac:(lia))).
   apply IH;lia. }
 assert(Bank0:rf_reference_bank_at(history 0%nat)bank).
 { intros index Index. destruct(Bank index Index)as[W V];split;[exact W|].
   rewrite <-(Hold 9259%nat index ltac:(lia) Index). rewrite Last;exact V. }
 assert(Addr:forall t,(500<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 2622(history t)=Some(Gval(Fuint 5)address)).
 { intros t Lower Upper. rewrite(reference_control_stable_2622_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Address. }
 pose proof(reference_second_register_read_history (generated_observation_input inputs k)nil history 9259 500 bank address Bank0 Size ltac:(lia) Steps Addr 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia))as Value.
 rewrite Last in Value;exact Value.
Qed.

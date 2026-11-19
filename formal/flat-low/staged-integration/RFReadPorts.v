Require Import ConcreteDecodeOperations CoreSocModel ComparisonNodes RFPreviewEffect RFArchitecturalNormalRelation RFWriteEffect DataAddressExpressionCertificates DataAddressPositionCertificate DataAddressSafetyCertificate SelectedNodeSafety FormalTypedNodeEquation FormalSuccessfulNodeEvaluation UIntMuxResultType ConcreteFormalValidIf FormalDeclaredWireCheck RFReadForwarding.
From Coq Require Import ZArith List Lia NArith.Nnat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_read_address_port (second:bool) : VarOrder.T := if second then 781 else 780.
Definition rf_read_stage (second:bool) (index:nat) : VarOrder.T := N.of_nat ((if second then 919 else 884)+index)%nat.
Definition rf_read_condition second index : hfexpr VarOrder.T :=
 @Eprim_binop VarOrder.T (Bcomp Beq)
 (@Econst VarOrder.T (Fuint (rf_preview_index_width index)) (from_N (rf_preview_index_width index) (N.of_nat index)))
 (@Eref VarOrder.T (@Eid VarOrder.T (rf_read_address_port second))).
Definition rf_read_stage_expr second (index:nat) : hfexpr VarOrder.T :=
 if index is O then @Evalidif VarOrder.T (rf_read_condition second 0) (@Eref VarOrder.T (@Eid VarOrder.T 851))
 else @Emux VarOrder.T (rf_read_condition second index)
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (851+index)%nat)))
 (@Eref VarOrder.T (@Eid VarOrder.T (rf_read_stage second (index-1)))).
Lemma rf_read_stage_member second (index:nat) : (index < 32)%coq_nat ->
 List.In (rf_read_stage second index,rf_read_stage_expr second index) data_address_expected_nodes.
Proof.
 intro Bound. apply (List.nth_error_In data_address_expected_nodes ((if second then 36 else 1)+index)%nat).
 destruct second; do 32 (destruct index as [|index];[vm_compute;reflexivity|]);lia.
Qed.
Lemma rf_read_condition_value second index invalid site mm old address :
 (index < 32)%coq_nat -> VM.find (rf_read_address_port second) old = Some (Gval (Fuint 5) address) ->
 eval_hfexpr_validif_policy (isolated_validif_policy invalid) site mm (rf_read_condition second index) old old =
 Some (Gval (Fuint 1) [::index == to_nat address]).
Proof.
 intros Bound Address. cbn [rf_read_condition eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Address size_from_N ltnn.
 assert (Constant : zext_to (rf_preview_index_width index) (from_N (rf_preview_index_width index) (N.of_nat index)) = from_N (rf_preview_index_width index) (N.of_nat index)).
 { unfold zext_to,zext. rewrite size_from_N subnn cats0. reflexivity. }
 rewrite Constant. unfold eval_binop. cbn [eval_binop_basic]. rewrite refine_concrete_uint.
 rewrite (rf_preview_index_exact index Bound) rf_preview_rd_match. reflexivity.
Qed.
Lemma rf_read_mux_exact mm old condition (yes no:VarOrder.T) invalid site bit left right word :
 (forall subsite, eval_hfexpr_validif_policy (isolated_validif_policy invalid) subsite mm condition old old = Some (Gval (Fuint 1) [::bit])) ->
 VM.find yes old = Some left -> type_of_val left = Gtyp (Fuint 32) ->
 VM.find no old = Some right -> type_of_val right = Gtyp (Fuint 32) ->
 (if bit then left else right) = Gval (Fuint 32) word -> size word = 32%nat ->
 eval_hfexpr_validif_policy (isolated_validif_policy invalid) site mm
 (@Emux VarOrder.T condition (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some (Gval (Fuint 32) word).
Proof.
 intros Condition Left LeftType Right RightType Selected Size.
 cbn [eval_hfexpr_validif_policy]. rewrite Condition.
 destruct bit;cbn in Selected;[subst left|subst right];
 cbn [is_zero eval_hfexpr_validif_policy eval_href_validif_policy];
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite Left Right;
 cbn [option_map];rewrite ?LeftType ?RightType;
 change (Some (Gval (Fuint 32%nat) (zext_to 32%nat (take 32%nat word))) = Some (Gval (Fuint 32%nat) word));
 rewrite -Size take_size;unfold zext_to,zext;rewrite subnn cats0;reflexivity.
Qed.
Lemma rf_read_base_type inputs path site mm old second address word value :
 VM.find (rf_read_address_port second) old = Some (Gval (Fuint 5) address) ->
 VM.find 851 old = Some (Gval (Fuint 32) word) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm (rf_read_stage_expr second 0) old old = Some value ->
 type_of_val value = Gtyp (Fuint 32).
Proof.
 intros Address Word Eval.
 change (eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm
 (@Evalidif VarOrder.T (rf_read_condition second 0) (@Eref VarOrder.T (@Eid VarOrder.T 851))) old old = Some value) in Eval.
 cbn [eval_hfexpr_validif_policy] in Eval.
 rewrite (rf_read_condition_value second 0 _ _ _ _ address ltac:(lia) Address) in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref eval_hfexpr_validif_policy eval_href_validif_policy] in Eval. rewrite Word in Eval.
 destruct (0%nat == to_nat address);cbn [validif_policy_result is_zero] in Eval;
 unfold isolated_validif_policy,formal_invalid_policy in Eval;cbn [input_value_of_type] in Eval;
 inversion Eval;reflexivity.
Qed.
Lemma rf_read_base_step_type inputs path second old result address word :
 VM.find (rf_read_address_port second) old = Some (Gval (Fuint 5) address) ->
 VM.find 851 old = Some (Gval (Fuint 32) word) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (rf_read_stage second 0) result = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros Address Word Step.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe (rf_read_stage_member second 0 ltac:(lia))) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ _ flat_memories old false old result Position Step) as [value Eval].
 assert (Typed : type_of_val value = Gtyp (Fuint 32)) by (eapply rf_read_base_type;[exact Address|exact Word|exact Eval]).
 exists value. split;[|exact Typed]. eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma rf_read_base_step_zero invalid second old result address word :
 VM.find (rf_read_address_port second) old = Some (Gval (Fuint 5) address) -> to_nat address = 0%nat ->
 VM.find 851 old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (rf_read_stage second 0) result = Some (Gval (Fuint 32) word).
Proof.
 intros Address Zero Word Step.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe (rf_read_stage_member second 0 ltac:(lia))) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories (@Evalidif VarOrder.T (rf_read_condition second 0) (@Eref VarOrder.T (@Eid VarOrder.T 851))) old old = Some (Gval (Fuint 32) word)).
 cbn [eval_hfexpr_validif_policy]. rewrite (rf_read_condition_value second 0 _ _ _ _ address ltac:(lia) Address) Zero.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Word. reflexivity.
Qed.
Lemma rf_read_successor_step_type second index invalid old result left right :
 (S index < 32)%coq_nat ->
 VM.find (N.of_nat (851+S index)%nat) old = Some left -> type_of_val left = Gtyp (Fuint 32) ->
 VM.find (rf_read_stage second index) old = Some right -> type_of_val right = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (rf_read_stage second (S index)) result = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros Bound Left LeftType Right RightType Step.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe (rf_read_stage_member second (S index) Bound)) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Position Step) as [value Eval].
 pose proof Eval as RawEval.
 cbn [rf_read_stage_expr] in Eval. rewrite subn1 in Eval; cbn [predn] in Eval.
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (rf_read_condition second (S index))
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (851+S index)%nat))) (@Eref VarOrder.T (@Eid VarOrder.T (rf_read_stage second index)))) old old = Some value) in Eval.
 assert (Typed : type_of_val value = Gtyp (Fuint 32)) by (eapply uint_mux_result_type;[exact Left|exact LeftType|exact Right|exact RightType|exact Eval]).
 exists value. split;[|exact Typed]. eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact RawEval|exact Typed|exact Step].
Qed.
Lemma rf_read_successor_step_exact second index invalid old result address left right word :
 (S index < 32)%coq_nat ->
 VM.find (rf_read_address_port second) old = Some (Gval (Fuint 5) address) ->
 VM.find (N.of_nat (851+S index)%nat) old = Some left -> type_of_val left = Gtyp (Fuint 32) ->
 VM.find (rf_read_stage second index) old = Some right -> type_of_val right = Gtyp (Fuint 32) ->
 (if S index == to_nat address then left else right) = Gval (Fuint 32) word -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (rf_read_stage second (S index)) result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Address Left LeftType Right RightType Selected Size Step.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe (rf_read_stage_member second (S index) Bound)) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rf_read_stage_expr]. rewrite subn1. cbn [predn].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories (@Emux VarOrder.T (rf_read_condition second (S index))
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (851+S index)%nat))) (@Eref VarOrder.T (@Eid VarOrder.T (rf_read_stage second index)))) old old = Some (Gval (Fuint 32) word)).
 eapply rf_read_mux_exact;[intros site;exact (rf_read_condition_value second (S index) invalid site flat_memories old address Bound Address)|exact Left|exact LeftType|exact Right|exact RightType|exact Selected|exact Size].
Qed.
Lemma rf_read_stage_history_type inputs path second history (limit start:nat) bank address :
 rf_dut_bank_at (history 0%nat) bank ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (start <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (rf_read_address_port second) (history time) = Some (Gval (Fuint 5) address)) ->
 forall index time, (index < 32)%coq_nat -> (Nat.add (Nat.add start index) 1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find (rf_read_stage second index) (history time) = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros Bank Steps Address index. induction index as [|index IH];intros time Bound Lower Upper;destruct time as [|time];[lia| |lia|].
 - eapply rf_read_base_step_type with (old:=history time) (address:=address) (word:=bank 0%nat);[apply Address;lia| |apply Steps;lia].
   exact (proj2 (rf_dut_bank_history_hold _ history limit bank Bank Steps time ltac:(lia) 0%nat ltac:(lia))).
 - destruct (IH time ltac:(lia) ltac:(lia) ltac:(lia)) as [right [Right Typed]].
   pose proof (rf_dut_bank_history_hold _ history limit bank Bank Steps time ltac:(lia) (S index) Bound) as [Size Left].
   eapply rf_read_successor_step_type with (old:=history time);[exact Bound|exact Left|reflexivity|exact Right|exact Typed|apply Steps;lia].
Qed.
Lemma rf_read_stage_history_exact inputs path second history (limit start:nat) bank address :
 rf_dut_bank_at (history 0%nat) bank ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (start <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (rf_read_address_port second) (history time) = Some (Gval (Fuint 5) address)) ->
 forall index time, (index < 32)%coq_nat -> (to_nat address <= index)%coq_nat -> (Nat.add (Nat.add start index) 1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (rf_read_stage second index) (history time) = Some (Gval (Fuint 32) (bank (to_nat address))).
Proof.
 intros Bank Steps Address index. induction index as [|index IH];intros time Bound AddrBound Lower Upper;destruct time as [|time];[lia| |lia|].
 - assert (Zero:to_nat address=0%nat) by lia.
   eapply rf_read_base_step_zero with (old:=history time) (address:=address);[apply Address;lia|exact Zero| |apply Steps;lia].
   rewrite Zero. exact (proj2 (rf_dut_bank_history_hold _ history limit bank Bank Steps time ltac:(lia) 0%nat ltac:(lia))).
 - pose proof (rf_dut_bank_history_hold _ history limit bank Bank Steps time ltac:(lia) (S index) Bound) as [Size Left].
   destruct (S index == to_nat address) eqn:Equal.
   + move/eqP: Equal => Equal.
     destruct (rf_read_stage_history_type inputs path second history limit start bank address Bank Steps Address index time ltac:(lia) ltac:(lia) ltac:(lia)) as [right [Right Typed]].
     eapply rf_read_successor_step_exact with (old:=history time) (address:=address);[exact Bound|apply Address;lia|exact Left|reflexivity|exact Right|exact Typed| | |apply Steps;lia].
     * rewrite Equal eqxx. reflexivity.
     * rewrite -Equal. exact Size.
   + assert (Smaller:(to_nat address<=index)%coq_nat) by (move/eqP: Equal => Equal;lia).
     pose proof (IH time ltac:(lia) Smaller ltac:(lia) ltac:(lia)) as Right.
     eapply rf_read_successor_step_exact with (old:=history time) (address:=address);[exact Bound|apply Address;lia|exact Left|reflexivity|exact Right|reflexivity|rewrite Equal;reflexivity| |apply Steps;lia].
     exact (proj1 (Bank (to_nat address) ltac:(lia))).
Qed.
Definition rf_read_tail_nodes second := if second then
 [::(918,address_expr_918);(951,address_expr_951);(952,address_expr_952)] else
 [::(883,address_expr_883);(916,address_expr_916);(917,address_expr_917)].
Definition rf_read_tail_entry second index := nth (0,@Econst VarOrder.T (Fuint 1) [::false]) (rf_read_tail_nodes second) index.
Lemma rf_read_tail_member second index : (index<3)%coq_nat -> List.In (rf_read_tail_entry second index) data_address_expected_nodes.
Proof.
 intros Bound. apply (List.nth_error_In data_address_expected_nodes ((if second then 35 else 0) + (if index is O then 0 else 32+index))%nat).
 destruct second;destruct index as [|[|[|index]]];try lia;vm_compute;reflexivity.
Qed.
Lemma rf_read_tail_step second index invalid old result width word :
 (index<3)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (snd(rf_read_tail_entry second index)) old old = Some (Gval (Fuint width) word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (fst(rf_read_tail_entry second index)) result = Some (Gval (Fuint width) word).
Proof.
 intros Bound Eval Step.
 pose proof (rf_read_tail_member second index Bound) as Member.
 rewrite (surjective_pairing (rf_read_tail_entry second index)) in Member.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|apply Eval|reflexivity|exact Step].
Qed.
Lemma rf_read_tail_guard second invalid old result address :
 VM.find (rf_read_address_port second) old = Some(Gval(Fuint 5)address) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (if second then 918 else 883) result = Some(Gval(Fuint 1)[::foldr orb false address]).
Proof.
 intros Address Step. replace (if second then 918 else 883) with (fst(rf_read_tail_entry second 0)) by (destruct second;reflexivity).
 eapply rf_read_tail_step;[lia| |exact Step]. intros site.
 destruct second;cbn [rf_read_tail_entry rf_read_tail_nodes snd nth address_expr_918 address_expr_883 rf_read_address_port eval_hfexpr_validif_policy eval_href_validif_policy] in *;rewrite Address;reflexivity.
Qed.
Lemma rf_read_tail_alias second invalid old result word :
 VM.find (rf_read_stage second 31) old = Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (if second then 951 else 916) result = Some(Gval(Fuint 32)word).
Proof.
 intros Word Step. replace (if second then 951 else 916) with (fst(rf_read_tail_entry second 1)) by (destruct second;reflexivity).
 eapply rf_read_tail_step;[lia| |exact Step]. intros site.
 destruct second;cbn [rf_read_tail_entry rf_read_tail_nodes snd nth address_expr_951 address_expr_916 rf_read_stage eval_hfexpr_validif_policy eval_href_validif_policy] in *;exact Word.
Qed.
Lemma rf_read_tail_mux second invalid old result bit word :
 size word = 32%nat ->
 VM.find (if second then 918 else 883) old = Some(Gval(Fuint 1)[::bit]) ->
 VM.find (if second then 951 else 916) old = Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (if second then 952 else 917) result = Some(Gval(Fuint 32)(if bit then word else zeros 32)).
Proof.
 intros Size Guard Word Step. replace (if second then 952 else 917) with (fst(rf_read_tail_entry second 2)) by (destruct second;reflexivity).
 eapply rf_read_tail_step;[lia| |exact Step]. intros site.
 destruct second;cbn [rf_read_tail_entry rf_read_tail_nodes snd nth address_expr_952 address_expr_917 eval_hfexpr_validif_policy eval_href_validif_policy] in *;rewrite Guard;
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite Word;
 destruct bit;cbn [is_zero eval_hfexpr_validif_policy eval_href_validif_policy];rewrite ?Word;
 try reflexivity;
 change (Some(Gval(Fuint 32%nat)(zext_to 32%nat(take 32%nat word)))=Some(Gval(Fuint 32%nat)word));
 rewrite -Size take_size;unfold zext_to,zext;rewrite subnn cats0;reflexivity.
Qed.
Require Import FormalDeclaredConnection DataAddressConnectionCertificates.
Lemma rf_read_output_wire second invalid old result word :
 size word = 32%nat -> VM.find (if second then 952 else 917) old = Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (rf_forward_raw second) result = Some(Gval(Fuint 32)word).
Proof.
 intros Size Word Step. destruct second;cbn [rf_forward_raw] in *.
 - eapply declared_connection_value;[exact data_address_connection_783_position|exact data_address_connection_783_split|exact data_address_connection_783_straight|exact data_address_connection_783_mid_safe|exact data_address_connection_783_tail_safe|exact data_address_connection_783_nonregister|reflexivity|exact Word| |exact Step].
   change(Some(Gval(Fuint 32%nat)(zext_to 32%nat(take 32%nat word)))=Some(Gval(Fuint 32%nat)word)). rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
 - eapply declared_connection_value;[exact data_address_connection_782_position|exact data_address_connection_782_split|exact data_address_connection_782_straight|exact data_address_connection_782_mid_safe|exact data_address_connection_782_tail_safe|exact data_address_connection_782_nonregister|reflexivity|exact Word| |exact Step].
   change(Some(Gval(Fuint 32%nat)(zext_to 32%nat(take 32%nat word)))=Some(Gval(Fuint 32%nat)word)). rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Theorem rf_actual_read_port_history inputs path second history (limit start:nat) bank address :
 rf_dut_bank_at (history 0%nat) bank -> bank 0%nat = zeros 32 -> size address = 5%nat ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (start <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (rf_read_address_port second) (history time) = Some (Gval (Fuint 5) address)) ->
 forall time, (Nat.add start 35 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (rf_forward_raw second) (history time) = Some(Gval(Fuint 32)(bank(to_nat address))).
Proof.
 intros Bank Zero AddressSize Steps Address time Lower Upper.
 assert (AddrBound:(to_nat address<32)%coq_nat).
 { pose proof(to_nat_bounded address) as H. rewrite AddressSize in H. exact (elimT ltP H). }
 destruct time as [|[|[|time]]];try lia.
 pose proof (rf_read_stage_history_exact inputs path second history limit start bank address Bank Steps Address 31 time ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Stage.
 pose proof (rf_read_tail_alias second _ (history time) (history(S time)) _ Stage (Steps time ltac:(lia))) as Alias.
 pose proof (rf_read_tail_guard second _ (history time) (history(S time)) address (Address time ltac:(lia) ltac:(lia)) (Steps time ltac:(lia))) as Guard.
 pose proof (rf_read_tail_mux second _ (history(S time)) (history(S(S time))) _ _ (proj1(Bank _ AddrBound)) Guard Alias (Steps (S time) ltac:(lia))) as Mux.
 assert (Choice:(if foldr orb false address then bank(to_nat address) else zeros 32)=bank(to_nat address)).
 { rewrite rf_address_nonzero. destruct (to_nat address);cbn;[rewrite Zero|];reflexivity. }
 rewrite Choice in Mux.
 exact (rf_read_output_wire second _ (history(S(S time))) (history(S(S(S time)))) _ (proj1(Bank _ AddrBound)) Mux (Steps (S(S time)) ltac:(lia))).
Qed.
Lemma rf_read_address_wire second invalid old result word :
 size word = 5%nat -> VM.find (rf_source_address second) old = Some(Gval(Fuint 5)word) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (rf_read_address_port second) result = Some(Gval(Fuint 5)word).
Proof.
 intros Size Word Step. destruct second;cbn [rf_read_address_port rf_source_address] in *.
 - eapply declared_connection_value;[exact data_address_connection_781_position|exact data_address_connection_781_split|exact data_address_connection_781_straight|exact data_address_connection_781_mid_safe|exact data_address_connection_781_tail_safe|exact data_address_connection_781_nonregister|reflexivity|exact Word| |exact Step].
   change(Some(Gval(Fuint 5%nat)(zext_to 5%nat(take 5%nat word)))=Some(Gval(Fuint 5%nat)word)). rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
 - eapply declared_connection_value;[exact data_address_connection_780_position|exact data_address_connection_780_split|exact data_address_connection_780_straight|exact data_address_connection_780_mid_safe|exact data_address_connection_780_tail_safe|exact data_address_connection_780_nonregister|reflexivity|exact Word| |exact Step].
   change(Some(Gval(Fuint 5%nat)(zext_to 5%nat(take 5%nat word)))=Some(Gval(Fuint 5%nat)word)). rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Theorem rf_actual_read_from_source_history inputs path second history (limit start:nat) bank address :
 rf_dut_bank_at (history 0%nat) bank -> bank 0%nat = zeros 32 -> size address = 5%nat ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (start <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (rf_source_address second) (history time) = Some (Gval (Fuint 5) address)) ->
 forall time, (Nat.add start 36 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (rf_forward_raw second) (history time) = Some(Gval(Fuint 32)(bank(to_nat address))).
Proof.
 intros Bank Zero Size Steps Address time Lower Upper.
 eapply (rf_actual_read_port_history inputs path second history limit (S start) bank address Bank Zero Size Steps);[|lia|exact Upper].
 intros t Start Bound. destruct t as [|t];[lia|].
 exact (rf_read_address_wire second _ (history t) (history(S t)) address Size (Address t ltac:(lia) ltac:(lia)) (Steps t ltac:(lia))).
Qed.
Require Import JointUpdateBoundaryHistory JointBoundaryRegisters.
Definition rf_instruction_address second (instruction:bits) := if second then drop 20 (take 25 instruction) else drop 15 (take 20 instruction).
Lemma rf_instruction_address_size second instruction : size instruction=32%nat -> size(rf_instruction_address second instruction)=5%nat.
Proof. intros Size. destruct second;unfold rf_instruction_address;rewrite size_drop size_take Size;reflexivity. Qed.
Lemma rf_instruction_address_step second invalid old result instruction :
 VM.find 7748 old = Some(Gval(Fuint 32)instruction) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(rf_source_address second)result=Some(Gval(Fuint 5)(rf_instruction_address second instruction)).
Proof.
 intros Front Step.
 assert(Member:List.In(rf_source_address second,if second then address_expr_7804 else address_expr_7803)data_address_expected_nodes).
 { destruct second;[apply(List.nth_error_In data_address_expected_nodes 126%nat)|apply(List.nth_error_In data_address_expected_nodes 125%nat)];vm_compute;reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 destruct second;cbn [rf_instruction_address address_expr_7803 address_expr_7804 eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Front;reflexivity.
Qed.
Lemma rf_read_front_member : List.In (7748%nat,32%nat) joint_boundary_registers.
Proof. apply(List.nth_error_In joint_boundary_registers 53%nat). vm_compute. reflexivity. Qed.
Theorem rf_actual_read_instruction_history inputs path second history (limit:nat) bank instruction :
 rf_dut_bank_at(history 0%nat)bank -> bank 0%nat=zeros 32 ->size instruction=32%nat ->
 VM.find 7748(history 0%nat)=Some(Gval(Fuint 32)instruction) ->
 (forall time,(time<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history time)false(history time)flat_statements=Some(history(S time))) ->
 forall time,(37<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find(rf_source_address second)(history time)=Some(Gval(Fuint 5)(rf_instruction_address second instruction)) /\
 VM.find(rf_forward_raw second)(history time)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address second instruction)))).
Proof.
 intros Bank Zero Size Front Steps.
 assert(Address:forall time,(1<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find(rf_source_address second)(history time)=Some(Gval(Fuint 5)(rf_instruction_address second instruction))).
 { intros time Lower Upper. destruct time as [|time];[lia|].
   apply(rf_instruction_address_step second (formal_invalid_policy inputs path) (history time) (history(S time)) instruction);[|apply Steps;lia].
   rewrite(joint_update_register_history_same _ history limit 7748 32 rf_read_front_member Steps time ltac:(lia)). exact Front. }
 intros time Lower Upper. split;[apply Address;lia|].
 exact(rf_actual_read_from_source_history inputs path second history limit 1 bank _ Bank Zero (rf_instruction_address_size second instruction Size) Steps Address time Lower Upper).
Qed.
Require Import RFNonAluBubbleHazard RFNonAluBubbleReachable.
Theorem rf_actual_forwarding_instruction_history inputs path second history (limit time:nat) bank reference instruction destination enabled low high alu_data write_data :
 let address := rf_instruction_address second instruction in
 rf_dut_bank_at(history 0%nat)bank -> bank 0%nat=zeros 32 ->size instruction=32%nat ->
 VM.find 7748(history 0%nat)=Some(Gval(Fuint 32)instruction) ->
 rf_nonalu_bubble_invariant(history 0%nat) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (36<=time)%coq_nat ->(Nat.add time 6<=limit)%coq_nat ->
 VM.find 7805(history(Nat.add time 2))=Some(Gval(Fuint 5)destination) ->
 VM.find 7757(history(Nat.add time 2))=Some(Gval(Fuint 1)[::enabled]) ->
 VM.find 7756(history(Nat.add time 3))=Some(Gval(Fuint 2)[::low;high]) ->
 size alu_data=32%nat ->
 VM.find 7752(history(Nat.add time 5))=Some(Gval(Fuint 32)alu_data) ->
 bank(to_nat address)=rf_apply_effect reference RFNoWrite(to_nat address) ->
 ((~~low && ~~high)=true ->alu_data=write_data) ->
 VM.find(rf_forward_node second)(history(Nat.add time 6))=Some(Gval(Fuint 32)
 (rf_apply_effect reference(if enabled then RFWrite(to_nat destination)write_data else RFNoWrite)(to_nat address))).
Proof.
 cbn zeta. intros Bank Zero Size Front Invariant Steps Lower Upper Destination Enabled Mode DataSize Data Paired AluData.
 pose proof(rf_actual_read_instruction_history inputs path second history limit bank instruction Bank Zero Size Front Steps) as Reads.
 assert(AddrBound:(to_nat(rf_instruction_address second instruction)<32)%coq_nat).
 { pose proof(to_nat_bounded(rf_instruction_address second instruction)) as H.
   rewrite(rf_instruction_address_size second instruction Size) in H. exact(elimT ltP H). }
 eapply (rf_actual_forwarding_with_bubble_invariant second (formal_invalid_policy inputs path)
 (history time)(history(Nat.add time 1))(history(Nat.add time 2))(history(Nat.add time 3))(history(Nat.add time 4))(history(Nat.add time 5))(history(Nat.add time 6)) bank reference _ destination enabled low high alu_data write_data).
 - exact(rf_nonalu_bubble_history_hold _ history limit Invariant Steps time ltac:(lia)).
 - exact(proj1(Reads (Nat.add time 1) ltac:(lia) ltac:(lia))).
 - exact(proj1(Reads (Nat.add time 2) ltac:(lia) ltac:(lia))).
 - exact Destination.
 - exact Enabled.
 - exact Mode.
 - exact DataSize.
 - exact(proj1(Bank _ AddrBound)).
 - exact Data.
 - exact(proj2(Reads (Nat.add time 5) ltac:(lia) ltac:(lia))).
 - exact Paired.
 - exact AluData.
 - replace(Nat.add time 1)with(S time)by lia. apply Steps;lia.
 - replace(Nat.add time 2)with(S(Nat.add time 1))by lia. apply Steps;lia.
 - replace(Nat.add time 3)with(S(Nat.add time 2))by lia. apply Steps;lia.
 - replace(Nat.add time 4)with(S(Nat.add time 3))by lia. apply Steps;lia.
 - replace(Nat.add time 5)with(S(Nat.add time 4))by lia. apply Steps;lia.
 - replace(Nat.add time 6)with(S(Nat.add time 5))by lia. apply Steps;lia.
Qed.
Require Import ConcreteRegisterInitialization FormalLocalHistory FormalObservationCommit StagedIterationCount JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation FormalFetchType EarlyControlStabilityHistory.
Lemma rf_read_bank_member index : (index<32)%coq_nat ->List.In ((851+index)%nat,32%nat) joint_boundary_registers.
Proof. intro Bound. apply(List.nth_error_In joint_boundary_registers (21+index)%nat). do 32(destruct index as[|index];[vm_compute;reflexivity|]);lia. Qed.
Lemma rf_read_alu_member : List.In(7752%nat,32%nat)joint_boundary_registers.
Proof. apply(List.nth_error_In joint_boundary_registers 57%nat). vm_compute. reflexivity. Qed.
Require Import StagedCircuitRegisterHold RFArchitecturalRelation StagedObservedRegister FlatRegFileX0.
Theorem rf_actual_forwarding_observed memory inputs k observed second bank reference instruction destination enabled low high alu_data write_data :
 let env:=top_environment observed in let address:=rf_instruction_address second instruction in
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 rf_dut_bank_at env bank ->size instruction=32%nat ->
 VM.find 7748 env=Some(Gval(Fuint 32)instruction) ->
 VM.find 7805 env=Some(Gval(Fuint 5)destination) ->
 VM.find 7757 env=Some(Gval(Fuint 1)[::enabled]) ->
 VM.find 7756 env=Some(Gval(Fuint 2)[::low;high]) ->
 size alu_data=32%nat ->VM.find 7752 env=Some(Gval(Fuint 32)alu_data) ->
 bank(to_nat address)=rf_apply_effect reference RFNoWrite(to_nat address) ->
 ((~~low && ~~high)=true ->alu_data=write_data) ->
 VM.find(rf_forward_node second)env=Some(Gval(Fuint 32)
 (rf_apply_effect reference(if enabled then RFWrite(to_nat destination)write_data else RFNoWrite)(to_nat address))).
Proof.
 cbn zeta. intros Observe Legal Bank Size Front Destination Enabled Mode DataSize Data Paired AluData.
 pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct(generated_run memory inputs k)as[committed|]eqn:Run;[|discriminate Expanded].
 destruct(circuit_initial_map_with_memory generated_modules generated_top(Some committed)(formal_external_inputs(generated_observation_input inputs k)))as[initial|]eqn:Prepare;[|discriminate Expanded].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Expanded.
 destruct(local_iteration_history(generated_observation_input inputs k)9259 initial observed Expanded)as[history[First[Last Steps]]].
 destruct(fetch9220_run_type memory inputs k committed Run)as[old[value[Old Rest]]].
 assert(Zero:bank 0%nat=zeros 32).
 { destruct(rf_storage_x0_reachable memory inputs k committed Run Legal)as[zeroenv[ZeroEnv ZeroValue]].
   rewrite Old in ZeroEnv. inversion ZeroEnv;subst zeroenv.
   destruct(rf_architectural_register_properties _ (rf_dut_register_member 0 ltac:(vm_compute;lia)))as[Present[Typed Safe]].
   destruct(rf_architectural_nonexternal _ (rf_dut_register_member 0 ltac:(vm_compute;lia)))as[NotClock NotReset].
   pose proof(staged_observed_register_copies memory inputs k committed old observed 851 NotClock NotReset Safe Present Run Old Observe)as Copy.
   rewrite ZeroValue in Copy.
   assert(ObservedZero:VM.find 851(top_environment observed)=Some rf_zero32).
   { unfold staged_register_lookup in Copy. unfold top_environment. destruct(SVM.find nil observed);[exact Copy|discriminate Copy]. }
   pose proof(proj2(Bank 0 ltac:(vm_compute;lia)))as Value.
   change(VM.find 851(top_environment observed)=Some(Gval(Fuint 32)(bank 0%nat)))in Value.
   rewrite ObservedZero in Value. inversion Value. reflexivity. }
 destruct(joint_boundary_reachable memory inputs k committed Run Legal)as[Registers Storage].
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member. rewrite First. eapply joint_boundary_prepared_concrete;[exact Member| |exact Old|exact Prepare].
   unfold joint_registers_concrete,top_environment in Registers. rewrite Old in Registers. exact(Registers node width Member). }
 assert(Same:forall node width,List.In(node,width)joint_boundary_registers ->forall time,(time<=9259)%coq_nat ->VM.find(N.of_nat node)(history time)=VM.find(N.of_nat node)(top_environment observed)).
 { intros node width Member time Bound. rewrite <-Last.
   rewrite(joint_update_register_history_same _ history 9259 node width Member Steps time Bound).
   symmetry. exact(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)). }
 assert(Bank0:rf_dut_bank_at(history 0%nat)bank).
 { intros index Bound. destruct(Bank index Bound)as[W V]. split;[exact W|]. rewrite(Same _ _ (rf_read_bank_member index Bound) 0 ltac:(vm_compute;lia)). exact V. }
 assert(Front0:VM.find 7748(history 0%nat)=Some(Gval(Fuint 32)instruction)).
 { rewrite(Same 7748 32 rf_read_front_member 0 ltac:(vm_compute;lia)). exact Front. }
 assert(Invariant:rf_nonalu_bubble_invariant(history 0%nat)).
 { rewrite First. eapply rf_nonalu_bubble_prepared;[exact Old| |exact Prepare].
   pose proof(rf_nonalu_bubble_run memory inputs k committed Run Legal)as Inv. unfold top_environment in Inv. rewrite Old in Inv. exact Inv. }
 rewrite <-Last.
 apply(rf_actual_forwarding_instruction_history(generated_observation_input inputs k)nil second history 9259 9253 bank reference instruction destination enabled low high alu_data write_data Bank0 Zero Size Front0 Invariant Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)).
 - rewrite(early_control_stable_7805_history _ _ history 9259 Boundary Steps 9255 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Destination.
 - rewrite(Same 7757 1 rf_nonalu_enable_member 9255 ltac:(vm_compute;lia)). exact Enabled.
 - rewrite(Same 7756 2 rf_nonalu_mode_member 9256 ltac:(vm_compute;lia)). exact Mode.
 - exact DataSize.
 - rewrite(Same 7752 32 rf_read_alu_member 9258 ltac:(vm_compute;lia)). exact Data.
 - exact Paired.
 - exact AluData.
Qed.

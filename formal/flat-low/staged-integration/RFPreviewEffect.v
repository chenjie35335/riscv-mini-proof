Require Import ConcreteDecodeOperations CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate FormalTypedNodeEquation ExactWordMux.
From Coq Require Import ZArith Arith Lia List NArith.Nnat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_preview_index_width (index : nat) := S (Nat.log2 index).
Definition rf_preview_old_expr (index : nat) : hfexpr VarOrder.T :=
 if index is O then @Econst VarOrder.T (Fuint 1) [::false] else @Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (851+index)%nat)).
Definition rf_preview_select_expr (index : nat) : hfexpr VarOrder.T :=
 @Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq)
  (@Econst VarOrder.T (Fuint (rf_preview_index_width index)) (from_N (rf_preview_index_width index) (N.of_nat index)))
  (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 988)) (rf_preview_old_expr index).
Definition rf_preview_output_expr (index : nat) : hfexpr VarOrder.T :=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (989+index)%nat))) (rf_preview_old_expr index).
Definition rf_preview_effect_nodes : seq (VarOrder.T * hfexpr VarOrder.T) :=
 (988,@Eref VarOrder.T(@Eid VarOrder.T 786)) ::
 map (fun i => (N.of_nat (989+i)%nat,rf_preview_select_expr i)) (iota 0 32) ++
 map (fun i => (N.of_nat (1053+i)%nat,rf_preview_output_expr i)) (iota 0 32).
Definition rf_preview_effect_offsets : seq nat := [::997%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;32%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_preview_effect_positions : select_node_offsets rf_preview_effect_offsets flat_statements = Some rf_preview_effect_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_preview_effect_safety : selected_node_safety flat_memories flat_statements rf_preview_effect_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque generated_modules generated_top flat_statements flat_memories.
(* Generic effect proof. *)
Definition rf_preview_word (index : nat) old rd data (enabled : bool) :=
 if enabled && (N.of_nat index == to_N rd) then data
 else if index is O then nseq 32 false else old.
Lemma rf_preview_index_exact index :
 (index < 32)%coq_nat ->
 to_N (from_N (rf_preview_index_width index) (N.of_nat index)) = N.of_nat index.
Proof.
 intro Bound. do 32 (destruct index as [|index]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma rf_preview_select_nonzero_eval mm env index rd data old :
 (S index < 32)%coq_nat ->
 size data = 32%nat -> size old = 32%nat ->
 VM.find 785 env = Some (Gval (Fuint 5) rd) ->
 VM.find 988 env = Some (Gval (Fuint 32) data) ->
 VM.find (N.of_nat (851+S index)%nat) env = Some (Gval (Fuint 32) old) ->
 eval_hfexpr_with_memory mm (rf_preview_select_expr (S index)) env env =
 Some (Gval (Fuint 32) (if N.of_nat (S index) == to_N rd then data else old)).
Proof.
 intros Bound DataSize OldSize RD Data Old.
 cbn [rf_preview_select_expr rf_preview_old_expr eval_hfexpr_with_memory eval_href_with_memory].
 rewrite RD size_from_N ltnn.
 assert (Constant : zext_to (rf_preview_index_width (S index)) (from_N (rf_preview_index_width (S index)) (N.of_nat (S index))) = from_N (rf_preview_index_width (S index)) (N.of_nat (S index))).
 { unfold zext_to,zext. rewrite size_from_N subnn cats0. reflexivity. }
 rewrite Constant.
 unfold eval_binop. cbn [eval_binop_basic]. rewrite refine_concrete_uint.
 rewrite (rf_preview_index_exact (S index) Bound).
 assert (ZT : is_zero [::true] = false) by (vm_compute; reflexivity).
 assert (ZF : is_zero [::false] = true) by (vm_compute; reflexivity).
 destruct (N.of_nat (S index) == to_N rd);
 cbn [eval_hfexpr_with_memory eval_href_with_memory];
 rewrite ?ZT ?ZF; cbn;
 unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref];
 rewrite ?Data ?Old; cbn [make_ftype_explicit type_of_val extend_hvalue_as_type ftype_mux fgtyp_mux option_map adapt_hvalue_as_type].
 - rewrite maxnn -DataSize take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
 - rewrite maxnn -OldSize take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Lemma rf_preview_select_member index : (index < 32)%coq_nat ->
 List.In (N.of_nat (989+index)%nat, rf_preview_select_expr index) rf_preview_effect_nodes.
Proof.
 intro Bound. apply (List.nth_error_In rf_preview_effect_nodes (S index)).
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Theorem rf_preview_select_nonzero_step invalid env current result index rd data old :
 (S index < 32)%coq_nat ->
 size data = 32%nat -> size old = 32%nat ->
 VM.find 785 env = Some (Gval (Fuint 5) rd) ->
 VM.find 988 env = Some (Gval (Fuint 32) data) ->
 VM.find (N.of_nat (851+S index)%nat) env = Some (Gval (Fuint 32) old) ->
 formal_value_iter invalid flat_memories env false current flat_statements = Some result ->
 VM.find (N.of_nat (989+S index)%nat) result =
 Some (Gval (Fuint 32) (if N.of_nat (S index) == to_N rd then data else old)).
Proof.
 intros Bound DataSize OldSize RD Data Old Step.
 destruct (selected_node_safe_position flat_memories flat_statements rf_preview_effect_offsets flat_statements
 rf_preview_effect_nodes _ _ rf_preview_effect_positions rf_preview_effect_safety (rf_preview_select_member (S index) Bound))
 as [count [tail [Position [Safe Nonregister]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonregister| |reflexivity|exact Step].
 change (eval_hfexpr_with_memory flat_memories (rf_preview_select_expr (S index)) env env =
 Some (Gval (Fuint 32) (if N.of_nat (S index) == to_N rd then data else old))).
 exact (rf_preview_select_nonzero_eval flat_memories env index rd data old Bound DataSize OldSize RD Data Old).
Qed.
Print Assumptions rf_preview_select_nonzero_step.
Require Import RFArchitecturalRelation StagedRegisterHold RFWriteEffect.
Lemma rf_preview_output_member index : (index < 32)%coq_nat ->
 List.In (N.of_nat (1053+index)%nat, rf_preview_output_expr index) rf_preview_effect_nodes.
Proof.
 intro Bound. apply (List.nth_error_In rf_preview_effect_nodes (33+index)%nat).
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Lemma rf_preview_register_member index : (index < 32)%coq_nat ->
 List.In (851+index)%nat rf_architectural_register_ids.
Proof.
 intro Bound. apply (List.nth_error_In rf_architectural_register_ids (2*index)%nat).
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Lemma rf_preview_rd_match index rd : (N.of_nat index == to_N rd) = (index == to_nat rd).
Proof.
 rewrite to_N_nat. apply/idP/idP.
 - move/eqP => Equal. apply/eqP. exact (Nat2N.inj _ _ Equal).
 - move/eqP => Equal. rewrite Equal. exact (eqxx _).
Qed.
Lemma rf_preview_nonzero_effect bank index rd data enabled :
 rf_preview_word (S index) (bank (S index)) rd data enabled =
 rf_apply_effect bank (if enabled then RFWrite (to_nat rd) data else RFNoWrite) (S index).
Proof.
 unfold rf_preview_word,rf_apply_effect. rewrite rf_preview_rd_match.
 destruct enabled; reflexivity.
Qed.
Theorem rf_preview_output_nonzero_step invalid env current result index chosen old enabled :
 (S index < 32)%coq_nat -> size chosen = 32%nat -> size old = 32%nat ->
 VM.find 954 env = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find (N.of_nat (989+S index)%nat) env = Some (Gval (Fuint 32) chosen) ->
 VM.find (N.of_nat (851+S index)%nat) env = Some (Gval (Fuint 32) old) ->
 formal_value_iter invalid flat_memories env false current flat_statements = Some result ->
 VM.find (N.of_nat (1053+S index)%nat) result = Some (Gval (Fuint 32) (if enabled then chosen else old)).
Proof.
 intros Bound ChosenSize OldSize Gate Chosen Old Step.
 destruct (selected_node_safe_position flat_memories flat_statements rf_preview_effect_offsets flat_statements
 rf_preview_effect_nodes _ _ rf_preview_effect_positions rf_preview_effect_safety (rf_preview_output_member (S index) Bound))
 as [count [tail [Position [Safe Nonregister]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonregister| |reflexivity|exact Step].
 change (eval_hfexpr_with_memory flat_memories (rf_preview_output_expr (S index)) env env =
 Some (Gval (Fuint 32) (if enabled then chosen else old))).
 pose proof (exact_word_mux flat_memories env 954 (N.of_nat (989+S index)%nat) (N.of_nat (851+S index)%nat)
 enabled chosen old Gate Chosen Old) as Value.
 assert (Same : mux_word enabled chosen old = if enabled then chosen else old).
 { unfold mux_word. destruct enabled.
 - rewrite -ChosenSize take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
 - rewrite -OldSize take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity. }
 rewrite Same in Value. exact Value.
Qed.
Theorem rf_preview_nonzero_two_steps invalid s0 s1 s2 index rd data bank enabled :
 (S index < 32)%coq_nat -> size data = 32%nat -> size (bank (S index)) = 32%nat ->
 VM.find 785 s0 = Some (Gval (Fuint 5) rd) ->
 VM.find 988 s0 = Some (Gval (Fuint 32) data) ->
 VM.find (N.of_nat (851+S index)%nat) s0 = Some (Gval (Fuint 32) (bank (S index))) ->
 VM.find 954 s1 = Some (Gval (Fuint 1) [::enabled]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find (N.of_nat (1053+S index)%nat) s2 = Some (Gval (Fuint 32)
 (rf_apply_effect bank (if enabled then RFWrite (to_nat rd) data else RFNoWrite) (S index))).
Proof.
 intros Bound DataSize OldSize RD Data Old Gate Step1 Step2.
 pose proof (rf_preview_select_nonzero_step invalid s0 s0 s1 index rd data (bank (S index))
 Bound DataSize OldSize RD Data Old Step1) as Selected.
 destruct (rf_architectural_register_properties (851+S index)%nat (rf_preview_register_member (S index) Bound)) as [Present Rest].
 assert (Old1 : VM.find (N.of_nat (851+S index)%nat) s1 = Some (Gval (Fuint 32) (bank (S index)))).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements
 (N.of_nat (851+S index)%nat) Present Step1). exact Old. }
 assert (SelectedSize : size (if N.of_nat (S index) == to_N rd then data else bank (S index)) = 32%nat).
 { destruct (N.of_nat (S index) == to_N rd); assumption. }
 pose proof (rf_preview_output_nonzero_step invalid s1 s1 s2 index _ _ enabled Bound SelectedSize OldSize Gate Selected Old1 Step2) as Output.
 rewrite <- (rf_preview_nonzero_effect bank index rd data enabled).
 destruct enabled; exact Output.
Qed.
Print Assumptions rf_preview_nonzero_two_steps.
Lemma rf_preview_data_step invalid env current result data :
 VM.find 786 env = Some (Gval (Fuint 32) data) ->
 formal_value_iter invalid flat_memories env false current flat_statements = Some result ->
 VM.find 988 result = Some (Gval (Fuint 32) data).
Proof.
 intros Data Step.
 assert (Member : List.In (988,@Eref VarOrder.T (@Eid VarOrder.T 786)) rf_preview_effect_nodes).
 { unfold rf_preview_effect_nodes. left. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements rf_preview_effect_offsets flat_statements
 rf_preview_effect_nodes _ _ rf_preview_effect_positions rf_preview_effect_safety Member)
 as [count [tail [Position [Safe Nonregister]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonregister| |reflexivity|exact Step].
 cbn [eval_hfexpr_with_memory]. exact Data.
Qed.
Theorem rf_preview_nonzero_three_steps invalid s0 s1 s2 s3 index rd data bank enabled :
 (S index < 32)%coq_nat -> size data = 32%nat -> size (bank (S index)) = 32%nat ->
 VM.find 786 s0 = Some (Gval (Fuint 32) data) ->
 VM.find 785 s1 = Some (Gval (Fuint 5) rd) ->
 VM.find (N.of_nat (851+S index)%nat) s0 = Some (Gval (Fuint 32) (bank (S index))) ->
 VM.find 954 s2 = Some (Gval (Fuint 1) [::enabled]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find (N.of_nat (1053+S index)%nat) s3 = Some (Gval (Fuint 32)
 (rf_apply_effect bank (if enabled then RFWrite (to_nat rd) data else RFNoWrite) (S index))).
Proof.
 intros Bound DataSize OldSize Data RD Old Gate Step1 Step2 Step3.
 pose proof (rf_preview_data_step invalid s0 s0 s1 data Data Step1) as Alias.
 destruct (rf_architectural_register_properties (851+S index)%nat (rf_preview_register_member (S index) Bound)) as [Present Rest].
 assert (Old1 : VM.find (N.of_nat (851+S index)%nat) s1 = Some (Gval (Fuint 32) (bank (S index)))).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements
 (N.of_nat (851+S index)%nat) Present Step1). exact Old. }
 exact (rf_preview_nonzero_two_steps invalid s1 s2 s3 index rd data bank enabled
 Bound DataSize OldSize RD Alias Old1 Gate Step2 Step3).
Qed.
Require Import FlatRegFileX0 FormalRegFileX0Iteration.
Theorem rf_preview_bank_three_steps invalid s0 s1 s2 s3 rd data bank write_enable enabled :
 size rd = 5%nat -> size data = 32%nat ->
 (forall index, (index < 32)%coq_nat -> size (bank index) = 32%nat) ->
 VM.find 786 s0 = Some (Gval (Fuint 32) data) ->
 VM.find 785 s0 = Some (Gval (Fuint 5) rd) ->
 VM.find 785 s1 = Some (Gval (Fuint 5) rd) ->
 VM.find 784 s1 = Some (Gval (Fuint 1) [::write_enable]) ->
 VM.find 954 s2 = Some (Gval (Fuint 1) [::enabled]) ->
 (forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (851+index)%nat) s0 = Some (Gval (Fuint 32) (bank index))) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (1053+index)%nat) s3 = Some (Gval (Fuint 32)
 (rf_apply_effect bank (if enabled then RFWrite (to_nat rd) data else RFNoWrite) index)).
Proof.
 intros RDSize DataSize BankSize Data RD0 RD1 Enable Gate Bank Step1 Step2 Step3 index Bound.
 destruct index as [|index].
 - change (VM.find 1053 s3 = Some rf_zero32).
   pose proof (rf_preview_data_step invalid s0 s0 s1 data Data Step1) as Alias.
   eapply real_three_iterations_rf_x0 with (enable:=write_enable) (address:=rd) (data:=data);
   [exact RDSize|exact RD0|exact RD1|exact Enable|exact Alias|exact Step1|exact Step2|exact Step3].
 - exact (rf_preview_nonzero_three_steps invalid s0 s1 s2 s3 index rd data bank enabled
   Bound DataSize (BankSize _ Bound) Data RD1 (Bank _ Bound) Gate Step1 Step2 Step3).
Qed.
Corollary rf_preview_bank_from_inputs invalid s0 s1 s2 s3 rd data bank write_enable :
 size rd = 5%nat -> size data = 32%nat ->
 (forall index, (index < 32)%coq_nat -> size (bank index) = 32%nat) ->
 VM.find 786 s0 = Some (Gval (Fuint 32) data) ->
 VM.find 785 s0 = Some (Gval (Fuint 5) rd) ->
 VM.find 785 s1 = Some (Gval (Fuint 5) rd) ->
 VM.find 784 s1 = Some (Gval (Fuint 1) [::write_enable]) ->
 (forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (851+index)%nat) s0 = Some (Gval (Fuint 32) (bank index))) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (1053+index)%nat) s3 = Some (Gval (Fuint 32)
 (rf_apply_effect bank
 (if write_enable && foldr orb false rd then RFWrite (to_nat rd) data else RFNoWrite) index)).
Proof.
 intros RDSize DataSize BankSize Data RD0 RD1 Enable Bank Step1 Step2 Step3.
 destruct (real_iteration_rf_round invalid s0 s0 s1 Step1) as [Reduction Rest1].
 destruct (real_iteration_rf_round invalid s1 s1 s2 Step2) as [_ [Guard Rest2]].
 rewrite (rf_addr_value s0 rd RD0) in Reduction.
 rewrite (rf_guard_value s1 write_enable _ Enable Reduction) in Guard.
 exact (rf_preview_bank_three_steps invalid s0 s1 s2 s3 rd data bank write_enable
 (write_enable && foldr orb false rd) RDSize DataSize BankSize Data RD0 RD1 Enable Guard Bank Step1 Step2 Step3).
Qed.
Require Import FormalX0AddressStability FormalRFDestination.
Theorem rf_preview_bank_from_instruction invalid s0 s1 s2 s3 s4 s5 instruction data bank write_enable :
 size instruction = 32%nat -> size data = 32%nat ->
 (forall index, (index < 32)%coq_nat -> size (bank index) = 32%nat) ->
 VM.find 7750 s0 = Some (Gval (Fuint 32) instruction) ->
 VM.find 786 s2 = Some (Gval (Fuint 32) data) ->
 VM.find 784 s3 = Some (Gval (Fuint 1) [::write_enable]) ->
 (forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (851+index)%nat) s0 = Some (Gval (Fuint 32) (bank index))) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (1053+index)%nat) s5 = Some (Gval (Fuint 32)
 (rf_apply_effect bank
 (if write_enable && foldr orb false (drop 7 (take 12 instruction))
 then RFWrite (to_nat (drop 7 (take 12 instruction))) data else RFNoWrite) index)).
Proof.
 intros InstSize DataSize BankSize Instruction Data Enable Bank Step1 Step2 Step3 Step4 Step5.
 destruct (x0_address_stable_after_three invalid s0 s1 s2 s3 instruction InstSize Instruction Step1 Step2 Step3) as [RD2 RD3].
 assert (Bank2 : forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (851+index)%nat) s2 = Some (Gval (Fuint 32) (bank index))).
 { intros index Bound.
   destruct (rf_architectural_register_properties (851+index)%nat (rf_preview_register_member index Bound)) as [Present Rest].
   rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements
    (N.of_nat (851+index)%nat) Present Step2).
   rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements
    (N.of_nat (851+index)%nat) Present Step1).
   exact (Bank index Bound). }
 exact (rf_preview_bank_from_inputs invalid s2 s3 s4 s5 (drop 7 (take 12 instruction)) data bank write_enable
 (rf_destination_width instruction InstSize) DataSize BankSize Data RD2 RD3 Enable Bank2 Step3 Step4 Step5).
Qed.
Require Import FormalRFDataConnection.
Lemma rf_preview_data_port_exact invalid old current result width word :
 (32 <= width)%coq_nat -> size word = width ->
 VM.find 7937 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 786 result = Some (Gval (Fuint 32) (take 32 word)).
Proof.
 intros Bound Size Source Step.
 assert (BoundB : (31 < width)%nat). { apply/ltP. lia. }
 assert (LowSize : size (take 32 word) = 32%nat).
 { rewrite size_take Size. have B : (32 < width)%nat \/ width = 32%nat.
   { destruct (Nat.eq_dec width 32) as [E|E]; [right;exact E|left;apply/ltP;lia]. }
   destruct B as [B| ->]; [rewrite B|]; reflexivity. }
 apply (rf_input_connection_786 invalid old current result (Gval (Fuint 32) (take 32 word)) _).
 - cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
   cbn [eval_unop]. rewrite BoundB leq0n. cbn [andb]. rewrite subn0 drop0. reflexivity.
 - change (Some (Gval (Fuint 32) (zext_to 32 (take 32 (take 32 word)))) = Some (Gval (Fuint 32) (take 32 word))).
   rewrite take_take; try reflexivity. unfold zext_to,zext. rewrite LowSize subnn cats0. reflexivity.
 - exact Step.
Qed.

Lemma rf_preview_nonzero_reduction_zero rd :
 foldr orb false rd = false -> to_nat rd = 0%nat.
Proof.
 induction rd as [|bit rd IH]; [reflexivity|].
 destruct bit; cbn [foldr orb]; [discriminate|].
 intro Zero. rewrite to_nat_cons (IH Zero). reflexivity.
Qed.
Lemma rf_preview_effect_remove_zero_guard bank rd data enabled index :
 rf_apply_effect bank (if enabled && foldr orb false rd then RFWrite (to_nat rd) data else RFNoWrite) index =
 rf_apply_effect bank (if enabled then RFWrite (to_nat rd) data else RFNoWrite) index.
Proof.
 destruct enabled; [|reflexivity].
 case Reduction: (foldr orb false rd); [reflexivity|].
 rewrite (rf_preview_nonzero_reduction_zero rd Reduction).
 unfold rf_apply_effect. cbn [andb]. case E: (index == 0%nat); reflexivity.
Qed.

Theorem rf_preview_bank_from_writeback_source invalid s0 s1 s2 s3 s4 s5 instruction source bank write_enable :
 size instruction = 32%nat -> size source = 33%nat ->
 (forall index, (index < 32)%coq_nat -> size (bank index) = 32%nat) ->
 VM.find 7750 s0 = Some (Gval (Fuint 32) instruction) ->
 VM.find 7937 s1 = Some (Gval (Fuint 33) source) ->
 VM.find 784 s3 = Some (Gval (Fuint 1) [::write_enable]) ->
 (forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (851+index)%nat) s0 = Some (Gval (Fuint 32) (bank index))) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (1053+index)%nat) s5 = Some (Gval (Fuint 32)
 (rf_apply_effect bank
 (if write_enable
 then RFWrite (to_nat (drop 7 (take 12 instruction))) (take 32 source) else RFNoWrite) index)).
Proof.
 intros InstSize SourceSize BankSize Instruction Source Enable Bank Step1 Step2 Step3 Step4 Step5.
 assert (Data : VM.find 786 s2 = Some (Gval (Fuint 32) (take 32 source))).
 { exact (rf_preview_data_port_exact invalid s1 s1 s2 33 source ltac:(lia) SourceSize Source Step2). }
 assert (DataSize : size (take 32 source) = 32%nat).
 { rewrite size_take SourceSize. reflexivity. }
 intros index Bound.
 rewrite <- (rf_preview_effect_remove_zero_guard bank (drop 7 (take 12 instruction)) (take 32 source) write_enable index).
 exact (rf_preview_bank_from_instruction invalid s0 s1 s2 s3 s4 s5 instruction (take 32 source) bank write_enable
 InstSize DataSize BankSize Instruction Data Enable Bank Step1 Step2 Step3 Step4 Step5 index Bound).
Qed.

Require Import ReferenceLoadRs1 ReferenceStoreObserved StoreTypeCorrespondence RFScalarControl ReferenceIllegalObserved RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory MemoryRequestObservedSemantics ReferenceRegisterRead ReferenceRs1Types ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCertificates0 ReferenceControlExpressions ReferenceRedirectSpine CoreSocModel ComparisonNodes LoadTypeCorrespondence LoadImmediateSemantics RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma reference_store_rs1_raw inputs path history limit reset time instruction lane :
 (lane<3)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(reference_load_rs1_yes(Nat.sub 7 lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Lane Resets Steps Lower Upper Source.
 destruct lane as [|lane].
 {
 assert (V0:VM.find 1942(history time)=Some(Gval(Fuint 25)(take 25 instruction))).
 { rewrite (reference_control_stable_1942_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1942 reference_control_expr_1942);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1942| |apply Steps;lia].
 intro site. cbn [reference_control_expr_1942 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V1:VM.find 1943(history time)=Some(Gval(Fuint 20)(take 20 instruction))).
 { rewrite (reference_control_stable_1943_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1943 reference_control_expr_1943);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1943| |apply Steps;lia].
 intro site. cbn [reference_control_expr_1943 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2:VM.find 1944(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { rewrite (reference_control_stable_1944_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1944 reference_control_expr_1944);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1944| |apply Steps;lia].
 intro site. cbn [reference_control_expr_1944 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1. cbn.
 unfold rf_instruction_address.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 exact V2. }
 destruct lane as [|lane].
 {
 assert (V0:VM.find 1947(history time)=Some(Gval(Fuint 25)(take 25 instruction))).
 { rewrite (reference_control_stable_1947_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1947 reference_control_expr_1947);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1947| |apply Steps;lia].
 intro site. cbn [reference_control_expr_1947 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V1:VM.find 1948(history time)=Some(Gval(Fuint 20)(take 20 instruction))).
 { rewrite (reference_control_stable_1948_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1948 reference_control_expr_1948);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1948| |apply Steps;lia].
 intro site. cbn [reference_control_expr_1948 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2:VM.find 1949(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { rewrite (reference_control_stable_1949_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1949 reference_control_expr_1949);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1949| |apply Steps;lia].
 intro site. cbn [reference_control_expr_1949 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1. cbn.
 unfold rf_instruction_address.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 exact V2. }
 destruct lane as [|lane].
 {
 assert (V0:VM.find 1952(history time)=Some(Gval(Fuint 25)(take 25 instruction))).
 { rewrite (reference_control_stable_1952_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1952 reference_control_expr_1952);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1952| |apply Steps;lia].
 intro site. cbn [reference_control_expr_1952 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V1:VM.find 1953(history time)=Some(Gval(Fuint 20)(take 20 instruction))).
 { rewrite (reference_control_stable_1953_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1953 reference_control_expr_1953);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1953| |apply Steps;lia].
 intro site. cbn [reference_control_expr_1953 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2:VM.find 1954(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { rewrite (reference_control_stable_1954_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1954 reference_control_expr_1954);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1954| |apply Steps;lia].
 intro site. cbn [reference_control_expr_1954 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1. cbn.
 unfold rf_instruction_address.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 exact V2. }
 lia.
Qed.
Theorem reference_store_rs1_history inputs path history limit reset time instruction lane :
 (lane<3)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<19)%coq_nat ->VM.find(reference_load_rs1_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 7 lane)])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 assert (TypedSource : forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(reference_store_rs1_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper (Source time ltac:(lia)ltac:(lia))) as Raw.
 assert (Selected : VM.find 2143(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { change (VM.find(reference_load_rs1_node 18)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time)) 19 (Nat.sub 7 lane) 5 (rf_instruction_address false instruction) 2124 reference_load_rs1_node reference_load_rs1_guard reference_load_rs1_yes);[lia|exact(rf_instruction_address_size false instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(reference_load_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(reference_load_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(reference_load_rs1_branch_types n _ history limit time Bound Steps TypedSource Lower ltac:(lia))).
 - intros n Bound. exact(proj2(reference_load_rs1_branch_types n _ history limit time Bound Steps TypedSource Lower ltac:(lia))). }
 assert (Gate : VM.find 2144(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(reference_load_rs1_aux_value 10 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn [reference_load_rs1_aux_expression reference_load_rs1_aux_expressions nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size false instruction Size). }
 eapply(reference_load_rs1_aux_value 11 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Lemma reference_store_rs1_decode instruction lane n : (lane<3)%coq_nat ->(n<19)%coq_nat ->store_type_is_store instruction lane ->
 N.eqb(reference_instruction_code(Nat.add 29 n))(N.land(to_N instruction)(reference_instruction_mask(Nat.add 29 n)))=Nat.eqb n(Nat.sub 7 lane).
Proof.
 intros Lane Bound Store.
 assert (Match : N.land (to_N instruction) (reference_instruction_mask (Nat.sub 36 lane)) = reference_instruction_code (Nat.sub 36 lane)).
 { unfold store_type_is_store in Store. do 3 (destruct lane as [|lane];[exact Store|]);lia. }
 rewrite (rf_reference_decode_onehot instruction (Nat.sub 36 lane) (Nat.add 29 n) ltac:(lia) ltac:(lia) Match).
 do 3 (destruct lane as [|lane];[do 19 (destruct n as [|n];[reflexivity|]);lia|]);lia.
Qed.
Theorem reference_store_rs1_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 3)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 store_type_is_store instruction lane ->
 VM.find 2145 (top_environment observed) = Some (Gval (Fuint 5) (rf_instruction_address false instruction)).
Proof.
 intros Observe Legal Reset Lane Instruction Load.
 pose proof (store_reference_enabled_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load) as Enabled.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (195 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert (Source : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Lower Upper. exact (memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert (Guards : forall n,(n<19)%coq_nat ->VM.find(reference_load_rs1_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 7 lane)])).
 { intros n Bound.
   set (h := fun t:nat => history (match t with O=>9248%nat | S O=>9249%nat | _=>9250%nat end)).
   assert (HS : forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
   { intros [|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
   assert (HI : forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
   { intros [|[|t]] T;unfold h;apply Source;vm_compute;lia. }
   pose proof(reference_instruction_decode_history _ h 2 instruction (Nat.add 29 n) ltac:(lia) HS HI 2 ltac:(lia) ltac:(lia))as Decode.
   rewrite(reference_store_rs1_decode instruction lane n Lane Bound Load)in Decode. exact Decode. }
 pose proof(reference_store_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Guards)as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem reference_store_rs1_bank_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction)))).
Proof.
 intros Observe Legal Reset Lane Instruction Load Bank.
 assert(Size:size instruction=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[W V]]. rewrite Instruction in V;inversion V;subst;exact W. }
 eapply(reference_register_read_observed memory inputs k observed bank (rf_instruction_address false instruction));[exact Observe|exact Legal|exact Bank|exact(rf_instruction_address_size false instruction Size)|].
 exact(reference_store_rs1_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load).
Qed.

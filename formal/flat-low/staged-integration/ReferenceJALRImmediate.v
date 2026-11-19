Require Import ReferenceControlNodeCongruence2 ReferenceRedirectSpine DUTRedirectDecode CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceBranchImmediate ReferenceImmediateTypes ReferenceLoadImmediate ReferenceControlExpressions ReferenceInstructionDecode LoadImmediateSemantics ReferenceLoadSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.

Require Import RFALUReferenceImmediate JALRAddressCycle ReferenceControlStabilityHistory ReferenceControlNodeCertificates2 ReferenceControlNodeCongruence1 ReferenceControlNodeCertificates1.

Lemma jalr_i_low_selected inputs path history limit reset time word lane :(lane<15)%coq_nat ->size word=12%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 VM.find(rf_i_low_yes lane)(history time)=Some(Gval(Fuint 12)word) ->
 VM.find 2248(history time)=Some(Gval(Fuint 12)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards Raw.
 assert(Selected:VM.find 2246(history time)=Some(Gval(Fuint 12)word)).
 { change(VM.find(rf_i_low_node 14)(history time)=Some(Gval(Fuint 12)word)).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history time)15 lane 12 word 2231 rf_i_low_node rf_i_low_guard rf_i_low_yes);[lia|exact Size| | |exact Guards| | |exact Raw|lia|lia].
 - intros;reflexivity.
 - intros n Bound value Eval. exact(rf_i_low_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_low_types n _ history limit time Bound Steps Source Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_i_low_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(Gate:VM.find 2247(history time)=Some(Gval(Fuint 12)word)).
 { eapply(reference_immediate_value_history 60 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2247 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact Size. }
 eapply(reference_immediate_value_history 61 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Lemma jalr_i_high_selected inputs path history limit reset time word lane :(lane<27)%coq_nat ->size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 VM.find(rf_i_high_yes lane)(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards Raw.
 assert(Selected:VM.find 2550(history time)=Some(Gval(Fuint 32)word)).
 { change(VM.find(rf_i_high_node 26)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history time)27 lane 32 word 2523 rf_i_high_node rf_i_high_guard rf_i_high_yes);[lia|exact Size| | |exact Guards| | |exact Raw|lia|lia].
 - intros;reflexivity.
 - intros n Bound value Eval. exact(rf_i_high_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_high_types n _ history limit time Bound Steps Source Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_i_high_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(Gate:VM.find 2551(history time)=Some(Gval(Fuint 32)word)).
 { eapply(reference_immediate_value_history 302 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact Size. }
 eapply(reference_immediate_value_history 303 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Lemma jalr_i_raw inputs path history limit reset time instruction :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find 2219(history time)=Some(Gval(Fuint 12)(drop 20(take 32 instruction))).
Proof. intros Resets Steps Lower Upper Source.
  eapply(reference_immediate_value_history 32 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2219 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. Qed.

Lemma jalr_i_sign inputs path history limit reset time word :size word=12%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 2248(history time)=Some(Gval(Fuint 12)word) ->
 VM.find 2449(history time)=Some(Gval(Fuint 32)(sext_to 32 word)).
Proof. intros Size Resets Steps Lower Upper Low.

assert(V0:VM.find 2446(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2446_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2446 reference_control_expr_2446);[exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2446| |apply Steps;lia]. intro site. cbn[reference_control_expr_2446 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2447(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2447_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2447 reference_control_expr_2447);[exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2447| |apply Steps;lia]. intro site. cbn[reference_control_expr_2447 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2448(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 223 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2448 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2449(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 224 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2449 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3.
Qed.

Theorem jalr_i_immediate_history inputs path history limit reset time instruction :
 size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n 6])) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n 9])) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled LowGuards HighGuards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 assert(RawSize:size(drop 20(take 32 instruction))=12%nat).
 { rewrite size_drop size_take Size;reflexivity. }
 pose proof(jalr_i_raw inputs path history limit reset time instruction Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as Raw.
 pose proof(jalr_i_low_selected inputs path history limit reset time(drop 20(take 32 instruction))6 ltac:(lia)RawSize Resets Steps Typed Lower Upper Enabled LowGuards Raw)as Low.
 pose proof(jalr_i_sign inputs path history limit reset time(drop 20(take 32 instruction))RawSize Resets Steps Lower Upper Low)as Sign.
 exact(jalr_i_high_selected inputs path history limit reset time(load_i_immediate instruction)9 ltac:(lia)(load_i_immediate_size instruction Size)Resets Steps Typed Lower Upper Enabled HighGuards Sign).
Qed.

Require Import ReferenceIllegalObserved LoadPipelineClassification FormalInstructionResetConstants RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory MemoryRequestObservedSemantics LoadTypeCorrespondence.

Lemma jalr_i_low_decode instruction n :(n<15)%coq_nat ->jalr_match instruction ->
 N.eqb(reference_instruction_code(rf_i_low_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_i_low_decoder n)))=Nat.eqb n 6.
Proof. intros Bound Match.
 rewrite(rf_reference_decode_onehot instruction 22 (rf_i_low_decoder n)ltac:(lia)ltac:(do 15(destruct n as[|n];[vm_compute;lia|]);lia)Match).
 do 15(destruct n as[|n];[reflexivity|]);lia.
Qed.

Lemma jalr_i_high_decode instruction n :(n<27)%coq_nat ->jalr_match instruction ->
 N.eqb(reference_instruction_code(rf_i_high_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_i_high_decoder n)))=Nat.eqb n 9.
Proof. intros Bound Match.
 rewrite(rf_reference_decode_onehot instruction 22 (rf_i_high_decoder n)ltac:(lia)ltac:(do 27(destruct n as[|n];[vm_compute;lia|]);lia)Match).
 do 27(destruct n as[|n];[reflexivity|]);lia.
Qed.

Theorem reference_jalr_immediate_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 jalr_match instruction ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Observe Legal Reset Instruction Match.
 assert(Enabled:VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true])).
 { destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Late Nop]].
 destruct bit.
 - specialize(Nop(Logic.eq_refl _)). rewrite Nop in Instruction;inversion Instruction;subst instruction. vm_compute in Match;discriminate.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late). }
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Inst:forall t,(t<=9259)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite<-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Instruction. }
 assert(Enable:forall t,(195<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::true])).
 { intros t Lower Upper. rewrite(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat ltac:(lia)ltac:(lia)Upper ltac:(lia))Last;exact Enabled. }
 assert(Source:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Lower Upper. exact(memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert(Decode:forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)(history 9250%nat)=Some(Gval(Fuint 1)[::N.eqb(reference_instruction_code row)(N.land(to_N instruction)(reference_instruction_mask row))])).
 { intros row Row. set(h:=fun t:nat=>history(match t with O=>9248%nat|S O=>9249%nat|_=>9250%nat end)).
 assert(HS:forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
 { intros[|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
 assert(HI:forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
 { intros[|[|t]] T;unfold h;apply Source;vm_compute;lia. }
 exact(reference_instruction_decode_history _ h 2 instruction row Row HS HI 2 ltac:(lia)ltac:(lia)). }
 assert(Low:forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n 6])).
 { intros n Bound. unfold rf_i_low_guard. rewrite(Decode (rf_i_low_decoder n)ltac:(do 15(destruct n as[|n];[vm_compute;lia|]);lia))(jalr_i_low_decode instruction n Bound Match);reflexivity. }
 assert(High:forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n 9])).
 { intros n Bound. unfold rf_i_high_guard. rewrite(Decode (rf_i_high_decoder n)ltac:(do 27(destruct n as[|n];[vm_compute;lia|]);lia))(jalr_i_high_decode instruction n Bound Match);reflexivity. }
 pose proof(jalr_i_immediate_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Low High)as Value.
 rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value;exact Value.
Qed.

Require Import RFAddCycle RFALUReferencePorts RFALUReferenceData ReferenceImmediatePrefix ReferenceRs1Types ReferenceRs2Types ReferenceControlExpressions ReferenceControlStabilityHistory ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceRedirectSpine ReferenceInstructionDecode RFReadPorts CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.

Definition rf_add_port_nodes :seq VarOrder.T :=[::2060;2061;2062;2097;2098;2099;2100;2101;2593;2594;2595;2596].
Definition rf_add_port_expr n :=nth (@Econst VarOrder.T(Fuint 1)[::false])[::reference_control_expr_2060;reference_control_expr_2061;reference_control_expr_2062;reference_control_expr_2097;reference_control_expr_2098;reference_control_expr_2099;reference_control_expr_2100;reference_control_expr_2101;reference_control_expr_2593;reference_control_expr_2594;reference_control_expr_2595;reference_control_expr_2596]n.
Lemma rf_add_port_value n inputs path history limit reset time width word :(n<12)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(rf_add_port_expr n)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(nth 0 rf_add_port_nodes n)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
destruct n as[|n]. { change(VM.find 2060(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2060_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2060 reference_control_expr_2060);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2060|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2061(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2061_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2061 reference_control_expr_2061);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2061|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2062(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2062_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2062 reference_control_expr_2062);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2062|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2097(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2097_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2097 reference_control_expr_2097);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2097|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2098(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2098_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2098 reference_control_expr_2098);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2098|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2099(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2099_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2099 reference_control_expr_2099);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2099|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2100(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2100_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2100 reference_control_expr_2100);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2100|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2101(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2101_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2101 reference_control_expr_2101);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2101|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2593(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2593_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2593 reference_control_expr_2593);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2593|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2594(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2594_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2594 reference_control_expr_2594);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2594|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2595(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2595_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2595 reference_control_expr_2595);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2595|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2596(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2596_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2596 reference_control_expr_2596);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2596|exact Eval|apply Steps;lia]. }
lia. Qed.
Theorem rf_add_port_slices inputs path history limit reset time instruction :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find 2062(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)) /\
 VM.find 2098(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)) /\
 VM.find 2593(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Resets Steps Lower Upper Source.
assert(V2060:VM.find 2060(history time)=Some(Gval(Fuint 25)(drop 0(take 25(instruction))))).
{ eapply(rf_add_port_value 0 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_add_port_expr nth reference_control_expr_2060 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2061:VM.find 2061(history time)=Some(Gval(Fuint 20)(drop 0(take 20(drop 0(take 25(instruction))))))).
{ eapply(rf_add_port_value 1 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_add_port_expr nth reference_control_expr_2061 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2060. reflexivity. }
assert(V2062:VM.find 2062(history time)=Some(Gval(Fuint 5)(drop 15(take 20(drop 0(take 20(drop 0(take 25(instruction))))))))).
{ eapply(rf_add_port_value 2 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_add_port_expr nth reference_control_expr_2062 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2061. reflexivity. }
assert(V2097:VM.find 2097(history time)=Some(Gval(Fuint 20)(drop 0(take 20(instruction))))).
{ eapply(rf_add_port_value 3 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_add_port_expr nth reference_control_expr_2097 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2098:VM.find 2098(history time)=Some(Gval(Fuint 5)(drop 15(take 20(drop 0(take 20(instruction))))))).
{ eapply(rf_add_port_value 4 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_add_port_expr nth reference_control_expr_2098 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2097. reflexivity. }
assert(V2593:VM.find 2593(history time)=Some(Gval(Fuint 5)(drop 20(take 25(drop 0(take 25(instruction))))))).
{ eapply(rf_add_port_value 8 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_add_port_expr nth reference_control_expr_2593 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2060. reflexivity. }
unfold rf_instruction_address. rewrite !drop0 !take_take in V2062,V2098,V2593;try reflexivity.
split;[exact V2062|]. split;assumption.
Qed.
(* Handwritten semantic composition. *)

Require Import ReferenceLoadImmediate DUTRedirectDecode.
Theorem rf_add_prefix_history second inputs path history limit reset time word :
 size word=5%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find(if second then 2593 else 2098)(history time)=Some(Gval(Fuint 5)word) ->
 VM.find(if second then 2059 else 2096)(history time)=Some(Gval(Fuint 1)[::true]) ->
 VM.find(if second then 2054 else 2092)(history time)=Some(Gval(Fuint 1)[::false]) ->
 VM.find(if second then 2049 else 2088)(history time)=Some(Gval(Fuint 1)[::false]) ->
 (exists value,VM.find(if second then 2592 else 2094)(history time)=Some value /\type_of_val value=Gtyp(Fuint 5)) ->
 (exists value,VM.find(if second then 2591 else 2090)(history time)=Some value /\type_of_val value=Gtyp(Fuint 5)) ->
 VM.find(if second then 2596 else 2101)(history time)=Some(Gval(Fuint 5)word).
Proof.
 intros Size Resets Steps Lower Upper Raw G0 G1 G2 [other1[Other1 Type1]][other2[Other2 Type2]].
 destruct second.
- assert(V2594:VM.find 2594(history time)=Some(Gval(Fuint 5)word)).
 { eapply(rf_add_port_value 9 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_add_port_expr nth reference_control_expr_2594 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite G0;cbn;rewrite Raw.
 unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref]. apply dut_decode_adapt;exact Size. }
assert(V2595:VM.find 2595(history time)=Some(Gval(Fuint 5)word)).
 { eapply(rf_add_port_value 10 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_add_port_expr nth]. unfold reference_control_expr_2595.
 apply(immediate_selected_mux _ _ _ _ _ _ 5 word other1 false Size G1 V2594 Other1 Type1). }
assert(V2596:VM.find 2596(history time)=Some(Gval(Fuint 5)word)).
 { eapply(rf_add_port_value 11 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_add_port_expr nth]. unfold reference_control_expr_2596.
 apply(immediate_selected_mux _ _ _ _ _ _ 5 word other2 false Size G2 V2595 Other2 Type2). }
 exact V2596.
- assert(V2099:VM.find 2099(history time)=Some(Gval(Fuint 5)word)).
 { eapply(rf_add_port_value 5 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_add_port_expr nth reference_control_expr_2099 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite G0;cbn;rewrite Raw.
 unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref]. apply dut_decode_adapt;exact Size. }
assert(V2100:VM.find 2100(history time)=Some(Gval(Fuint 5)word)).
 { eapply(rf_add_port_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_add_port_expr nth]. unfold reference_control_expr_2100.
 apply(immediate_selected_mux _ _ _ _ _ _ 5 word other1 false Size G1 V2099 Other1 Type1). }
assert(V2101:VM.find 2101(history time)=Some(Gval(Fuint 5)word)).
 { eapply(rf_add_port_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_add_port_expr nth]. unfold reference_control_expr_2101.
 apply(immediate_selected_mux _ _ _ _ _ _ 5 word other2 false Size G2 V2100 Other2 Type2). }
 exact V2101.
Qed.
Lemma rf_add_rs1_guards instruction_lane env : (instruction_lane<2)%coq_nat ->
 (forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)env=Some(Gval(Fuint 1)[::Nat.eqb row(rf_add_class instruction_lane)])) ->
 forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)env=Some(Gval(Fuint 1)[::if Nat.eqb instruction_lane 0 then Nat.eqb n 6 else false]).
Proof.
 intros Lane Decode n Bound. unfold rf_alu_rs1_guard.
 rewrite(Decode(rf_alu_rs1_decoder n)ltac:(do 42(destruct n as[|n];[cbn[rf_alu_rs1_decoder nth];lia|]);lia)).
 do 2(destruct instruction_lane as[|instruction_lane];[do 42(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.
Lemma rf_add_rs2_guards env :
 (forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)env=Some(Gval(Fuint 1)[::Nat.eqb row 11])) ->
 forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)env=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Decode n Bound. unfold rf_alu_rs2_guard.
 rewrite(Decode(rf_alu_rs2_decoder n)ltac:(do 24(destruct n as[|n];[cbn[rf_alu_rs2_decoder nth];lia|]);lia)).
 do 24(destruct n as[|n];[reflexivity|]);lia.
Qed.
Theorem rf_add_rs1_history inputs path history limit reset time instruction lane :
 (lane<2)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)(history time)=Some(Gval(Fuint 1)[::Nat.eqb row(rf_add_class lane)])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Decode.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 destruct(rf_add_port_slices inputs path history limit reset time instruction Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as[Add[Addi Rs2]].
 pose proof(rf_add_rs1_guards lane(history time)Lane Decode)as Guards.
 assert(Selected:VM.find 2143(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { destruct lane as[|[|lane]];[| |lia].
 - change(VM.find(rf_alu_rs1_node 41)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
   eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))42 6 5(rf_instruction_address false instruction)2101 rf_alu_rs1_node rf_alu_rs1_guard rf_alu_rs1_yes);[lia|exact(rf_instruction_address_size false instruction Size)| | |exact Guards| | |exact Add|lia|lia].
   + intros n Bound. exact(rf_alu_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
   + intros n Bound value Eval. apply(rf_alu_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
   + intros n Bound. exact(proj1(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
   + intros n Bound. exact(proj2(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - assert(Prefix:VM.find 2101(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
   { apply(rf_add_prefix_history false inputs path history limit reset time _ (rf_instruction_address_size false instruction Size)Resets Steps Lower Upper Addi).
   + exact(Decode 0%nat ltac:(lia)).
   + exact(Decode 1%nat ltac:(lia)).
   + exact(Decode 2%nat ltac:(lia)).
   + exact(reference_rs1_types_history _ history limit 200 Steps Typed 120%nat ltac:(lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)ltac:(lia)).
   + exact(reference_rs1_types_history _ history limit 200 Steps Typed 118%nat ltac:(lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)ltac:(lia)). }
   change(VM.find(rf_alu_rs1_node 41)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
   apply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time)42 5(rf_instruction_address false instruction)2101 rf_alu_rs1_node rf_alu_rs1_guard rf_alu_rs1_yes(rf_instruction_address_size false instruction Size));[|exact Guards| |exact Prefix|lia].
   + intros n Bound value Eval. rewrite(rf_alu_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper). apply(rf_alu_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
   + intros n Bound. exact(proj1(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2144(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(rf_alu_rs1_value 15 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size false instruction Size). }
 eapply(rf_alu_rs1_value 16 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Theorem rf_add_rs2_history inputs path history limit reset time instruction :
 size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)(history time)=Some(Gval(Fuint 1)[::Nat.eqb row 11])) ->
 VM.find 2622(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Decode.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 destruct(rf_add_port_slices inputs path history limit reset time instruction Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as[Add[Addi Raw]].
 pose proof(rf_add_rs2_guards(history time)Decode)as Guards.
 assert(Prefix:VM.find 2596(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { apply(rf_add_prefix_history true inputs path history limit reset time _ (rf_instruction_address_size true instruction Size)Resets Steps Lower Upper Raw).
 - exact(Decode 11%nat ltac:(lia)).
 - exact(Decode 12%nat ltac:(lia)).
 - exact(Decode 13%nat ltac:(lia)).
 - exact(reference_rs2_types_history _ history limit 200 Steps Typed 58%nat ltac:(lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)ltac:(lia)).
 - exact(reference_rs2_types_history _ history limit 200 Steps Typed 57%nat ltac:(lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)ltac:(lia)). }
 assert(Selected:VM.find 2620(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { change(VM.find(rf_alu_rs2_node 23)(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 apply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time)24 5(rf_instruction_address true instruction)2596 rf_alu_rs2_node rf_alu_rs2_guard rf_alu_rs2_yes(rf_instruction_address_size true instruction Size));[|exact Guards| |exact Prefix|lia].
 - intros n Bound value Eval. rewrite(rf_alu_rs2_same n inputs path history limit reset time Bound Resets Steps Lower Upper). apply(rf_alu_rs2_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2621(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(rf_alu_rs2_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2621 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size true instruction Size). }
 eapply(rf_alu_rs2_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Require Import RFScalarControl FormalLocalHistory FormalObservedHistory JointUpdateBoundaryHistory ObservedJointRegisterConcrete LoadTypeCorrespondence MemoryRequestObservedSemantics ReferenceLoadRs1 ReferenceRegisterRead ReferenceSecondRegisterRead RFReferenceNopHistory.
Theorem rf_reference_operand_context memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (row<37)%coq_nat ->N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 size instruction=32%nat /\exists reset history,
 history 9259%nat=top_environment observed /\
 (forall t,(t<=9259)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) /\
 (forall t,(t<9259)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) /\
 (forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) /\
 VM.find 1707(history 9250%nat)=Some(Gval(Fuint 1)[::true]) /\
 (forall n,(n<48)%coq_nat ->VM.find(reference_instruction_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n row])).
Proof.
 intros Observe Legal Enabled Instruction Row Match.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(vm_compute;lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (195 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia) Upper ltac:(vm_compute;lia)) Last. exact Enabled. }
 assert (Source : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Lower Upper. exact (memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }

 split;[exact Size|]. exists reset,history. split;[exact Last|]. split;[exact Resets|]. split;[exact Steps|]. split;[exact Source|].
 split;[apply Enable;vm_compute;lia|].
 intros n Bound.
 set(h:=fun t:nat=>history(match t with O=>9248%nat|S O=>9249%nat|_=>9250%nat end)).
 assert(HS:forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
 { intros[|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
 assert(HI:forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
 { intros[|[|t]] T;unfold h;apply Source;vm_compute;lia. }
 pose proof(reference_instruction_decode_history _ h 2 instruction n Bound HS HI 2 ltac:(lia)ltac:(lia))as Decode.
 rewrite(rf_reference_decode_onehot instruction row n Row Bound Match)in Decode. exact Decode.
Qed.
Theorem rf_add_index_observed second memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<2)%coq_nat ->(second=true ->lane=0%nat) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 VM.find(if second then 2622 else 2145)(top_environment observed)=Some(Gval(Fuint 5)(rf_instruction_address second instruction)).
Proof.
 intros Observe Legal Enabled Lane Reg Instruction Match.
 destruct(rf_reference_operand_context memory inputs k observed instruction(rf_add_class lane)Observe Legal Enabled Instruction ltac:(do 2(destruct lane as[|lane];[vm_compute;lia|]);lia)Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 destruct second.
 - specialize(Reg(Logic.eq_refl true));subst lane.
 pose proof(rf_add_rs2_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable Decode)as Value.
 rewrite(reference_control_stable_2622_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
 - pose proof(rf_add_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable Decode)as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem rf_add_bank_observed second memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<2)%coq_nat ->(second=true ->lane=0%nat) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(if second then 2804 else 2209)(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address second instruction)))).
Proof.
 intros Observe Legal Enabled Lane Reg Instruction Match Bank.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
 rewrite Instruction in Word;inversion Word;subst word.
 pose proof(rf_add_index_observed second memory inputs k observed instruction lane Observe Legal Enabled Lane Reg Instruction Match)as Index.
 destruct second.
 - exact(reference_second_register_read_observed memory inputs k observed bank _ Observe Legal Bank(rf_instruction_address_size true instruction Size)Index).
 - exact(reference_register_read_observed memory inputs k observed bank _ Observe Legal Bank(rf_instruction_address_size false instruction Size)Index).
Qed.

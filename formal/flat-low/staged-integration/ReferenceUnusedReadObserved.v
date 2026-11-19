Require Import ReferenceUnusedReadPorts RFAddReferencePorts RFALUReferencePorts ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem unused_rs1_index_observed memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 row=21%nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find 2145(top_environment observed)=Some(Gval(Fuint 5)(zeros 5)).
Proof.
 intros Observe Legal Enabled Instruction Row Match.
 assert(Bound:(row<37)%coq_nat)by lia.
 destruct(rf_reference_operand_context memory inputs k observed instruction row Observe Legal Enabled Instruction Bound Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 assert(Prefix:forall n,(n<3)%coq_nat ->VM.find(nth 0 unused_rs1_prefix_guards n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 { intros n N. pose proof(Decode (Nat.add 0 n) ltac:(lia))as D.
 subst row.
 do 3(destruct n as[|n];[exact D|]);lia. }
 assert(Guards:forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 { intros n N. pose proof(Decode(rf_alu_rs1_decoder n) ltac:(do 42(destruct n as[|n];[vm_compute;lia|]);lia))as D.
 subst row.
 do 42(destruct n as[|n];[exact D|]);lia. }
 pose proof(unused_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable Prefix Guards)as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem unused_rs2_index_observed memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (row=21%nat \/ row=22%nat) ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find 2622(top_environment observed)=Some(Gval(Fuint 5)(zeros 5)).
Proof.
 intros Observe Legal Enabled Instruction Row Match.
 assert(Bound:(row<37)%coq_nat)by lia.
 destruct(rf_reference_operand_context memory inputs k observed instruction row Observe Legal Enabled Instruction Bound Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 assert(Prefix:forall n,(n<3)%coq_nat ->VM.find(nth 0 unused_rs2_prefix_guards n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 { intros n N. pose proof(Decode (Nat.add 11 n) ltac:(lia))as D.
 destruct Row as[Row|Row];subst row;
 do 3(destruct n as[|n];[exact D|]);lia. }
 assert(Guards:forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 { intros n N. pose proof(Decode(rf_alu_rs2_decoder n) ltac:(do 24(destruct n as[|n];[vm_compute;lia|]);lia))as D.
 destruct Row as[Row|Row];subst row;
 do 24(destruct n as[|n];[exact D|]);lia. }
 pose proof(unused_rs2_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable Prefix Guards)as Value.
 rewrite(reference_control_stable_2622_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Require Import ReferenceLoadRs1 ReferenceSecondRegisterRead RFReadPorts RFReferenceNopHistory.
Theorem unused_link_bank_observed second memory inputs k observed instruction row bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (if second then row=21%nat \/ row=22%nat else row=21%nat) ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(if second then 2804 else 2209)(top_environment observed)=Some(Gval(Fuint 32)(bank 0%nat)).
Proof.
 intros Observe Legal Enabled Instruction Row Match Bank.
 destruct second.
 - change(VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(zeros 5))))).
   apply(reference_second_register_read_observed memory inputs k observed bank(zeros 5)Observe Legal Bank ltac:(reflexivity)).
   exact(unused_rs2_index_observed memory inputs k observed instruction row Observe Legal Enabled Instruction Row Match).
 - change(VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(zeros 5))))).
   apply(reference_register_read_observed memory inputs k observed bank(zeros 5)Observe Legal Bank ltac:(reflexivity)).
   exact(unused_rs1_index_observed memory inputs k observed instruction row Observe Legal Enabled Instruction Row Match).
Qed.

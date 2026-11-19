from pathlib import Path
p=Path('formal/flat-low/staged-integration/ReferenceUnusedReadObserved.v')
s='''Require Import ReferenceUnusedReadPorts RFAddReferencePorts RFALUReferencePorts ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for port,count,node,base in [(1,42,2145,0),(2,24,2622,11)]:
 condition='row=21%nat' if port==1 else '(row=21%nat '+chr(92)+'/ row=22%nat)'
 s+=f'''Theorem unused_rs{port}_index_observed memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 {condition} ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find {node}(top_environment observed)=Some(Gval(Fuint 5)(zeros 5)).
Proof.
 intros Observe Legal Enabled Instruction Row Match.
 assert(Bound:(row<37)%coq_nat)by lia.
 destruct(rf_reference_operand_context memory inputs k observed instruction row Observe Legal Enabled Instruction Bound Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 assert(Prefix:forall n,(n<3)%coq_nat ->VM.find(nth 0 unused_rs{port}_prefix_guards n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 {{ intros n N. pose proof(Decode (Nat.add {base} n) ltac:(lia))as D.
 {'subst row.' if port==1 else 'destruct Row as[Row|Row];subst row;'}
 do 3(destruct n as[|n];[exact D|]);lia. }}
 assert(Guards:forall n,(n<{count})%coq_nat ->VM.find(rf_alu_rs{port}_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 {{ intros n N. pose proof(Decode(rf_alu_rs{port}_decoder n) ltac:(do {count}(destruct n as[|n];[vm_compute;lia|]);lia))as D.
 {'subst row.' if port==1 else 'destruct Row as[Row|Row];subst row;'}
 do {count}(destruct n as[|n];[exact D|]);lia. }}
 pose proof(unused_rs{port}_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable Prefix Guards)as Value.
 rewrite(reference_control_stable_{node}_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
'''
tail=p.read_text().split('Require Import ReferenceLoadRs1 ReferenceSecondRegisterRead RFReadPorts.',1)
if len(tail)==2:s+='Require Import ReferenceLoadRs1 ReferenceSecondRegisterRead RFReadPorts.'+tail[1]
p.write_text(s)

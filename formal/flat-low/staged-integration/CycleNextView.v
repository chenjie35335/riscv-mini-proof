Require Import CycleReferenceBankInputs CycleISAReferenceAdvance ReferenceBankConcreteReachable
 ReferenceBankObservation RFAluWritebackObserved CycleViewClosure CycleViewConstruction
 ConcreteRegisterInitialization CycleView CoreSocModel FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem cycle_reference_bank_normal_next memory inputs k current next before csr :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_banks_agree before ->cycle_isa_pending before ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 reference_bank_concrete_zero(top_environment next).
Proof.
 intros Transition Reset Before Banks Pending CSR Width.
 destruct Transition as[Observe[Legal[NextObserve[NextLegal[committed Run]]]]].
 assert(Bank:reference_bank_concrete_zero(top_environment current)).
 { exists(cv_reference_bank before). split;[exact(cva_reference_bank _ _ Before)|].
   rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before). }
 pose proof(cycle_reference_bank_inputs memory inputs k current before csr Observe Legal Reset Before Pending CSR Width)as Inputs.
 destruct(reference_bank_normal_or_nop_run_next memory inputs k current committed Observe Legal Run Reset Bank Inputs)as[bank[Concrete Zero]].
 exists bank. split;[exact(reference_bank_run_observed memory inputs(S k)committed next bank Run NextObserve Concrete)|exact Zero].
Qed.
Theorem cycle_view_normal_next memory inputs k current next before csr :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_banks_agree before ->cycle_isa_pending before ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 map_uint_concrete 7331 32(top_environment next) ->
 cycle_view_at(top_environment next)(cycle_snapshot(top_environment next)).
Proof.
 intros Transition Reset Before Banks Pending CSR Width PC.
 destruct(cycle_reference_bank_normal_next memory inputs k current next before csr Transition Reset Before Banks Pending CSR Width)as[bank[Bank Zero]].
 destruct Transition as[Observe[Legal[NextObserve[NextLegal Run]]]].
 exact(cycle_view_from_reference_bank memory inputs(S k)next bank NextObserve NextLegal Bank PC).
Qed.

Require Import ReferenceRedirectSpine CycleView JALRAddressCycle ReferenceJALRImmediate ReferenceJALRRead ReferenceRedirectAlignmentObserved ReferenceRedirectSemantics DUTRedirectReachability ReferenceLoadSemantics LoadImmediateSemantics RFReadPorts FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition cycle_jalr_address v :=reference_load_address
 (cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v))))
 (load_i_immediate(cv_commit_instruction v)).
Definition cycle_jalr_pending v :Prop :=jalr_match(cv_commit_instruction v) ->cv_pending_alu v=cycle_jalr_address v.
Lemma jalr_sum_low_bit rs1 immediate :
 N.testbit(to_N(reference_load_address rs1 immediate))1=N.testbit(to_N rs1+to_N immediate)1.
Proof.
 unfold reference_load_address. rewrite(redirect_to_N_testbit _ 1)nth_take;[|reflexivity].
 rewrite -(redirect_to_N_testbit(from_N 33(to_N rs1+to_N immediate))1) to_N_from_N.
 apply N.mod_pow2_bits_low;reflexivity.
Qed.
Theorem cycle_jalr_pending_aligned memory inputs k observed v compressed :
 CoreSocModel.generated_observe memory inputs k=Some observed ->CoreSocModel.generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_jalr_pending v ->jalr_match(cv_commit_instruction v) ->cv_delayed_redirect v=true ->
 reference_redirect_aligned compressed(N.clearbit
 (to_N(cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v))))+
 to_N(load_i_immediate(cv_commit_instruction v)))0)=true.
Proof.
 intros Observe Legal Reset View Pending Match Taken.
 pose proof(dut_no_trap_target_bit_observed memory inputs k observed(cv_pending_alu v)Observe Legal Reset
 ltac:(rewrite(cva_delayed_redirect _ _ View)Taken;reflexivity)(cva_pending_alu _ _ View)(cva_pending_width _ _ View))as Low.
 rewrite(Pending Match)in Low. unfold cycle_jalr_address in Low. rewrite jalr_sum_low_bit in Low.
 rewrite reference_redirect_aligned_bits N.clearbit_eq N.clearbit_neq;[|discriminate].
 rewrite Low. destruct compressed;reflexivity.
Qed.
Theorem cycle_jalr_alignment_guard memory inputs k observed v csr :
 CoreSocModel.generated_observe memory inputs k=Some observed ->CoreSocModel.generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_jalr_pending v ->jalr_match(cv_commit_instruction v) ->cv_delayed_redirect v=true ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 VM.find 2949(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Pending Match Taken Csr CsrSize.
 pose proof(reference_jalr_rs1_bank_observed memory inputs k observed(cv_commit_instruction v)(cv_reference_bank v)
 Observe Legal Reset(cva_commit_instruction _ _ View)Match(cva_reference_bank _ _ View))as Rs1.
 pose proof(reference_jalr_immediate_observed memory inputs k observed(cv_commit_instruction v)
 Observe Legal Reset(cva_commit_instruction _ _ View)Match)as Immediate.
 pose proof(reference_redirect_alignments_observed memory inputs k observed
 (cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v))))
 (load_i_immediate(cv_commit_instruction v))(cv_reference_pc v)csr
 Observe Legal Rs1 Immediate(cva_reference_pc _ _ View)Csr(cva_reference_pc_width _ _ View)CsrSize)as Values.
 destruct Values as[H0[H1[H2[H3[H4[H5[H6 H7]]]]]]].
 rewrite(cycle_jalr_pending_aligned memory inputs k observed v(N.testbit(to_N csr)2)Observe Legal Reset View Pending Match Taken)in H6.
 exact H6.
Qed.

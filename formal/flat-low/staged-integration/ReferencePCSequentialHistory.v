Require Import CoreSocModel ComparisonNodes ReferencePCSequentialSteps ReferencePCSequentialValues ReferencePCUpdateNodes ExceptionPCPayloadNodes ExceptionPCPayloadConnections ReferencePCNextConnections ReferencePCNormalCommit ExceptionPCSourceRegisters StagedRegisterHold FormalRFResetPropagation FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem reference_pc_sequential_payload_after_nine invalid s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 pc :
 size pc = 32%nat ->
 VM.find 7331 s0 = Some (Gval (Fuint 32) pc) ->
 VM.find 6507 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6780 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1707 s1 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 6780 s5 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1707 s6 = Some (Gval (Fuint 1) [::true]) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 formal_flat_local_step invalid s2 s3 -> formal_flat_local_step invalid s3 s4 ->
 formal_flat_local_step invalid s4 s5 -> formal_flat_local_step invalid s5 s6 ->
 formal_flat_local_step invalid s6 s7 -> formal_flat_local_step invalid s7 s8 ->
 formal_flat_local_step invalid s8 s9 ->
 VM.find 1819 s9 = Some (Gval (Fuint 32) (reference_pc_plus_four pc)).
Proof.
 intros Size PC Redirect Exception0 Valid1 Exception5 Valid6 S1 S2 S3 S4 S5 S6 S7 S8 S9.
 pose proof (exception_pc_1749_value invalid s0 s0 s1 _ _ PC (sized_uint_adapt_identity 32 pc Size) S1) as P1.
 pose proof (exception_pc_2812_value invalid s1 s1 s2 pc P1 S2) as P2.
 pose proof (reference_pc_seq_add invalid s2 s2 s3 pc P2 S3) as P3.
 pose proof (reference_pc_seq_tail invalid s3 s3 s4 pc P3 S4) as P4.
 destruct (reference_pc_seq_mux_6804 invalid s0 s0 s1 [::false] _ (reference_pc_seq_base [::false]) Exception0 Redirect S1)
 as [z1 [Z1 E1]].
 destruct (reference_pc_seq_mux_6805 invalid s1 s1 s2 [::false] z1 E1 Valid1 Z1 S2)
 as [z2 [Z2 E2]].
 pose proof (reference_pc_seq_alias_6806 invalid s2 s2 s3 [::false] z2 E2 Z2 S3) as Z3.
 pose proof (reference_pc_seq_zero_test invalid s3 s3 s4 z2 E2 Z3 S4) as Z4.
 pose proof (reference_pc_plus_four_size pc) as OutputSize.
 assert (Base : reference_pc_seq_extension (reference_pc_plus_four pc) (Gval (Fuint 32) (reference_pc_plus_four pc))).
 { pose proof (reference_pc_seq_base (reference_pc_plus_four pc)) as Base. rewrite OutputSize in Base. exact Base. }
 destruct (reference_pc_seq_mux_6810 invalid s4 s4 s5 _ _ Base Z4 P4 S5) as [v5 [V5 E5]].
 destruct (reference_pc_seq_mux_7094 invalid s5 s5 s6 _ _ E5 Exception5 V5 S6) as [v6 [V6 E6]].
 destruct (reference_pc_seq_mux_7109 invalid s6 s6 s7 _ _ E6 Valid6 V6 S7) as [v7 [V7 [width [Bound Shape]]]]. subst v7.
 assert (V8 : VM.find 7149 s8 = Some (Gval (Fuint 32) (reference_pc_plus_four pc))).
 { apply (reference_pc_update_7149_value invalid s7 s7 s8 32 _); [|exact S8].
   cbn [reference_pc_update_7149_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite V7.
   exact (reference_pc_seq_low_extract _ width OutputSize Bound). }
 exact (exception_pc_1819_value invalid s8 s8 s9 _ _ V8 (sized_uint_adapt_identity 32 _ OutputSize) S9).
Qed.
Theorem reference_pc_sequential_commit_after_nine invalid s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 result pc :
 size pc = 32%nat ->
 VM.find 7331 s0 = Some (Gval (Fuint 32) pc) ->
 VM.find 6507 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6780 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1707 s1 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 6780 s5 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1707 s6 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1515 s9 = Some (Gval (Fuint 1) [::false]) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 formal_flat_local_step invalid s2 s3 -> formal_flat_local_step invalid s3 s4 ->
 formal_flat_local_step invalid s4 s5 -> formal_flat_local_step invalid s5 s6 ->
 formal_flat_local_step invalid s6 s7 -> formal_flat_local_step invalid s7 s8 ->
 formal_flat_local_step invalid s8 s9 ->
 formal_value_iter invalid flat_memories s9 true s9 flat_statements = Some result ->
 VM.find 7331 result = Some (Gval (Fuint 32) (reference_pc_plus_four pc)).
Proof.
 intros Size PC Redirect Exception0 Valid1 Exception5 Valid6 Reset S1 S2 S3 S4 S5 S6 S7 S8 S9 Commit.
 pose proof (reference_pc_sequential_payload_after_nine invalid s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 pc
 Size PC Redirect Exception0 Valid1 Exception5 Valid6 S1 S2 S3 S4 S5 S6 S7 S8 S9) as Value.
 assert (Hold : forall a b, formal_flat_local_step invalid a b -> VM.find 7331 b = VM.find 7331 a).
 { intros a b Step. exact (staged_combinational_holds_registers invalid flat_memories a a b flat_statements 7331 exception_pc_reference_register Step). }
 assert (PC9 : VM.find 7331 s9 = Some (Gval (Fuint 32) pc)).
 { rewrite (Hold _ _ S9) (Hold _ _ S8) (Hold _ _ S7) (Hold _ _ S6) (Hold _ _ S5) (Hold _ _ S4) (Hold _ _ S3) (Hold _ _ S2) (Hold _ _ S1). exact PC. }
 exact (reference_pc_formal_normal_commit invalid s9 s9 result _ _ PC9 (Logic.eq_refl _) Reset Value (reference_pc_plus_four_size pc) Commit).
Qed.
Print Assumptions reference_pc_sequential_commit_after_nine.

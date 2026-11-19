Require Import CoreSocModel ComparisonNodes ExceptionPCPayloadNodes ExceptionPCPayloadConnections ReferencePCStutterSelection ReferencePCNextConnections ReferencePCNormalCommit ExceptionPCSourceRegisters StagedRegisterHold FormalRFResetPropagation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem reference_pc_disabled_payload_after_five invalid s0 s1 s2 s3 s4 s5 bits :
 size bits = 32%nat ->
 VM.find 7331 s0 = Some (Gval (Fuint 32) bits) ->
 VM.find 1707 s2 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 1819 s5 = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Source Disabled S1 S2 S3 S4 S5.
 pose proof (sized_uint_adapt_identity 32 bits Size) as Adapt.
 pose proof (exception_pc_1749_value invalid s0 s0 s1 _ _ Source Adapt S1) as V1.
 pose proof (exception_pc_2812_value invalid s1 s1 s2 bits V1 S2) as V2.
 pose proof (reference_pc_stutter_selection_after_two invalid s2 s3 s4 bits Size Disabled V2 S3 S4) as V4.
 exact (exception_pc_1819_value invalid s4 s4 s5 _ _ V4 Adapt S5).
Qed.
Theorem reference_pc_disabled_commit_after_five invalid s0 s1 s2 s3 s4 s5 result bits :
 size bits = 32%nat ->
 VM.find 7331 s0 = Some (Gval (Fuint 32) bits) ->
 VM.find 1707 s2 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1515 s5 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 true s5 flat_statements = Some result ->
 VM.find 7331 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Source Disabled Reset S1 S2 S3 S4 S5 Commit.
 pose proof (reference_pc_disabled_payload_after_five invalid s0 s1 s2 s3 s4 s5 bits Size Source Disabled S1 S2 S3 S4 S5) as Next.
 assert (Hold : forall a b,
 formal_value_iter invalid flat_memories a false a flat_statements = Some b ->
 VM.find 7331 b = VM.find 7331 a).
 { intros a b Step. exact (staged_combinational_holds_registers invalid flat_memories a a b flat_statements 7331 exception_pc_reference_register Step). }
 assert (Old : VM.find 7331 s5 = Some (Gval (Fuint 32) bits)).
 { rewrite (Hold s4 s5 S5) (Hold s3 s4 S4) (Hold s2 s3 S3) (Hold s1 s2 S2) (Hold s0 s1 S1). exact Source. }
 exact (reference_pc_formal_normal_commit invalid s5 s5 result _ bits Old (Logic.eq_refl _) Reset Next Size Commit).
Qed.
Print Assumptions reference_pc_disabled_commit_after_five.

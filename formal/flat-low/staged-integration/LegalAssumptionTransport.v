Require Import CoreSocModel ComparisonNodes LegalAssumptionNodes LegalAssumptionConnections LegalAssumptionActivation NormalizedBit BooleanControlFacts.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem active_assumption_source_adapts_true invalid s0 s1 s2 s3 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 generated_assume_m0_0_local s3 ->
 VM.find 9238 s3 = Some (Gval (Fuint 1) [::true]) ->
 exists source, VM.find 9141 s0 = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros S1 S2 S3 Assume Enabled.
 destruct (legal_connection_63_observation invalid s0 s0 s1 S1)
 as [source [value [Source [Adapt Value]]]].
 assert (Alias2 : VM.find 9239 s2 = Some value).
 { rewrite (legal_equation_9239 invalid s1 s1 s2 S2).
   cbn [legal_expr_9239 eval_hfexpr_with_memory eval_href_with_memory]. exact Value. }
 assert (Alias3 : VM.find 9240 s3 = Some value).
 { rewrite (legal_equation_9240 invalid s2 s2 s3 S3).
   cbn [legal_expr_9240 eval_hfexpr_with_memory eval_href_with_memory]. exact Alias2. }
 pose proof (active_assumption_normalized_value s3 value Assume Enabled Alias3
 (adapted_bit_normalized source value Adapt)) as TrueValue.
 exists source. split; [exact Source|]. rewrite <- TrueValue. exact Adapt.
Qed.
Theorem active_assumption_normalized_source_true invalid s0 s1 s2 s3 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 generated_assume_m0_0_local s3 ->
 VM.find 9238 s3 = Some (Gval (Fuint 1) [::true]) ->
 (forall value, VM.find 9141 s0 = Some value -> normalized_bit value) ->
 VM.find 9141 s0 = Some (Gval (Fuint 1) [::true]).
Proof.
 intros S1 S2 S3 Assume Enabled Normal.
 destruct (active_assumption_source_adapts_true invalid s0 s1 s2 s3 S1 S2 S3 Assume Enabled)
 as [source [Source Adapt]].
 pose proof (normalized_adaptation_recovers_bit source true (Normal source Source) Adapt) as TrueSource.
 rewrite <- TrueSource. exact Source.
Qed.
Print Assumptions active_assumption_normalized_source_true.

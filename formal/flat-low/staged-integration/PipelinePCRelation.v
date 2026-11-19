Require Import CoreSocModel InitialPipelinePhase InitialPipelinePCValues FetchPCResetValue ReferencePCResetValue ReferencePCResetFacts ObservedAssertion43FromPCSources.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq div.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition pipeline_pc_phase env bits : Prop :=
 (VM.find 7947 env = Some (Gval (Fuint 1) [::false]) /\
  VM.find 7751 env = Some (Gval (Fuint 32) bits)) \/
 (VM.find 7947 env = Some (Gval (Fuint 1) [::true]) /\
  VM.find 7945 env = Some (Gval (Fuint 1) [::false]) /\
  VM.find 7749 env = Some (Gval (Fuint 32) bits)) \/
 (VM.find 7947 env = Some (Gval (Fuint 1) [::true]) /\
  VM.find 7945 env = Some (Gval (Fuint 1) [::true]) /\
  exists fetch, size fetch = 33%nat /\
   VM.find 7768 env = Some (Gval (Fuint 33) fetch) /\
   ((VM.find 7762 env = Some (Gval (Fuint 1) [::false]) /\ bits = take 32 fetch) \/
    (VM.find 7762 env = Some (Gval (Fuint 1) [::true]) /\
     N.of_nat (to_nat bits) = N.modulo (N.add (N.of_nat (to_nat fetch)) 4) (N.pow 2 32)))).
Definition pipeline_pc_relation env : Prop :=
 exists bits, size bits = 32%nat /\ take 2 bits = [::false;false] /\
 VM.find 7331 env = Some (Gval (Fuint 32) bits) /\ pipeline_pc_phase env bits.
Theorem pipeline_pc_relation_initial memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\ pipeline_pc_relation env.
Proof.
 intro Run.
 destruct (initial_pipeline_phase_run_zero memory inputs states Run)
 as [env [Env [Fetch [Reference [Early [Late Started]]]]]].
 exists env. split; [exact Env|]. exists reference_pc_reset_bits.
 split; [exact reference_pc_reset_size|]. split; [exact reference_pc_reset_aligned|].
 split; [exact Reference|]. right. right. split; [exact Late|]. split; [exact Early|].
 exists fetch_pc_reset_word33. split; [exact fetch_pc_reset_size33|].
 split; [exact Fetch|]. right. split; [exact Started|].
 rewrite reference_pc_reset_unsigned fetch_pc_reset_unsigned. vm_compute. reflexivity.
Qed.
Theorem pipeline_pc_relation_commit env :
 pipeline_pc_relation env ->
 VM.find 7947 env = Some (Gval (Fuint 1) [::false]) ->
 exception_pc_sources_agree env.
Proof.
 intros [bits [Size [Aligned [Reference Phase]]]] Late.
 destruct Phase as [[Flag Commit]|[[Flag Rest]|[Flag Rest]]].
 - exists bits. repeat split; assumption.
 - rewrite Late in Flag. discriminate Flag.
 - rewrite Late in Flag. discriminate Flag.
Qed.
Print Assumptions pipeline_pc_relation_initial.
Print Assumptions pipeline_pc_relation_commit.

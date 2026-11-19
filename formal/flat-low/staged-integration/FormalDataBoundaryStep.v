Require Import CoreSocModel FormalLocalHistory DataWriterBoundaryRegisters DataWriterBoundaryIncludesAddress ConcreteRegisterInitialization FormalDataStorageInitialization FormalDataStorageRunStep ObservedDataCommitReady FormalLoadFromDataBoundary.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem data_memory_boundary_step memory inputs k committed old observed next :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some next ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old) ->
 data_storage_concrete committed ->
 data_storage_concrete next /\
 exists word, VM.find 9222 (top_environment next) = Some (Gval (Fuint 32) word).
Proof.
 intros Run Old Observe Next Legal Boundary Storage. split.
 - exact (data_storage_run_step memory inputs k committed observed next Run Observe Next Storage
     (observed_data_commit_ready memory inputs k committed old observed Run Old Observe Legal Boundary Storage)).
 - eapply (load_commit_from_data_boundary memory inputs k committed old observed next Run Old Observe Next Legal); [|exact Storage].
   intros node width Member. apply Boundary. apply data_writer_includes_address. exact Member.
Qed.
Print Assumptions data_memory_boundary_step.

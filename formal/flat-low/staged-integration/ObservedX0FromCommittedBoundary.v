Require Import CoreSocModel ObservedX0FromBoundaryState X0BoundaryPreparation X0BoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem observed_x0_from_committed_boundary memory inputs k committed old states :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 (forall node width, List.In (node,width) x0_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old) ->
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 generated_assert_m0_8_all states.
Proof.
 intros Run Old Boundary Observe Legal.
 apply (observed_x0_from_boundary_state memory inputs k states Observe Legal).
 intros node width Member.
 exact (x0_boundary_observed_concrete memory inputs k committed old states node width
 Member (Boundary node width Member) Run Old Observe).
Qed.
Print Assumptions observed_x0_from_committed_boundary.

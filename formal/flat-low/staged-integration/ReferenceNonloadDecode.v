Require Import CoreSocModel ComparisonNodes MemoryRequestObservedSemantics ReferenceMemoryRequest LoadTypeCorrespondence ReferenceControlStabilityHistory FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_nonload_guards_observed memory inputs k observed instruction enabled :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 load_type_decode(to_N instruction)49=from_N 3 0 ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::enabled]) ->
 forall row,(row<5)%coq_nat ->VM.find(reference_memory_guard row)(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Instruction Zero Enabled row Row.
 pose proof(memory_reference_decode_observed memory inputs k observed instruction enabled row Observe Legal ltac:(lia) Instruction Enabled)as Decode.
 assert(Test:N.eqb(reference_memory_code row)(N.land(to_N(memory_reference_instruction instruction enabled))28799)=false).
 { destruct enabled.
 - apply N.eqb_neq. intro Equal.
   pose proof(memory_request_decode_zero(to_N instruction)Zero row Row)as NotLoad. apply NotLoad.
   assert(Codes:reference_memory_code row=load_type_lane_code row)by(do 5(destruct row as[|row];[reflexivity|]);lia).
   rewrite <-Codes. symmetry;exact Equal.
 - do 5(destruct row as[|row];[reflexivity|]);lia. }
 rewrite Test in Decode;exact Decode.
Qed.

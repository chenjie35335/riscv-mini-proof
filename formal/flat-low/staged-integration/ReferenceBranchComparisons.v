Require Import ReferenceRedirectSemantics ReferenceRedirectSpine ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_branch_comparisons_observed memory inputs k observed rs1 rs2 :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)rs1) ->
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)rs2) ->
 size rs1=32%nat ->size rs2=32%nat ->
 VM.find 2806(top_environment observed)=Some(Gval(Fuint 1)[::N.leb(to_N rs2)(to_N rs1)]) /\
 VM.find 2830(top_environment observed)=Some(Gval(Fuint 1)[::Z.leb(reference_redirect_signed(to_N rs2))(reference_redirect_signed(to_N rs1))]) /\
 VM.find 2850(top_environment observed)=Some(Gval(Fuint 1)[::N.ltb(to_N rs1)(to_N rs2)]) /\
 VM.find 2872(top_environment observed)=Some(Gval(Fuint 1)[::Z.ltb(reference_redirect_signed(to_N rs1))(reference_redirect_signed(to_N rs2))]) /\
 VM.find 2892(top_environment observed)=Some(Gval(Fuint 1)[::negb(N.eqb(to_N rs1)(to_N rs2))]) /\
 VM.find 2912(top_environment observed)=Some(Gval(Fuint 1)[::N.eqb(to_N rs1)(to_N rs2)]).
Proof.
 intros Observe Legal Rs1 Rs2 Size1 Size2.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(H2209:VM.find 2209(history 9258%nat)=Some(Gval(Fuint 32)rs1)).
 { rewrite(reference_control_stable_2209_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last;exact Rs1. }
 assert(H2804:VM.find 2804(history 9258%nat)=Some(Gval(Fuint 32)rs2)).
 { rewrite(reference_control_stable_2804_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last;exact Rs2. }
 pose proof(reference_redirect_comparisons_history (generated_observation_input inputs k)nil history 9259 reset 9258 rs1 rs2 Resets Steps ltac:(vm_compute;lia)ltac:(vm_compute;lia)H2209 H2804)as Values.
 rewrite(reference_control_stable_2806_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))in Values.
 rewrite(reference_control_stable_2830_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))in Values.
 rewrite(reference_control_stable_2850_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))in Values.
 rewrite(reference_control_stable_2872_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))in Values.
 rewrite(reference_control_stable_2892_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))in Values.
 rewrite(reference_control_stable_2912_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))in Values.
 rewrite Last(reference_redirect_signed32 rs1 Size1)(reference_redirect_signed32 rs2 Size2)Z.geb_leb !redirect_N_eqb in Values. exact Values.
Qed.

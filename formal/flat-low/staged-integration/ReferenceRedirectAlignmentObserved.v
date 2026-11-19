Require Import ReferenceRedirectSemantics ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_redirect_alignments_observed memory inputs k observed rs1 immediate pc csr :
 generated_observe memory inputs k=Some observed -> generated_legal_trace memory inputs k ->
 VM.find 2209 (top_environment observed)=Some(Gval(Fuint 32)rs1) ->
 VM.find 2552 (top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find 7331 (top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find 7332 (top_environment observed)=Some(Gval(Fuint 32)csr) ->
 size pc=32%nat -> size csr=32%nat ->
 VM.find 2825 (top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned (N.testbit(to_N csr)2) (to_N pc+to_N immediate)]) /\
 VM.find 2847 (top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned (N.testbit(to_N csr)2) (to_N pc+to_N immediate)]) /\
 VM.find 2867 (top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned (N.testbit(to_N csr)2) (to_N pc+to_N immediate)]) /\
 VM.find 2889 (top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned (N.testbit(to_N csr)2) (to_N pc+to_N immediate)]) /\
 VM.find 2909 (top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned (N.testbit(to_N csr)2) (to_N pc+to_N immediate)]) /\
 VM.find 2929 (top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned (N.testbit(to_N csr)2) (to_N pc+to_N immediate)]) /\
 VM.find 2949 (top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned (N.testbit(to_N csr)2) (N.clearbit(to_N rs1+to_N immediate)0)]) /\
 VM.find 2966 (top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned (N.testbit(to_N csr)2) (to_N pc+to_N immediate)]).
Proof.
 intros Observe Legal Rs1 Immediate Pc Csr PcSize CsrSize.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(H2209:VM.find 2209(history 9258)=Some(Gval(Fuint 32)rs1)).
 { rewrite(reference_control_stable_2209_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Rs1. }
 assert(H2552:VM.find 2552(history 9258)=Some(Gval(Fuint 32)immediate)).
 { rewrite(reference_control_stable_2552_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Immediate. }
 assert(H7331:VM.find 7331(history 9258)=Some(Gval(Fuint 32)pc)).
 { rewrite(reference_control_stable_7331_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Pc. }
 assert(H7332:VM.find 7332(history 9258)=Some(Gval(Fuint 32)csr)).
 { rewrite(reference_control_stable_7332_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Csr. }
 destruct(reference_redirect_aliases_history (generated_observation_input inputs k) nil history 9259 reset 9258 pc csr Resets Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia) H7331 H7332 PcSize CsrSize)as[PcAlias CsrAlias].
 pose proof(reference_redirect_alignments_history (generated_observation_input inputs k) nil history 9259 reset 9258 csr pc immediate rs1 Resets Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia) CsrAlias PcAlias H2552 H2209 CsrSize)as Alignment.
 rewrite(reference_control_stable_2825_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) in Alignment.
 rewrite(reference_control_stable_2847_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) in Alignment.
 rewrite(reference_control_stable_2867_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) in Alignment.
 rewrite(reference_control_stable_2889_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) in Alignment.
 rewrite(reference_control_stable_2909_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) in Alignment.
 rewrite(reference_control_stable_2929_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) in Alignment.
 rewrite(reference_control_stable_2949_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) in Alignment.
 rewrite(reference_control_stable_2966_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) in Alignment.
 rewrite Last in Alignment. exact Alignment.
Qed.
Definition reference_pc_alignment_nodes := [::2825;2847;2867;2889;2909;2929;2966].
Theorem reference_pc_alignment_guards_true memory inputs k observed rs1 immediate pc csr :
 generated_observe memory inputs k=Some observed -> generated_legal_trace memory inputs k ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)rs1) ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->
 size pc=32%nat -> size csr=32%nat ->
 reference_redirect_aligned(N.testbit(to_N csr)2)(to_N pc+to_N immediate)=true ->
 forall node,List.In node reference_pc_alignment_nodes ->
 VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Rs1 Immediate Pc Csr PcSize CsrSize Aligned node Member.
 pose proof(reference_redirect_alignments_observed memory inputs k observed rs1 immediate pc csr Observe Legal Rs1 Immediate Pc Csr PcSize CsrSize)as Values.
 rewrite Aligned in Values.
 destruct Values as[H0[H1[H2[H3[H4[H5[H6 H7]]]]]]].
 cbn [reference_pc_alignment_nodes] in Member.
 repeat destruct Member as[Member|Member];try contradiction;subst node;assumption.
Qed.

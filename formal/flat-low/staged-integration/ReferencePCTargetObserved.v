Require Import ReferenceRedirectSpine ReferenceControlStabilityHistory ReferenceControlExpressions ReferenceControlNodeCongruence3.
From Coq Require Import ZArith Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Require Import CoreSocModel ComparisonNodes.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ReferenceRedirectSemantics ReferencePCTargetSemantics ReferencePCTargetHistory ExceptionPCPayloadNodes.
From nbits Require Import NBits.
Definition reference_pc_target_guards instruction rs1 rs2 immediate pc csr (node:VarOrder.T) :bool :=
 match node with
 | 1974 =>N.eqb(N.land instruction 28799)28771
 | 1980 =>N.eqb(N.land instruction 28799)20579
 | 1986 =>N.eqb(N.land instruction 28799)24675
 | 1992 =>N.eqb(N.land instruction 28799)16483
 | 1998 =>N.eqb(N.land instruction 28799)4195
 | 2004 =>N.eqb(N.land instruction 28799)99
 | 2010 =>N.eqb(N.land instruction 28799)103
 | 2357 =>N.eqb(N.land instruction 127)111
 | 2806 =>N.leb rs2 rs1
 | 2830 =>Z.leb(reference_redirect_signed rs2)(reference_redirect_signed rs1)
 | 2850 =>N.ltb rs1 rs2
 | 2872 =>Z.ltb(reference_redirect_signed rs1)(reference_redirect_signed rs2)
 | 2892 =>negb(N.eqb rs1 rs2)
 | 2912 =>N.eqb rs1 rs2
 | 2949 =>reference_redirect_aligned(N.testbit csr 2)(N.clearbit(rs1+immediate)0)
 | _ =>reference_redirect_aligned(N.testbit csr 2)(pc+immediate)
 end.
Definition reference_pc_target_function instruction rs1 rs2 immediate pc csr :=reference_pc_target_value(reference_pc_target_guards(to_N instruction)(to_N rs1)(to_N rs2)(to_N immediate)(to_N pc)(to_N csr))pc immediate rs1.
Require Import ReferenceRedirectSemantics.
Theorem reference_pc_target_function_history inputs path history limit reset time instruction rs1 rs2 immediate pc csr :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (225 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction) ->
 VM.find 2209 (history time) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2804 (history time) = Some (Gval (Fuint 32) rs2) ->
 VM.find 2552 (history time) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (history time) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (history time) = Some (Gval (Fuint 32) csr) ->
 size rs1 = 32%nat -> size rs2 = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 VM.find 6508(history time)=Some(Gval(Fuint 32)(reference_pc_target_function instruction rs1 rs2 immediate pc csr)).
Proof.
 intros Resets Steps Lower Upper Instruction Rs1 Rs2 Immediate Pc Csr Rs1Size Rs2Size PcSize CsrSize.
 destruct (reference_redirect_aliases_history inputs path history limit reset time pc csr Resets Steps ltac:(lia) Upper Pc Csr PcSize CsrSize) as [PcAlias CsrAlias].
 destruct (reference_redirect_decoders_history inputs path history limit reset time instruction Resets Steps ltac:(lia) Upper Instruction)
 as [H1974 [H1980 [H1986 [H1992 [H1998 [H2004 [H2010 H2357]]]]]]].
 destruct (reference_redirect_comparisons_history inputs path history limit reset time rs1 rs2 Resets Steps ltac:(lia) Upper Rs1 Rs2)
 as [H2806 [H2830 [H2850 [H2872 [H2892 H2912]]]]].
 destruct (reference_redirect_alignments_history inputs path history limit reset time csr pc immediate rs1 Resets Steps ltac:(lia) Upper CsrAlias PcAlias Immediate Rs1 CsrSize)
 as [H2825 [H2847 [H2867 [H2889 [H2909 [H2929 [H2949 H2966]]]]]]].
 rewrite (reference_redirect_signed32 rs1 Rs1Size) (reference_redirect_signed32 rs2 Rs2Size) Z.geb_leb in H2830.
 rewrite (reference_redirect_signed32 rs1 Rs1Size) (reference_redirect_signed32 rs2 Rs2Size) in H2872.
 rewrite redirect_N_eqb in H2892, H2912.
 assert(PC2812:VM.find 2812(history time)=Some(Gval(Fuint 32)pc)).
 { rewrite(reference_control_stable_2812_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 exact(exception_pc_2812_value _ (history time)(history time)(history(S time))pc PcAlias(Steps time Upper)). }
 unfold reference_pc_target_function. apply(reference_pc_target_semantics inputs path history limit reset time _ pc immediate rs1 Resets Steps Lower Upper PcSize Rs1Size PC2812 Immediate Rs1).
 intros node Member. cbn[reference_pc_target_guard_nodes List.In]in Member.
 repeat destruct Member as[<-|Member];try contradiction;cbn[reference_pc_target_guards];assumption.
Qed.
Require Import FormalObservedHistory FormalLocalHistory.
Theorem reference_pc_target_function_observed memory inputs k observed instruction rs1 rs2 immediate pc csr :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1884 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2804 (top_environment observed) = Some (Gval (Fuint 32) rs2) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (top_environment observed) = Some (Gval (Fuint 32) csr) ->
 size rs1 = 32%nat -> size rs2 = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 VM.find 6508(top_environment observed)=Some(Gval(Fuint 32)(reference_pc_target_function instruction rs1 rs2 immediate pc csr)).
Proof.
 intros Observe Legal Instruction Rs1 Rs2 Immediate Pc Csr Rs1Size Rs2Size PcSize CsrSize.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 rewrite <- Last.
 rewrite <- (reference_pc_target_6508_stable (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)).
 eapply (reference_pc_target_function_history (generated_observation_input inputs k) nil history 9259 reset 9258 instruction rs1 rs2 immediate pc csr Resets Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)); try assumption.
 - rewrite (reference_control_stable_1884_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Instruction.
 - rewrite (reference_control_stable_2209_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Rs1.
 - rewrite (reference_control_stable_2804_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Rs2.
 - rewrite (reference_control_stable_2552_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Immediate.
 - rewrite (reference_control_stable_7331_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Pc.
 - rewrite (reference_control_stable_7332_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Csr.
Qed.

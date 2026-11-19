Require Import CycleBranchAlignment ReferenceEventSelectedObserved ReferenceEventSelectedHistory ReferenceEventSpineTypes ReferenceEventConditions ReferenceMISAConcrete CycleRedirectEventAlignment CycleMemoryEventAlignment ReferenceByteAlignment ReferenceSystemDecode ReferenceIllegalObserved RFALUReferenceData ReferenceInstructionDecode RFScalarControl CycleView MemoryPendingInvariant PCRelativePendingInvariant CycleRedirectDecision JALRPendingAlignment JALRTakenInvariant ReferenceBranchOperands FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem cycle_reference_no_exception_active memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cv_late_bubble v=false ->cycle_memory_pending v ->
 cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->cycle_jalr_pending v ->cycle_jalr_taken v ->
 VM.find 6780(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset View Late Memory PC Relative Decision Jalr Taken.
 set env:=top_environment observed.
 set g:=reference_event_observed_bit env.
 assert(Enabled:VM.find 1707 env=Some(Gval(Fuint 1)[::true])).
 { exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset ltac:(rewrite(cva_late_bubble _ _ View)Late;reflexivity)). }
 destruct(reference_misa_observed_concrete memory inputs k observed Observe Legal)as[csr[CsrSize Csr]].
 assert(Actual:forall node bit,VM.find node env=Some(Gval(Fuint 1)[::bit]) ->g node=bit).
 { intros node bit Value;exact(reference_event_observed_bit_actual env node bit Value). }
 assert(Known:forall node,(exists bit,VM.find node env=Some(Gval(Fuint 1)[::bit])) ->VM.find node env=Some(Gval(Fuint 1)[::g node])).
 { intros node Value;exact(reference_event_observed_bit_lookup env node Value). }
 assert(Decode:forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)env=Some(Gval(Fuint 1)[::g(reference_instruction_guard row)])).
 { intros row Row;apply Known;eexists;exact(rf_reference_decoder_observed memory inputs k observed(cv_commit_instruction v)row Observe Legal(cva_commit_instruction _ _ View)Enabled Row). }
 assert(MemoryGuard:forall index,(index<5)%coq_nat ->VM.find(fst(cycle_memory_event_pair index))env=Some(Gval(Fuint 1)[::g(fst(cycle_memory_event_pair index))])).
 { intros[|[|[|[|[|index]]]]]Index;[exact(Decode 36%nat ltac:(lia))|exact(Decode 35%nat ltac:(lia))|exact(Decode 33%nat ltac:(lia))|exact(Decode 31%nat ltac:(lia))|exact(Decode 30%nat ltac:(lia))|lia]. }
 assert(MemoryAlign:forall index,(index<5)%coq_nat ->g(fst(cycle_memory_event_pair index))=true ->VM.find(snd(cycle_memory_event_pair index))env=Some(Gval(Fuint 1)[::true])).
 { intros index Index Active. apply(cycle_memory_event_alignment memory inputs k observed v index Observe Legal Reset View Memory Index). rewrite(MemoryGuard index Index)Active;reflexivity. }
 assert(BranchCompare:forall lane,(lane<6)%coq_nat ->g(reference_instruction_guard(Nat.add 23 lane))=true ->VM.find(branch_comparison_node lane)env=Some(Gval(Fuint 1)[::g(branch_comparison_node lane)])).
 { intros lane Lane Active;apply Known. apply(cycle_branch_event_comparison memory inputs k observed v lane Observe Legal Reset View Late Lane). rewrite(Decode(Nat.add 23 lane)ltac:(lia))Active;reflexivity. }
 assert(BranchAlign:forall lane,(lane<6)%coq_nat ->g(reference_instruction_guard(Nat.add 23 lane))=true ->g(branch_comparison_node lane)=true ->VM.find(branch_alignment_node lane)env=Some(Gval(Fuint 1)[::true])).
 { intros lane Lane Active Compare. apply(cycle_branch_event_alignment memory inputs k observed v lane csr Observe Legal Reset View Late PC Relative Decision Csr CsrSize Lane).
 - rewrite(Decode(Nat.add 23 lane)ltac:(lia))Active;reflexivity.
 - rewrite(BranchCompare lane Lane Active)Compare;reflexivity. }
 assert(JalAlign:g 2357=true ->VM.find 2966 env=Some(Gval(Fuint 1)[::true])).
 { intro Active;apply(cycle_jal_event_alignment memory inputs k observed v csr Observe Legal Reset View Late PC Relative Decision Csr CsrSize). rewrite(Decode 21%nat ltac:(lia))Active;reflexivity. }
 assert(JalrAlign:g 2010=true ->VM.find 2949 env=Some(Gval(Fuint 1)[::true])).
 { intro Active;apply(cycle_jalr_event_alignment memory inputs k observed v csr Observe Legal Reset View Late Jalr Taken Csr CsrSize). rewrite(Decode 22%nat ltac:(lia))Active;reflexivity. }
 assert(V3042:VM.find 3042 env=Some(Gval(Fuint 1)[::false]))by(exact(reference_illegal_absent_observed memory inputs k observed Observe Legal Reset)).
 assert(G3042:g 3042=false)by(exact(Actual 3042 false V3042)).
 assert(V1933:VM.find 1933 env=Some(Gval(Fuint 1)[::false]))by(exact(reference_system_absent_observed memory inputs k observed(cv_commit_instruction v)true false Observe Legal Reset(cva_commit_instruction _ _ View)Enabled)).
 assert(G1933:g 1933=false)by(exact(Actual 1933 false V1933)).
 assert(V1937:VM.find 1937 env=Some(Gval(Fuint 1)[::false]))by(exact(reference_system_absent_observed memory inputs k observed(cv_commit_instruction v)true true Observe Legal Reset(cva_commit_instruction _ _ View)Enabled)).
 assert(G1937:g 1937=false)by(exact(Actual 1937 false V1937)).
 assert(V2736:VM.find 2736 env=Some(Gval(Fuint 1)[::false]))by(exact(reference_byte_invalid_observed memory inputs k observed true Observe Legal)).
 assert(G2736:g 2736=false)by(exact(Actual 2736 false V2736)).
 assert(V2634:VM.find 2634 env=Some(Gval(Fuint 1)[::false]))by(exact(reference_byte_invalid_observed memory inputs k observed false Observe Legal)).
 assert(G2634:g 2634=false)by(exact(Actual 2634 false V2634)).
 assert(V2679:VM.find 2679 env=Some(Gval(Fuint 1)[::true]))by(exact(reference_lb_aligned_observed memory inputs k observed Observe Legal)).
 assert(G2679:g 2679=true)by(exact(Actual 2679 true V2679)).
 assert(Safe:reference_event_safe g).
 { unfold reference_event_safe. split;[exact G3042|]. split;[exact G1933|]. split;[exact G1937|].
 split;[intro Active;exact(Actual _ _ (MemoryAlign 0%nat ltac:(lia)Active))|].
 split;[intro Active;exact(Actual _ _ (MemoryAlign 1%nat ltac:(lia)Active))|].
 split;[intro Active;exact G2736|].
 split;[intro Active;exact(Actual _ _ (MemoryAlign 2%nat ltac:(lia)Active))|].
 split;[intro Active;exact G2634|].
 split;[intro Active;exact(Actual _ _ (MemoryAlign 3%nat ltac:(lia)Active))|].
 split;[intro Active;exact(Actual _ _ (MemoryAlign 4%nat ltac:(lia)Active))|].
 split;[intro Active;exact G2679|].
 split;[intros Active Compare;exact(Actual _ _ (BranchAlign 5%nat ltac:(lia)Active Compare))|].
 split;[intros Active Compare;exact(Actual _ _ (BranchAlign 4%nat ltac:(lia)Active Compare))|].
 split;[intros Active Compare;exact(Actual _ _ (BranchAlign 3%nat ltac:(lia)Active Compare))|].
 split;[intros Active Compare;exact(Actual _ _ (BranchAlign 2%nat ltac:(lia)Active Compare))|].
 split;[intros Active Compare;exact(Actual _ _ (BranchAlign 1%nat ltac:(lia)Active Compare))|].
 split;[intros Active Compare;exact(Actual _ _ (BranchAlign 0%nat ltac:(lia)Active Compare))|].
 split;[intro Active;exact(Actual _ _ (JalrAlign Active))|intro Active;exact(Actual _ _ (JalAlign Active))]. }
 apply(reference_event_selected_zero_observed memory inputs k observed g Observe Legal Safe).
 intros i Bound Needed. change(VM.find(reference_event_selected_guard i)env=Some(Gval(Fuint 1)[::g(reference_event_selected_guard i)])).
 destruct i as[|i]. { apply Known;exists true;apply JalAlign;exact Needed. }
 destruct i as[|i]. { exact(Decode 21%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists true;apply JalrAlign;exact Needed. }
 destruct i as[|i]. { exact(Decode 22%nat ltac:(lia)). }
 destruct i as[|i]. { destruct Needed as[Active Compare];apply Known;exists true;exact(BranchAlign 0%nat ltac:(lia)Active Compare). }
 destruct i as[|i]. { exact(BranchCompare 0%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 23%nat ltac:(lia)). }
 destruct i as[|i]. { destruct Needed as[Active Compare];apply Known;exists true;exact(BranchAlign 1%nat ltac:(lia)Active Compare). }
 destruct i as[|i]. { exact(BranchCompare 1%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 24%nat ltac:(lia)). }
 destruct i as[|i]. { destruct Needed as[Active Compare];apply Known;exists true;exact(BranchAlign 2%nat ltac:(lia)Active Compare). }
 destruct i as[|i]. { exact(BranchCompare 2%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 25%nat ltac:(lia)). }
 destruct i as[|i]. { destruct Needed as[Active Compare];apply Known;exists true;exact(BranchAlign 3%nat ltac:(lia)Active Compare). }
 destruct i as[|i]. { exact(BranchCompare 3%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 26%nat ltac:(lia)). }
 destruct i as[|i]. { destruct Needed as[Active Compare];apply Known;exists true;exact(BranchAlign 4%nat ltac:(lia)Active Compare). }
 destruct i as[|i]. { exact(BranchCompare 4%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 27%nat ltac:(lia)). }
 destruct i as[|i]. { destruct Needed as[Active Compare];apply Known;exists true;exact(BranchAlign 5%nat ltac:(lia)Active Compare). }
 destruct i as[|i]. { exact(BranchCompare 5%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 28%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists true;exact V2679. }
 destruct i as[|i]. { exact(Decode 29%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists true;exact(MemoryAlign 4%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 30%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists true;exact(MemoryAlign 3%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 31%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists false;exact V2634. }
 destruct i as[|i]. { exact(Decode 32%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists true;exact(MemoryAlign 2%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 33%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists false;exact V2736. }
 destruct i as[|i]. { exact(Decode 34%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists true;exact(MemoryAlign 1%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 35%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists true;exact(MemoryAlign 0%nat ltac:(lia)Needed). }
 destruct i as[|i]. { exact(Decode 36%nat ltac:(lia)). }
 destruct i as[|i]. { apply Known;exists false;exact V1937. }
 destruct i as[|i]. { contradiction Needed. }
 destruct i as[|i]. { contradiction Needed. }
 destruct i as[|i]. { contradiction Needed. }
 destruct i as[|i]. { apply Known;exists false;exact V1933. }
 destruct i as[|i]. { apply Known;exists false;exact V3042. }
 destruct i as[|i]. { apply Known;exists true;exact Enabled. }
 lia.
Qed.
Require Import ReferenceEventDisabledZero ReferenceEventObserved.
Theorem cycle_reference_no_exception memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->cycle_jalr_pending v ->cycle_jalr_taken v ->
 VM.find 6780(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset View Memory PC Relative Decision Jalr Taken.
 destruct(cv_late_bubble v)eqn:Late.
 - apply(reference_event_disabled_zero_observed memory inputs k observed Observe Legal).
   exact(reference_enable_observed_bubble memory inputs k observed true Observe Legal Reset ltac:(rewrite(cva_late_bubble _ _ View)Late;reflexivity)).
 - exact(cycle_reference_no_exception_active memory inputs k observed v Observe Legal Reset View Late Memory PC Relative Decision Jalr Taken).
Qed.
Theorem cycle_reference_no_exception_output memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->cycle_jalr_pending v ->cycle_jalr_taken v ->
 VM.find 1667(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset View Memory PC Relative Decision Jalr Taken.
 apply(reference_event_zero_observed memory inputs k observed(negb(cv_late_bubble v))Observe Legal).
 - exact(cycle_reference_no_exception memory inputs k observed v Observe Legal Reset View Memory PC Relative Decision Jalr Taken).
 - exact(reference_enable_observed_bubble memory inputs k observed(cv_late_bubble v)Observe Legal Reset(cva_late_bubble _ _ View)).
Qed.

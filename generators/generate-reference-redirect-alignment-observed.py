#!/usr/bin/env python3
"""Expose the eight proven redirect alignment guards at observation boundaries."""
from pathlib import Path
root = Path(__file__).resolve().parents[2]
nodes = [2825,2847,2867,2889,2909,2929,2949,2966]
lines = ["Require Import ReferenceRedirectSemantics ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes.",
"From Coq Require Import NArith List Lia.",
"From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.",
"From nbits Require Import NBits.",
"From simplssrlib Require Import Var.",
"From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.",
"Local Open Scope N_scope.",
"Local Opaque flat_statements flat_memories generated_modules generated_top.",
"Theorem reference_redirect_alignments_observed memory inputs k observed rs1 immediate pc csr :",
" generated_observe memory inputs k=Some observed -> generated_legal_trace memory inputs k ->"]
for node, word in [(2209,'rs1'),(2552,'immediate'),(7331,'pc'),(7332,'csr')]:
 lines.append(f" VM.find {node} (top_environment observed)=Some(Gval(Fuint 32){word}) ->")
lines.append(" size pc=32%nat -> size csr=32%nat ->")
for i,node in enumerate(nodes):
 target = '(N.clearbit(to_N rs1+to_N immediate)0)' if node==2949 else '(to_N pc+to_N immediate)'
 lines.append(f" VM.find {node} (top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned (N.testbit(to_N csr)2) {target}])" + (" /\\" if i<7 else "."))
lines += ["Proof."," intros Observe Legal Rs1 Immediate Pc Csr PcSize CsrSize.",
" destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]]."]
ctx='(generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)'
for node,word,hyp in [(2209,'rs1','Rs1'),(2552,'immediate','Immediate'),(7331,'pc','Pc'),(7332,'csr','Csr')]:
 lines += [f" assert(H{node}:VM.find {node}(history 9258)=Some(Gval(Fuint 32){word})).",f" {{ rewrite(reference_control_stable_{node}_history {ctx}) Last. exact {hyp}. }}"]
prefix='(generated_observation_input inputs k) nil history 9259 reset 9258'
lines += [f" destruct(reference_redirect_aliases_history {prefix} pc csr Resets Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia) H7331 H7332 PcSize CsrSize)as[PcAlias CsrAlias].",f" pose proof(reference_redirect_alignments_history {prefix} csr pc immediate rs1 Resets Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia) CsrAlias PcAlias H2552 H2209 CsrSize)as Alignment."]
for node in nodes:
 lines.append(f" rewrite(reference_control_stable_{node}_history {ctx}) in Alignment.")
lines += [' rewrite Last in Alignment. exact Alignment.','Qed.']
lines += [
"Definition reference_pc_alignment_nodes := [::2825;2847;2867;2889;2909;2929;2966].",
"Theorem reference_pc_alignment_guards_true memory inputs k observed rs1 immediate pc csr :",
" generated_observe memory inputs k=Some observed -> generated_legal_trace memory inputs k ->",
" VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)rs1) ->",
" VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)immediate) ->",
" VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->",
" VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->",
" size pc=32%nat -> size csr=32%nat ->",
" reference_redirect_aligned(N.testbit(to_N csr)2)(to_N pc+to_N immediate)=true ->",
" forall node,List.In node reference_pc_alignment_nodes ->",
" VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::true]).",
"Proof.",
" intros Observe Legal Rs1 Immediate Pc Csr PcSize CsrSize Aligned node Member.",
" pose proof(reference_redirect_alignments_observed memory inputs k observed rs1 immediate pc csr Observe Legal Rs1 Immediate Pc Csr PcSize CsrSize)as Values.",
" rewrite Aligned in Values.",
" destruct Values as[H0[H1[H2[H3[H4[H5[H6 H7]]]]]]].",
" cbn [reference_pc_alignment_nodes] in Member.",
" repeat destruct Member as[Member|Member];try contradiction;subst node;assumption.",
"Qed."]
(root/'formal/flat-low/staged-integration/ReferenceRedirectAlignmentObserved.v').write_text('\n'.join(lines)+'\n')

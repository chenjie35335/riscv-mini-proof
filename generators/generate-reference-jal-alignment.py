#!/usr/bin/env python3
"""Select the actual JAL alignment cone from the shared redirect node proof."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').read_text()
body=s[s.index('Theorem reference_redirect_alignments_history'):s.index('Require Import ReferenceControlWires2')]
head=s[:s.index('(* Six-input')]
parts=[head,'Require Import ReferenceRedirectSemantics FormalObservedHistory FormalLocalHistory ReferenceControlNodeCertificates2 ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence2.\nFrom nbits Require Import NBits.\n', '''Theorem reference_jal_alignment_history inputs path history limit reset time csr pc immediate :
 (forall i,(i<=limit)%coq_nat ->VM.find 1(history i)=Some(Gval(Fuint 1)[::reset])) ->
 (forall i,(i<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history i)false(history i)flat_statements=Some(history(S i))) ->
 (127<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1750(history time)=Some(Gval(Fuint 32)csr) ->
 VM.find 1749(history time)=Some(Gval(Fuint 32)pc) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)immediate) ->size csr=32%nat ->
 VM.find 2966(history time)=Some(Gval(Fuint 1)[::reference_redirect_aligned(N.testbit(to_N csr)2)(to_N pc+to_N immediate)]).
Proof.
 intros Resets Steps Lower Upper Csr Pc Immediate Size.
 pose proof(Steps time Upper)as Step.
''']
needed={2807,2812,*range(2950,2967)}
lines=body.splitlines()
for i,line in enumerate(lines):
 m=re.search(r' as \[site(\d+) E\d+\]',line)
 if m and int(m.group(1)) in needed:
  parts.extend([line+'\n',lines[i+1]+'\n'])
end=body[body.index(' - rewrite E2966.'):body.index('\nQed.',body.index(' - rewrite E2966.'))]
end=end.replace(' - rewrite E2966.',' rewrite E2966.').replace(' ?Rs1','')
parts.append(end+'\nQed.\n')
parts.append('''Theorem reference_jal_alignment_observed memory inputs k observed pc immediate csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size pc=32%nat ->size csr=32%nat ->
 VM.find 2966(top_environment observed)=Some(Gval(Fuint 1)[::reference_redirect_aligned(N.testbit(to_N csr)2)(to_N pc+to_N immediate)]).
Proof.
 intros Observe Legal Pc Immediate Csr PcSize CsrSize.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
''')
ctx='(generated_observation_input inputs k)nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)'
for n,word,hyp in [(7331,'pc','Pc'),(2552,'immediate','Immediate'),(7332,'csr','Csr')]:
 parts.append(f' assert(H{n}:VM.find {n}(history 9258%nat)=Some(Gval(Fuint 32){word})).\n {{ rewrite(reference_control_stable_{n}_history {ctx})Last;exact {hyp}. }}\n')
prefix='(generated_observation_input inputs k)nil history 9259 reset 9258'
parts.append(f''' destruct(reference_redirect_aliases_history {prefix} pc csr Resets Steps ltac:(vm_compute;lia)ltac:(vm_compute;lia)H7331 H7332 PcSize CsrSize)as[PcAlias CsrAlias].
 pose proof(reference_jal_alignment_history {prefix} csr pc immediate Resets Steps ltac:(vm_compute;lia)ltac:(vm_compute;lia)CsrAlias PcAlias H2552 CsrSize)as Value.
 rewrite(reference_control_stable_2966_history {ctx})Last in Value;exact Value.
Qed.
''')
assert sum(' as [site' in part for part in parts)==19
(root/'formal/flat-low/staged-integration/ReferenceJALAlignment.v').write_text(''.join(parts))

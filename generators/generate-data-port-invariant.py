"""Build the joint reader/writer port type invariant, without concrete source premises."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]; p=root/'formal/flat-low/staged-integration'
readers=[2,3,4,5,1]
fields=[f'{f}{n}' for n in readers for f in 'aecmd']
writer=['wa','we','wc','wm','wd']
row=lambda n:f'(data_port_fields a{n} e{n} c{n} m{n} d{n})'
types=[(f'a{n}','(Fuint 16)') for n in []]
types=[(f'{f}{n}',t) for n in readers for f,t in [('a','(Fuint 16)'),('e','(Fuint 1)'),('c','Fclock')]]+[('d1','(Fuint 32)'),('wa','(Fuint 16)'),('we','(Fuint 1)'),('wc','Fclock'),('wm','(Fuint 1)')]
names=['Value']+[f'T_{v}' for v,t in types]
chain=lambda xs:'['+' ['.join(xs[:-1])+' '+xs[-1]+']'*(len(xs)-1)
out='''Require Import FormalDataWriterTypedIteration FormalDataPortPreparation DataReaderEnableConnections FormalLocalHistory StagedFlatCircuitIteration CoreSocModel.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition data_ports_typed env := exists '+' '.join(writer+fields)+',\n VM.find 9178 env = Some (data_ports '+' '.join(row(n) for n in readers)+' (data_port_fields wa we wc wm wd)) /\\\n'
out+=' /\\\n'.join(f' type_of_val {v} = Gtyp {t}' for v,t in types)+'.\n'
out+='''Lemma data_ports_initial_typed env :
 VM.find 9178 env = Some (memory_bundle_initial data_port_memory) -> data_ports_typed env.
Proof.
 intro Value. unfold data_ports_typed.
'''
for _ in range(6):out+=' exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).\n'
out+=' split; [exact Value|]. repeat split; reflexivity.\nQed.\n'
out+='''Lemma data_ports_typed_step invalid old current result phase :
 data_ports_typed old ->
 formal_value_iter invalid ComparisonNodes.flat_memories old phase current ComparisonNodes.flat_statements = Some result ->
 data_ports_typed result.
Proof.
 intros Typed Step. unfold data_ports_typed in Typed.
'''
# existential and conjunction destruct patterns have the same nested pair structure
out+=' destruct Typed as '+chain(writer+fields+names)+'.\n'
out+=' destruct (data_writer_iteration_typed invalid phase old current result '+' '.join(writer+fields+names)+' Step)\n'
outputs=[x for n in readers for x in [f'na{n}',f'nc{n}']]+['address0','enable0','clock0','mask0','data0']
checks=['Address0','Enable0','Mask0','Clock0']+[f'NA{n}' for n in readers]+[f'NC{n}' for n in readers]+['Final']
out+=' as '+chain(outputs+checks)+'.\n unfold data_ports_typed.\n exists address0, enable0, clock0, mask0, data0.\n'
for n in readers:out+=f' exists na{n}, (Gval (Fuint 1) [::true]), nc{n}, m{n}, d{n}.\n'
out+=' split; [exact Final|]. repeat split; try assumption; reflexivity.\nQed.\n'
out+='''Local Opaque generated_modules generated_top.
Lemma circuit_data_ports_typed_step invalid before after phase :
 data_ports_typed (top_environment before) ->
 formal_circuit_value_iter invalid generated_modules generated_top before phase = Some after ->
 data_ports_typed (top_environment after).
Proof.
 intros Typed Step.
 destruct (flat_iteration_projection invalid before phase after Step) as [old [next [Old [Local Next]]]].
 unfold top_environment in *. rewrite Old in Typed. rewrite Next.
 exact (data_ports_typed_step (invalid nil) old old next phase Typed Local).
Qed.
Lemma circuit_data_ports_typed_iterations inputs n initial result :
 data_ports_typed (top_environment initial) ->
 circuit_formal_iterations generated_modules generated_top inputs n initial = Some result ->
 data_ports_typed (top_environment result).
Proof.
 revert initial result. induction n as [|n IH]; intros initial result Typed Steps.
 - cbn [circuit_formal_iterations] in Steps. inversion Steps; subst; exact Typed.
 - cbn [circuit_formal_iterations] in Steps.
   destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top initial false)
   as [next|] eqn:Next; [|discriminate Steps].
   exact (IH next result (circuit_data_ports_typed_step _ initial next false Typed Next) Steps).
Qed.
Print Assumptions circuit_data_ports_typed_iterations.
'''
f=p/'FormalDataPortsInvariant.v'
if not f.exists() or f.read_text()!=out:f.write_text(out)

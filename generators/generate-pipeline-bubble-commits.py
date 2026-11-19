"""Actual formal commit observations for pipeline bubble registers7945/7947."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
model=(root/'formal/flat-low/CoreSocModel.v').read_text()
template=(base/'FormalRF852CommitSource.v').read_text()
header=template[:template.index('Definition rf_852_reg')]
out=header
for node in [7945,7947]:
 def position(pattern):
  m=re.search(pattern,model);assert m
  return len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1
 start=position(r'\(@Sreg VarOrder.T '+str(node)+' ')
 end=position(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(node)+r'\) ')
 text=template[template.index('Definition rf_852_reg'):]
 text=text.replace('Definition rf_852_yes := @Eref VarOrder.T (@Eid VarOrder.T 1086).','Definition rf_852_yes := @Econst VarOrder.T (Fuint 1) [::true].')
 text=text.replace('rf_852',f'pipeline_bubble_{node}')
 mapping={852:node,778:64,779:65,1022:node-1,32:1,861:start,862:start+1,331:end-start-1,1194:end+1}
 text=re.sub(r'\b\d+\b',lambda m:str(mapping.get(int(m[0]),int(m[0]))),text)
 out+=text+'\n'
p=base/'PipelineBubbleCommitSources.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
init_template=(base/'FormalPrivilegeInitialization.v').read_text()
init_header=init_template[:init_template.index('Lemma privilege150_present')]
initialization=init_header
reset='''Require Import CoreSocModel ComparisonNodes PipelineBubbleCommitSources SelectedBitConstantMux.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for node in [7945,7947]:
 text=init_template[init_template.index('Lemma privilege150_present'):].replace('privilege150',f'bubble{node}')
 text=re.sub(r'\b(?:150|2)\b',lambda m:str(node) if m[0]=='150' else '1',text)
 initialization+=text+'\n'
 reset+=f'''Theorem pipeline_bubble_{node}_reset_commit invalid old current result old_value :
 VM.find {node} old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find {node} result = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Old Typed Reset Step.
 destruct (pipeline_bubble_{node}_formal_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 unfold pipeline_bubble_{node}_cond, pipeline_bubble_{node}_yes, pipeline_bubble_{node}_no in Source.
 pose proof (selected_bit_constant_mux_identity flat_memories old 65 {node-1} true source value Reset Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Print Assumptions pipeline_bubble_{node}_reset_commit.
'''
for name,text in [('PipelineBubbleInitialization',initialization),('PipelineBubbleResetCommit',reset)]:
 p=base/(name+'.v')
 if not p.exists() or p.read_text()!=text:p.write_text(text)

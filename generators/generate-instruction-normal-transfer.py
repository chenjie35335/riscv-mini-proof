from pathlib import Path
import re
p=Path('formal/flat-low/staged-integration');src=(p/'FrontInstructionNopNodes.v').read_text();s=src[:src.index('Lemma front_instruction_member')];part=src[src.index('Lemma front_instruction_member_7797'):src.index('Lemma front_instruction_member_7801')];ids=list(map(int,re.findall(r'\((\d+),joint_update_expr_', (p/'JointUpdateNodePositions.v').read_text())))
s=s.replace('FormalInstructionResetConstants.','FormalInstructionResetConstants FormalInstructionWordsNormalCommit CommitPCAdvance CommitPCSelection JointBoundaryRegisters RegisterInvariants.')
for n in [7861,7878]:s+=part.replace('front_instruction','instruction_transfer').replace('7797',str(n)).replace('900%nat',str(ids.index(n))+'%nat')
s+='''Lemma instruction_transfer_register : has_register 7750 flat_statements = true.
Proof. exact (proj2 (joint_boundary_register_properties 7750 32 ltac:(apply (List.nth_error_In joint_boundary_registers 55%nat); vm_compute;reflexivity))). Qed.
'''
for filename in ['CommitPCSelection','CommitPCControlledPropagation','CommitPCNormalAdvance','CommitPCNormalFullHistory']:
 t=(p/(filename+'.v')).read_text()
 t=re.sub(r'Print Assumptions [^.]+\.','',t)
 # Remove imports of existing PC composition modules, preserving shared helpers.
 for mod in ['CommitPCSelectionNodes','CommitPCSelection','CommitPCControlledPropagation','CommitPCNormalAdvance']:
  t=re.sub(r'\b'+mod+r'\b','',t)
 t=t.replace('Require Import .','')
 t=re.sub(r'\b(7749|7751|7860|7877)\b',lambda m:{'7749':'7748','7751':'7750','7860':'7861','7877':'7878'}[m[0]],t)
 t=t.replace('exception_pc_implementation_register','instruction_transfer_register')
 t=re.sub(r'\b54%nat', '53%nat', t)
 # Reuse purely bitvector definitions, do not redefine them.
 if filename=='CommitPCSelection':
  a=t.index('Definition commit_pc_next');b=t.index('Theorem commit_pc_after_two');t=t[:a]+t[b:]
 t=t.replace('commit_pc_source_node_7860', 'instruction_transfer_node_7861').replace('commit_pc_source_node_7877','instruction_transfer_node_7878')
 t=t.replace('commit_pc_formal_normal_commit','instruction_7750_formal_normal_commit')
 for name in ['commit_pc_after_two','commit_pc_controlled_after_four','commit_pc_normal_advance','commit_pc_normal_full_history']:
  t=t.replace(name,name.replace('commit_pc','instruction_transfer'))
 t=t.replace('.commit_pc_next','CommitPCSelection.commit_pc_next') if '(.commit_pc_next' in t else t
 s+='\n'+t
(p/'InstructionNormalTransfer.v').write_text(s)

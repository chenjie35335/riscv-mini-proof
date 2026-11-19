"""Derive the shared selected-data fold/commit interfaces from audited schema."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';out=p/'ReferenceSelectedWriteEffect.v'
s=out.read_text().split('(* Selected-data fold and commit. *)')[0]
def theorem(file,name):
 t=(p/file).read_text();a=t.index('Theorem '+name+' ');b=t.index('\nQed.',a)+len('\nQed.');return t[a:b]
condition='(guards stage && rf_reference_permission_value stage(permissions stage)=true) ->'
for file,name,new in [('RFReferenceWriteEffect.v','rf_reference_effect_history','reference_selected_effect_history'),('RFArchitecturalWriteEffect.v','rf_reference_nonzero_effect_commit','reference_selected_nonzero_commit')]:
 t=theorem(file,name).replace(name,new).replace('(forall stage t,(stage<36)%coq_nat ->(start<=t)',f'(forall stage t,(stage<36)%coq_nat ->{condition}(start<=t)')
 t=t.replace('rf_reference_write_stage_three_steps','reference_selected_stage').replace('rf_reference_effect_history','reference_selected_effect_history')
 if new=='reference_selected_effect_history':t=t.replace('+ apply Data;lia.','+ intro Selected;apply Data;try assumption;lia.')
 s+='\n(* Selected-data fold and commit. *)\n'if new=='reference_selected_effect_history'else'\n'
 s+='Require Import RFArchitecturalWriteEffect RFReferenceNopIngress RFWriteEffect.\n'+t+'\n'
out.write_text(s)

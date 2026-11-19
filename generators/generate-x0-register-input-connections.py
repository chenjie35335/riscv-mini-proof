"""Generate missing direct register-to-wire transfers in the x0 dependency cone."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[2]
s = (root / 'formal/flat-low/CoreSocModel.v').read_text()
template = (root / 'formal/flat-low/staged-integration/FormalRFInputConnections.v').read_text()
header, rest = template.split('Definition rf_input_decl_784', 1)
body = 'Definition rf_input_decl_784' + rest.split('Definition rf_input_decl_785', 1)[0]
out = header
for node, source in [(123,7750),(118,7758),(122,7752),(127,7760),(124,7759),(126,7755),(125,7754)]:
    decl = re.search(r'\(@Swire VarOrder.T '+str(node)+r' \(Gtyp \(Fuint (\d+)\)\)\)', s)
    conn = re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(node)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(source)+r'\)\)\)', s)
    if not decl or not conn: raise ValueError(node)
    a = len(re.findall(r'\(@Qcons VarOrder.T ',s[:decl.start()]))-1
    b = len(re.findall(r'\(@Qcons VarOrder.T ',s[:conn.start()]))-1
    width = int(decl[1])
    replacements = {793:a,794:a+1,8802:b+1,8007:b-a-1,784:node,7941:source}
    part = re.sub(r'\b(?:793|794|8802|8007|784|7941)\b',lambda m:str(replacements[int(m[0])]),body)
    part = part.replace('_784',f'_{node}').replace('rf_input_', 'x0_register_input_')
    part = part.replace('(Fuint 1)',f'(Fuint {width})').replace(f'{node} {source} 1 source_value',f'{node} {source} {width} source_value')
    out += part
    out += f'''Theorem x0_register_input_concrete_{node} invalid old current result width bits :
 VM.find {source} old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find {node} result = Some (Gval (Fuint {width}) word).
Proof.
 intros Source Step. eexists.
 eapply x0_register_input_connection_{node}; [exact Source|reflexivity|exact Step].
Qed.
'''
out += 'Print Assumptions x0_register_input_concrete_125.\n'
generated_path = root / 'formal/flat-low/staged-integration/X0RegisterInputConnections.v'
generated_text = out
if not generated_path.exists() or generated_path.read_text() != generated_text:
    generated_path.write_text(generated_text)
print('Generated seven register-input connection certificates.')

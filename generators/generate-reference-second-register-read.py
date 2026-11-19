"""Instantiate the existing read-port proof schema for actual reference rs2."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
s=(base/'ReferenceRegisterRead.v').read_text()
s=s.replace('Require Import ScalarNodeFrames','Require Import ReferenceControlNodeCertificates2 ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence2 ReferenceControlNodeCongruence3 ScalarNodeFrames')
s=s.replace('reference_bank_read_', 'reference_second_bank_read_').replace('reference_register_read_history','reference_second_register_read_history')
# Only real node IDs and their certificate names; source bank aliases stay identical.
s=re.sub(r'(?<![0-9])(?:2145|21[789][0-9]|220[0-9])(?![0-9])',lambda m:str(2622 if int(m[0])==2145 else int(m[0])+595) if int(m[0])==2145 or 2178<=int(m[0])<=2209 else m[0],s)
s=s.replace('reference_control_0_','reference_control_2_').replace('reference_control_1_','reference_control_2_').replace('Nat.ltb index 5','Nat.ltb index 10')
# Stored proof template is checked again against the frozen actual-node certificates.
p=base/'ReferenceSecondRegisterRead.v';mark='(* Second read observed bridge. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(s+mark+tail)

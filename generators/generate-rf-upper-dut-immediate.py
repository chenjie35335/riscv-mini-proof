from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];b=root/'formal/flat-low/staged-integration'
s=(b/'DUTImmediateModes.v').read_text()
a=s.index('Definition dut_s_immediate');z=s.index('Theorem dut_imm_selected_history',a)
s=s[:a]+'''Definition dut_imm_result (mode:nat) instruction :=rf_upper_immediate instruction.
Lemma dut_imm_result_size mode instruction :(mode<1)%coq_nat ->size instruction=32%nat ->size(dut_imm_result mode instruction)=32%nat.
Proof. intros Mode Size. exact(rf_upper_immediate_size instruction Size). Qed.
Lemma dut_imm_final_value mode instruction :(mode<1)%coq_nat ->size instruction=32%nat ->
 dut_imm_value mode 1354 instruction=Gval(Fuint 32)(dut_imm_result mode instruction).
Proof.
 intros Mode Size. destruct mode as[|mode];[|lia].
 change(Gval(Fuint 32)(dut_imm_mode_word_1354 0 instruction)=Gval(Fuint 32)(rf_upper_immediate instruction)).
 unfold dut_imm_mode_word_1354,dut_imm_mode_word_1353,dut_imm_mode_word_1352,dut_imm_mode_word_1351,dut_imm_mode_word_1350,dut_imm_mode_word_1349,dut_imm_mode_word_1348.
 cbn[nth hd]. change(load_imm_word_1326 instruction)with(rf_upper_immediate instruction).
 rewrite !(load_imm_resize_id _ 32 (rf_upper_immediate_size instruction Size)). reflexivity.
Qed.
'''+s[z:]
s='Require Import RFUpperSemantics.\n'+s
s=s.replace('dut_imm','rf_upper_dut_imm').replace('(mode<4)','(mode<1)').replace('[::1;2;5;4]','[::3]')
for node in [1342,1344,1346,1348,1350,1352]:
 pattern=rf'(Definition rf_upper_dut_imm_mode_word_{node} .*? := ).*?(\n)'
 value='true' if node==1348 else 'false'
 s=re.sub(pattern,rf'\1[::{value}].\2',s)
(b/'RFUpperDUTImmediate.v').write_text(s)

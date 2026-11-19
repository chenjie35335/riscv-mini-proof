"""Index the 36 actual RF write-data sources and destination in the shared DAG."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2]
proof=root/'formal/flat-low/staged-integration'
s=(proof/'ReferenceBankCycleStability.v').read_text().split('Definition ref_bank_cycle_offsets')[0]
ids=list(map(int,re.findall(r'\((\d+),\(@E',s)))
plan=json.loads((root/'formal/flat-low/reference-bank-cycle-stability-plan.json').read_text())
indices=[ids.index(t)for t in plan['targets']]
out='''Require Import ReferenceBankCycleHistory ReferenceBankCycleCuts RFReferenceWriteEffect ReferenceBankCycleStability CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition ref_bank_target_indices := [::'+';'.join(str(i)+'%nat'for i in indices)+'].\n'
out+=r'''Definition ref_bank_target_index stage :=nth 0%nat ref_bank_target_indices stage.
Definition ref_bank_target_node stage :=if Nat.eqb stage 36 then 3221 else rf_reference_write_data stage.
Lemma ref_bank_target_certificate stage :(stage<37)%coq_nat ->
 (ref_bank_target_index stage<438)%coq_nat /\ref_bank_cycle_node(ref_bank_target_index stage)=ref_bank_target_node stage /\(ref_bank_cycle_rank(ref_bank_target_index stage)<=44)%coq_nat.
Proof. intro Bound. do 37(destruct stage as[|stage];[vm_compute;repeat split;try reflexivity;lia|]);lia. Qed.
'''
p=proof/'ReferenceBankCycleTargets.v'
mark='(* Shared target facts. *)'
tail=p.read_text().split(mark,1)[1]if p.exists()and mark in p.read_text()else'\n'
p.write_text(out+mark+tail)

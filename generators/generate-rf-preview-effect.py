"""One parametric RF preview proof and one batch of actual-node certificates."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text()
positions=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
ids=[988]+list(range(989,1021))+list(range(1053,1085))
ps=[bisect.bisect_left(positions,s.index(f'(@Snode VarOrder.T {n} '))-1 for n in ids]
offsets=[ps[0]]+[b-a-1 for a,b in zip(ps,ps[1:])]
header='''Require Import ConcreteDecodeOperations CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate FormalTypedNodeEquation ExactWordMux.
From Coq Require Import ZArith Arith Lia List NArith.Nnat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_preview_index_width (index : nat) := S (Nat.log2 index).
Definition rf_preview_old_expr (index : nat) : hfexpr VarOrder.T :=
 if index is O then @Econst VarOrder.T (Fuint 1) [::false] else @Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (851+index)%nat)).
Definition rf_preview_select_expr (index : nat) : hfexpr VarOrder.T :=
 @Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq)
  (@Econst VarOrder.T (Fuint (rf_preview_index_width index)) (from_N (rf_preview_index_width index) (N.of_nat index)))
  (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 988)) (rf_preview_old_expr index).
Definition rf_preview_output_expr (index : nat) : hfexpr VarOrder.T :=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (989+index)%nat))) (rf_preview_old_expr index).
Definition rf_preview_effect_nodes : seq (VarOrder.T * hfexpr VarOrder.T) :=
 (988,@Eref VarOrder.T(@Eid VarOrder.T 786)) ::
 map (fun i => (N.of_nat (989+i)%nat,rf_preview_select_expr i)) (iota 0 32) ++
 map (fun i => (N.of_nat (1053+i)%nat,rf_preview_output_expr i)) (iota 0 32).
'''
header+='Definition rf_preview_effect_offsets : seq nat := [::'+';'.join(str(n)+'%nat' for n in offsets)+'].\n'
header+='''Lemma rf_preview_effect_positions : select_node_offsets rf_preview_effect_offsets flat_statements = Some rf_preview_effect_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_preview_effect_safety : selected_node_safety flat_memories flat_statements rf_preview_effect_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque generated_modules generated_top flat_statements flat_memories.
'''
p=base/'staged-integration/RFPreviewEffect.v'
# Only replace the certificate prefix, preserving any hand-written generic proof.
marker='(* Generic effect proof. *)'
rest=p.read_text().split(marker,1)[1] if p.exists() and marker in p.read_text() else '\n'
text=header+marker+rest
if not p.exists() or p.read_text()!=text:p.write_text(text)
print('one schema; checked actual nodes:',len(ids))

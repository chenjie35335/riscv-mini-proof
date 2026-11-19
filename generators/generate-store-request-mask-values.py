from pathlib import Path
base=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration'
s='''Require Import StoreRequestMaskNodes StoreTypeCorrespondence CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_request_half b0 b1 :=zext_to 5(zeros(to_nat[::b0;b1])++[::true;true]).
Definition store_request_byte b0 b1 :=zext_to 4(zeros(to_nat[::b0;b1])++[::true]).
Definition store_request_wordmask lane :=if Nat.eqb lane 0 then [::true;true;true;true]else [::false;false;false;false].
Definition store_request_half_select lane b0 b1 :=if Nat.eqb lane 1 then store_request_half b0 b1 else zext_to 5(store_request_wordmask lane).
Definition store_request_mask5 lane b0 b1 :=if Nat.eqb lane 2 then zext_to 5(store_request_byte b0 b1)else store_request_half_select lane b0 b1.
Definition store_request_mask4 lane b0 b1 :=take 4(store_request_mask5 lane b0 b1).
'''
rows=[
(7838,'lane previous',[(7765,1,'[::false]'),(7754,2,'previous'),(91,2,'(from_N 2(store_type_lane_kind lane))')],2,'(from_N 2(store_type_lane_kind lane))',''),
(7839,'b0 b1 tail',[(1155,32,'(b0::b1::tail)')],2,'[::b0;b1]',''),
(7840,'b0 b1',[(7839,2,'[::b0;b1]')],5,'(store_request_half b0 b1)','destruct b0,b1;'),
(7841,'b0 b1 tail',[(1155,32,'(b0::b1::tail)')],2,'[::b0;b1]',''),
(7842,'b0 b1',[(7841,2,'[::b0;b1]')],4,'(store_request_byte b0 b1)','destruct b0,b1;'),
(7843,'lane',[(7838,2,'(from_N 2(store_type_lane_kind lane))')],1,'[::Nat.eqb lane 0]',''),
(7844,'lane',[(7843,1,'[::Nat.eqb lane 0]')],4,'(store_request_wordmask lane)',''),
(7845,'lane',[(7838,2,'(from_N 2(store_type_lane_kind lane))')],1,'[::Nat.eqb lane 1]',''),
(7846,'lane b0 b1',[(7845,1,'[::Nat.eqb lane 1]'),(7840,5,'(store_request_half b0 b1)'),(7844,4,'(store_request_wordmask lane)')],5,'(store_request_half_select lane b0 b1)','destruct b0,b1;'),
(7847,'lane',[(7838,2,'(from_N 2(store_type_lane_kind lane))')],1,'[::Nat.eqb lane 2]',''),
(7848,'lane b0 b1',[(7847,1,'[::Nat.eqb lane 2]'),(7842,4,'(store_request_byte b0 b1)'),(7846,5,'(store_request_half_select lane b0 b1)')],5,'(store_request_mask5 lane b0 b1)','destruct b0,b1;')]
for n,args,ins,w,out,cases in rows:
 lane='lane' in args
 s+=f'\nTheorem store_request_mask_value_{n} invalid old current result {args} :\n'
 if lane:s+=' (lane<3)%coq_nat ->\n'
 for node,width,bits in ins:s+=f' VM.find {node} old=Some(Gval(Fuint {width}){bits}) ->\n'
 s+=f''' formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find {n} result=Some(Gval(Fuint {w}){out}).
Proof.
 intros {'Lane ' if lane else ''}{' '.join('H'+str(i)for i in range(len(ins)))} Step.
 eapply(store_request_mask_node_step {n} store_request_mask_expr_{n} invalid old current result).
 - unfold store_request_mask_nodes. '''+(f'do {n-7838} right. 'if n>7838 else '')+'''left;reflexivity.
 - intro site. cbn[store_request_mask_expr_'''+str(n)+''' eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite '''+' '.join('H'+str(i)for i in range(len(ins)))+'''.
'''
 if n==7838:s+='   unfold eval_type_of_expr. cbn[type_of_expr\' eval_type_of_ref]. rewrite H1.\n'
 if n in [7846,7848]:s+='   unfold eval_type_of_expr. cbn[type_of_expr\' eval_type_of_ref]. rewrite H1 H2.\n'
 if lane:s+='   do 3(destruct lane as[|lane];['+cases+'reflexivity|]);lia.\n'
 elif n in [7839,7841]:s+='   cbn[eval_unop]. rewrite !take_cons ?take0. reflexivity.\n'
 else:s+='   '+cases+'reflexivity.\n'
 s+=' - exact Step.\nQed.\n'
s+='''
Lemma store_request_mask4_size lane b0 b1 :(lane<3)%coq_nat ->size(store_request_mask4 lane b0 b1)=4%nat.
Proof. intro Lane. do 3(destruct lane as[|lane];[destruct b0,b1;reflexivity|]);lia. Qed.
'''
(base/'StoreRequestMaskValues.v').write_text(s)

Require Import StoreTypeCorrespondence DUTRedirectDecode.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Lemma store_nonstore_guard instruction lane :
 (lane<3)%coq_nat ->
 N.land instruction 28799 <>store_type_lane_code lane ->
 dut_decode_test instruction (store_type_lane_row lane)=false.
Proof.
 intros Lane NonStore. apply N.eqb_neq.
 do 3(destruct lane as[|lane];[exact NonStore|]);lia.
Qed.
Theorem store_nonstore_decode instruction count :
 (count<=49)%coq_nat ->
 (forall lane,(lane<3)%coq_nat ->N.land instruction 28799 <>store_type_lane_code lane) ->
 store_type_decode instruction count=from_N 2 0.
Proof.
 intros Count NonStore.
 pose proof(NonStore 0%nat ltac:(lia))as NS0.
 pose proof(NonStore 1%nat ltac:(lia))as NS1.
 pose proof(NonStore 2%nat ltac:(lia))as NS2.
 induction count as[|count IH];[reflexivity|].
 cbn[store_type_decode]. rewrite(IH ltac:(lia)).
 assert(Row:(Nat.sub 48 count<49)%coq_nat)by lia.
 remember (Nat.sub 48 count) as row eqn:RowEq. clear RowEq Count IH.
 do 15(destruct row as[|row];[destruct(dut_decode_test instruction _);reflexivity|]).
 destruct row as[|row].
 - change ((if dut_decode_test instruction (store_type_lane_row 2) then from_N 2 3 else from_N 2 0)=from_N 2 0).
   rewrite(store_nonstore_guard instruction 2 ltac:(lia)NS2). reflexivity.
 - destruct row as[|row].
   + change ((if dut_decode_test instruction (store_type_lane_row 1) then from_N 2 2 else from_N 2 0)=from_N 2 0).
     rewrite(store_nonstore_guard instruction 1 ltac:(lia)NS1). reflexivity.
   + destruct row as[|row].
     * change ((if dut_decode_test instruction (store_type_lane_row 0) then from_N 2 1 else from_N 2 0)=from_N 2 0).
       rewrite(store_nonstore_guard instruction 0 ltac:(lia)NS0). reflexivity.
     * do 31(destruct row as[|row];[destruct(dut_decode_test instruction _);reflexivity|]);lia.
Qed.
Corollary store_nonstore_instruction_decode instruction :
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) ->
 store_type_decode (to_N instruction) 49=from_N 2 0.
Proof. intro NonStore. apply store_nonstore_decode;[lia|exact NonStore]. Qed.

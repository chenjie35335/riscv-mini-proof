From Coq Require Import Lia ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From firrtl Require Import Semantics_with_implicit_widths.
Require Import RFWritebackSelection ReferenceLoadArithmetic.
Local Open Scope N_scope.
Definition load_result32 low middle high raw b0 b1 :=
 let word := rf_load_shift raw b0 b1 in
 if low && negb middle && high then zext_to 32 (take 8 word) else
 if negb low && negb middle && high then zext_to 32 (take 16 word) else
 if low && middle && negb high then sext_to 32 (take 8 word) else
 if negb low && middle && negb high then sext_to 32 (take 16 word) else raw.
Theorem dut_load_result32 low middle high raw b0 b1 :
 size raw = 32%nat ->
 take 32 (rf_load_result low middle high raw b0 b1) =
 load_result32 low middle high raw b0 b1.
Proof.
 intro Size.
 assert (Byte : (size (take 8 (rf_load_shift raw b0 b1)) < 32)%nat).
 { rewrite size_take (rf_load_shift_size raw b0 b1 Size). reflexivity. }
 assert (Half : (size (take 16 (rf_load_shift raw b0 b1)) < 32)%nat).
 { rewrite size_take (rf_load_shift_size raw b0 b1 Size). reflexivity. }
 assert (Whole : take 32 (zext 1 raw) = raw).
 { unfold zext. rewrite take_cat Size ltnn subnn take0 cats0. reflexivity. }
 unfold rf_load_result,rf_load_selected,load_result32.
 destruct low,middle,high; cbn [negb andb]; try exact Whole;
 try (apply reference_load_unsigned32; assumption);
 apply reference_load_sext_truncate; try reflexivity;
 apply ltnW; assumption.
Qed.
Print Assumptions dut_load_result32.
Require Import CoreSocModel SharedLoadInput FormalLocalHistory.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_memory.
Theorem dut_load_observed_result32 memory inputs k observed low middle high b0 b1 rest raw :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 size raw = 32%nat ->
 VM.find 7755 (top_environment observed) = Some (Gval (Fuint 3) [::low;middle;high]) ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 9222 (top_environment observed) = Some (Gval (Fuint 32) raw) ->
 exists result,
 VM.find 7904 (top_environment observed) = Some (Gval (Fsint 33) result) /\
 take 32 result = load_result32 low middle high raw b0 b1.
Proof.
 intros Observe Legal Size Mode Address Raw.
 exists (rf_load_result low middle high raw b0 b1). split.
 - exact (shared_load_observed_result memory inputs k observed low middle high b0 b1 rest raw Observe Legal Size Mode Address Raw).
 - exact (dut_load_result32 low middle high raw b0 b1 Size).
Qed.
Lemma load_byte_offset b0 b1 rest :
 to_nat (zeros 3 ++ take 2 (b0::b1::rest)) =
 ((if b1 then 16 else 0)+(if b0 then 8 else 0))%nat.
Proof.
 destruct rest as [|bit rest]; destruct b0,b1; vm_compute; reflexivity.
Qed.
Theorem load_shift_correspondence raw b0 b1 rest :
 zext_to 32 (drop (to_nat (zeros 3 ++ take 2 (b0::b1::rest))) raw) =
 rf_load_shift raw b0 b1.
Proof. rewrite load_byte_offset. reflexivity. Qed.
Theorem load_aligned_word raw : size raw = 32%nat ->
 rf_load_shift raw false false = raw.
Proof.
 intro Size. unfold rf_load_shift. rewrite drop0.
 unfold zext_to. rewrite Size subnn. unfold zext. rewrite cats0. reflexivity.
Qed.
Print Assumptions load_shift_correspondence.
Print Assumptions load_aligned_word.
Lemma load_result32_size low middle high raw b0 b1 :
 size raw = 32%nat -> size (load_result32 low middle high raw b0 b1) = 32%nat.
Proof.
 intro Size.
 assert (Shift : size (rf_load_shift raw b0 b1) = 32%nat) by exact (rf_load_shift_size raw b0 b1 Size).
 unfold load_result32.
 destruct low,middle,high; cbn [negb andb]; try exact Size;
 unfold zext_to,sext_to; rewrite ?size_zext ?size_sext size_take Shift; reflexivity.
Qed.
Print Assumptions load_result32_size.
Require Import ReferenceLoadSemantics.
Definition load_lane_kind lane := nth (false,false,false)
 [::(false,false,true);(true,false,true);(true,false,false);(false,true,false);(true,true,false)] lane.
Theorem load_lane_correspondence lane raw b0 b1 rest :
 (lane < 5)%coq_nat -> size raw = 32%nat ->
 (lane = 2%nat -> b0 = false /\ b1 = false) ->
 let '(low,middle,high) := load_lane_kind lane in
 load_result32 low middle high raw b0 b1 =
 reference_load_extend lane
 (take (reference_load_width lane) (reference_load_shift raw (b0::b1::rest))).
Proof.
 intros Lane Size Aligned.
 unfold reference_load_shift. rewrite load_shift_correspondence.
 do 2 (destruct lane as [|lane]; [reflexivity|]).
 destruct lane as [|lane].
 - destruct (Aligned (Logic.eq_refl 2%nat)) as [B0 B1]. subst b0 b1.
   cbn [load_lane_kind nth load_result32 reference_load_extend reference_load_width Nat.eqb].
   rewrite load_aligned_word; [|exact Size].
   change (raw = take 32 (take 32 raw)).
   rewrite take_take; [|reflexivity].
   rewrite -(Size) take_size. reflexivity.
 - do 2 (destruct lane as [|lane]; [reflexivity|]). lia.
Qed.
Print Assumptions load_lane_correspondence.
Require Import LoadAddressAlignment.
Theorem load_observed_correspondence memory inputs k observed lane low middle high b0 b1 rest raw rs1 immediate :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (lane < 5)%coq_nat -> size raw = 32%nat ->
 (low,middle,high) = load_lane_kind lane ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size (b0::b1::rest) = 32%nat ->
 take 2 (reference_load_address rs1 immediate) = [::b0;b1] ->
 VM.find 7755 (top_environment observed) = Some (Gval (Fuint 3) [::low;middle;high]) ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 9222 (top_environment observed) = Some (Gval (Fuint 32) raw) ->
 exists result,
 VM.find 7904 (top_environment observed) = Some (Gval (Fsint 33) result) /\
 VM.find (reference_load_output lane) (top_environment observed) = Some (Gval (Fuint 32) (take 32 result)).
Proof.
 intros Observe Legal Lane Size Kind Reset AddressSize Low Mode Address Rs1 Immediate Raw.
 assert (Aligned : lane = 2%nat -> b0 = false /\ b1 = false).
 { intro IsWord. subst lane. cbn [load_lane_kind nth] in Kind.
   inversion Kind; subst low middle high.
   exact (load_word_aligned_observed memory inputs k observed b0 b1 rest Observe Legal Reset AddressSize Mode Address). }
 destruct (dut_load_observed_result32 memory inputs k observed low middle high b0 b1 rest raw Observe Legal Size Mode Address Raw) as [result [Dut Result]].
 pose proof (reference_load_function_observed memory inputs k observed lane rs1 immediate raw Observe Legal Lane Size Rs1 Immediate Raw) as Ref.
 pose proof (load_lane_correspondence lane raw b0 b1 [::] Lane Size Aligned) as Equal.
 rewrite <- Kind in Equal. cbn beta iota zeta in Equal.
 assert (Shift : reference_load_shift raw (reference_load_address rs1 immediate) = reference_load_shift raw [::b0;b1]).
 { unfold reference_load_shift. rewrite Low. reflexivity. }
 rewrite Shift -Equal -Result in Ref.
 exists result. split; assumption.
Qed.
Require Import LoadTypeCorrespondence.
Theorem load_instruction_observed_correspondence memory inputs k observed lane instruction b0 b1 rest raw rs1 immediate :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (lane < 5)%coq_nat -> size raw = 32%nat ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size (b0::b1::rest) = 32%nat ->
 take 2 (reference_load_address rs1 immediate) = [::b0;b1] ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 9222 (top_environment observed) = Some (Gval (Fuint 32) raw) ->
 exists result,
 VM.find 7904 (top_environment observed) = Some (Gval (Fsint 33) result) /\
 VM.find (reference_load_output lane) (top_environment observed) = Some (Gval (Fuint 32) (take 32 result)).
Proof.
 intros Observe Legal Lane Size Instruction Load Reset AddressSize Low Address Rs1 Immediate Raw.
 pose proof (load_type_instruction_observed memory inputs k observed instruction lane Observe Legal Lane Instruction Load) as Mode.
 assert (Kinds : let '(lo,mid,hi) := load_lane_kind lane in
 from_N 3 (load_type_lane_kind lane) = [::lo;mid;hi]).
 { do 5 (destruct lane as [|lane]; [reflexivity|]). lia. }
 destruct (load_lane_kind lane) as [[lo mid] hi] eqn:Kind.
 rewrite Kinds in Mode.
 exact (load_observed_correspondence memory inputs k observed lane lo mid hi b0 b1 rest raw rs1 immediate Observe Legal Lane Size (Logic.eq_sym Kind) Reset AddressSize Low Mode Address Rs1 Immediate Raw).
Qed.

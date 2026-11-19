Require Import StoreCheckerDataValues StoreOutputValues StoreMaskValues StoreOutputOffsetValues StoreOutputOffsetHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_checker_data_word a0 a1 b0 b1 b2 b3 word :=
 zext_to 32(drop(to_nat(store_output_offset_word a0 a1))(andB word(store_mask_word b0 b1 b2 b3))).
Lemma store_checker_data_word_size a0 a1 b0 b1 b2 b3 word :size word=32%nat ->
 size(store_checker_data_word a0 a1 b0 b1 b2 b3 word)=32%nat.
Proof.
 intro Size. unfold store_checker_data_word,zext_to. rewrite size_zext.
 apply subnKC. rewrite size_drop size_andB Size.
 have MaskSize:size(store_mask_word b0 b1 b2 b3)=32%nat by reflexivity.
 rewrite MaskSize maxnn. apply leq_subr.
Qed.
Theorem store_checker_data_history invalid history limit a0 a1 tail b0 b1 b2 b3 word :
 size word=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 8004(history t)=Some(Gval(Fuint 32)(a0::a1::tail))) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 7924(history t)=Some(Gval(Fuint 4)[::b0;b1;b2;b3])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 7925(history t)=Some(Gval(Fuint 32)word)) ->
 forall t,(10<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 1481(history t)=Some(Gval(Fuint 32)(store_checker_data_word a0 a1 b0 b1 b2 b3 word)).
Proof.
 intros Size Steps Address Mask Word.
 assert(Masks:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8018(history t)=Some(Gval(Fuint 32)(store_mask_word b0 b1 b2 b3))).
 { intros t Lower Upper. do 4(destruct t as[|t];[lia|]).
 eapply(store_mask_four_steps _ (history t)(history(S t))(history(S(S t)))(history(S(S(S t))))(history(S(S(S(S t)))))b0 b1 b2 b3);
 [apply Mask|apply Steps|apply Steps|apply Steps|apply Steps];lia. }
 assert(Offsets:forall t,(5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8037(history t)=Some(Gval(Fuint 5)(store_output_offset_word a0 a1))).
 { intros t Lower Upper. apply(store_output_offset_history invalid history limit 0 a0 a1 tail Steps).
 - intros i Lo Hi. apply Address. exact Hi.
 - exact Lower.
 - exact Upper. }
 assert(Outputs:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8039(history t)=Some(Gval(Fuint 32)(store_checker_data_word a0 a1 b0 b1 b2 b3 word))).
 { intros[|[|t]]Lower Upper;try lia.
 eapply(store_output_two_steps _ (history t)(history(S t))(history(S(S t)))word(store_mask_word b0 b1 b2 b3)(store_output_offset_word a0 a1));
 [apply Word|apply Masks|apply Offsets|apply Steps|apply Steps];lia. }
 intros t Lower Upper. do 4(destruct t as[|t];[lia|]).
 eapply(store_checker_data_four_steps _ (history t)(history(S t))(history(S(S t)))(history(S(S(S t))))(history(S(S(S(S t)))))).
 - apply store_checker_data_word_size. exact Size.
 - apply Outputs;lia.
 - apply Steps;lia.
 - apply Steps;lia.
 - apply Steps;lia.
 - apply Steps;lia.
Qed.
Require Import StoreMaskObserved StoreDataRegister StoreOutputOffsetObserved RegisterInvariants StagedRegisterHold.
Theorem store_checker_data_history_from_last invalid history limit a0 a1 tail b0 b1 b2 b3 word :
 size word=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 8004(history limit)=Some(Gval(Fuint 32)(a0::a1::tail)) ->
 VM.find 7924(history limit)=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 VM.find 7925(history limit)=Some(Gval(Fuint 32)word) ->
 forall t,(10<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 1481(history t)=Some(Gval(Fuint 32)(store_checker_data_word a0 a1 b0 b1 b2 b3 word)).
Proof.
 intros Size Steps Address Mask Word.
 assert(Held:forall node,has_register node flat_statements=true ->forall t,(t<=limit)%coq_nat ->VM.find node(history t)=VM.find node(history limit)).
 { intros node Register.
 assert(H:forall t,(t<=limit)%coq_nat ->VM.find node(history t)=VM.find node(history 0%nat)).
 { intros t. induction t as[|t IH];intro Bound;[reflexivity|].
 rewrite(staged_combinational_holds_registers _ flat_memories(history t)(history t)(history(S t))flat_statements node Register(Steps t ltac:(lia))). apply IH;lia. }
 intros t Bound. rewrite(H t Bound) -(H limit ltac:(lia)). reflexivity. }
 apply(store_checker_data_history invalid history limit a0 a1 tail b0 b1 b2 b3 word Size Steps).
 - intros t Bound. rewrite(Held 8004 store_output_address_register t Bound). exact Address.
 - intros t Bound. rewrite(Held 7924 store_mask_register t Bound). exact Mask.
 - intros t Bound. rewrite(Held 7925 store_data_register t Bound). exact Word.
Qed.

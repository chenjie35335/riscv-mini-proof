Require Import CoreSocModel ComparisonNodes ReferencePCTargetStability ReferencePCTargetEquations ReferenceRedirectSpine.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma ref_pc_target_resize32 word :size word=32%nat ->zext_to 32(take 32 word)=word.
Proof. intro Size. assert(Take:take 32 word=word)by(rewrite <-Size;apply take_size).
 rewrite Take. unfold zext_to,zext. rewrite Size subnn cats0. reflexivity. Qed.
Definition reference_pc_target_value (guards:VarOrder.T->bool) pc immediate rs1 :=
 let w6309 := from_N 33(to_N pc+to_N immediate) in
 let w6310 := take 32 w6309 in
 let w6315 := if guards 2966 then w6310 else pc in
 let w6326 := if guards 2357 then w6315 else pc in
 let w6335 := rs1 in
 let w6336 := from_N 33(to_N w6335+to_N immediate) in
 let w6337 := take 32 w6336 in
 let w6338 := drop 1(take 32 w6337) in
 let w6339 := [::false]++w6338 in
 let w6347 := if guards 2949 then w6339 else w6326 in
 let w6360 := if guards 2010 then w6347 else w6326 in
 let w6369 := from_N 33(to_N pc+to_N immediate) in
 let w6370 := take 32 w6369 in
 let w6374 := if guards 2929 then w6370 else w6360 in
 let w6378 := if guards 2912 then w6374 else w6360 in
 let w6388 := if guards 2004 then w6378 else w6360 in
 let w6393 := from_N 33(to_N pc+to_N immediate) in
 let w6394 := take 32 w6393 in
 let w6398 := if guards 2909 then w6394 else w6388 in
 let w6402 := if guards 2892 then w6398 else w6388 in
 let w6412 := if guards 1998 then w6402 else w6388 in
 let w6417 := from_N 33(to_N pc+to_N immediate) in
 let w6418 := take 32 w6417 in
 let w6422 := if guards 2889 then w6418 else w6412 in
 let w6426 := if guards 2872 then w6422 else w6412 in
 let w6436 := if guards 1992 then w6426 else w6412 in
 let w6441 := from_N 33(to_N pc+to_N immediate) in
 let w6442 := take 32 w6441 in
 let w6446 := if guards 2867 then w6442 else w6436 in
 let w6450 := if guards 2850 then w6446 else w6436 in
 let w6460 := if guards 1986 then w6450 else w6436 in
 let w6465 := from_N 33(to_N pc+to_N immediate) in
 let w6466 := take 32 w6465 in
 let w6470 := if guards 2847 then w6466 else w6460 in
 let w6474 := if guards 2830 then w6470 else w6460 in
 let w6484 := if guards 1980 then w6474 else w6460 in
 let w6489 := from_N 33(to_N pc+to_N immediate) in
 let w6490 := take 32 w6489 in
 let w6494 := if guards 2825 then w6490 else w6484 in
 let w6498 := if guards 2806 then w6494 else w6484 in
 let w6508 := if guards 1974 then w6498 else w6484 in
 w6508.
Definition reference_pc_target_guard_nodes :seq VarOrder.T := [::1974;1980;1986;1992;1998;2004;2010;2357;2806;2825;2830;2847;2850;2867;2872;2889;2892;2909;2912;2929;2949;2966].
Theorem reference_pc_target_semantics inputs path history limit reset time guards pc immediate rs1 :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (225<=time)%coq_nat ->(time<limit)%coq_nat ->size pc=32%nat ->size rs1=32%nat ->
 VM.find 2812(history time)=Some(Gval(Fuint 32)pc) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)immediate) ->
 VM.find 2209(history time)=Some(Gval(Fuint 32)rs1) ->
 (forall node,List.In node reference_pc_target_guard_nodes ->VM.find node(history time)=Some(Gval(Fuint 1)[::guards node])) ->
 VM.find 6508(history time)=Some(Gval(Fuint 32)(reference_pc_target_value guards pc immediate rs1)).
Proof.
 intros Resets Steps Lower Upper PCSize Rs1Size PC Immediate Rs1 Guards.
 set(w6309:=from_N 33(to_N pc+to_N immediate)).
 assert(Size6309:size w6309=33%nat)by(unfold w6309;rewrite size_from_N;reflexivity).
 assert(V6309:VM.find 6309(history time)=Some(Gval(Fuint 33)w6309)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 0%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6309(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite PC Immediate. reflexivity.
 }
 set(w6310:=take 32 w6309).
 assert(Size6310:size w6310=32%nat).
 { unfold w6310. rewrite size_take Size6309;reflexivity. }
 assert(V6310:VM.find 6310(history time)=Some(Gval(Fuint 32)w6310)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 1%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6310(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6309))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6309. reflexivity.
 }
 set(w6315:=if guards 2966 then w6310 else pc).
 assert(Size6315:size w6315=32%nat).
 { unfold w6315. destruct(guards 2966);[exact Size6310|exact PCSize]. }
 assert(V6315:VM.find 6315(history time)=Some(Gval(Fuint 32)w6315)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 2%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6315(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2966)) (@Eref VarOrder.T (@Eid VarOrder.T 6310)) (@Eref VarOrder.T (@Eid VarOrder.T 2812))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2966 ltac:(vm_compute;tauto)). destruct(guards 2966);cbn[is_zero];rewrite V6310 PC;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6310 ?PC.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6310)))=Some(Gval(Fuint 32)w6310)). rewrite(ref_pc_target_resize32 _ Size6310);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 pc)))=Some(Gval(Fuint 32)pc)). rewrite(ref_pc_target_resize32 _ PCSize);reflexivity.
 }
 set(w6326:=if guards 2357 then w6315 else pc).
 assert(Size6326:size w6326=32%nat).
 { unfold w6326. destruct(guards 2357);[exact Size6315|exact PCSize]. }
 assert(V6326:VM.find 6326(history time)=Some(Gval(Fuint 32)w6326)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 3%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6326(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2357)) (@Eref VarOrder.T (@Eid VarOrder.T 6315)) (@Eref VarOrder.T (@Eid VarOrder.T 2812))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2357 ltac:(vm_compute;tauto)). destruct(guards 2357);cbn[is_zero];rewrite V6315 PC;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6315 ?PC.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6315)))=Some(Gval(Fuint 32)w6315)). rewrite(ref_pc_target_resize32 _ Size6315);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 pc)))=Some(Gval(Fuint 32)pc)). rewrite(ref_pc_target_resize32 _ PCSize);reflexivity.
 }
 set(w6335:=rs1).
 assert(Size6335:size w6335=32%nat).
 { unfold w6335. exact Rs1Size. }
 assert(V6335:VM.find 6335(history time)=Some(Gval(Fuint 32)w6335)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 4%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6335(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eref VarOrder.T (@Eid VarOrder.T 2209)) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Rs1. reflexivity.
 }
 set(w6336:=from_N 33(to_N w6335+to_N immediate)).
 assert(Size6336:size w6336=33%nat)by(unfold w6336;rewrite size_from_N;reflexivity).
 assert(V6336:VM.find 6336(history time)=Some(Gval(Fuint 33)w6336)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 5%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6336(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6335)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6335 Immediate. reflexivity.
 }
 set(w6337:=take 32 w6336).
 assert(Size6337:size w6337=32%nat).
 { unfold w6337. rewrite size_take Size6336;reflexivity. }
 assert(V6337:VM.find 6337(history time)=Some(Gval(Fuint 32)w6337)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 6%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6337(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6336))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6336. reflexivity.
 }
 set(w6338:=drop 1(take 32 w6337)).
 assert(Size6338:size w6338=31%nat).
 { unfold w6338. rewrite size_drop size_take Size6337;reflexivity. }
 assert(V6338:VM.find 6338(history time)=Some(Gval(Fuint 31)w6338)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 7%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6338(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_unop VarOrder.T (Uextr 31 1) (@Eref VarOrder.T (@Eid VarOrder.T 6337))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6337. reflexivity.
 }
 set(w6339:=[::false]++w6338).
 assert(Size6339:size w6339=32%nat).
 { unfold w6339. rewrite size_cat Size6338;reflexivity. }
 assert(V6339:VM.find 6339(history time)=Some(Gval(Fuint 32)w6339)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 8%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6339(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 6338)) (@Econst VarOrder.T (Fuint 1) [::false])) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6338. reflexivity.
 }
 set(w6347:=if guards 2949 then w6339 else w6326).
 assert(Size6347:size w6347=32%nat).
 { unfold w6347. destruct(guards 2949);[exact Size6339|exact Size6326]. }
 assert(V6347:VM.find 6347(history time)=Some(Gval(Fuint 32)w6347)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 9%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6347(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2949)) (@Eref VarOrder.T (@Eid VarOrder.T 6339)) (@Eref VarOrder.T (@Eid VarOrder.T 6326))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2949 ltac:(vm_compute;tauto)). destruct(guards 2949);cbn[is_zero];rewrite V6339 V6326;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6339 ?V6326.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6339)))=Some(Gval(Fuint 32)w6339)). rewrite(ref_pc_target_resize32 _ Size6339);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6326)))=Some(Gval(Fuint 32)w6326)). rewrite(ref_pc_target_resize32 _ Size6326);reflexivity.
 }
 set(w6360:=if guards 2010 then w6347 else w6326).
 assert(Size6360:size w6360=32%nat).
 { unfold w6360. destruct(guards 2010);[exact Size6347|exact Size6326]. }
 assert(V6360:VM.find 6360(history time)=Some(Gval(Fuint 32)w6360)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 10%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6360(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2010)) (@Eref VarOrder.T (@Eid VarOrder.T 6347)) (@Eref VarOrder.T (@Eid VarOrder.T 6326))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2010 ltac:(vm_compute;tauto)). destruct(guards 2010);cbn[is_zero];rewrite V6347 V6326;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6347 ?V6326.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6347)))=Some(Gval(Fuint 32)w6347)). rewrite(ref_pc_target_resize32 _ Size6347);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6326)))=Some(Gval(Fuint 32)w6326)). rewrite(ref_pc_target_resize32 _ Size6326);reflexivity.
 }
 set(w6369:=from_N 33(to_N pc+to_N immediate)).
 assert(Size6369:size w6369=33%nat)by(unfold w6369;rewrite size_from_N;reflexivity).
 assert(V6369:VM.find 6369(history time)=Some(Gval(Fuint 33)w6369)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 11%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6369(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite PC Immediate. reflexivity.
 }
 set(w6370:=take 32 w6369).
 assert(Size6370:size w6370=32%nat).
 { unfold w6370. rewrite size_take Size6369;reflexivity. }
 assert(V6370:VM.find 6370(history time)=Some(Gval(Fuint 32)w6370)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 12%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6370(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6369))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6369. reflexivity.
 }
 set(w6374:=if guards 2929 then w6370 else w6360).
 assert(Size6374:size w6374=32%nat).
 { unfold w6374. destruct(guards 2929);[exact Size6370|exact Size6360]. }
 assert(V6374:VM.find 6374(history time)=Some(Gval(Fuint 32)w6374)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 13%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6374(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2929)) (@Eref VarOrder.T (@Eid VarOrder.T 6370)) (@Eref VarOrder.T (@Eid VarOrder.T 6360))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2929 ltac:(vm_compute;tauto)). destruct(guards 2929);cbn[is_zero];rewrite V6370 V6360;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6370 ?V6360.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6370)))=Some(Gval(Fuint 32)w6370)). rewrite(ref_pc_target_resize32 _ Size6370);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6360)))=Some(Gval(Fuint 32)w6360)). rewrite(ref_pc_target_resize32 _ Size6360);reflexivity.
 }
 set(w6378:=if guards 2912 then w6374 else w6360).
 assert(Size6378:size w6378=32%nat).
 { unfold w6378. destruct(guards 2912);[exact Size6374|exact Size6360]. }
 assert(V6378:VM.find 6378(history time)=Some(Gval(Fuint 32)w6378)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 14%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6378(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2912)) (@Eref VarOrder.T (@Eid VarOrder.T 6374)) (@Eref VarOrder.T (@Eid VarOrder.T 6360))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2912 ltac:(vm_compute;tauto)). destruct(guards 2912);cbn[is_zero];rewrite V6374 V6360;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6374 ?V6360.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6374)))=Some(Gval(Fuint 32)w6374)). rewrite(ref_pc_target_resize32 _ Size6374);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6360)))=Some(Gval(Fuint 32)w6360)). rewrite(ref_pc_target_resize32 _ Size6360);reflexivity.
 }
 set(w6388:=if guards 2004 then w6378 else w6360).
 assert(Size6388:size w6388=32%nat).
 { unfold w6388. destruct(guards 2004);[exact Size6378|exact Size6360]. }
 assert(V6388:VM.find 6388(history time)=Some(Gval(Fuint 32)w6388)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 15%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6388(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2004)) (@Eref VarOrder.T (@Eid VarOrder.T 6378)) (@Eref VarOrder.T (@Eid VarOrder.T 6360))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2004 ltac:(vm_compute;tauto)). destruct(guards 2004);cbn[is_zero];rewrite V6378 V6360;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6378 ?V6360.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6378)))=Some(Gval(Fuint 32)w6378)). rewrite(ref_pc_target_resize32 _ Size6378);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6360)))=Some(Gval(Fuint 32)w6360)). rewrite(ref_pc_target_resize32 _ Size6360);reflexivity.
 }
 set(w6393:=from_N 33(to_N pc+to_N immediate)).
 assert(Size6393:size w6393=33%nat)by(unfold w6393;rewrite size_from_N;reflexivity).
 assert(V6393:VM.find 6393(history time)=Some(Gval(Fuint 33)w6393)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 16%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6393(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite PC Immediate. reflexivity.
 }
 set(w6394:=take 32 w6393).
 assert(Size6394:size w6394=32%nat).
 { unfold w6394. rewrite size_take Size6393;reflexivity. }
 assert(V6394:VM.find 6394(history time)=Some(Gval(Fuint 32)w6394)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 17%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6394(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6393))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6393. reflexivity.
 }
 set(w6398:=if guards 2909 then w6394 else w6388).
 assert(Size6398:size w6398=32%nat).
 { unfold w6398. destruct(guards 2909);[exact Size6394|exact Size6388]. }
 assert(V6398:VM.find 6398(history time)=Some(Gval(Fuint 32)w6398)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 18%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6398(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2909)) (@Eref VarOrder.T (@Eid VarOrder.T 6394)) (@Eref VarOrder.T (@Eid VarOrder.T 6388))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2909 ltac:(vm_compute;tauto)). destruct(guards 2909);cbn[is_zero];rewrite V6394 V6388;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6394 ?V6388.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6394)))=Some(Gval(Fuint 32)w6394)). rewrite(ref_pc_target_resize32 _ Size6394);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6388)))=Some(Gval(Fuint 32)w6388)). rewrite(ref_pc_target_resize32 _ Size6388);reflexivity.
 }
 set(w6402:=if guards 2892 then w6398 else w6388).
 assert(Size6402:size w6402=32%nat).
 { unfold w6402. destruct(guards 2892);[exact Size6398|exact Size6388]. }
 assert(V6402:VM.find 6402(history time)=Some(Gval(Fuint 32)w6402)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 19%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6402(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2892)) (@Eref VarOrder.T (@Eid VarOrder.T 6398)) (@Eref VarOrder.T (@Eid VarOrder.T 6388))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2892 ltac:(vm_compute;tauto)). destruct(guards 2892);cbn[is_zero];rewrite V6398 V6388;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6398 ?V6388.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6398)))=Some(Gval(Fuint 32)w6398)). rewrite(ref_pc_target_resize32 _ Size6398);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6388)))=Some(Gval(Fuint 32)w6388)). rewrite(ref_pc_target_resize32 _ Size6388);reflexivity.
 }
 set(w6412:=if guards 1998 then w6402 else w6388).
 assert(Size6412:size w6412=32%nat).
 { unfold w6412. destruct(guards 1998);[exact Size6402|exact Size6388]. }
 assert(V6412:VM.find 6412(history time)=Some(Gval(Fuint 32)w6412)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 20%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6412(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1998)) (@Eref VarOrder.T (@Eid VarOrder.T 6402)) (@Eref VarOrder.T (@Eid VarOrder.T 6388))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 1998 ltac:(vm_compute;tauto)). destruct(guards 1998);cbn[is_zero];rewrite V6402 V6388;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6402 ?V6388.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6402)))=Some(Gval(Fuint 32)w6402)). rewrite(ref_pc_target_resize32 _ Size6402);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6388)))=Some(Gval(Fuint 32)w6388)). rewrite(ref_pc_target_resize32 _ Size6388);reflexivity.
 }
 set(w6417:=from_N 33(to_N pc+to_N immediate)).
 assert(Size6417:size w6417=33%nat)by(unfold w6417;rewrite size_from_N;reflexivity).
 assert(V6417:VM.find 6417(history time)=Some(Gval(Fuint 33)w6417)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 21%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6417(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite PC Immediate. reflexivity.
 }
 set(w6418:=take 32 w6417).
 assert(Size6418:size w6418=32%nat).
 { unfold w6418. rewrite size_take Size6417;reflexivity. }
 assert(V6418:VM.find 6418(history time)=Some(Gval(Fuint 32)w6418)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 22%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6418(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6417))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6417. reflexivity.
 }
 set(w6422:=if guards 2889 then w6418 else w6412).
 assert(Size6422:size w6422=32%nat).
 { unfold w6422. destruct(guards 2889);[exact Size6418|exact Size6412]. }
 assert(V6422:VM.find 6422(history time)=Some(Gval(Fuint 32)w6422)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 23%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6422(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2889)) (@Eref VarOrder.T (@Eid VarOrder.T 6418)) (@Eref VarOrder.T (@Eid VarOrder.T 6412))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2889 ltac:(vm_compute;tauto)). destruct(guards 2889);cbn[is_zero];rewrite V6418 V6412;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6418 ?V6412.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6418)))=Some(Gval(Fuint 32)w6418)). rewrite(ref_pc_target_resize32 _ Size6418);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6412)))=Some(Gval(Fuint 32)w6412)). rewrite(ref_pc_target_resize32 _ Size6412);reflexivity.
 }
 set(w6426:=if guards 2872 then w6422 else w6412).
 assert(Size6426:size w6426=32%nat).
 { unfold w6426. destruct(guards 2872);[exact Size6422|exact Size6412]. }
 assert(V6426:VM.find 6426(history time)=Some(Gval(Fuint 32)w6426)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 24%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6426(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2872)) (@Eref VarOrder.T (@Eid VarOrder.T 6422)) (@Eref VarOrder.T (@Eid VarOrder.T 6412))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2872 ltac:(vm_compute;tauto)). destruct(guards 2872);cbn[is_zero];rewrite V6422 V6412;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6422 ?V6412.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6422)))=Some(Gval(Fuint 32)w6422)). rewrite(ref_pc_target_resize32 _ Size6422);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6412)))=Some(Gval(Fuint 32)w6412)). rewrite(ref_pc_target_resize32 _ Size6412);reflexivity.
 }
 set(w6436:=if guards 1992 then w6426 else w6412).
 assert(Size6436:size w6436=32%nat).
 { unfold w6436. destruct(guards 1992);[exact Size6426|exact Size6412]. }
 assert(V6436:VM.find 6436(history time)=Some(Gval(Fuint 32)w6436)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 25%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6436(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1992)) (@Eref VarOrder.T (@Eid VarOrder.T 6426)) (@Eref VarOrder.T (@Eid VarOrder.T 6412))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 1992 ltac:(vm_compute;tauto)). destruct(guards 1992);cbn[is_zero];rewrite V6426 V6412;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6426 ?V6412.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6426)))=Some(Gval(Fuint 32)w6426)). rewrite(ref_pc_target_resize32 _ Size6426);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6412)))=Some(Gval(Fuint 32)w6412)). rewrite(ref_pc_target_resize32 _ Size6412);reflexivity.
 }
 set(w6441:=from_N 33(to_N pc+to_N immediate)).
 assert(Size6441:size w6441=33%nat)by(unfold w6441;rewrite size_from_N;reflexivity).
 assert(V6441:VM.find 6441(history time)=Some(Gval(Fuint 33)w6441)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 26%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6441(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite PC Immediate. reflexivity.
 }
 set(w6442:=take 32 w6441).
 assert(Size6442:size w6442=32%nat).
 { unfold w6442. rewrite size_take Size6441;reflexivity. }
 assert(V6442:VM.find 6442(history time)=Some(Gval(Fuint 32)w6442)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 27%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6442(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6441))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6441. reflexivity.
 }
 set(w6446:=if guards 2867 then w6442 else w6436).
 assert(Size6446:size w6446=32%nat).
 { unfold w6446. destruct(guards 2867);[exact Size6442|exact Size6436]. }
 assert(V6446:VM.find 6446(history time)=Some(Gval(Fuint 32)w6446)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 28%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6446(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2867)) (@Eref VarOrder.T (@Eid VarOrder.T 6442)) (@Eref VarOrder.T (@Eid VarOrder.T 6436))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2867 ltac:(vm_compute;tauto)). destruct(guards 2867);cbn[is_zero];rewrite V6442 V6436;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6442 ?V6436.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6442)))=Some(Gval(Fuint 32)w6442)). rewrite(ref_pc_target_resize32 _ Size6442);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6436)))=Some(Gval(Fuint 32)w6436)). rewrite(ref_pc_target_resize32 _ Size6436);reflexivity.
 }
 set(w6450:=if guards 2850 then w6446 else w6436).
 assert(Size6450:size w6450=32%nat).
 { unfold w6450. destruct(guards 2850);[exact Size6446|exact Size6436]. }
 assert(V6450:VM.find 6450(history time)=Some(Gval(Fuint 32)w6450)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 29%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6450(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2850)) (@Eref VarOrder.T (@Eid VarOrder.T 6446)) (@Eref VarOrder.T (@Eid VarOrder.T 6436))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2850 ltac:(vm_compute;tauto)). destruct(guards 2850);cbn[is_zero];rewrite V6446 V6436;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6446 ?V6436.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6446)))=Some(Gval(Fuint 32)w6446)). rewrite(ref_pc_target_resize32 _ Size6446);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6436)))=Some(Gval(Fuint 32)w6436)). rewrite(ref_pc_target_resize32 _ Size6436);reflexivity.
 }
 set(w6460:=if guards 1986 then w6450 else w6436).
 assert(Size6460:size w6460=32%nat).
 { unfold w6460. destruct(guards 1986);[exact Size6450|exact Size6436]. }
 assert(V6460:VM.find 6460(history time)=Some(Gval(Fuint 32)w6460)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 30%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6460(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1986)) (@Eref VarOrder.T (@Eid VarOrder.T 6450)) (@Eref VarOrder.T (@Eid VarOrder.T 6436))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 1986 ltac:(vm_compute;tauto)). destruct(guards 1986);cbn[is_zero];rewrite V6450 V6436;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6450 ?V6436.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6450)))=Some(Gval(Fuint 32)w6450)). rewrite(ref_pc_target_resize32 _ Size6450);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6436)))=Some(Gval(Fuint 32)w6436)). rewrite(ref_pc_target_resize32 _ Size6436);reflexivity.
 }
 set(w6465:=from_N 33(to_N pc+to_N immediate)).
 assert(Size6465:size w6465=33%nat)by(unfold w6465;rewrite size_from_N;reflexivity).
 assert(V6465:VM.find 6465(history time)=Some(Gval(Fuint 33)w6465)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 31%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6465(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite PC Immediate. reflexivity.
 }
 set(w6466:=take 32 w6465).
 assert(Size6466:size w6466=32%nat).
 { unfold w6466. rewrite size_take Size6465;reflexivity. }
 assert(V6466:VM.find 6466(history time)=Some(Gval(Fuint 32)w6466)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 32%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6466(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6465))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6465. reflexivity.
 }
 set(w6470:=if guards 2847 then w6466 else w6460).
 assert(Size6470:size w6470=32%nat).
 { unfold w6470. destruct(guards 2847);[exact Size6466|exact Size6460]. }
 assert(V6470:VM.find 6470(history time)=Some(Gval(Fuint 32)w6470)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 33%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6470(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2847)) (@Eref VarOrder.T (@Eid VarOrder.T 6466)) (@Eref VarOrder.T (@Eid VarOrder.T 6460))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2847 ltac:(vm_compute;tauto)). destruct(guards 2847);cbn[is_zero];rewrite V6466 V6460;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6466 ?V6460.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6466)))=Some(Gval(Fuint 32)w6466)). rewrite(ref_pc_target_resize32 _ Size6466);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6460)))=Some(Gval(Fuint 32)w6460)). rewrite(ref_pc_target_resize32 _ Size6460);reflexivity.
 }
 set(w6474:=if guards 2830 then w6470 else w6460).
 assert(Size6474:size w6474=32%nat).
 { unfold w6474. destruct(guards 2830);[exact Size6470|exact Size6460]. }
 assert(V6474:VM.find 6474(history time)=Some(Gval(Fuint 32)w6474)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 34%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6474(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2830)) (@Eref VarOrder.T (@Eid VarOrder.T 6470)) (@Eref VarOrder.T (@Eid VarOrder.T 6460))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2830 ltac:(vm_compute;tauto)). destruct(guards 2830);cbn[is_zero];rewrite V6470 V6460;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6470 ?V6460.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6470)))=Some(Gval(Fuint 32)w6470)). rewrite(ref_pc_target_resize32 _ Size6470);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6460)))=Some(Gval(Fuint 32)w6460)). rewrite(ref_pc_target_resize32 _ Size6460);reflexivity.
 }
 set(w6484:=if guards 1980 then w6474 else w6460).
 assert(Size6484:size w6484=32%nat).
 { unfold w6484. destruct(guards 1980);[exact Size6474|exact Size6460]. }
 assert(V6484:VM.find 6484(history time)=Some(Gval(Fuint 32)w6484)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 35%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6484(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1980)) (@Eref VarOrder.T (@Eid VarOrder.T 6474)) (@Eref VarOrder.T (@Eid VarOrder.T 6460))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 1980 ltac:(vm_compute;tauto)). destruct(guards 1980);cbn[is_zero];rewrite V6474 V6460;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6474 ?V6460.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6474)))=Some(Gval(Fuint 32)w6474)). rewrite(ref_pc_target_resize32 _ Size6474);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6460)))=Some(Gval(Fuint 32)w6460)). rewrite(ref_pc_target_resize32 _ Size6460);reflexivity.
 }
 set(w6489:=from_N 33(to_N pc+to_N immediate)).
 assert(Size6489:size w6489=33%nat)by(unfold w6489;rewrite size_from_N;reflexivity).
 assert(V6489:VM.find 6489(history time)=Some(Gval(Fuint 33)w6489)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 36%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6489(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite PC Immediate. reflexivity.
 }
 set(w6490:=take 32 w6489).
 assert(Size6490:size w6490=32%nat).
 { unfold w6490. rewrite size_take Size6489;reflexivity. }
 assert(V6490:VM.find 6490(history time)=Some(Gval(Fuint 32)w6490)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 37%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6490(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6489))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V6489. reflexivity.
 }
 set(w6494:=if guards 2825 then w6490 else w6484).
 assert(Size6494:size w6494=32%nat).
 { unfold w6494. destruct(guards 2825);[exact Size6490|exact Size6484]. }
 assert(V6494:VM.find 6494(history time)=Some(Gval(Fuint 32)w6494)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 38%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6494(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2825)) (@Eref VarOrder.T (@Eid VarOrder.T 6490)) (@Eref VarOrder.T (@Eid VarOrder.T 6484))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2825 ltac:(vm_compute;tauto)). destruct(guards 2825);cbn[is_zero];rewrite V6490 V6484;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6490 ?V6484.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6490)))=Some(Gval(Fuint 32)w6490)). rewrite(ref_pc_target_resize32 _ Size6490);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6484)))=Some(Gval(Fuint 32)w6484)). rewrite(ref_pc_target_resize32 _ Size6484);reflexivity.
 }
 set(w6498:=if guards 2806 then w6494 else w6484).
 assert(Size6498:size w6498=32%nat).
 { unfold w6498. destruct(guards 2806);[exact Size6494|exact Size6484]. }
 assert(V6498:VM.find 6498(history time)=Some(Gval(Fuint 32)w6498)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 39%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6498(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2806)) (@Eref VarOrder.T (@Eid VarOrder.T 6494)) (@Eref VarOrder.T (@Eid VarOrder.T 6484))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 2806 ltac:(vm_compute;tauto)). destruct(guards 2806);cbn[is_zero];rewrite V6494 V6484;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6494 ?V6484.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6494)))=Some(Gval(Fuint 32)w6494)). rewrite(ref_pc_target_resize32 _ Size6494);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6484)))=Some(Gval(Fuint 32)w6484)). rewrite(ref_pc_target_resize32 _ Size6484);reflexivity.
 }
 set(w6508:=if guards 1974 then w6498 else w6484).
 assert(Size6508:size w6508=32%nat).
 { unfold w6508. destruct(guards 1974);[exact Size6498|exact Size6484]. }
 assert(V6508:VM.find 6508(history time)=Some(Gval(Fuint 32)w6508)).
 { destruct(reference_pc_target_equation inputs path history limit reset time 40%nat Resets Steps Lower Upper ltac:(lia))as[site E].
 change(VM.find 6508(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1974)) (@Eref VarOrder.T (@Eid VarOrder.T 6498)) (@Eref VarOrder.T (@Eid VarOrder.T 6484))) (history time)(history time))in E.
 rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Guards 1974 ltac:(vm_compute;tauto)). destruct(guards 1974);cbn[is_zero];rewrite V6498 V6484;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V6498 ?V6484.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6498)))=Some(Gval(Fuint 32)w6498)). rewrite(ref_pc_target_resize32 _ Size6498);reflexivity.
 - change(Some(Gval(Fuint 32)(zext_to 32(take 32 w6484)))=Some(Gval(Fuint 32)w6484)). rewrite(ref_pc_target_resize32 _ Size6484);reflexivity.
 }
 exact V6508.
Qed.

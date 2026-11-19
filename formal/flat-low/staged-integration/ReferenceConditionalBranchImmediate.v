Require Import ReferenceBranchImmediate ReferenceImmediateTypes ReferenceControlExpressions CoreSocModel ComparisonNodes.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition branch_raw_index stage lane :=nth 0%nat(nth [::] [::[::6%nat;9%nat;12%nat;15%nat;18%nat;21%nat];[::7%nat;10%nat;13%nat;16%nat;19%nat;22%nat];[::8%nat;11%nat;14%nat;17%nat;20%nat;23%nat];[::123%nat;127%nat;131%nat;135%nat;139%nat;143%nat];[::124%nat;128%nat;132%nat;136%nat;140%nat;144%nat];[::125%nat;129%nat;133%nat;137%nat;141%nat;145%nat];[::126%nat;130%nat;134%nat;138%nat;142%nat;146%nat];[::109%nat;110%nat;111%nat;112%nat;113%nat;114%nat];[::160%nat;161%nat;162%nat;163%nat;164%nat;165%nat];[::175%nat;176%nat;177%nat;178%nat;179%nat;180%nat]] stage)lane.
Definition branch_raw_node stage lane :=reference_immediate_node(branch_raw_index stage lane).
Definition branch_raw_width stage :=nth 0%nat [::31%nat;25%nat;20%nat;15%nat;12%nat;8%nat;1%nat;1%nat;6%nat;4%nat] stage.
Definition branch_raw_word stage (instruction:bits) :=nth [::] [::(take 31 instruction);(take 25 instruction);(take 20 instruction);(take 15 instruction);(take 12 instruction);(take 8 instruction);(drop 7(take 8 instruction));(drop 31(take 32 instruction));(drop 25(take 31 instruction));(drop 8(take 12 instruction))] stage.
Lemma branch_raw_bound stage lane : (stage<10)%coq_nat ->(lane<6)%coq_nat ->(branch_raw_index stage lane<304)%coq_nat.
Proof. do 10(destruct stage as[|stage];[do 6(destruct lane as[|lane];[vm_compute;lia|]);lia|]);lia. Qed.
Lemma branch_raw_eval stage lane invalid old instruction :
 (stage<10)%coq_nat ->(lane<6)%coq_nat ->
 VM.find 1884 old=Some(Gval(Fuint 32)instruction) ->
 (forall previous,(previous<stage)%coq_nat ->VM.find(branch_raw_node previous lane)old=Some(Gval(Fuint(branch_raw_width previous))(branch_raw_word previous instruction))) ->
 forall site,eval_hfexpr_validif_policy invalid site flat_memories(reference_immediate_expression(branch_raw_index stage lane))old old=Some(Gval(Fuint(branch_raw_width stage))(branch_raw_word stage instruction)).
Proof.
 intros Stage Lane Source Previous site.
 destruct stage as[|stage].
 {
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1975 old old=Some(Gval(Fuint 31)(take 31 instruction))).
 cbn[reference_control_expr_1975 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1981 old old=Some(Gval(Fuint 31)(take 31 instruction))).
 cbn[reference_control_expr_1981 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1987 old old=Some(Gval(Fuint 31)(take 31 instruction))).
 cbn[reference_control_expr_1987 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1993 old old=Some(Gval(Fuint 31)(take 31 instruction))).
 cbn[reference_control_expr_1993 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1999 old old=Some(Gval(Fuint 31)(take 31 instruction))).
 cbn[reference_control_expr_1999 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2005 old old=Some(Gval(Fuint 31)(take 31 instruction))).
 cbn[reference_control_expr_2005 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 destruct stage as[|stage].
 {
 pose proof(Previous 0%nat ltac:(lia))as Dep.
 destruct lane as[|lane].
 { change(VM.find 1975 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1976 old old=Some(Gval(Fuint 25)(take 25 instruction))).
 cbn[reference_control_expr_1976 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1981 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1982 old old=Some(Gval(Fuint 25)(take 25 instruction))).
 cbn[reference_control_expr_1982 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1987 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1988 old old=Some(Gval(Fuint 25)(take 25 instruction))).
 cbn[reference_control_expr_1988 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1993 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1994 old old=Some(Gval(Fuint 25)(take 25 instruction))).
 cbn[reference_control_expr_1994 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1999 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2000 old old=Some(Gval(Fuint 25)(take 25 instruction))).
 cbn[reference_control_expr_2000 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2005 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2006 old old=Some(Gval(Fuint 25)(take 25 instruction))).
 cbn[reference_control_expr_2006 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 destruct stage as[|stage].
 {
 pose proof(Previous 1%nat ltac:(lia))as Dep.
 destruct lane as[|lane].
 { change(VM.find 1976 old=Some(Gval(Fuint 25)(take 25 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1977 old old=Some(Gval(Fuint 20)(take 20 instruction))).
 cbn[reference_control_expr_1977 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1982 old=Some(Gval(Fuint 25)(take 25 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1983 old old=Some(Gval(Fuint 20)(take 20 instruction))).
 cbn[reference_control_expr_1983 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1988 old=Some(Gval(Fuint 25)(take 25 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1989 old old=Some(Gval(Fuint 20)(take 20 instruction))).
 cbn[reference_control_expr_1989 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1994 old=Some(Gval(Fuint 25)(take 25 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_1995 old old=Some(Gval(Fuint 20)(take 20 instruction))).
 cbn[reference_control_expr_1995 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2000 old=Some(Gval(Fuint 25)(take 25 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2001 old old=Some(Gval(Fuint 20)(take 20 instruction))).
 cbn[reference_control_expr_2001 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2006 old=Some(Gval(Fuint 25)(take 25 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2007 old old=Some(Gval(Fuint 20)(take 20 instruction))).
 cbn[reference_control_expr_2007 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 destruct stage as[|stage].
 {
 pose proof(Previous 2%nat ltac:(lia))as Dep.
 destruct lane as[|lane].
 { change(VM.find 1977 old=Some(Gval(Fuint 20)(take 20 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2332 old old=Some(Gval(Fuint 15)(take 15 instruction))).
 cbn[reference_control_expr_2332 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1983 old=Some(Gval(Fuint 20)(take 20 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2336 old old=Some(Gval(Fuint 15)(take 15 instruction))).
 cbn[reference_control_expr_2336 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1989 old=Some(Gval(Fuint 20)(take 20 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2340 old old=Some(Gval(Fuint 15)(take 15 instruction))).
 cbn[reference_control_expr_2340 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1995 old=Some(Gval(Fuint 20)(take 20 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2344 old old=Some(Gval(Fuint 15)(take 15 instruction))).
 cbn[reference_control_expr_2344 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2001 old=Some(Gval(Fuint 20)(take 20 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2348 old old=Some(Gval(Fuint 15)(take 15 instruction))).
 cbn[reference_control_expr_2348 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2007 old=Some(Gval(Fuint 20)(take 20 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2352 old old=Some(Gval(Fuint 15)(take 15 instruction))).
 cbn[reference_control_expr_2352 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 destruct stage as[|stage].
 {
 pose proof(Previous 3%nat ltac:(lia))as Dep.
 destruct lane as[|lane].
 { change(VM.find 2332 old=Some(Gval(Fuint 15)(take 15 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2333 old old=Some(Gval(Fuint 12)(take 12 instruction))).
 cbn[reference_control_expr_2333 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2336 old=Some(Gval(Fuint 15)(take 15 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2337 old old=Some(Gval(Fuint 12)(take 12 instruction))).
 cbn[reference_control_expr_2337 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2340 old=Some(Gval(Fuint 15)(take 15 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2341 old old=Some(Gval(Fuint 12)(take 12 instruction))).
 cbn[reference_control_expr_2341 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2344 old=Some(Gval(Fuint 15)(take 15 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2345 old old=Some(Gval(Fuint 12)(take 12 instruction))).
 cbn[reference_control_expr_2345 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2348 old=Some(Gval(Fuint 15)(take 15 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2349 old old=Some(Gval(Fuint 12)(take 12 instruction))).
 cbn[reference_control_expr_2349 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2352 old=Some(Gval(Fuint 15)(take 15 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2353 old old=Some(Gval(Fuint 12)(take 12 instruction))).
 cbn[reference_control_expr_2353 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 destruct stage as[|stage].
 {
 pose proof(Previous 4%nat ltac:(lia))as Dep.
 destruct lane as[|lane].
 { change(VM.find 2333 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2334 old old=Some(Gval(Fuint 8)(take 8 instruction))).
 cbn[reference_control_expr_2334 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2337 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2338 old old=Some(Gval(Fuint 8)(take 8 instruction))).
 cbn[reference_control_expr_2338 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2341 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2342 old old=Some(Gval(Fuint 8)(take 8 instruction))).
 cbn[reference_control_expr_2342 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2345 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2346 old old=Some(Gval(Fuint 8)(take 8 instruction))).
 cbn[reference_control_expr_2346 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2349 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2350 old old=Some(Gval(Fuint 8)(take 8 instruction))).
 cbn[reference_control_expr_2350 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2353 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2354 old old=Some(Gval(Fuint 8)(take 8 instruction))).
 cbn[reference_control_expr_2354 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 destruct stage as[|stage].
 {
 pose proof(Previous 5%nat ltac:(lia))as Dep.
 destruct lane as[|lane].
 { change(VM.find 2334 old=Some(Gval(Fuint 8)(take 8 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2335 old old=Some(Gval(Fuint 1)(drop 7(take 8 instruction)))).
 cbn[reference_control_expr_2335 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2338 old=Some(Gval(Fuint 8)(take 8 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2339 old old=Some(Gval(Fuint 1)(drop 7(take 8 instruction)))).
 cbn[reference_control_expr_2339 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2342 old=Some(Gval(Fuint 8)(take 8 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2343 old old=Some(Gval(Fuint 1)(drop 7(take 8 instruction)))).
 cbn[reference_control_expr_2343 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2346 old=Some(Gval(Fuint 8)(take 8 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2347 old old=Some(Gval(Fuint 1)(drop 7(take 8 instruction)))).
 cbn[reference_control_expr_2347 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2350 old=Some(Gval(Fuint 8)(take 8 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2351 old old=Some(Gval(Fuint 1)(drop 7(take 8 instruction)))).
 cbn[reference_control_expr_2351 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2354 old=Some(Gval(Fuint 8)(take 8 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2355 old old=Some(Gval(Fuint 1)(drop 7(take 8 instruction)))).
 cbn[reference_control_expr_2355 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 destruct stage as[|stage].
 {
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2318 old old=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2318 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2319 old old=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2319 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2320 old old=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2320 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2321 old old=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2321 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2322 old old=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2322 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1884 old=Some(Gval(Fuint 32)(instruction)))in Source.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2323 old old=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2323 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 destruct stage as[|stage].
 {
 pose proof(Previous 0%nat ltac:(lia))as Dep.
 destruct lane as[|lane].
 { change(VM.find 1975 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2371 old old=Some(Gval(Fuint 6)(drop 25(take 31 instruction)))).
 cbn[reference_control_expr_2371 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1981 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2372 old old=Some(Gval(Fuint 6)(drop 25(take 31 instruction)))).
 cbn[reference_control_expr_2372 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1987 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2373 old old=Some(Gval(Fuint 6)(drop 25(take 31 instruction)))).
 cbn[reference_control_expr_2373 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1993 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2374 old old=Some(Gval(Fuint 6)(drop 25(take 31 instruction)))).
 cbn[reference_control_expr_2374 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 1999 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2375 old old=Some(Gval(Fuint 6)(drop 25(take 31 instruction)))).
 cbn[reference_control_expr_2375 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2005 old=Some(Gval(Fuint 31)(take 31 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2376 old old=Some(Gval(Fuint 6)(drop 25(take 31 instruction)))).
 cbn[reference_control_expr_2376 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 destruct stage as[|stage].
 {
 pose proof(Previous 4%nat ltac:(lia))as Dep.
 destruct lane as[|lane].
 { change(VM.find 2333 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2386 old old=Some(Gval(Fuint 4)(drop 8(take 12 instruction)))).
 cbn[reference_control_expr_2386 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2337 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2387 old old=Some(Gval(Fuint 4)(drop 8(take 12 instruction)))).
 cbn[reference_control_expr_2387 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2341 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2388 old old=Some(Gval(Fuint 4)(drop 8(take 12 instruction)))).
 cbn[reference_control_expr_2388 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2345 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2389 old old=Some(Gval(Fuint 4)(drop 8(take 12 instruction)))).
 cbn[reference_control_expr_2389 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2349 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2390 old old=Some(Gval(Fuint 4)(drop 8(take 12 instruction)))).
 cbn[reference_control_expr_2390 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 destruct lane as[|lane].
 { change(VM.find 2353 old=Some(Gval(Fuint 12)(take 12 instruction)))in Dep.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_2391 old old=Some(Gval(Fuint 4)(drop 8(take 12 instruction)))).
 cbn[reference_control_expr_2391 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Dep;cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }
 lia. }
 lia.
Qed.
Theorem branch_raw_fields_history inputs path history limit reset time instruction lane :
 (lane<6)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 forall stage,(stage<10)%coq_nat ->VM.find(branch_raw_node stage lane)(history time)=Some(Gval(Fuint(branch_raw_width stage))(branch_raw_word stage instruction)).
Proof.
 intros Lane Resets Steps Lower Upper Source stage. induction stage using lt_wf_ind;intro Stage.
 eapply(reference_immediate_value_history (branch_raw_index stage lane) inputs path history limit reset time);[apply branch_raw_bound;assumption|exact Resets|exact Steps|exact Lower|exact Upper|].
 eapply(branch_raw_eval stage lane _ _ instruction Stage Lane Source). intros previous Before;apply H;lia.
Qed.
(* Branch selection and assembly. *)
Require Import DUTRedirectDecode ReferenceLoadImmediate.
Lemma immediate_selected_expression_mux invalid old guard yes no width word bit :
 size word=width ->VM.find guard old=Some(Gval(Fuint 1)[::bit]) ->
 (forall site,eval_hfexpr_validif_policy invalid site flat_memories(if bit then yes else no)old old=Some(Gval(Fuint width)word)) ->
 eval_type_of_expr(if bit then no else yes)old=Some(Gtyp(Fuint width)) ->
 forall site,eval_hfexpr_validif_policy invalid site flat_memories
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T guard)) yes no)old old=Some(Gval(Fuint width)word).
Proof.
 intros Size Guard Selected Other site. cbn[eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Guard.
 destruct bit;cbn;rewrite Selected Other;
 change(adapt_hvalue_as_type(Gval(Fuint width)word)(Gtyp(Fuint(maxn width width)))=Some(Gval(Fuint width)word));rewrite maxnn;apply dut_decode_adapt;exact Size.
Qed.
Theorem immediate_stable_expression_suffix invalid old count selected width word prefix (node guard:nat->VarOrder.T)(yes:nat->hfexpr VarOrder.T) :
 (selected<count)%coq_nat ->size word=width ->
 (forall n,(n<count)%coq_nat ->forall value,
 (forall site,eval_hfexpr_validif_policy invalid site flat_memories
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T(guard n)))(yes n)
 (match n with O=>prefix|S before=>@Eref VarOrder.T (@Eid VarOrder.T(node before))end))old old=Some(Gval(Fuint width)value)) ->
 VM.find(node n)old=Some(Gval(Fuint width)value)) ->
 (forall n,(n<count)%coq_nat ->VM.find(guard n)old=Some(Gval(Fuint 1)[::Nat.eqb n selected])) ->
 (forall n,(n<count)%coq_nat ->eval_type_of_expr(yes n)old=Some(Gtyp(Fuint width))) ->
 (forall n,(n<count)%coq_nat ->eval_type_of_expr(match n with O=>prefix|S before=>@Eref VarOrder.T (@Eid VarOrder.T(node before))end)old=Some(Gtyp(Fuint width))) ->
 (forall site,eval_hfexpr_validif_policy invalid site flat_memories(yes selected)old old=Some(Gval(Fuint width)word)) ->
 forall n,(selected<=n)%coq_nat ->(n<count)%coq_nat ->VM.find(node n)old=Some(Gval(Fuint width)word).
Proof.
 intros Selected Size Node Guard YesType NoType Source n. induction n as[|n IH];intros Lower Upper.
 - assert(Equal:selected=0%nat)by lia;subst selected. apply(Node 0%nat Upper word).
   eapply(immediate_selected_expression_mux _ _ _ _ _ _ word true);[exact Size|exact(Guard 0%nat Upper)|exact Source|exact(NoType 0%nat Upper)].
 - destruct(Nat.eq_dec selected(S n))as[Equal|Different].
   + subst selected. apply(Node(S n)Upper word).
     eapply(immediate_selected_expression_mux _ _ _ _ _ _ word true);[exact Size|rewrite <-(Nat.eqb_refl(S n));exact(Guard(S n)Upper)|exact Source|exact(NoType(S n)Upper)].
   + pose proof(IH ltac:(lia)ltac:(lia))as Previous. apply(Node(S n)Upper word).
     eapply(immediate_selected_expression_mux _ _ _ _ _ _ word false);[exact Size|rewrite(Guard(S n)Upper)(proj2(Nat.eqb_neq(S n)selected)ltac:(lia));reflexivity|intro site;exact Previous|exact(YesType(S n)Upper)].
Qed.
(* Four branch field selections. *)
Definition branch_field_stage group :=nth 0%nat [::7%nat;6%nat;8%nat;9%nat]group.
Definition branch_field_width group :=branch_raw_width(branch_field_stage group).
Definition branch_field_word group instruction :=branch_raw_word(branch_field_stage group)instruction.
Definition branch_field_index group n :=nth 0%nat(nth [::][::[::115%nat;116%nat;117%nat;118%nat;119%nat;120%nat];[::151%nat;152%nat;153%nat;154%nat;155%nat;156%nat];[::166%nat;167%nat;168%nat;169%nat;170%nat;171%nat];[::181%nat;182%nat;183%nat;184%nat;185%nat;186%nat]]group)n.
Definition branch_field_yes_index group n :=nth 0%nat(nth [::][::[::114%nat;113%nat;112%nat;111%nat;110%nat;109%nat];[::146%nat;142%nat;138%nat;134%nat;130%nat;126%nat];[::165%nat;164%nat;163%nat;162%nat;161%nat;160%nat];[::180%nat;179%nat;178%nat;177%nat;176%nat;175%nat]]group)n.
Definition branch_field_node group n :=reference_immediate_node(branch_field_index group n).
Definition branch_field_yes group n :=reference_immediate_node(branch_field_yes_index group n).
Definition branch_field_guard n : VarOrder.T :=nth 0 [::2004;1998;1992;1986;1980;1974]n.
Definition branch_field_prefix group :=if Nat.eqb group 1 then @Eref VarOrder.T (@Eid VarOrder.T 2361)
 else @Econst VarOrder.T (Fuint(branch_field_width group))(nseq(branch_field_width group)false).
Lemma branch_field_metadata group n : (group<4)%coq_nat ->(n<6)%coq_nat ->
 (branch_field_index group n<304)%coq_nat /\(branch_field_yes_index group n<304)%coq_nat /\
 reference_immediate_width(branch_field_index group n)=branch_field_width group /\
 reference_immediate_width(branch_field_yes_index group n)=branch_field_width group /\
 reference_immediate_expression(branch_field_index group n)=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T(branch_field_guard n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(branch_field_yes group n)))
 (match n with O=>branch_field_prefix group|S before=>@Eref VarOrder.T (@Eid VarOrder.T(branch_field_node group before))end).
Proof. do 4(destruct group as[|group];[do 6(destruct n as[|n];[vm_compute;intuition lia|]);lia|]);lia. Qed.
Lemma branch_field_selected group lane : (group<4)%coq_nat ->(lane<6)%coq_nat ->
 (branch_field_stage group<10)%coq_nat /\branch_field_yes group(Nat.sub 5 lane)=branch_raw_node(branch_field_stage group)lane.
Proof. do 4(destruct group as[|group];[do 6(destruct lane as[|lane];[vm_compute;intuition lia|]);lia|]);lia. Qed.
Lemma branch_field_size group instruction : (group<4)%coq_nat ->size instruction=32%nat ->size(branch_field_word group instruction)=branch_field_width group.
Proof. intros Group Size. do 4(destruct group as[|group];[cbn[branch_field_word branch_field_width branch_field_stage branch_raw_word branch_raw_width nth];rewrite size_drop size_take Size;reflexivity|]);lia. Qed.
Lemma immediate_ref_type old node width value : VM.find node old=Some value ->type_of_val value=Gtyp(Fuint width) ->
 eval_type_of_expr(@Eref VarOrder.T (@Eid VarOrder.T node))old=Some(Gtyp(Fuint width)).
Proof. intros Lookup Typed. unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Lookup;cbn[option_map];rewrite Typed;reflexivity. Qed.
Theorem branch_field_mux_history group lane inputs path history limit reset time instruction :
 (group<4)%coq_nat ->(lane<6)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])) ->
 VM.find(branch_field_node group 5)(history time)=Some(Gval(Fuint(branch_field_width group))(branch_field_word group instruction)).
Proof.
 intros Group Lane Size Resets Steps Source Lower Upper Guards.
 assert(TypedSource:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)).
 { intros t L U;exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 eapply(immediate_stable_expression_suffix (isolated_validif_policy(formal_invalid_policy inputs path))(history time)6(Nat.sub 5 lane)(branch_field_width group)(branch_field_word group instruction)(branch_field_prefix group)(branch_field_node group)branch_field_guard(fun n=>@Eref VarOrder.T (@Eid VarOrder.T(branch_field_yes group n))));[lia|apply branch_field_size;assumption| |exact Guards| | | |lia|lia].
 - intros n Bound value Eval. destruct(branch_field_metadata group n Group Bound)as[IB[YB[Width[YesWidth Expr]]]].
 eapply(reference_immediate_value_history (branch_field_index group n) inputs path history limit reset time);[exact IB|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;rewrite Expr;apply Eval.
 - intros n Bound. destruct(branch_field_metadata group n Group Bound)as[IB[YB[Width[YesWidth Expr]]]].
 destruct(reference_immediate_typed_history (branch_field_yes_index group n) _ history limit time YB Steps TypedSource Lower ltac:(lia))as[value[Lookup Typed]].
 eapply immediate_ref_type;[exact Lookup|rewrite YesWidth in Typed;exact Typed].
 - intros n Bound. destruct n as[|n].
   + destruct group as[|[|[|[|group]]]];[vm_compute;reflexivity| |vm_compute;reflexivity|vm_compute;reflexivity|lia].
     destruct(reference_immediate_typed_history 150 _ history limit time ltac:(lia) Steps TypedSource Lower ltac:(lia))as[value[Lookup Typed]].
     eapply immediate_ref_type;[exact Lookup|exact Typed].
   + destruct(branch_field_metadata group n Group ltac:(lia))as[IB[YB[Width[YesWidth Expr]]]].
     destruct(reference_immediate_typed_history (branch_field_index group n) _ history limit time IB Steps TypedSource Lower ltac:(lia))as[value[Lookup Typed]].
     eapply immediate_ref_type;[exact Lookup|rewrite Width in Typed;exact Typed].
 - intro site. destruct(branch_field_selected group lane Group Lane)as[Stage Selected].
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Selected.
 exact(branch_raw_fields_history inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper ltac:(apply Source;lia)(branch_field_stage group)Stage).
Qed.
(* Branch field enable. *)
Definition branch_field_output group : VarOrder.T :=nth 0 [::2331;2369;2384;2399]group.
Theorem branch_field_output_history group lane inputs path history limit reset time instruction :
 (group<4)%coq_nat ->(lane<6)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])) ->
 VM.find(branch_field_output group)(history time)=Some(Gval(Fuint(branch_field_width group))(branch_field_word group instruction)).
Proof.
 intros Group Lane Size Resets Steps Source Lower Upper Enabled Guards.
 pose proof(branch_field_mux_history group lane inputs path history limit reset time instruction Group Lane Size Resets Steps Source Lower Upper Guards)as Final.
 pose proof(branch_field_size group instruction Group Size)as WordSize.
 destruct group as[|group].
 { change(VM.find 2329(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction))))in Final.
 assert(Value:VM.find 2330(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 { eapply(reference_immediate_value_history 121 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2330(history time)(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2330 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Final.
 change(adapt_hvalue_as_type(Gval(Fuint 1)(drop 31(take 32 instruction)))(Gtyp(Fuint 1))=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))). apply dut_decode_adapt;exact WordSize. }
 eapply(reference_immediate_value_history 122 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Value. }
 destruct group as[|group].
 { change(VM.find 2367(history time)=Some(Gval(Fuint 1)(drop 7(take 8 instruction))))in Final.
 assert(Value:VM.find 2368(history time)=Some(Gval(Fuint 1)(drop 7(take 8 instruction)))).
 { eapply(reference_immediate_value_history 157 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2368(history time)(history time)=Some(Gval(Fuint 1)(drop 7(take 8 instruction)))).
 cbn[reference_control_expr_2368 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Final.
 change(adapt_hvalue_as_type(Gval(Fuint 1)(drop 7(take 8 instruction)))(Gtyp(Fuint 1))=Some(Gval(Fuint 1)(drop 7(take 8 instruction)))). apply dut_decode_adapt;exact WordSize. }
 eapply(reference_immediate_value_history 158 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Value. }
 destruct group as[|group].
 { change(VM.find 2382(history time)=Some(Gval(Fuint 6)(drop 25(take 31 instruction))))in Final.
 assert(Value:VM.find 2383(history time)=Some(Gval(Fuint 6)(drop 25(take 31 instruction)))).
 { eapply(reference_immediate_value_history 172 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2383(history time)(history time)=Some(Gval(Fuint 6)(drop 25(take 31 instruction)))).
 cbn[reference_control_expr_2383 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Final.
 change(adapt_hvalue_as_type(Gval(Fuint 6)(drop 25(take 31 instruction)))(Gtyp(Fuint 6))=Some(Gval(Fuint 6)(drop 25(take 31 instruction)))). apply dut_decode_adapt;exact WordSize. }
 eapply(reference_immediate_value_history 173 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Value. }
 destruct group as[|group].
 { change(VM.find 2397(history time)=Some(Gval(Fuint 4)(drop 8(take 12 instruction))))in Final.
 assert(Value:VM.find 2398(history time)=Some(Gval(Fuint 4)(drop 8(take 12 instruction)))).
 { eapply(reference_immediate_value_history 187 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2398(history time)(history time)=Some(Gval(Fuint 4)(drop 8(take 12 instruction)))).
 cbn[reference_control_expr_2398 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Final.
 change(adapt_hvalue_as_type(Gval(Fuint 4)(drop 8(take 12 instruction)))(Gtyp(Fuint 4))=Some(Gval(Fuint 4)(drop 8(take 12 instruction)))). apply dut_decode_adapt;exact WordSize. }
 eapply(reference_immediate_value_history 188 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Value. }
 lia.
Qed.
(* Parameterized branch assembly. *)
Require Import ReferenceControlNodeCongruence1 ReferenceControlNodeCertificates1 ReferenceControlStabilityHistory ReferenceRedirectSpine ReferenceLoadSemantics.
Definition branch_assembly_node lane stage : VarOrder.T :=nth 0(nth [::][::[::2370;2385;2400;2401;2402;2403;2404;2405];[::2406;2407;2408;2409;2410;2411;2412;2413];[::2414;2415;2416;2417;2418;2419;2420;2421];[::2422;2423;2424;2425;2426;2427;2428;2429];[::2430;2431;2432;2433;2434;2435;2436;2437];[::2438;2439;2440;2441;2442;2443;2444;2445]]lane)stage.
Definition branch_assembly_expression lane stage :=nth (@Econst VarOrder.T(Fuint 1)[::false])[::(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 2331)) (@Eref VarOrder.T (@Eid VarOrder.T 2369)));(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T (branch_assembly_node lane 0))) (@Eref VarOrder.T (@Eid VarOrder.T 2384)));(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 2399)) (@Econst VarOrder.T (Fuint 1)[::false]));(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T (branch_assembly_node lane 1))) (@Eref VarOrder.T (@Eid VarOrder.T (branch_assembly_node lane 2))));(@Eprim_unop VarOrder.T(Uextr 12 12)(@Eref VarOrder.T (@Eid VarOrder.T (branch_assembly_node lane 3))));(@Eprim_unop VarOrder.T(Uextr 0 0)(@Eref VarOrder.T (@Eid VarOrder.T (branch_assembly_node lane 4))));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (branch_assembly_node lane 5))) (@Econst VarOrder.T(Fuint 19)(nseq 19 true))(@Econst VarOrder.T(Fuint 19)(nseq 19 false)));(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T (branch_assembly_node lane 6))) (@Eref VarOrder.T (@Eid VarOrder.T (branch_assembly_node lane 3))))]stage.
Lemma branch_assembly_member lane stage : (lane<6)%coq_nat ->(stage<8)%coq_nat ->
 List.In(branch_assembly_node lane stage,branch_assembly_expression lane stage)reference_control_1_nodes.
Proof.
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[intros;exact reference_control_member_2370|].
 destruct stage as[|stage];[intros;exact reference_control_member_2385|].
 destruct stage as[|stage];[intros;exact reference_control_member_2400|].
 destruct stage as[|stage];[intros;exact reference_control_member_2401|].
 destruct stage as[|stage];[intros;exact reference_control_member_2402|].
 destruct stage as[|stage];[intros;exact reference_control_member_2403|].
 destruct stage as[|stage];[intros;exact reference_control_member_2404|].
 destruct stage as[|stage];[intros;exact reference_control_member_2405|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[intros;exact reference_control_member_2406|].
 destruct stage as[|stage];[intros;exact reference_control_member_2407|].
 destruct stage as[|stage];[intros;exact reference_control_member_2408|].
 destruct stage as[|stage];[intros;exact reference_control_member_2409|].
 destruct stage as[|stage];[intros;exact reference_control_member_2410|].
 destruct stage as[|stage];[intros;exact reference_control_member_2411|].
 destruct stage as[|stage];[intros;exact reference_control_member_2412|].
 destruct stage as[|stage];[intros;exact reference_control_member_2413|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[intros;exact reference_control_member_2414|].
 destruct stage as[|stage];[intros;exact reference_control_member_2415|].
 destruct stage as[|stage];[intros;exact reference_control_member_2416|].
 destruct stage as[|stage];[intros;exact reference_control_member_2417|].
 destruct stage as[|stage];[intros;exact reference_control_member_2418|].
 destruct stage as[|stage];[intros;exact reference_control_member_2419|].
 destruct stage as[|stage];[intros;exact reference_control_member_2420|].
 destruct stage as[|stage];[intros;exact reference_control_member_2421|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[intros;exact reference_control_member_2422|].
 destruct stage as[|stage];[intros;exact reference_control_member_2423|].
 destruct stage as[|stage];[intros;exact reference_control_member_2424|].
 destruct stage as[|stage];[intros;exact reference_control_member_2425|].
 destruct stage as[|stage];[intros;exact reference_control_member_2426|].
 destruct stage as[|stage];[intros;exact reference_control_member_2427|].
 destruct stage as[|stage];[intros;exact reference_control_member_2428|].
 destruct stage as[|stage];[intros;exact reference_control_member_2429|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[intros;exact reference_control_member_2430|].
 destruct stage as[|stage];[intros;exact reference_control_member_2431|].
 destruct stage as[|stage];[intros;exact reference_control_member_2432|].
 destruct stage as[|stage];[intros;exact reference_control_member_2433|].
 destruct stage as[|stage];[intros;exact reference_control_member_2434|].
 destruct stage as[|stage];[intros;exact reference_control_member_2435|].
 destruct stage as[|stage];[intros;exact reference_control_member_2436|].
 destruct stage as[|stage];[intros;exact reference_control_member_2437|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[intros;exact reference_control_member_2438|].
 destruct stage as[|stage];[intros;exact reference_control_member_2439|].
 destruct stage as[|stage];[intros;exact reference_control_member_2440|].
 destruct stage as[|stage];[intros;exact reference_control_member_2441|].
 destruct stage as[|stage];[intros;exact reference_control_member_2442|].
 destruct stage as[|stage];[intros;exact reference_control_member_2443|].
 destruct stage as[|stage];[intros;exact reference_control_member_2444|].
 destruct stage as[|stage];[intros;exact reference_control_member_2445|].
 lia. }
 lia.
Qed.
Lemma branch_assembly_stable lane stage inputs path history limit reset time :
 (lane<6)%coq_nat ->(stage<8)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find(branch_assembly_node lane stage)(history time)=VM.find(branch_assembly_node lane stage)(history(S time)).
Proof.
 intros Lane Stage Resets Steps Lower Upper.
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[exact(reference_control_stable_2370_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2385_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2400_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2401_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2402_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2403_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2404_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2405_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[exact(reference_control_stable_2406_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2407_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2408_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2409_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2410_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2411_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2412_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2413_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[exact(reference_control_stable_2414_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2415_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2416_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2417_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2418_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2419_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2420_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2421_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[exact(reference_control_stable_2422_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2423_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2424_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2425_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2426_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2427_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2428_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2429_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[exact(reference_control_stable_2430_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2431_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2432_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2433_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2434_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2435_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2436_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2437_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 lia. }
 destruct lane as[|lane].
 {
 destruct stage as[|stage];[exact(reference_control_stable_2438_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2439_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2440_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2441_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2442_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2443_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2444_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 destruct stage as[|stage];[exact(reference_control_stable_2445_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].
 lia. }
 lia.
Qed.
Theorem branch_assembly_value lane stage inputs path history limit reset time width word :
 (lane<6)%coq_nat ->(stage<8)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(branch_assembly_expression lane stage)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(branch_assembly_node lane stage)(history time)=Some(Gval(Fuint width)word).
Proof.
 intros Lane Stage Resets Steps Lower Upper Eval.
 rewrite(branch_assembly_stable lane stage inputs path history limit reset time Lane Stage Resets Steps Lower Upper).
 eapply(reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes _ (branch_assembly_expression lane stage));[exact reference_control_1_positions|exact reference_control_1_safety|apply branch_assembly_member;assumption|exact Eval|apply Steps;lia].
Qed.
Theorem branch_assembly_history lane inputs path history limit reset time sign bit high low :
 (lane<6)%coq_nat ->size sign=1%nat ->size bit=1%nat ->size high=6%nat ->size low=4%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 2331(history time)=Some(Gval(Fuint 1)sign) ->VM.find 2369(history time)=Some(Gval(Fuint 1)bit) ->
 VM.find 2384(history time)=Some(Gval(Fuint 6)high) ->VM.find 2399(history time)=Some(Gval(Fuint 4)low) ->
 VM.find(branch_assembly_node lane 7)(history time)=Some(Gval(Fuint 32)(sext_to 32(([::false]++low)++(high++(bit++sign))))).
Proof.
 intros Lane SignSize BitSize HighSize LowSize Resets Steps Lower Upper Sign Bit High Low.
 set(payload:=([::false]++low)++(high++(bit++sign))).
 assert(Size:size payload=13%nat)by(unfold payload;repeat rewrite size_cat;rewrite SignSize BitSize HighSize LowSize;reflexivity).
 assert(V0:VM.find(branch_assembly_node lane 0)(history time)=Some(Gval(Fuint 2)(bit++sign))).
 { eapply(branch_assembly_value lane 0 inputs path history limit reset time);[exact Lane|lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[branch_assembly_expression nth eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Sign Bit. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity. }
 assert(V1:VM.find(branch_assembly_node lane 1)(history time)=Some(Gval(Fuint 8)(high++(bit++sign)))).
 { eapply(branch_assembly_value lane 1 inputs path history limit reset time);[exact Lane|lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[branch_assembly_expression nth eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0 High. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity. }
 assert(V2:VM.find(branch_assembly_node lane 2)(history time)=Some(Gval(Fuint 5)([::false]++low))).
 { eapply(branch_assembly_value lane 2 inputs path history limit reset time);[exact Lane|lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[branch_assembly_expression nth eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity. }
 assert(V3:VM.find(branch_assembly_node lane 3)(history time)=Some(Gval(Fuint 13)(payload))).
 { eapply(branch_assembly_value lane 3 inputs path history limit reset time);[exact Lane|lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[branch_assembly_expression nth eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1 V2. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity. }
 assert(V4:VM.find(branch_assembly_node lane 4)(history time)=Some(Gval(Fuint 1)([::msb payload]))).
 { eapply(branch_assembly_value lane 4 inputs path history limit reset time);[exact Lane|lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[branch_assembly_expression nth eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V3. change(Some(Gval(Fuint 1)(drop(13-1)%nat(take 13 payload)))=Some(Gval(Fuint 1)[::msb payload])). rewrite(reference_load_sign_bit 13 payload Size(eq_refl true));reflexivity. }
 assert(V5:VM.find(branch_assembly_node lane 5)(history time)=Some(Gval(Fuint 1)([::msb payload]))).
 { eapply(branch_assembly_value lane 5 inputs path history limit reset time);[exact Lane|lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[branch_assembly_expression nth eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V4;destruct(msb payload);reflexivity. }
 assert(V6:VM.find(branch_assembly_node lane 6)(history time)=Some(Gval(Fuint 19)(nseq 19(msb payload)))).
 { eapply(branch_assembly_value lane 6 inputs path history limit reset time);[exact Lane|lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[branch_assembly_expression nth eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V5;destruct(msb payload);reflexivity. }
 assert(V7:VM.find(branch_assembly_node lane 7)(history time)=Some(Gval(Fuint 32)(sext_to 32 payload))).
 { eapply(branch_assembly_value lane 7 inputs path history limit reset time);[exact Lane|lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[branch_assembly_expression nth eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V6 V3. unfold eval_binop;try rewrite immediate_cat_no_absorbing. change(Some(Gval(Fuint 32)(payload++nseq 19(msb payload)))=Some(Gval(Fuint 32)(sext_to 32 payload))). unfold sext_to,sext;rewrite Size;reflexivity. }
 exact V7.
Qed.
(* Final branch composition. *)
Require Import DUTImmediateModes.
Definition branch_final_index n :=nth 0%nat[::285%nat;286%nat;287%nat;288%nat;289%nat;290%nat]n.
Definition branch_final_node n :=reference_immediate_node(branch_final_index n).
Definition branch_final_yes_index n :=nth 0%nat[::222%nat;216%nat;210%nat;204%nat;198%nat;192%nat]n.
Definition branch_final_yes n :=reference_immediate_node(branch_final_yes_index n).
Lemma branch_final_metadata n : (n<6)%coq_nat ->
 (branch_final_index n<304)%coq_nat /\(branch_final_yes_index n<304)%coq_nat /\
 reference_immediate_width(branch_final_index n)=32%nat /\reference_immediate_width(branch_final_yes_index n)=32%nat /\
 reference_immediate_expression(branch_final_index n)=@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T(branch_field_guard n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(branch_final_yes n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(match n with O=>2533|S before=>branch_final_node before end))).
Proof. do 6(destruct n as[|n];[vm_compute;intuition lia|]);lia. Qed.
Lemma branch_final_selected lane : (lane<6)%coq_nat ->branch_final_yes(Nat.sub 5 lane)=branch_assembly_node lane 7.
Proof. do 6(destruct lane as[|lane];[reflexivity|]);lia. Qed.
Lemma branch_upper_metadata n : (n<11)%coq_nat ->
 (jal_final_index(Nat.add 7 n)<304)%coq_nat /\
 reference_immediate_node(jal_final_index(Nat.add 7 n))=load_imm_mux_node true n /\
 reference_immediate_expression(jal_final_index(Nat.add 7 n))=load_imm_mux_expression true n.
Proof. do 11(destruct n as[|n];[vm_compute;intuition lia|]);lia. Qed.
Theorem reference_branch_final_history lane inputs path history limit reset time word :
 (lane<6)%coq_nat ->size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])) ->
 (forall n,(n<11)%coq_nat ->VM.find(load_imm_mux_guard true n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find(branch_assembly_node lane 7)(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards UpperGuards Selected.
 assert(Start:VM.find 2539(history time)=Some(Gval(Fuint 32)word)).
 { change(VM.find(branch_final_node 5)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history time)6(Nat.sub 5 lane)32 word 2533 branch_final_node branch_field_guard branch_final_yes);[lia|exact Size|intros;reflexivity| |exact Guards| | | |lia|lia].
 - intros n Bound value Eval. destruct(branch_final_metadata n Bound)as[IB[YB[Width[YesWidth Expr]]]].
   eapply(reference_immediate_value_history (branch_final_index n)inputs path history limit reset time);[exact IB|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;rewrite Expr;apply Eval.
 - intros n Bound. destruct(branch_final_metadata n Bound)as[IB[YB[Width[YesWidth Expr]]]].
   pose proof(reference_immediate_typed_history(branch_final_yes_index n)_ history limit time YB Steps Source Lower ltac:(lia))as Typed. rewrite YesWidth in Typed;exact Typed.
 - intros n Bound. destruct n as[|n].
   + exact(reference_immediate_typed_history 284 _ history limit time ltac:(lia) Steps Source Lower ltac:(lia)).
   + destruct(branch_final_metadata n ltac:(lia))as[IB[YB[Width[YesWidth Expr]]]].
     pose proof(reference_immediate_typed_history(branch_final_index n)_ history limit time IB Steps Source Lower ltac:(lia))as Typed. rewrite Width in Typed;exact Typed.
 - rewrite(branch_final_selected lane Lane);exact Selected. }
 assert(Final:VM.find 2550(history time)=Some(Gval(Fuint 32)word)).
 { change(VM.find(load_imm_mux_node true 10)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_fallback (formal_invalid_policy inputs path)(history time)(history time)11 32 word 2539(load_imm_mux_node true)(load_imm_mux_guard true)(load_imm_mux_yes true));[exact Size|intros;reflexivity| |exact UpperGuards| |exact Start|lia].
 - intros n Bound value Eval. destruct(branch_upper_metadata n Bound)as[IB[Node Expr]]. rewrite <-Node.
   eapply(reference_immediate_value_history (jal_final_index(Nat.add 7 n))inputs path history limit reset time);[exact IB|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;rewrite Expr;apply Eval.
 - intros n Bound. exact(proj1(load_imm_mux_branch_types true n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(EnabledValue:VM.find 2551(history time)=Some(Gval(Fuint 32)word)).
 { eapply(load_imm_aux_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Final.
 change(adapt_hvalue_as_type(Gval(Fuint 32)word)(Gtyp(Fuint 32))=Some(Gval(Fuint 32)word));apply dut_decode_adapt;exact Size. }
 eapply(load_imm_aux_value 28 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact EnabledValue.
Qed.
Theorem reference_branch_immediate_history lane inputs path history limit reset time instruction :
 (lane<6)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])) ->
 (forall n,(n<11)%coq_nat ->VM.find(load_imm_mux_guard true n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)(dut_b_immediate instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards UpperGuards.
 pose proof(branch_field_output_history 0 lane inputs path history limit reset time instruction ltac:(lia) Lane Size Resets Steps Source Lower Upper Enabled Guards)as Sign.
 pose proof(branch_field_output_history 1 lane inputs path history limit reset time instruction ltac:(lia) Lane Size Resets Steps Source Lower Upper Enabled Guards)as Bit.
 pose proof(branch_field_output_history 2 lane inputs path history limit reset time instruction ltac:(lia) Lane Size Resets Steps Source Lower Upper Enabled Guards)as High.
 pose proof(branch_field_output_history 3 lane inputs path history limit reset time instruction ltac:(lia) Lane Size Resets Steps Source Lower Upper Enabled Guards)as Low.
 pose proof(branch_assembly_history lane inputs path history limit reset time (drop 31(take 32 instruction))(drop 7(take 8 instruction))(drop 25(take 31 instruction))(drop 8(take 12 instruction))Lane
 ltac:(rewrite size_drop size_take Size;reflexivity)ltac:(rewrite size_drop size_take Size;reflexivity)ltac:(rewrite size_drop size_take Size;reflexivity)ltac:(rewrite size_drop size_take Size;reflexivity)
 Resets Steps Lower Upper Sign Bit High Low)as Value.
 eapply(reference_branch_final_history lane inputs path history limit reset time);[exact Lane|exact(dut_imm_result_size 2 instruction ltac:(lia) Size)|exact Resets|exact Steps| |exact Lower|exact Upper|exact Enabled|exact Guards|exact UpperGuards|exact Value].
 intros t L U;exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity].
Qed.
(* Branch observed interface. *)
Require Import ReferenceIllegalObserved JointUpdateBoundaryHistory RFScalarControl ReferenceInstructionDecode FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete LoadPipelineClassification LoadTypeCorrespondence ReferenceMemoryRequest MemoryRequestObservedSemantics.
Definition reference_branch_match (instruction:bits) lane :=N.land(to_N instruction)(reference_instruction_mask(Nat.sub 28 lane))=reference_instruction_code(Nat.sub 28 lane).
Lemma branch_reference_enabled_observed lane memory inputs k observed instruction :
 (lane<6)%coq_nat ->generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->reference_branch_match instruction lane ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Lane Observe Legal Reset Instruction Match.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Late Nop]]. destruct bit.
 - specialize(Nop(Logic.eq_refl _)). rewrite Nop in Instruction. inversion Instruction;subst instruction.
 do 6(destruct lane as[|lane];[vm_compute in Match;discriminate|]);lia.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late).
Qed.
Lemma branch_field_guard_decoder n : (n<6)%coq_nat ->branch_field_guard n=reference_instruction_guard(Nat.add 23 n).
Proof. do 6(destruct n as[|n];[reflexivity|]);lia. Qed.
Lemma branch_upper_guard_decoder n : (n<11)%coq_nat ->load_imm_mux_guard true n=reference_instruction_guard(Nat.add 29 n).
Proof. do 11(destruct n as[|n];[reflexivity|]);lia. Qed.
Lemma branch_decode_lane lane n : (lane<6)%coq_nat ->(n<6)%coq_nat ->Nat.eqb(Nat.add 23 n)(Nat.sub 28 lane)=Nat.eqb n(Nat.sub 5 lane).
Proof. do 6(destruct lane as[|lane];[do 6(destruct n as[|n];[reflexivity|]);lia|]);lia. Qed.
Theorem reference_branch_immediate_observed lane memory inputs k observed instruction :
 (lane<6)%coq_nat ->generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 reference_branch_match instruction lane ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(dut_b_immediate instruction)).
Proof.
 intros Lane Observe Legal Reset Instruction Match.
 pose proof(branch_reference_enabled_observed lane memory inputs k observed instruction Lane Observe Legal Reset Instruction Match)as Enabled.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Inst:forall t,(t<=9259)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite <-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Instruction. }
 assert(Enable:forall t,(195<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::true])).
 { intros t Lower Upper. rewrite(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat ltac:(lia)ltac:(lia)Upper ltac:(lia)) Last;exact Enabled. }
 assert(Source:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Lower Upper. exact(memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert(Decode:forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb row(Nat.sub 28 lane)])).
 { intros row Row.
 pose proof(reference_instruction_decode_history (formal_invalid_policy(generated_observation_input inputs k)nil)(fun t=>history(Nat.add 9248 t))2 instruction row Row
 ltac:(intros i I;destruct i as[|[|i]];[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia])
 ltac:(intros i I;destruct i as[|[|[|i]]];[apply Source;vm_compute;lia|apply Source;vm_compute;lia|apply Source;vm_compute;lia|lia])
 2 ltac:(lia)ltac:(lia))as Value.
 change(VM.find(reference_instruction_guard row)(history 9250%nat)=Some(Gval(Fuint 1)[::N.eqb(reference_instruction_code row)(N.land(to_N instruction)(reference_instruction_mask row))]))in Value.
 rewrite(rf_reference_decode_onehot instruction (Nat.sub 28 lane) row ltac:(lia) Row Match)in Value;exact Value. }
 assert(Guards:forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])).
 { intros n Bound. rewrite(branch_field_guard_decoder n Bound)(Decode(Nat.add 23 n)ltac:(lia))(branch_decode_lane lane n Lane Bound);reflexivity. }
 assert(UpperGuards:forall n,(n<11)%coq_nat ->VM.find(load_imm_mux_guard true n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 { intros n Bound. rewrite(branch_upper_guard_decoder n Bound)(Decode(Nat.add 29 n)ltac:(lia)). rewrite(proj2(Nat.eqb_neq(Nat.add 29 n)(Nat.sub 28 lane))ltac:(lia));reflexivity. }
 pose proof(reference_branch_immediate_history lane (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)
 (Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Guards UpperGuards)as Value.
 rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)) Last in Value;exact Value.
Qed.

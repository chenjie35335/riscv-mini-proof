Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate FormalTypedNodeEquation FormalGroundNodeEquation ReferenceLoadArithmetic.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_load_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(3348,(@Eref VarOrder.T (@Eid VarOrder.T 2209)));(3349,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3348)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(3350,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3349))));(3351,(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3350))));(3352,(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3351))));(3353,(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3352))));(3354,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true])));(3355,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true])));(3356,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true])));(3357,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true])));(3358,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3357)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])));(3359,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3356)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3358))));(3360,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3355)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3359))));(3361,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3354)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3360))));(3362,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3353)) (@Eref VarOrder.T (@Eid VarOrder.T 3361))));(3363,(@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 3362))));(3364,(@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 16) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3363))));(3365,(@Eref VarOrder.T (@Eid VarOrder.T 3364)));(3366,(@Eref VarOrder.T (@Eid VarOrder.T 2209)));(3367,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3366)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(3368,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3367))));(3369,(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3368))));(3370,(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3369))));(3371,(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3370))));(3372,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])));(3373,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])));(3374,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])));(3375,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])));(3376,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3375)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])));(3377,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3374)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3376))));(3378,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3373)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3377))));(3379,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3372)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3378))));(3380,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3371)) (@Eref VarOrder.T (@Eid VarOrder.T 3379))));(3381,(@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 3380))));(3382,(@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 24) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3381))));(3383,(@Eref VarOrder.T (@Eid VarOrder.T 3382)));(3384,(@Eref VarOrder.T (@Eid VarOrder.T 2209)));(3385,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3384)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(3386,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3385))));(3387,(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3386))));(3388,(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3387))));(3389,(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3388))));(3390,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true])));(3391,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true])));(3392,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true])));(3393,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true])));(3394,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3393)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])));(3395,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3392)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3394))));(3396,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3391)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3395))));(3397,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3390)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3396))));(3398,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3389)) (@Eref VarOrder.T (@Eid VarOrder.T 3397))));(3399,(@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 3398))));(3400,(@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 3399))));(3401,(@Eref VarOrder.T (@Eid VarOrder.T 3400)));(3402,(@Eref VarOrder.T (@Eid VarOrder.T 2209)));(3403,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3402)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(3404,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3403))));(3405,(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3404))));(3406,(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3405))));(3407,(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3406))));(3408,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true])));(3409,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true])));(3410,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true])));(3411,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true])));(3412,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3411)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])));(3413,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3410)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3412))));(3414,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3409)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3413))));(3415,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3408)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3414))));(3416,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3407)) (@Eref VarOrder.T (@Eid VarOrder.T 3415))));(3417,(@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 3416))));(3418,(@Eprim_unop VarOrder.T (Uextr 15 15) (@Eref VarOrder.T (@Eid VarOrder.T 3417))));(3419,(@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 3418))));(3420,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3419)) (@Econst VarOrder.T (Fuint 16) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Econst VarOrder.T (Fuint 16) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])));(3421,(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 3420)) (@Eref VarOrder.T (@Eid VarOrder.T 3417))));(3422,(@Eref VarOrder.T (@Eid VarOrder.T 3421)));(3423,(@Eref VarOrder.T (@Eid VarOrder.T 2209)));(3424,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3423)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(3425,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3424))));(3426,(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3425))));(3427,(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3426))));(3428,(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3427))));(3429,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])));(3430,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])));(3431,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])));(3432,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])));(3433,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3432)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])));(3434,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3431)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3433))));(3435,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3430)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3434))));(3436,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3429)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3435))));(3437,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3428)) (@Eref VarOrder.T (@Eid VarOrder.T 3436))));(3438,(@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 3437))));(3439,(@Eprim_unop VarOrder.T (Uextr 7 7) (@Eref VarOrder.T (@Eid VarOrder.T 3438))));(3440,(@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 3439))));(3441,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3440)) (@Econst VarOrder.T (Fuint 24) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Econst VarOrder.T (Fuint 24) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])));(3442,(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 3441)) (@Eref VarOrder.T (@Eid VarOrder.T 3438))));(3443,(@Eref VarOrder.T (@Eid VarOrder.T 3442)))].
Definition reference_load_offsets := [::3427%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Definition reference_load_rows : seq (seq (hfexpr VarOrder.T)) := [::[::(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3350)));(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3351)));(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3352)));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3357)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3356)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3358)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3355)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3359)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3354)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3360)));(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3353)) (@Eref VarOrder.T (@Eid VarOrder.T 3361)));(@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 3362)));(@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 16) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3363)));(@Eref VarOrder.T (@Eid VarOrder.T 3364))];[::(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3368)));(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3369)));(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3370)));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3375)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3374)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3376)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3373)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3377)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3372)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3378)));(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3371)) (@Eref VarOrder.T (@Eid VarOrder.T 3379)));(@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 3380)));(@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 24) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3381)));(@Eref VarOrder.T (@Eid VarOrder.T 3382))];[::(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3386)));(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3387)));(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3388)));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3393)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3392)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3394)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3391)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3395)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3390)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3396)));(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3389)) (@Eref VarOrder.T (@Eid VarOrder.T 3397)));(@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 3398)));(@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 3399)));(@Eref VarOrder.T (@Eid VarOrder.T 3400))];[::(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3404)));(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3405)));(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3406)));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3411)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3410)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3412)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3409)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3413)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3408)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3414)));(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3407)) (@Eref VarOrder.T (@Eid VarOrder.T 3415)));(@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 3416)));(@Eprim_unop VarOrder.T (Uextr 15 15) (@Eref VarOrder.T (@Eid VarOrder.T 3417)));(@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 3418)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3419)) (@Econst VarOrder.T (Fuint 16) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Econst VarOrder.T (Fuint 16) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]));(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 3420)) (@Eref VarOrder.T (@Eid VarOrder.T 3417)));(@Eref VarOrder.T (@Eid VarOrder.T 3421))];[::(@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 3425)));(@Eprim_unop VarOrder.T (Ushl 3) (@Eref VarOrder.T (@Eid VarOrder.T 3426)));(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3347)) (@Eref VarOrder.T (@Eid VarOrder.T 3427)));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]));(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3432)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3431)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3433)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3430)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 3434)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3429)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3435)));(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3428)) (@Eref VarOrder.T (@Eid VarOrder.T 3436)));(@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 3437)));(@Eprim_unop VarOrder.T (Uextr 7 7) (@Eref VarOrder.T (@Eid VarOrder.T 3438)));(@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 3439)));(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3440)) (@Econst VarOrder.T (Fuint 24) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Econst VarOrder.T (Fuint 24) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]));(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 3441)) (@Eref VarOrder.T (@Eid VarOrder.T 3438)));(@Eref VarOrder.T (@Eid VarOrder.T 3442))]].
Definition reference_load_address_rows : seq (seq (hfexpr VarOrder.T)) := [::[::(@Eref VarOrder.T (@Eid VarOrder.T 2209));(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3348)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)));(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3349)))];[::(@Eref VarOrder.T (@Eid VarOrder.T 2209));(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3366)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)));(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3367)))];[::(@Eref VarOrder.T (@Eid VarOrder.T 2209));(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3384)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)));(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3385)))];[::(@Eref VarOrder.T (@Eid VarOrder.T 2209));(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3402)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)));(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3403)))];[::(@Eref VarOrder.T (@Eid VarOrder.T 2209));(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3423)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)));(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3424)))]].
Definition reference_load_base lane : VarOrder.T := nth 0 [::3351;3369;3387;3405;3426] lane.
Definition reference_load_width lane : nat := nth 0%nat [::16%nat;8%nat;32%nat;16%nat;8%nat] lane.
Definition reference_load_length lane : nat := nth 0%nat [::15%nat;15%nat;15%nat;18%nat;18%nat] lane.
Definition reference_load_node lane stage := reference_load_base lane + N.of_nat stage.
Definition reference_load_expression lane stage := nth (@Econst VarOrder.T (Fuint 1) [::false]) (nth [::] reference_load_rows lane) stage.
Definition reference_load_address_node lane stage := reference_load_base lane - 3 + N.of_nat stage.
Definition reference_load_address_expression lane stage := nth (@Econst VarOrder.T (Fuint 1) [::false]) (nth [::] reference_load_address_rows lane) stage.
Definition reference_load_mask lane := from_N 64 (nth 0 [::65535;255;4294967295;65535;255] lane).
Lemma reference_load_positions : select_node_offsets reference_load_offsets flat_statements = Some reference_load_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma reference_load_safety : selected_node_safety flat_memories flat_statements reference_load_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma reference_load_member lane stage : (lane < 5)%coq_nat -> (stage < reference_load_length lane)%coq_nat ->
 List.In (reference_load_node lane stage,reference_load_expression lane stage) reference_load_nodes.
Proof.
 intros Lane Stage.
 apply (List.nth_error_In reference_load_nodes ((nth 0%nat [::3%nat;21%nat;39%nat;57%nat;78%nat] lane) + stage)%nat).
 do 5 (destruct lane as [|lane]; [cbn [reference_load_length nth] in Stage;
 do 18 (destruct stage as [|stage]; [try (vm_compute;reflexivity);try lia|]);lia|]). lia.
Qed.
Lemma reference_load_address_member lane stage : (lane < 5)%coq_nat -> (stage < 3)%coq_nat ->
 List.In (reference_load_address_node lane stage,reference_load_address_expression lane stage) reference_load_nodes.
Proof.
 intros Lane Stage.
 apply (List.nth_error_In reference_load_nodes ((nth 0%nat [::0%nat;18%nat;36%nat;54%nat;75%nat] lane) + stage)%nat).
 do 5 (destruct lane as [|lane]; [do 3 (destruct stage as [|stage]; [vm_compute;reflexivity|]);lia|]). lia.
Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Shared load-lane semantics. *)
Theorem reference_load_node_step invalid old current result lane stage ground word :
 (lane < 5)%coq_nat -> (stage < reference_load_length lane)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories
 (reference_load_expression lane stage) old old = Some (Gval ground word)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (reference_load_node lane stage) result = Some (Gval ground word).
Proof.
 intros Lane Stage Eval Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_load_offsets flat_statements
 reference_load_nodes _ _ reference_load_positions reference_load_safety (reference_load_member lane stage Lane Stage))
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_ground_node;
 [exact Position|exact Safe|exact Nonreg|apply Eval|reflexivity|exact Step].
Qed.
Definition reference_load_guard lane which :=
 nth false [::false;Nat.eqb lane 2;orb (Nat.eqb lane 0) (Nat.eqb lane 3);orb (Nat.eqb lane 1) (Nat.eqb lane 4)] which.
Theorem reference_load_guard_step invalid old current result lane which :
 (lane < 5)%coq_nat -> (which < 4)%coq_nat ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (reference_load_node lane (Nat.add 3 which)) result = Some (Gval (Fuint 1) [::reference_load_guard lane which]).
Proof.
 intros Lane Which Step. eapply reference_load_node_step; [exact Lane| | |exact Step].
 - do 5 (destruct lane as [|lane]; [do 4 (destruct which as [|which]; [vm_compute;lia|]);lia|]). lia.
 - intro site. do 5 (destruct lane as [|lane]; [do 4 (destruct which as [|which]; [reflexivity|]);lia|]). lia.
Qed.
Definition reference_load_partial_mask lane stage := from_N 64
 (if Nat.eqb lane 2 then (if (2 <= stage)%nat then 4294967295 else 0)
 else if orb (Nat.eqb lane 0) (Nat.eqb lane 3) then (if (1 <= stage)%nat then 65535 else 0) else 255).
Theorem reference_load_mask_step invalid old current result lane stage :
 (lane < 5)%coq_nat -> (stage < 4)%coq_nat ->
 VM.find (reference_load_node lane (Nat.sub 6 stage)) old = Some (Gval (Fuint 1) [::reference_load_guard lane (Nat.sub 3 stage)]) ->
 (stage = 0%nat \/ VM.find (reference_load_node lane (Nat.add 6 stage)) old = Some (Gval (Fuint 64) (reference_load_partial_mask lane (Nat.sub stage 1)))) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (reference_load_node lane (Nat.add 7 stage)) result = Some (Gval (Fuint 64) (reference_load_partial_mask lane stage)).
Proof.
 intros Lane Stage Guard Previous Step.
 eapply reference_load_node_step; [exact Lane| | |exact Step].
 - do 5 (destruct lane as [|lane]; [do 4 (destruct stage as [|stage]; [vm_compute;lia|]);lia|]). lia.
 - intro site.
   do 5 (destruct lane as [|lane]; [do 4 (destruct stage as [|stage];
   [cbn [reference_load_expression reference_load_rows nth Nat.add Nat.sub addn addn_rec eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_node reference_load_base reference_load_guard nth Nat.add Nat.sub subn subn_rec addn addn_rec N.of_nat N.add] in Guard;
    rewrite Guard; cbn [Nat.eqb orb is_zero]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref];
    destruct Previous as [Impossible|Previous];try discriminate;
    try (cbn [reference_load_node reference_load_base nth Nat.add Nat.sub subn subn_rec addn addn_rec N.of_nat N.add] in Previous;rewrite Previous);
    reflexivity|]);lia|]). lia.
Qed.
Theorem reference_load_mask_history invalid history lane :
 (lane < 5)%coq_nat ->
 (forall i, (i < 5)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find (reference_load_node lane 10) (history 5%nat) = Some (Gval (Fuint 64) (reference_load_mask lane)).
Proof.
 intros Lane Steps.
 pose proof (reference_load_guard_step invalid (history 0%nat) (history 0%nat) (history 1%nat) lane 3 Lane ltac:(lia) (Steps 0%nat ltac:(lia))) as G0.
 pose proof (reference_load_guard_step invalid (history 1%nat) (history 1%nat) (history 2%nat) lane 2 Lane ltac:(lia) (Steps 1%nat ltac:(lia))) as G1.
 pose proof (reference_load_guard_step invalid (history 2%nat) (history 2%nat) (history 3%nat) lane 1 Lane ltac:(lia) (Steps 2%nat ltac:(lia))) as G2.
 pose proof (reference_load_guard_step invalid (history 3%nat) (history 3%nat) (history 4%nat) lane 0 Lane ltac:(lia) (Steps 3%nat ltac:(lia))) as G3.
 pose proof (reference_load_mask_step invalid (history 1%nat) (history 1%nat) (history 2%nat) lane 0 Lane ltac:(lia) G0 (or_introl (Logic.eq_refl 0%nat)) (Steps 1%nat ltac:(lia))) as M0.
 pose proof (reference_load_mask_step invalid (history 2%nat) (history 2%nat) (history 3%nat) lane 1 Lane ltac:(lia) G1 (or_intror M0) (Steps 2%nat ltac:(lia))) as M1.
 pose proof (reference_load_mask_step invalid (history 3%nat) (history 3%nat) (history 4%nat) lane 2 Lane ltac:(lia) G2 (or_intror M1) (Steps 3%nat ltac:(lia))) as M2.
 pose proof (reference_load_mask_step invalid (history 4%nat) (history 4%nat) (history 5%nat) lane 3 Lane ltac:(lia) G3 (or_intror M2) (Steps 4%nat ltac:(lia))) as M3.
 assert (Same : reference_load_partial_mask lane 3 = reference_load_mask lane).
 { do 5 (destruct lane as [|lane]; [reflexivity|]). lia. }
 rewrite Same in M3. exact M3.
Qed.
Theorem reference_load_low_step invalid old current result lane address :
 (lane < 5)%coq_nat ->
 VM.find (reference_load_base lane - 1) old = Some (Gval (Fuint 32) address) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (reference_load_node lane 0) result = Some (Gval (Fuint 2) (take 2 address)).
Proof.
 intros Lane Address Step. eapply reference_load_node_step; [exact Lane| | |exact Step].
 - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
 - intro site. do 5 (destruct lane as [|lane];
   [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_base nth] in Address; rewrite Address; cbn [eval_unop]; rewrite ?drop0; reflexivity|]). lia.
Qed.
Theorem reference_load_offset_step invalid old current result lane address :
 (lane < 5)%coq_nat ->
 VM.find (reference_load_node lane 0) old = Some (Gval (Fuint 2) (take 2 address)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (reference_load_node lane 1) result = Some (Gval (Fuint 5) (zeros 3 ++ take 2 address)).
Proof.
 intros Lane Address Step. eapply reference_load_node_step; [exact Lane| | |exact Step].
 - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
 - intro site. do 5 (destruct lane as [|lane];
   [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_node reference_load_base nth N.of_nat N.add] in Address; rewrite Address; cbn [eval_unop]; rewrite ?drop0; reflexivity|]). lia.
Qed.
Definition reference_load_shift raw address := zext_to 32 (drop (to_nat (zeros 3 ++ take 2 address)) raw).
Theorem reference_load_shift_step invalid old current result lane address raw :
 (lane < 5)%coq_nat ->
 VM.find (reference_load_node lane 1) old = Some (Gval (Fuint 5) (zeros 3 ++ take 2 address)) ->
 VM.find 3347 old = Some (Gval (Fuint 32) raw) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (reference_load_node lane 2) result = Some (Gval (Fuint 32) (reference_load_shift raw address)).
Proof.
 intros Lane Address Raw Step. eapply reference_load_node_step; [exact Lane| | |exact Step].
 - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
 - intro site. do 5 (destruct lane as [|lane];
   [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_node reference_load_base nth N.of_nat N.add] in Address; rewrite Address Raw;reflexivity|]). lia.
Qed.
Theorem reference_load_and_step invalid old current result lane shifted :
 (lane < 5)%coq_nat ->
 VM.find (reference_load_node lane 2) old = Some (Gval (Fuint 32) shifted) ->
 VM.find (reference_load_node lane 10) old = Some (Gval (Fuint 64) (reference_load_mask lane)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (reference_load_node lane 11) result = Some (Gval (Fuint 64) (andB shifted (reference_load_mask lane))).
Proof.
 intros Lane Shift Mask Step. eapply reference_load_node_step; [exact Lane| | |exact Step].
 - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
 - intro site. do 5 (destruct lane as [|lane];
   [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_node reference_load_base nth N.of_nat N.add] in Shift,Mask; rewrite Shift Mask;reflexivity|]). lia.
Qed.
Theorem reference_load_slice_step invalid old current result lane word :
 (lane < 5)%coq_nat ->
 VM.find (reference_load_node lane 11) old = Some (Gval (Fuint 64) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (reference_load_node lane 12) result = Some (Gval (Fuint (reference_load_width lane)) (take (reference_load_width lane) word)).
Proof.
 intros Lane Word Step. eapply reference_load_node_step; [exact Lane| | |exact Step].
 - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
 - intro site. do 5 (destruct lane as [|lane];
   [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_node reference_load_base nth N.of_nat N.add] in Word; rewrite Word; cbn [eval_unop]; rewrite ?drop0; reflexivity|]). lia.
Qed.
Lemma reference_load_shift_size raw address : size raw = 32%nat -> size (reference_load_shift raw address) = 32%nat.
Proof.
 intro Size. unfold reference_load_shift,zext_to. rewrite size_zext addnC subnK; [reflexivity|].
 rewrite size_drop Size. apply leq_subr.
Qed.
Lemma reference_load_remove_mask lane shifted : (lane < 5)%coq_nat -> size shifted = 32%nat ->
 take (reference_load_width lane) (andB shifted (reference_load_mask lane)) = take (reference_load_width lane) shifted.
Proof.
 intros Lane Size.
 do 5 (destruct lane as [|lane];
 [cbv [reference_load_width reference_load_mask nth]; rewrite ?reference_load_mask8 ?reference_load_mask16 ?reference_load_mask32;
 apply reference_load_mask_low;rewrite Size;lia|]). lia.
Qed.
Theorem reference_load_extract_history invalid history lane address raw :
 (lane < 5)%coq_nat -> size raw = 32%nat ->
 VM.find (reference_load_base lane - 1) (history 3%nat) = Some (Gval (Fuint 32) address) ->
 VM.find 3347 (history 5%nat) = Some (Gval (Fuint 32) raw) ->
 (forall i, (i < 8)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find (reference_load_node lane 12) (history 8%nat) = Some (Gval (Fuint (reference_load_width lane)) (take (reference_load_width lane) (reference_load_shift raw address))).
Proof.
 intros Lane Size Address Raw Steps.
 pose proof (reference_load_low_step invalid (history 3%nat) (history 3%nat) (history 4%nat) lane address Lane Address (Steps 3%nat ltac:(lia))) as A.
 pose proof (reference_load_offset_step invalid (history 4%nat) (history 4%nat) (history 5%nat) lane address Lane A (Steps 4%nat ltac:(lia))) as B.
 pose proof (reference_load_shift_step invalid (history 5%nat) (history 5%nat) (history 6%nat) lane address raw Lane B Raw (Steps 5%nat ltac:(lia))) as C.
 pose proof (reference_load_mask_history invalid (fun i => history (S i)) lane Lane (fun i Bound => Steps (S i) ltac:(lia))) as Mask.
 pose proof (reference_load_and_step invalid (history 6%nat) (history 6%nat) (history 7%nat) lane _ Lane C Mask (Steps 6%nat ltac:(lia))) as D.
 pose proof (reference_load_slice_step invalid (history 7%nat) (history 7%nat) (history 8%nat) lane _ Lane D (Steps 7%nat ltac:(lia))) as E.
 rewrite (reference_load_remove_mask lane _ Lane (reference_load_shift_size raw address Size)) in E. exact E.
Qed.
Lemma reference_load_sign_bit width word : size word = width -> (0 < width)%nat ->
 drop (width-1)%nat (take width word) = [::msb word].
Proof.
 intros Size Positive. rewrite -Size take_size.
 pose proof (high1_msb word) as H. unfold high in H.
 assert (Zero : (1-size word)%nat = 0%nat).
 { apply/eqP. rewrite subn_eq0 Size. exact Positive. }
 rewrite Zero /= in H. exact H.
Qed.
Definition reference_load_extend lane word :=
 if (lane < 2)%nat then zext_to 32 word else
 if Nat.eqb lane 2 then take 32 word else sext_to 32 word.
Theorem reference_load_unsigned_extension invalid s0 s1 s2 lane word :
 (lane < 3)%coq_nat -> size word = reference_load_width lane ->
 VM.find (reference_load_node lane 12) s0 = Some (Gval (Fuint (reference_load_width lane)) word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find (reference_load_node lane 14) s2 = Some (Gval (Fuint 32) (reference_load_extend lane word)).
Proof.
 intros Lane Size Word S1 S2.
 assert (E : VM.find (reference_load_node lane 13) s1 = Some (Gval (Fuint 32) (reference_load_extend lane word))).
 { eapply reference_load_node_step; [lia| | |exact S1].
   - do 3 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
   - intro site. do 3 (destruct lane as [|lane];
     [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
      cbn [reference_load_node reference_load_base reference_load_width nth N.of_nat N.add] in Word,Size;
      rewrite Word; unfold reference_load_extend; cbn; unfold zext_to,zext; rewrite ?Size; rewrite ?drop0;reflexivity|]). lia. }
 eapply reference_load_node_step; [lia| | |exact S2].
 - do 3 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
 - intro site. do 3 (destruct lane as [|lane];
   [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_node reference_load_base nth N.of_nat N.add] in E;exact E|]). lia.
Qed.
Theorem reference_load_signed_extension invalid s0 s1 s2 s3 s4 s5 (lane : nat) word :
 ((3 <= lane)%coq_nat /\ (lane < 5)%coq_nat) -> size word = reference_load_width lane ->
 VM.find (reference_load_node lane 12) s0 = Some (Gval (Fuint (reference_load_width lane)) word) ->
 VM.find (reference_load_node lane 12) s3 = Some (Gval (Fuint (reference_load_width lane)) word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find (reference_load_node lane 17) s5 = Some (Gval (Fuint 32) (reference_load_extend lane word)).
Proof.
 intros Lane Size Word WordLater S1 S2 S3 S4 S5.
 assert (Sign : VM.find (reference_load_node lane 13) s1 = Some (Gval (Fuint 1) [::msb word])).
 { eapply reference_load_node_step; [lia| | |exact S1].
   - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
   - intro site. do 3 (destruct lane as [|lane]; [lia|]).
     do 2 (destruct lane as [|lane];
     [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
      cbn [reference_load_node reference_load_base reference_load_width nth N.of_nat N.add] in Word,Size;
      rewrite Word; cbn [eval_unop]; rewrite (reference_load_sign_bit _ _ Size ltac:(reflexivity));reflexivity|]). lia. }
 assert (Bit : VM.find (reference_load_node lane 14) s2 = Some (Gval (Fuint 1) [::msb word])).
 { eapply reference_load_node_step; [lia| | |exact S2].
   - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
   - intro site. do 3 (destruct lane as [|lane]; [lia|]).
     do 2 (destruct lane as [|lane];
     [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
      cbn [reference_load_node reference_load_base nth N.of_nat N.add] in Sign; rewrite Sign;reflexivity|]). lia. }
 assert (Pad : VM.find (reference_load_node lane 15) s3 = Some (Gval (Fuint (32-reference_load_width lane)%nat)
 (nseq (32-reference_load_width lane)%nat (msb word)))).
 { eapply reference_load_node_step; [lia| | |exact S3].
   - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
   - intro site. do 3 (destruct lane as [|lane]; [lia|]).
     do 2 (destruct lane as [|lane];
     [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
      cbn [reference_load_node reference_load_base nth N.of_nat N.add] in Bit;rewrite Bit;destruct (msb word);reflexivity|]). lia. }
 assert (Extended : VM.find (reference_load_node lane 16) s4 = Some (Gval (Fuint 32) (reference_load_extend lane word))).
 { eapply reference_load_node_step; [lia| | |exact S4].
   - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
   - intro site. do 3 (destruct lane as [|lane]; [lia|]).
     do 2 (destruct lane as [|lane];
     [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
      cbn [reference_load_node reference_load_base reference_load_width nth N.of_nat N.add] in WordLater,Pad,Size;
      rewrite WordLater Pad; unfold reference_load_extend; cbn;unfold sext_to,sext;rewrite Size;reflexivity|]). lia. }
 eapply reference_load_node_step; [lia| | |exact S5].
 - do 5 (destruct lane as [|lane]; [vm_compute;lia|]). lia.
 - intro site. do 3 (destruct lane as [|lane]; [lia|]).
   do 2 (destruct lane as [|lane];
   [cbn [reference_load_expression reference_load_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_node reference_load_base nth N.of_nat N.add] in Extended; exact Extended|]). lia.
Qed.
Definition reference_load_output lane := reference_load_node lane (if Nat.ltb lane 3 then 14%nat else 17%nat).
Theorem reference_load_lane_history invalid history lane address raw :
 (lane < 5)%coq_nat -> size raw = 32%nat ->
 (forall i, (i <= 6)%coq_nat -> VM.find (reference_load_base lane - 1) (history i) = Some (Gval (Fuint 32) address)) ->
 (forall i, (i <= 8)%coq_nat -> VM.find 3347 (history i) = Some (Gval (Fuint 32) raw)) ->
 (forall i, (i < 13)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find (reference_load_output lane) (history 13%nat) = Some (Gval (Fuint 32)
 (reference_load_extend lane (take (reference_load_width lane) (reference_load_shift raw address)))).
Proof.
 intros Lane Size Address Raw Steps.
 pose proof (reference_load_extract_history invalid history lane address raw Lane Size (Address 3%nat ltac:(lia)) (Raw 5%nat ltac:(lia))
 (fun i Bound => Steps i ltac:(lia))) as A.
 pose proof (reference_load_extract_history invalid (fun i => history (Nat.add 3 i)) lane address raw Lane Size
 (Address 6%nat ltac:(lia)) (Raw 8%nat ltac:(lia)) (fun i Bound => Steps (Nat.add 3 i) ltac:(lia))) as B.
 assert (WordSize : size (take (reference_load_width lane) (reference_load_shift raw address)) = reference_load_width lane).
 { rewrite size_take (reference_load_shift_size raw address Size).
   do 5 (destruct lane as [|lane]; [reflexivity|]). lia. }
 unfold reference_load_output. destruct (Nat.ltb lane 3) eqn:Kind.
 - apply Nat.ltb_lt in Kind.
   exact (reference_load_unsigned_extension invalid (history 11%nat) (history 12%nat) (history 13%nat)
   lane _ Kind WordSize B (Steps 11%nat ltac:(lia)) (Steps 12%nat ltac:(lia))).
 - apply Nat.ltb_ge in Kind.
   exact (reference_load_signed_extension invalid (history 8%nat) (history 9%nat) (history 10%nat) (history 11%nat) (history 12%nat) (history 13%nat)
   lane _ ltac:(lia) WordSize A B (Steps 8%nat ltac:(lia)) (Steps 9%nat ltac:(lia)) (Steps 10%nat ltac:(lia)) (Steps 11%nat ltac:(lia)) (Steps 12%nat ltac:(lia))).
Qed.
Theorem reference_load_address_node_step invalid old current result lane stage ground word :
 (lane < 5)%coq_nat -> (stage < 3)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories
 (reference_load_address_expression lane stage) old old = Some (Gval ground word)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (reference_load_address_node lane stage) result = Some (Gval ground word).
Proof.
 intros Lane Stage Eval Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_load_offsets flat_statements
 reference_load_nodes _ _ reference_load_positions reference_load_safety (reference_load_address_member lane stage Lane Stage))
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_ground_node;
 [exact Position|exact Safe|exact Nonreg|apply Eval|reflexivity|exact Step].
Qed.
Definition reference_load_address rs1 immediate := take 32 (from_N 33 (to_N rs1 + to_N immediate)).
Theorem reference_load_address_history invalid s0 s1 s2 s3 lane rs1 immediate :
 (lane < 5)%coq_nat ->
 VM.find 2209 s0 = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 s1 = Some (Gval (Fuint 32) immediate) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find (reference_load_base lane - 1) s3 = Some (Gval (Fuint 32) (reference_load_address rs1 immediate)).
Proof.
 intros Lane Rs1 Immediate S1 S2 S3.
 assert (A : VM.find (reference_load_address_node lane 0) s1 = Some (Gval (Fuint 32) rs1)).
 { eapply reference_load_address_node_step; [exact Lane|lia| |exact S1].
   intro site. do 5 (destruct lane as [|lane]; [exact Rs1|]). lia. }
 assert (B : VM.find (reference_load_address_node lane 1) s2 = Some (Gval (Fuint 33) (from_N 33 (to_N rs1 + to_N immediate)))).
 { eapply reference_load_address_node_step; [exact Lane|lia| |exact S2].
   intro site. do 5 (destruct lane as [|lane];
   [cbn [reference_load_address_expression reference_load_address_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_address_node reference_load_base nth N.of_nat N.add N.sub] in A;rewrite A Immediate;reflexivity|]). lia. }
 assert (C : VM.find (reference_load_address_node lane 2) s3 = Some (Gval (Fuint 32) (reference_load_address rs1 immediate))).
 { eapply reference_load_address_node_step; [exact Lane|lia| |exact S3].
   intro site. do 5 (destruct lane as [|lane];
   [cbn [reference_load_address_expression reference_load_address_rows nth eval_hfexpr_validif_policy eval_href_validif_policy];
    cbn [reference_load_address_node reference_load_base nth N.of_nat N.add N.sub] in B;rewrite B;reflexivity|]). lia. }
 assert (Same : reference_load_base lane - 1 = reference_load_address_node lane 2).
 { do 5 (destruct lane as [|lane]; [reflexivity|]). lia. }
 rewrite Same. exact C.
Qed.
Theorem reference_load_sources_history invalid history lane rs1 immediate raw :
 (lane < 5)%coq_nat -> size raw = 32%nat ->
 (forall i, (i <= 6)%coq_nat -> VM.find 2209 (history i) = Some (Gval (Fuint 32) rs1)) ->
 (forall i, (i <= 7)%coq_nat -> VM.find 2552 (history i) = Some (Gval (Fuint 32) immediate)) ->
 (forall i, (i <= 11)%coq_nat -> VM.find 3347 (history i) = Some (Gval (Fuint 32) raw)) ->
 (forall i, (i < 16)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find (reference_load_output lane) (history 16%nat) = Some (Gval (Fuint 32)
 (reference_load_extend lane (take (reference_load_width lane) (reference_load_shift raw (reference_load_address rs1 immediate))))).
Proof.
 intros Lane Size Rs1 Immediate Raw Steps.
 apply (reference_load_lane_history invalid (fun i => history (S (S (S i)))) lane (reference_load_address rs1 immediate) raw Lane Size).
 - intros i Bound. exact (reference_load_address_history invalid (history i) (history (S i)) (history (S (S i))) (history (S (S (S i))))
   lane rs1 immediate Lane (Rs1 i Bound) (Immediate (S i) ltac:(lia)) (Steps i ltac:(lia)) (Steps (S i) ltac:(lia)) (Steps (S (S i)) ltac:(lia))).
 - intros i Bound. apply Raw. lia.
 - intros i Bound. apply Steps. lia.
Qed.
Require Import SharedLoadInput RFWritebackSelection ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory StagedRegisterHold.
Theorem reference_load_raw_history invalid history limit raw :
 size raw = 32%nat -> VM.find 9222 (history 0%nat) = Some (Gval (Fuint 32) raw) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 3347 (history time) = Some (Gval (Fuint 32) raw).
Proof.
 intros Size Initial Steps time Lower Upper.
 set start := Nat.sub time 9.
 assert (End : Nat.add (S (S start)) 7 = time) by (unfold start;lia).
 rewrite <- End.
 apply (shared_load_seven_steps invalid (fun i => history (Nat.add (S (S start)) i)) raw Size).
 - rewrite Nat.add_0_r. exact (rf_load_raw_history invalid history limit raw Size Initial Steps start ltac:(unfold start;lia)).
 - intros i Bound. rewrite Nat.add_succ_r. apply Steps. unfold start. lia.
Qed.
Theorem reference_load_function_history inputs path history limit reset start lane rs1 immediate raw :
 (lane < 5)%coq_nat -> size raw = 32%nat ->
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (97 <= start)%coq_nat -> (Nat.add start 16 <= limit)%coq_nat ->
 VM.find 2209 (history (Nat.add start 16)) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 (history (Nat.add start 16)) = Some (Gval (Fuint 32) immediate) ->
 VM.find 9222 (history 0%nat) = Some (Gval (Fuint 32) raw) ->
 VM.find (reference_load_output lane) (history (Nat.add start 16)) = Some (Gval (Fuint 32)
 (reference_load_extend lane (take (reference_load_width lane) (reference_load_shift raw (reference_load_address rs1 immediate))))).
Proof.
 intros Lane Size Resets Steps Lower Upper Rs1 Immediate Raw.
 apply (reference_load_sources_history (formal_invalid_policy inputs path) (fun i => history (Nat.add start i)) lane rs1 immediate raw Lane Size).
 - intros i Bound. rewrite (reference_control_stable_2209_history inputs path history limit reset Resets Steps
   (Nat.add start i) (Nat.add start 16) ltac:(lia) ltac:(lia) ltac:(lia) Upper). exact Rs1.
 - intros i Bound. rewrite (reference_control_stable_2552_history inputs path history limit reset Resets Steps
   (Nat.add start i) (Nat.add start 16) ltac:(lia) ltac:(lia) ltac:(lia) Upper). exact Immediate.
 - intros i Bound. exact (reference_load_raw_history (formal_invalid_policy inputs path) history limit raw Size Raw Steps (Nat.add start i) ltac:(lia) ltac:(lia)).
 - intros i Bound. rewrite Nat.add_succ_r. apply Steps. lia.
Qed.
Theorem reference_load_function_observed memory inputs k observed lane rs1 immediate raw :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (lane < 5)%coq_nat -> size raw = 32%nat ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 9222 (top_environment observed) = Some (Gval (Fuint 32) raw) ->
 VM.find (reference_load_output lane) (top_environment observed) = Some (Gval (Fuint 32)
 (reference_load_extend lane (take (reference_load_width lane) (reference_load_shift raw (reference_load_address rs1 immediate))))).
Proof.
 intros Observe Legal Lane Size Rs1 Immediate Raw.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Held : forall i, (i <= 9259)%coq_nat -> VM.find 9222 (history i) = VM.find 9222 (history 0%nat)).
 { induction i as [|i IH]; intro Bound; [reflexivity|].
   rewrite (staged_combinational_holds_registers (formal_invalid_policy (generated_observation_input inputs k) nil)
    flat_memories (history i) (history i) (history (S i)) flat_statements 9222 rf_load_raw_register (Steps i ltac:(lia))).
   apply IH. lia. }
 assert (Initial : VM.find 9222 (history 0%nat) = Some (Gval (Fuint 32) raw)).
 { rewrite - (Held 9259%nat ltac:(vm_compute;lia)) Last. exact Raw. }
 rewrite <- Last.
 exact (reference_load_function_history (generated_observation_input inputs k) nil history 9259 reset 9243 lane rs1 immediate raw
 Lane Size Resets Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)
 ltac:(change (VM.find 2209 (history 9259%nat) = Some (Gval (Fuint 32) rs1));rewrite Last;exact Rs1)
 ltac:(change (VM.find 2552 (history 9259%nat) = Some (Gval (Fuint 32) immediate));rewrite Last;exact Immediate) Initial).
Qed.

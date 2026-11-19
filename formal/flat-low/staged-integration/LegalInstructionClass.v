Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition legal_class_expr_9029 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9030 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9029))).
Definition legal_class_expr_9031 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9032 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9031))).
Definition legal_class_expr_9033 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9034 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9033))).
Definition legal_class_expr_9035 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9036 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9035))).
Definition legal_class_expr_9037 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9038 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9037))).
Definition legal_class_expr_9039 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9040 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9039))).
Definition legal_class_expr_9041 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9042 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9041))).
Definition legal_class_expr_9043 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9044 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9043))).
Definition legal_class_expr_9045 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9046 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 31) [::true; true; false; false; true; false; false; false; false; false; false; false; true; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9045))).
Definition legal_class_expr_9047 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 7) [::true; true; true; true; true; true; true])).
Definition legal_class_expr_9048 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::true; true; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9047))).
Definition legal_class_expr_9049 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 7) [::true; true; true; true; true; true; true])).
Definition legal_class_expr_9050 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9049))).
Definition legal_class_expr_9051 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9030)) (@Eref VarOrder.T (@Eid VarOrder.T 9032))).
Definition legal_class_expr_9052 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9051)) (@Eref VarOrder.T (@Eid VarOrder.T 9034))).
Definition legal_class_expr_9053 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9052)) (@Eref VarOrder.T (@Eid VarOrder.T 9036))).
Definition legal_class_expr_9054 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9053)) (@Eref VarOrder.T (@Eid VarOrder.T 9038))).
Definition legal_class_expr_9055 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9054)) (@Eref VarOrder.T (@Eid VarOrder.T 9040))).
Definition legal_class_expr_9056 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9055)) (@Eref VarOrder.T (@Eid VarOrder.T 9042))).
Definition legal_class_expr_9057 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9056)) (@Eref VarOrder.T (@Eid VarOrder.T 9044))).
Definition legal_class_expr_9058 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9057)) (@Eref VarOrder.T (@Eid VarOrder.T 9046))).
Definition legal_class_expr_9059 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9058)) (@Eref VarOrder.T (@Eid VarOrder.T 9048))).
Definition legal_class_expr_9060 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9059)) (@Eref VarOrder.T (@Eid VarOrder.T 9050))).
Definition legal_class_expr_9061 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9062 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::true; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9061))).
Definition legal_class_expr_9063 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9064 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9063))).
Definition legal_class_expr_9065 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9066 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; true; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9065))).
Definition legal_class_expr_9067 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9068 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9067))).
Definition legal_class_expr_9069 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9070 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9069))).
Definition legal_class_expr_9071 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9072 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9071))).
Definition legal_class_expr_9073 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9074 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; true; true; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9073))).
Definition legal_class_expr_9075 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9076 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9075))).
Definition legal_class_expr_9077 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9078 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 31) [::true; true; false; false; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9077))).
Definition legal_class_expr_9079 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])).
Definition legal_class_expr_9080 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 31) [::true; true; false; false; true; true; false; false; false; false; false; false; true; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9079))).
Definition legal_class_expr_9081 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9062)) (@Eref VarOrder.T (@Eid VarOrder.T 9064))).
Definition legal_class_expr_9082 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9081)) (@Eref VarOrder.T (@Eid VarOrder.T 9066))).
Definition legal_class_expr_9083 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9082)) (@Eref VarOrder.T (@Eid VarOrder.T 9068))).
Definition legal_class_expr_9084 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9083)) (@Eref VarOrder.T (@Eid VarOrder.T 9070))).
Definition legal_class_expr_9085 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9084)) (@Eref VarOrder.T (@Eid VarOrder.T 9072))).
Definition legal_class_expr_9086 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9085)) (@Eref VarOrder.T (@Eid VarOrder.T 9074))).
Definition legal_class_expr_9087 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9086)) (@Eref VarOrder.T (@Eid VarOrder.T 9076))).
Definition legal_class_expr_9088 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9087)) (@Eref VarOrder.T (@Eid VarOrder.T 9078))).
Definition legal_class_expr_9089 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9088)) (@Eref VarOrder.T (@Eid VarOrder.T 9080))).
Definition legal_class_expr_9090 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9060)) (@Eref VarOrder.T (@Eid VarOrder.T 9089))).
Definition legal_class_expr_9091 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 7) [::true; true; true; true; true; true; true])).
Definition legal_class_expr_9092 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; true; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9091))).
Definition legal_class_expr_9093 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9094 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9093))).
Definition legal_class_expr_9095 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9096 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9095))).
Definition legal_class_expr_9097 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9098 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; false; true; true; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9097))).
Definition legal_class_expr_9099 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9100 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9099))).
Definition legal_class_expr_9101 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9102 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9101))).
Definition legal_class_expr_9103 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9104 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9103))).
Definition legal_class_expr_9105 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9106 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9105))).
Definition legal_class_expr_9107 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9092)) (@Eref VarOrder.T (@Eid VarOrder.T 9094))).
Definition legal_class_expr_9108 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9107)) (@Eref VarOrder.T (@Eid VarOrder.T 9096))).
Definition legal_class_expr_9109 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9108)) (@Eref VarOrder.T (@Eid VarOrder.T 9098))).
Definition legal_class_expr_9110 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9109)) (@Eref VarOrder.T (@Eid VarOrder.T 9100))).
Definition legal_class_expr_9111 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9110)) (@Eref VarOrder.T (@Eid VarOrder.T 9102))).
Definition legal_class_expr_9112 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9111)) (@Eref VarOrder.T (@Eid VarOrder.T 9104))).
Definition legal_class_expr_9113 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9112)) (@Eref VarOrder.T (@Eid VarOrder.T 9106))).
Definition legal_class_expr_9114 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9090)) (@Eref VarOrder.T (@Eid VarOrder.T 9113))).
Definition legal_class_expr_9115 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9116 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9115))).
Definition legal_class_expr_9117 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9118 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9117))).
Definition legal_class_expr_9119 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9120 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9119))).
Definition legal_class_expr_9121 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9122 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9121))).
Definition legal_class_expr_9123 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9124 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; false; false; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9123))).
Definition legal_class_expr_9125 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9126 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::true; true; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9125))).
Definition legal_class_expr_9127 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9128 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; false; true; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9127))).
Definition legal_class_expr_9129 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])).
Definition legal_class_expr_9130 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; false; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9129))).
Definition legal_class_expr_9131 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9116)) (@Eref VarOrder.T (@Eid VarOrder.T 9118))).
Definition legal_class_expr_9132 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9131)) (@Eref VarOrder.T (@Eid VarOrder.T 9120))).
Definition legal_class_expr_9133 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9132)) (@Eref VarOrder.T (@Eid VarOrder.T 9122))).
Definition legal_class_expr_9134 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9133)) (@Eref VarOrder.T (@Eid VarOrder.T 9124))).
Definition legal_class_expr_9135 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9134)) (@Eref VarOrder.T (@Eid VarOrder.T 9126))).
Definition legal_class_expr_9136 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9135)) (@Eref VarOrder.T (@Eid VarOrder.T 9128))).
Definition legal_class_expr_9137 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9136)) (@Eref VarOrder.T (@Eid VarOrder.T 9130))).
Definition legal_class_expr_9138 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9114)) (@Eref VarOrder.T (@Eid VarOrder.T 9137))).
Definition legal_class_nodes := [::(9029,legal_class_expr_9029);(9030,legal_class_expr_9030);(9031,legal_class_expr_9031);(9032,legal_class_expr_9032);(9033,legal_class_expr_9033);(9034,legal_class_expr_9034);(9035,legal_class_expr_9035);(9036,legal_class_expr_9036);(9037,legal_class_expr_9037);(9038,legal_class_expr_9038);(9039,legal_class_expr_9039);(9040,legal_class_expr_9040);(9041,legal_class_expr_9041);(9042,legal_class_expr_9042);(9043,legal_class_expr_9043);(9044,legal_class_expr_9044);(9045,legal_class_expr_9045);(9046,legal_class_expr_9046);(9047,legal_class_expr_9047);(9048,legal_class_expr_9048);(9049,legal_class_expr_9049);(9050,legal_class_expr_9050);(9051,legal_class_expr_9051);(9052,legal_class_expr_9052);(9053,legal_class_expr_9053);(9054,legal_class_expr_9054);(9055,legal_class_expr_9055);(9056,legal_class_expr_9056);(9057,legal_class_expr_9057);(9058,legal_class_expr_9058);(9059,legal_class_expr_9059);(9060,legal_class_expr_9060);(9061,legal_class_expr_9061);(9062,legal_class_expr_9062);(9063,legal_class_expr_9063);(9064,legal_class_expr_9064);(9065,legal_class_expr_9065);(9066,legal_class_expr_9066);(9067,legal_class_expr_9067);(9068,legal_class_expr_9068);(9069,legal_class_expr_9069);(9070,legal_class_expr_9070);(9071,legal_class_expr_9071);(9072,legal_class_expr_9072);(9073,legal_class_expr_9073);(9074,legal_class_expr_9074);(9075,legal_class_expr_9075);(9076,legal_class_expr_9076);(9077,legal_class_expr_9077);(9078,legal_class_expr_9078);(9079,legal_class_expr_9079);(9080,legal_class_expr_9080);(9081,legal_class_expr_9081);(9082,legal_class_expr_9082);(9083,legal_class_expr_9083);(9084,legal_class_expr_9084);(9085,legal_class_expr_9085);(9086,legal_class_expr_9086);(9087,legal_class_expr_9087);(9088,legal_class_expr_9088);(9089,legal_class_expr_9089);(9090,legal_class_expr_9090);(9091,legal_class_expr_9091);(9092,legal_class_expr_9092);(9093,legal_class_expr_9093);(9094,legal_class_expr_9094);(9095,legal_class_expr_9095);(9096,legal_class_expr_9096);(9097,legal_class_expr_9097);(9098,legal_class_expr_9098);(9099,legal_class_expr_9099);(9100,legal_class_expr_9100);(9101,legal_class_expr_9101);(9102,legal_class_expr_9102);(9103,legal_class_expr_9103);(9104,legal_class_expr_9104);(9105,legal_class_expr_9105);(9106,legal_class_expr_9106);(9107,legal_class_expr_9107);(9108,legal_class_expr_9108);(9109,legal_class_expr_9109);(9110,legal_class_expr_9110);(9111,legal_class_expr_9111);(9112,legal_class_expr_9112);(9113,legal_class_expr_9113);(9114,legal_class_expr_9114);(9115,legal_class_expr_9115);(9116,legal_class_expr_9116);(9117,legal_class_expr_9117);(9118,legal_class_expr_9118);(9119,legal_class_expr_9119);(9120,legal_class_expr_9120);(9121,legal_class_expr_9121);(9122,legal_class_expr_9122);(9123,legal_class_expr_9123);(9124,legal_class_expr_9124);(9125,legal_class_expr_9125);(9126,legal_class_expr_9126);(9127,legal_class_expr_9127);(9128,legal_class_expr_9128);(9129,legal_class_expr_9129);(9130,legal_class_expr_9130);(9131,legal_class_expr_9131);(9132,legal_class_expr_9132);(9133,legal_class_expr_9133);(9134,legal_class_expr_9134);(9135,legal_class_expr_9135);(9136,legal_class_expr_9136);(9137,legal_class_expr_9137);(9138,legal_class_expr_9138)].
Definition legal_class_offsets := [::9802%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma legal_class_positions : select_node_offsets legal_class_offsets flat_statements = Some legal_class_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma legal_class_safety : selected_node_safety flat_memories flat_statements legal_class_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition legal_class_word_9029 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9030 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 19.
Definition legal_class_word_9030 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 19].
Definition legal_class_word_9031 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9032 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 8211.
Definition legal_class_word_9032 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 8211].
Definition legal_class_word_9033 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9034 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 12307.
Definition legal_class_word_9034 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 12307].
Definition legal_class_word_9035 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9036 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 28691.
Definition legal_class_word_9036 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 28691].
Definition legal_class_word_9037 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9038 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 24595.
Definition legal_class_word_9038 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 24595].
Definition legal_class_word_9039 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9040 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 16403.
Definition legal_class_word_9040 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 16403].
Definition legal_class_word_9041 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9042 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 4115.
Definition legal_class_word_9042 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 4115].
Definition legal_class_word_9043 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9044 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 20499.
Definition legal_class_word_9044 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 20499].
Definition legal_class_word_9045 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9046 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 1073762323.
Definition legal_class_word_9046 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 1073762323].
Definition legal_class_word_9047 (instruction:bits) := andB instruction (from_N 7 127).
Definition legal_class_bit_9048 (instruction:bits) := N.eqb (N.land (to_N instruction) 127) 55.
Definition legal_class_word_9048 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 127) 55].
Definition legal_class_word_9049 (instruction:bits) := andB instruction (from_N 7 127).
Definition legal_class_bit_9050 (instruction:bits) := N.eqb (N.land (to_N instruction) 127) 23.
Definition legal_class_word_9050 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 127) 23].
Definition legal_class_bit_9051 (instruction:bits) := (legal_class_bit_9030 instruction)||(legal_class_bit_9032 instruction).
Definition legal_class_word_9051 (instruction:bits) := [::(legal_class_bit_9030 instruction)||(legal_class_bit_9032 instruction)].
Definition legal_class_bit_9052 (instruction:bits) := (legal_class_bit_9051 instruction)||(legal_class_bit_9034 instruction).
Definition legal_class_word_9052 (instruction:bits) := [::(legal_class_bit_9051 instruction)||(legal_class_bit_9034 instruction)].
Definition legal_class_bit_9053 (instruction:bits) := (legal_class_bit_9052 instruction)||(legal_class_bit_9036 instruction).
Definition legal_class_word_9053 (instruction:bits) := [::(legal_class_bit_9052 instruction)||(legal_class_bit_9036 instruction)].
Definition legal_class_bit_9054 (instruction:bits) := (legal_class_bit_9053 instruction)||(legal_class_bit_9038 instruction).
Definition legal_class_word_9054 (instruction:bits) := [::(legal_class_bit_9053 instruction)||(legal_class_bit_9038 instruction)].
Definition legal_class_bit_9055 (instruction:bits) := (legal_class_bit_9054 instruction)||(legal_class_bit_9040 instruction).
Definition legal_class_word_9055 (instruction:bits) := [::(legal_class_bit_9054 instruction)||(legal_class_bit_9040 instruction)].
Definition legal_class_bit_9056 (instruction:bits) := (legal_class_bit_9055 instruction)||(legal_class_bit_9042 instruction).
Definition legal_class_word_9056 (instruction:bits) := [::(legal_class_bit_9055 instruction)||(legal_class_bit_9042 instruction)].
Definition legal_class_bit_9057 (instruction:bits) := (legal_class_bit_9056 instruction)||(legal_class_bit_9044 instruction).
Definition legal_class_word_9057 (instruction:bits) := [::(legal_class_bit_9056 instruction)||(legal_class_bit_9044 instruction)].
Definition legal_class_bit_9058 (instruction:bits) := (legal_class_bit_9057 instruction)||(legal_class_bit_9046 instruction).
Definition legal_class_word_9058 (instruction:bits) := [::(legal_class_bit_9057 instruction)||(legal_class_bit_9046 instruction)].
Definition legal_class_bit_9059 (instruction:bits) := (legal_class_bit_9058 instruction)||(legal_class_bit_9048 instruction).
Definition legal_class_word_9059 (instruction:bits) := [::(legal_class_bit_9058 instruction)||(legal_class_bit_9048 instruction)].
Definition legal_class_bit_9060 (instruction:bits) := (legal_class_bit_9059 instruction)||(legal_class_bit_9050 instruction).
Definition legal_class_word_9060 (instruction:bits) := [::(legal_class_bit_9059 instruction)||(legal_class_bit_9050 instruction)].
Definition legal_class_word_9061 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9062 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 51.
Definition legal_class_word_9062 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 51].
Definition legal_class_word_9063 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9064 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 8243.
Definition legal_class_word_9064 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 8243].
Definition legal_class_word_9065 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9066 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 12339.
Definition legal_class_word_9066 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 12339].
Definition legal_class_word_9067 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9068 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 28723.
Definition legal_class_word_9068 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 28723].
Definition legal_class_word_9069 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9070 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 24627.
Definition legal_class_word_9070 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 24627].
Definition legal_class_word_9071 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9072 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 16435.
Definition legal_class_word_9072 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 16435].
Definition legal_class_word_9073 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9074 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 4147.
Definition legal_class_word_9074 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 4147].
Definition legal_class_word_9075 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9076 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 20531.
Definition legal_class_word_9076 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 20531].
Definition legal_class_word_9077 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9078 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 1073741875.
Definition legal_class_word_9078 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 1073741875].
Definition legal_class_word_9079 (instruction:bits) := andB instruction (from_N 32 4261441663).
Definition legal_class_bit_9080 (instruction:bits) := N.eqb (N.land (to_N instruction) 4261441663) 1073762355.
Definition legal_class_word_9080 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 4261441663) 1073762355].
Definition legal_class_bit_9081 (instruction:bits) := (legal_class_bit_9062 instruction)||(legal_class_bit_9064 instruction).
Definition legal_class_word_9081 (instruction:bits) := [::(legal_class_bit_9062 instruction)||(legal_class_bit_9064 instruction)].
Definition legal_class_bit_9082 (instruction:bits) := (legal_class_bit_9081 instruction)||(legal_class_bit_9066 instruction).
Definition legal_class_word_9082 (instruction:bits) := [::(legal_class_bit_9081 instruction)||(legal_class_bit_9066 instruction)].
Definition legal_class_bit_9083 (instruction:bits) := (legal_class_bit_9082 instruction)||(legal_class_bit_9068 instruction).
Definition legal_class_word_9083 (instruction:bits) := [::(legal_class_bit_9082 instruction)||(legal_class_bit_9068 instruction)].
Definition legal_class_bit_9084 (instruction:bits) := (legal_class_bit_9083 instruction)||(legal_class_bit_9070 instruction).
Definition legal_class_word_9084 (instruction:bits) := [::(legal_class_bit_9083 instruction)||(legal_class_bit_9070 instruction)].
Definition legal_class_bit_9085 (instruction:bits) := (legal_class_bit_9084 instruction)||(legal_class_bit_9072 instruction).
Definition legal_class_word_9085 (instruction:bits) := [::(legal_class_bit_9084 instruction)||(legal_class_bit_9072 instruction)].
Definition legal_class_bit_9086 (instruction:bits) := (legal_class_bit_9085 instruction)||(legal_class_bit_9074 instruction).
Definition legal_class_word_9086 (instruction:bits) := [::(legal_class_bit_9085 instruction)||(legal_class_bit_9074 instruction)].
Definition legal_class_bit_9087 (instruction:bits) := (legal_class_bit_9086 instruction)||(legal_class_bit_9076 instruction).
Definition legal_class_word_9087 (instruction:bits) := [::(legal_class_bit_9086 instruction)||(legal_class_bit_9076 instruction)].
Definition legal_class_bit_9088 (instruction:bits) := (legal_class_bit_9087 instruction)||(legal_class_bit_9078 instruction).
Definition legal_class_word_9088 (instruction:bits) := [::(legal_class_bit_9087 instruction)||(legal_class_bit_9078 instruction)].
Definition legal_class_bit_9089 (instruction:bits) := (legal_class_bit_9088 instruction)||(legal_class_bit_9080 instruction).
Definition legal_class_word_9089 (instruction:bits) := [::(legal_class_bit_9088 instruction)||(legal_class_bit_9080 instruction)].
Definition legal_class_bit_9090 (instruction:bits) := (legal_class_bit_9060 instruction)||(legal_class_bit_9089 instruction).
Definition legal_class_word_9090 (instruction:bits) := [::(legal_class_bit_9060 instruction)||(legal_class_bit_9089 instruction)].
Definition legal_class_word_9091 (instruction:bits) := andB instruction (from_N 7 127).
Definition legal_class_bit_9092 (instruction:bits) := N.eqb (N.land (to_N instruction) 127) 111.
Definition legal_class_word_9092 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 127) 111].
Definition legal_class_word_9093 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9094 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 103.
Definition legal_class_word_9094 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 103].
Definition legal_class_word_9095 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9096 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 99.
Definition legal_class_word_9096 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 99].
Definition legal_class_word_9097 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9098 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 4195.
Definition legal_class_word_9098 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 4195].
Definition legal_class_word_9099 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9100 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 16483.
Definition legal_class_word_9100 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 16483].
Definition legal_class_word_9101 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9102 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 24675.
Definition legal_class_word_9102 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 24675].
Definition legal_class_word_9103 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9104 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 20579.
Definition legal_class_word_9104 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 20579].
Definition legal_class_word_9105 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9106 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 28771.
Definition legal_class_word_9106 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 28771].
Definition legal_class_bit_9107 (instruction:bits) := (legal_class_bit_9092 instruction)||(legal_class_bit_9094 instruction).
Definition legal_class_word_9107 (instruction:bits) := [::(legal_class_bit_9092 instruction)||(legal_class_bit_9094 instruction)].
Definition legal_class_bit_9108 (instruction:bits) := (legal_class_bit_9107 instruction)||(legal_class_bit_9096 instruction).
Definition legal_class_word_9108 (instruction:bits) := [::(legal_class_bit_9107 instruction)||(legal_class_bit_9096 instruction)].
Definition legal_class_bit_9109 (instruction:bits) := (legal_class_bit_9108 instruction)||(legal_class_bit_9098 instruction).
Definition legal_class_word_9109 (instruction:bits) := [::(legal_class_bit_9108 instruction)||(legal_class_bit_9098 instruction)].
Definition legal_class_bit_9110 (instruction:bits) := (legal_class_bit_9109 instruction)||(legal_class_bit_9100 instruction).
Definition legal_class_word_9110 (instruction:bits) := [::(legal_class_bit_9109 instruction)||(legal_class_bit_9100 instruction)].
Definition legal_class_bit_9111 (instruction:bits) := (legal_class_bit_9110 instruction)||(legal_class_bit_9102 instruction).
Definition legal_class_word_9111 (instruction:bits) := [::(legal_class_bit_9110 instruction)||(legal_class_bit_9102 instruction)].
Definition legal_class_bit_9112 (instruction:bits) := (legal_class_bit_9111 instruction)||(legal_class_bit_9104 instruction).
Definition legal_class_word_9112 (instruction:bits) := [::(legal_class_bit_9111 instruction)||(legal_class_bit_9104 instruction)].
Definition legal_class_bit_9113 (instruction:bits) := (legal_class_bit_9112 instruction)||(legal_class_bit_9106 instruction).
Definition legal_class_word_9113 (instruction:bits) := [::(legal_class_bit_9112 instruction)||(legal_class_bit_9106 instruction)].
Definition legal_class_bit_9114 (instruction:bits) := (legal_class_bit_9090 instruction)||(legal_class_bit_9113 instruction).
Definition legal_class_word_9114 (instruction:bits) := [::(legal_class_bit_9090 instruction)||(legal_class_bit_9113 instruction)].
Definition legal_class_word_9115 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9116 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 3.
Definition legal_class_word_9116 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 3].
Definition legal_class_word_9117 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9118 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 4099.
Definition legal_class_word_9118 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 4099].
Definition legal_class_word_9119 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9120 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 8195.
Definition legal_class_word_9120 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 8195].
Definition legal_class_word_9121 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9122 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 16387.
Definition legal_class_word_9122 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 16387].
Definition legal_class_word_9123 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9124 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 20483.
Definition legal_class_word_9124 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 20483].
Definition legal_class_word_9125 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9126 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 35.
Definition legal_class_word_9126 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 35].
Definition legal_class_word_9127 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9128 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 4131.
Definition legal_class_word_9128 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 4131].
Definition legal_class_word_9129 (instruction:bits) := andB instruction (from_N 15 28799).
Definition legal_class_bit_9130 (instruction:bits) := N.eqb (N.land (to_N instruction) 28799) 8227.
Definition legal_class_word_9130 (instruction:bits) := [::N.eqb (N.land (to_N instruction) 28799) 8227].
Definition legal_class_bit_9131 (instruction:bits) := (legal_class_bit_9116 instruction)||(legal_class_bit_9118 instruction).
Definition legal_class_word_9131 (instruction:bits) := [::(legal_class_bit_9116 instruction)||(legal_class_bit_9118 instruction)].
Definition legal_class_bit_9132 (instruction:bits) := (legal_class_bit_9131 instruction)||(legal_class_bit_9120 instruction).
Definition legal_class_word_9132 (instruction:bits) := [::(legal_class_bit_9131 instruction)||(legal_class_bit_9120 instruction)].
Definition legal_class_bit_9133 (instruction:bits) := (legal_class_bit_9132 instruction)||(legal_class_bit_9122 instruction).
Definition legal_class_word_9133 (instruction:bits) := [::(legal_class_bit_9132 instruction)||(legal_class_bit_9122 instruction)].
Definition legal_class_bit_9134 (instruction:bits) := (legal_class_bit_9133 instruction)||(legal_class_bit_9124 instruction).
Definition legal_class_word_9134 (instruction:bits) := [::(legal_class_bit_9133 instruction)||(legal_class_bit_9124 instruction)].
Definition legal_class_bit_9135 (instruction:bits) := (legal_class_bit_9134 instruction)||(legal_class_bit_9126 instruction).
Definition legal_class_word_9135 (instruction:bits) := [::(legal_class_bit_9134 instruction)||(legal_class_bit_9126 instruction)].
Definition legal_class_bit_9136 (instruction:bits) := (legal_class_bit_9135 instruction)||(legal_class_bit_9128 instruction).
Definition legal_class_word_9136 (instruction:bits) := [::(legal_class_bit_9135 instruction)||(legal_class_bit_9128 instruction)].
Definition legal_class_bit_9137 (instruction:bits) := (legal_class_bit_9136 instruction)||(legal_class_bit_9130 instruction).
Definition legal_class_word_9137 (instruction:bits) := [::(legal_class_bit_9136 instruction)||(legal_class_bit_9130 instruction)].
Definition legal_class_bit_9138 (instruction:bits) := (legal_class_bit_9114 instruction)||(legal_class_bit_9137 instruction).
Definition legal_class_word_9138 (instruction:bits) := [::(legal_class_bit_9114 instruction)||(legal_class_bit_9137 instruction)].
Definition legal_class_value (node:nat) instruction : hvalue := if Nat.eqb node 44 then Gval(Fuint 32)instruction else match Nat.sub node 9029 with
|0%nat=>Gval(Fuint 32)(legal_class_word_9029 instruction)
|1%nat=>Gval(Fuint 1)(legal_class_word_9030 instruction)
|2%nat=>Gval(Fuint 32)(legal_class_word_9031 instruction)
|3%nat=>Gval(Fuint 1)(legal_class_word_9032 instruction)
|4%nat=>Gval(Fuint 32)(legal_class_word_9033 instruction)
|5%nat=>Gval(Fuint 1)(legal_class_word_9034 instruction)
|6%nat=>Gval(Fuint 32)(legal_class_word_9035 instruction)
|7%nat=>Gval(Fuint 1)(legal_class_word_9036 instruction)
|8%nat=>Gval(Fuint 32)(legal_class_word_9037 instruction)
|9%nat=>Gval(Fuint 1)(legal_class_word_9038 instruction)
|10%nat=>Gval(Fuint 32)(legal_class_word_9039 instruction)
|11%nat=>Gval(Fuint 1)(legal_class_word_9040 instruction)
|12%nat=>Gval(Fuint 32)(legal_class_word_9041 instruction)
|13%nat=>Gval(Fuint 1)(legal_class_word_9042 instruction)
|14%nat=>Gval(Fuint 32)(legal_class_word_9043 instruction)
|15%nat=>Gval(Fuint 1)(legal_class_word_9044 instruction)
|16%nat=>Gval(Fuint 32)(legal_class_word_9045 instruction)
|17%nat=>Gval(Fuint 1)(legal_class_word_9046 instruction)
|18%nat=>Gval(Fuint 32)(legal_class_word_9047 instruction)
|19%nat=>Gval(Fuint 1)(legal_class_word_9048 instruction)
|20%nat=>Gval(Fuint 32)(legal_class_word_9049 instruction)
|21%nat=>Gval(Fuint 1)(legal_class_word_9050 instruction)
|22%nat=>Gval(Fuint 1)(legal_class_word_9051 instruction)
|23%nat=>Gval(Fuint 1)(legal_class_word_9052 instruction)
|24%nat=>Gval(Fuint 1)(legal_class_word_9053 instruction)
|25%nat=>Gval(Fuint 1)(legal_class_word_9054 instruction)
|26%nat=>Gval(Fuint 1)(legal_class_word_9055 instruction)
|27%nat=>Gval(Fuint 1)(legal_class_word_9056 instruction)
|28%nat=>Gval(Fuint 1)(legal_class_word_9057 instruction)
|29%nat=>Gval(Fuint 1)(legal_class_word_9058 instruction)
|30%nat=>Gval(Fuint 1)(legal_class_word_9059 instruction)
|31%nat=>Gval(Fuint 1)(legal_class_word_9060 instruction)
|32%nat=>Gval(Fuint 32)(legal_class_word_9061 instruction)
|33%nat=>Gval(Fuint 1)(legal_class_word_9062 instruction)
|34%nat=>Gval(Fuint 32)(legal_class_word_9063 instruction)
|35%nat=>Gval(Fuint 1)(legal_class_word_9064 instruction)
|36%nat=>Gval(Fuint 32)(legal_class_word_9065 instruction)
|37%nat=>Gval(Fuint 1)(legal_class_word_9066 instruction)
|38%nat=>Gval(Fuint 32)(legal_class_word_9067 instruction)
|39%nat=>Gval(Fuint 1)(legal_class_word_9068 instruction)
|40%nat=>Gval(Fuint 32)(legal_class_word_9069 instruction)
|41%nat=>Gval(Fuint 1)(legal_class_word_9070 instruction)
|42%nat=>Gval(Fuint 32)(legal_class_word_9071 instruction)
|43%nat=>Gval(Fuint 1)(legal_class_word_9072 instruction)
|44%nat=>Gval(Fuint 32)(legal_class_word_9073 instruction)
|45%nat=>Gval(Fuint 1)(legal_class_word_9074 instruction)
|46%nat=>Gval(Fuint 32)(legal_class_word_9075 instruction)
|47%nat=>Gval(Fuint 1)(legal_class_word_9076 instruction)
|48%nat=>Gval(Fuint 32)(legal_class_word_9077 instruction)
|49%nat=>Gval(Fuint 1)(legal_class_word_9078 instruction)
|50%nat=>Gval(Fuint 32)(legal_class_word_9079 instruction)
|51%nat=>Gval(Fuint 1)(legal_class_word_9080 instruction)
|52%nat=>Gval(Fuint 1)(legal_class_word_9081 instruction)
|53%nat=>Gval(Fuint 1)(legal_class_word_9082 instruction)
|54%nat=>Gval(Fuint 1)(legal_class_word_9083 instruction)
|55%nat=>Gval(Fuint 1)(legal_class_word_9084 instruction)
|56%nat=>Gval(Fuint 1)(legal_class_word_9085 instruction)
|57%nat=>Gval(Fuint 1)(legal_class_word_9086 instruction)
|58%nat=>Gval(Fuint 1)(legal_class_word_9087 instruction)
|59%nat=>Gval(Fuint 1)(legal_class_word_9088 instruction)
|60%nat=>Gval(Fuint 1)(legal_class_word_9089 instruction)
|61%nat=>Gval(Fuint 1)(legal_class_word_9090 instruction)
|62%nat=>Gval(Fuint 32)(legal_class_word_9091 instruction)
|63%nat=>Gval(Fuint 1)(legal_class_word_9092 instruction)
|64%nat=>Gval(Fuint 32)(legal_class_word_9093 instruction)
|65%nat=>Gval(Fuint 1)(legal_class_word_9094 instruction)
|66%nat=>Gval(Fuint 32)(legal_class_word_9095 instruction)
|67%nat=>Gval(Fuint 1)(legal_class_word_9096 instruction)
|68%nat=>Gval(Fuint 32)(legal_class_word_9097 instruction)
|69%nat=>Gval(Fuint 1)(legal_class_word_9098 instruction)
|70%nat=>Gval(Fuint 32)(legal_class_word_9099 instruction)
|71%nat=>Gval(Fuint 1)(legal_class_word_9100 instruction)
|72%nat=>Gval(Fuint 32)(legal_class_word_9101 instruction)
|73%nat=>Gval(Fuint 1)(legal_class_word_9102 instruction)
|74%nat=>Gval(Fuint 32)(legal_class_word_9103 instruction)
|75%nat=>Gval(Fuint 1)(legal_class_word_9104 instruction)
|76%nat=>Gval(Fuint 32)(legal_class_word_9105 instruction)
|77%nat=>Gval(Fuint 1)(legal_class_word_9106 instruction)
|78%nat=>Gval(Fuint 1)(legal_class_word_9107 instruction)
|79%nat=>Gval(Fuint 1)(legal_class_word_9108 instruction)
|80%nat=>Gval(Fuint 1)(legal_class_word_9109 instruction)
|81%nat=>Gval(Fuint 1)(legal_class_word_9110 instruction)
|82%nat=>Gval(Fuint 1)(legal_class_word_9111 instruction)
|83%nat=>Gval(Fuint 1)(legal_class_word_9112 instruction)
|84%nat=>Gval(Fuint 1)(legal_class_word_9113 instruction)
|85%nat=>Gval(Fuint 1)(legal_class_word_9114 instruction)
|86%nat=>Gval(Fuint 32)(legal_class_word_9115 instruction)
|87%nat=>Gval(Fuint 1)(legal_class_word_9116 instruction)
|88%nat=>Gval(Fuint 32)(legal_class_word_9117 instruction)
|89%nat=>Gval(Fuint 1)(legal_class_word_9118 instruction)
|90%nat=>Gval(Fuint 32)(legal_class_word_9119 instruction)
|91%nat=>Gval(Fuint 1)(legal_class_word_9120 instruction)
|92%nat=>Gval(Fuint 32)(legal_class_word_9121 instruction)
|93%nat=>Gval(Fuint 1)(legal_class_word_9122 instruction)
|94%nat=>Gval(Fuint 32)(legal_class_word_9123 instruction)
|95%nat=>Gval(Fuint 1)(legal_class_word_9124 instruction)
|96%nat=>Gval(Fuint 32)(legal_class_word_9125 instruction)
|97%nat=>Gval(Fuint 1)(legal_class_word_9126 instruction)
|98%nat=>Gval(Fuint 32)(legal_class_word_9127 instruction)
|99%nat=>Gval(Fuint 1)(legal_class_word_9128 instruction)
|100%nat=>Gval(Fuint 32)(legal_class_word_9129 instruction)
|101%nat=>Gval(Fuint 1)(legal_class_word_9130 instruction)
|102%nat=>Gval(Fuint 1)(legal_class_word_9131 instruction)
|103%nat=>Gval(Fuint 1)(legal_class_word_9132 instruction)
|104%nat=>Gval(Fuint 1)(legal_class_word_9133 instruction)
|105%nat=>Gval(Fuint 1)(legal_class_word_9134 instruction)
|106%nat=>Gval(Fuint 1)(legal_class_word_9135 instruction)
|107%nat=>Gval(Fuint 1)(legal_class_word_9136 instruction)
|108%nat=>Gval(Fuint 1)(legal_class_word_9137 instruction)
|109%nat=>Gval(Fuint 1)(legal_class_word_9138 instruction)
|_=>Gval(Fuint 1)[::false] end.
Definition legal_class_rank (node:nat) := match Nat.sub node 9029 with
|0%nat=>1%nat
|1%nat=>2%nat
|2%nat=>1%nat
|3%nat=>2%nat
|4%nat=>1%nat
|5%nat=>2%nat
|6%nat=>1%nat
|7%nat=>2%nat
|8%nat=>1%nat
|9%nat=>2%nat
|10%nat=>1%nat
|11%nat=>2%nat
|12%nat=>1%nat
|13%nat=>2%nat
|14%nat=>1%nat
|15%nat=>2%nat
|16%nat=>1%nat
|17%nat=>2%nat
|18%nat=>1%nat
|19%nat=>2%nat
|20%nat=>1%nat
|21%nat=>2%nat
|22%nat=>3%nat
|23%nat=>4%nat
|24%nat=>5%nat
|25%nat=>6%nat
|26%nat=>7%nat
|27%nat=>8%nat
|28%nat=>9%nat
|29%nat=>10%nat
|30%nat=>11%nat
|31%nat=>12%nat
|32%nat=>1%nat
|33%nat=>2%nat
|34%nat=>1%nat
|35%nat=>2%nat
|36%nat=>1%nat
|37%nat=>2%nat
|38%nat=>1%nat
|39%nat=>2%nat
|40%nat=>1%nat
|41%nat=>2%nat
|42%nat=>1%nat
|43%nat=>2%nat
|44%nat=>1%nat
|45%nat=>2%nat
|46%nat=>1%nat
|47%nat=>2%nat
|48%nat=>1%nat
|49%nat=>2%nat
|50%nat=>1%nat
|51%nat=>2%nat
|52%nat=>3%nat
|53%nat=>4%nat
|54%nat=>5%nat
|55%nat=>6%nat
|56%nat=>7%nat
|57%nat=>8%nat
|58%nat=>9%nat
|59%nat=>10%nat
|60%nat=>11%nat
|61%nat=>13%nat
|62%nat=>1%nat
|63%nat=>2%nat
|64%nat=>1%nat
|65%nat=>2%nat
|66%nat=>1%nat
|67%nat=>2%nat
|68%nat=>1%nat
|69%nat=>2%nat
|70%nat=>1%nat
|71%nat=>2%nat
|72%nat=>1%nat
|73%nat=>2%nat
|74%nat=>1%nat
|75%nat=>2%nat
|76%nat=>1%nat
|77%nat=>2%nat
|78%nat=>3%nat
|79%nat=>4%nat
|80%nat=>5%nat
|81%nat=>6%nat
|82%nat=>7%nat
|83%nat=>8%nat
|84%nat=>9%nat
|85%nat=>14%nat
|86%nat=>1%nat
|87%nat=>2%nat
|88%nat=>1%nat
|89%nat=>2%nat
|90%nat=>1%nat
|91%nat=>2%nat
|92%nat=>1%nat
|93%nat=>2%nat
|94%nat=>1%nat
|95%nat=>2%nat
|96%nat=>1%nat
|97%nat=>2%nat
|98%nat=>1%nat
|99%nat=>2%nat
|100%nat=>1%nat
|101%nat=>2%nat
|102%nat=>3%nat
|103%nat=>4%nat
|104%nat=>5%nat
|105%nat=>6%nat
|106%nat=>7%nat
|107%nat=>8%nat
|108%nat=>9%nat
|109%nat=>15%nat
|_=>0%nat end.
Definition legal_class_dependencies (node:nat) := match Nat.sub node 9029 with
|0%nat=>[::44%nat]
|1%nat=>[::9029%nat]
|2%nat=>[::44%nat]
|3%nat=>[::9031%nat]
|4%nat=>[::44%nat]
|5%nat=>[::9033%nat]
|6%nat=>[::44%nat]
|7%nat=>[::9035%nat]
|8%nat=>[::44%nat]
|9%nat=>[::9037%nat]
|10%nat=>[::44%nat]
|11%nat=>[::9039%nat]
|12%nat=>[::44%nat]
|13%nat=>[::9041%nat]
|14%nat=>[::44%nat]
|15%nat=>[::9043%nat]
|16%nat=>[::44%nat]
|17%nat=>[::9045%nat]
|18%nat=>[::44%nat]
|19%nat=>[::9047%nat]
|20%nat=>[::44%nat]
|21%nat=>[::9049%nat]
|22%nat=>[::9030%nat;9032%nat]
|23%nat=>[::9051%nat;9034%nat]
|24%nat=>[::9052%nat;9036%nat]
|25%nat=>[::9053%nat;9038%nat]
|26%nat=>[::9054%nat;9040%nat]
|27%nat=>[::9055%nat;9042%nat]
|28%nat=>[::9056%nat;9044%nat]
|29%nat=>[::9057%nat;9046%nat]
|30%nat=>[::9058%nat;9048%nat]
|31%nat=>[::9059%nat;9050%nat]
|32%nat=>[::44%nat]
|33%nat=>[::9061%nat]
|34%nat=>[::44%nat]
|35%nat=>[::9063%nat]
|36%nat=>[::44%nat]
|37%nat=>[::9065%nat]
|38%nat=>[::44%nat]
|39%nat=>[::9067%nat]
|40%nat=>[::44%nat]
|41%nat=>[::9069%nat]
|42%nat=>[::44%nat]
|43%nat=>[::9071%nat]
|44%nat=>[::44%nat]
|45%nat=>[::9073%nat]
|46%nat=>[::44%nat]
|47%nat=>[::9075%nat]
|48%nat=>[::44%nat]
|49%nat=>[::9077%nat]
|50%nat=>[::44%nat]
|51%nat=>[::9079%nat]
|52%nat=>[::9062%nat;9064%nat]
|53%nat=>[::9081%nat;9066%nat]
|54%nat=>[::9082%nat;9068%nat]
|55%nat=>[::9083%nat;9070%nat]
|56%nat=>[::9084%nat;9072%nat]
|57%nat=>[::9085%nat;9074%nat]
|58%nat=>[::9086%nat;9076%nat]
|59%nat=>[::9087%nat;9078%nat]
|60%nat=>[::9088%nat;9080%nat]
|61%nat=>[::9060%nat;9089%nat]
|62%nat=>[::44%nat]
|63%nat=>[::9091%nat]
|64%nat=>[::44%nat]
|65%nat=>[::9093%nat]
|66%nat=>[::44%nat]
|67%nat=>[::9095%nat]
|68%nat=>[::44%nat]
|69%nat=>[::9097%nat]
|70%nat=>[::44%nat]
|71%nat=>[::9099%nat]
|72%nat=>[::44%nat]
|73%nat=>[::9101%nat]
|74%nat=>[::44%nat]
|75%nat=>[::9103%nat]
|76%nat=>[::44%nat]
|77%nat=>[::9105%nat]
|78%nat=>[::9092%nat;9094%nat]
|79%nat=>[::9107%nat;9096%nat]
|80%nat=>[::9108%nat;9098%nat]
|81%nat=>[::9109%nat;9100%nat]
|82%nat=>[::9110%nat;9102%nat]
|83%nat=>[::9111%nat;9104%nat]
|84%nat=>[::9112%nat;9106%nat]
|85%nat=>[::9090%nat;9113%nat]
|86%nat=>[::44%nat]
|87%nat=>[::9115%nat]
|88%nat=>[::44%nat]
|89%nat=>[::9117%nat]
|90%nat=>[::44%nat]
|91%nat=>[::9119%nat]
|92%nat=>[::44%nat]
|93%nat=>[::9121%nat]
|94%nat=>[::44%nat]
|95%nat=>[::9123%nat]
|96%nat=>[::44%nat]
|97%nat=>[::9125%nat]
|98%nat=>[::44%nat]
|99%nat=>[::9127%nat]
|100%nat=>[::44%nat]
|101%nat=>[::9129%nat]
|102%nat=>[::9116%nat;9118%nat]
|103%nat=>[::9131%nat;9120%nat]
|104%nat=>[::9132%nat;9122%nat]
|105%nat=>[::9133%nat;9124%nat]
|106%nat=>[::9134%nat;9126%nat]
|107%nat=>[::9135%nat;9128%nat]
|108%nat=>[::9136%nat;9130%nat]
|109%nat=>[::9114%nat;9137%nat]
|_=>[::] end.
Lemma legal_class_step index invalid old result instruction : (index<110)%coq_nat ->
 (forall dep,List.In dep(legal_class_dependencies(9029+index)%nat)->VM.find(N.of_nat dep)old=Some(legal_class_value dep instruction))->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(N.of_nat(9029+index)%nat)result=Some(legal_class_value(9029+index)%nat instruction).
Proof. intros Bound Values Step.
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9029 legal_class_expr_9029);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 0%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9029 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9029%nat ltac:(vm_compute;tauto))as H9029.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9030 legal_class_expr_9030);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 1%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9030 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9029.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 5)(from_N 5 19))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9030 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9031 legal_class_expr_9031);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 2%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9031 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9031%nat ltac:(vm_compute;tauto))as H9031.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9032 legal_class_expr_9032);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 3%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9032 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9031.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 14)(from_N 14 8211))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9032 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9033 legal_class_expr_9033);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 4%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9033 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9033%nat ltac:(vm_compute;tauto))as H9033.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9034 legal_class_expr_9034);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 5%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9034 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9033.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 14)(from_N 14 12307))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9034 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9035 legal_class_expr_9035);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 6%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9035 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9035%nat ltac:(vm_compute;tauto))as H9035.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9036 legal_class_expr_9036);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 7%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9036 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9035.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 28691))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9036 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9037 legal_class_expr_9037);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 8%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9037 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9037%nat ltac:(vm_compute;tauto))as H9037.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9038 legal_class_expr_9038);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 9%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9038 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9037.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 24595))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9038 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9039 legal_class_expr_9039);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 10%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9039 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9039%nat ltac:(vm_compute;tauto))as H9039.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9040 legal_class_expr_9040);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 11%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9040 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9039.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 16403))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9040 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9041 legal_class_expr_9041);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 12%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9041 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9041%nat ltac:(vm_compute;tauto))as H9041.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9042 legal_class_expr_9042);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 13%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9042 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9041.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 13)(from_N 13 4115))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9042 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9043 legal_class_expr_9043);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 14%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9043 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9043%nat ltac:(vm_compute;tauto))as H9043.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9044 legal_class_expr_9044);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 15%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9044 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9043.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 20499))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9044 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9045 legal_class_expr_9045);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 16%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9045 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9045%nat ltac:(vm_compute;tauto))as H9045.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9046 legal_class_expr_9046);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 17%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9046 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9045.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 31)(from_N 31 1073762323))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9046 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9047 legal_class_expr_9047);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 18%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9047 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9047%nat ltac:(vm_compute;tauto))as H9047.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9048 legal_class_expr_9048);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 19%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9048 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9047.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 6)(from_N 6 55))(Gval(Fuint(maxn 32 7))(andB instruction(from_N 7 127)))=Some(Gval(Fuint 1)(legal_class_word_9048 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9049 legal_class_expr_9049);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 20%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9049 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9049%nat ltac:(vm_compute;tauto))as H9049.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9050 legal_class_expr_9050);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 21%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9050 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9049.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 5)(from_N 5 23))(Gval(Fuint(maxn 32 7))(andB instruction(from_N 7 127)))=Some(Gval(Fuint 1)(legal_class_word_9050 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 9030%nat ltac:(vm_compute;tauto))as H9030.
pose proof(Values 9032%nat ltac:(vm_compute;tauto))as H9032.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9051 legal_class_expr_9051);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 22%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9051 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9030 H9032.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9030 instruction])(Gval(Fuint 1)[::legal_class_bit_9032 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9030 instruction || legal_class_bit_9032 instruction])).
destruct(legal_class_bit_9030 instruction),(legal_class_bit_9032 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9051%nat ltac:(vm_compute;tauto))as H9051.
pose proof(Values 9034%nat ltac:(vm_compute;tauto))as H9034.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9052 legal_class_expr_9052);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 23%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9052 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9051 H9034.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9051 instruction])(Gval(Fuint 1)[::legal_class_bit_9034 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9051 instruction || legal_class_bit_9034 instruction])).
destruct(legal_class_bit_9051 instruction),(legal_class_bit_9034 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9052%nat ltac:(vm_compute;tauto))as H9052.
pose proof(Values 9036%nat ltac:(vm_compute;tauto))as H9036.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9053 legal_class_expr_9053);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 24%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9053 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9052 H9036.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9052 instruction])(Gval(Fuint 1)[::legal_class_bit_9036 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9052 instruction || legal_class_bit_9036 instruction])).
destruct(legal_class_bit_9052 instruction),(legal_class_bit_9036 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9053%nat ltac:(vm_compute;tauto))as H9053.
pose proof(Values 9038%nat ltac:(vm_compute;tauto))as H9038.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9054 legal_class_expr_9054);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 25%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9054 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9053 H9038.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9053 instruction])(Gval(Fuint 1)[::legal_class_bit_9038 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9053 instruction || legal_class_bit_9038 instruction])).
destruct(legal_class_bit_9053 instruction),(legal_class_bit_9038 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9054%nat ltac:(vm_compute;tauto))as H9054.
pose proof(Values 9040%nat ltac:(vm_compute;tauto))as H9040.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9055 legal_class_expr_9055);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 26%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9055 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9054 H9040.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9054 instruction])(Gval(Fuint 1)[::legal_class_bit_9040 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9054 instruction || legal_class_bit_9040 instruction])).
destruct(legal_class_bit_9054 instruction),(legal_class_bit_9040 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9055%nat ltac:(vm_compute;tauto))as H9055.
pose proof(Values 9042%nat ltac:(vm_compute;tauto))as H9042.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9056 legal_class_expr_9056);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 27%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9056 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9055 H9042.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9055 instruction])(Gval(Fuint 1)[::legal_class_bit_9042 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9055 instruction || legal_class_bit_9042 instruction])).
destruct(legal_class_bit_9055 instruction),(legal_class_bit_9042 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9056%nat ltac:(vm_compute;tauto))as H9056.
pose proof(Values 9044%nat ltac:(vm_compute;tauto))as H9044.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9057 legal_class_expr_9057);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 28%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9057 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9056 H9044.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9056 instruction])(Gval(Fuint 1)[::legal_class_bit_9044 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9056 instruction || legal_class_bit_9044 instruction])).
destruct(legal_class_bit_9056 instruction),(legal_class_bit_9044 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9057%nat ltac:(vm_compute;tauto))as H9057.
pose proof(Values 9046%nat ltac:(vm_compute;tauto))as H9046.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9058 legal_class_expr_9058);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 29%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9058 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9057 H9046.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9057 instruction])(Gval(Fuint 1)[::legal_class_bit_9046 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9057 instruction || legal_class_bit_9046 instruction])).
destruct(legal_class_bit_9057 instruction),(legal_class_bit_9046 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9058%nat ltac:(vm_compute;tauto))as H9058.
pose proof(Values 9048%nat ltac:(vm_compute;tauto))as H9048.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9059 legal_class_expr_9059);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 30%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9059 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9058 H9048.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9058 instruction])(Gval(Fuint 1)[::legal_class_bit_9048 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9058 instruction || legal_class_bit_9048 instruction])).
destruct(legal_class_bit_9058 instruction),(legal_class_bit_9048 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9059%nat ltac:(vm_compute;tauto))as H9059.
pose proof(Values 9050%nat ltac:(vm_compute;tauto))as H9050.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9060 legal_class_expr_9060);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 31%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9060 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9059 H9050.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9059 instruction])(Gval(Fuint 1)[::legal_class_bit_9050 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9059 instruction || legal_class_bit_9050 instruction])).
destruct(legal_class_bit_9059 instruction),(legal_class_bit_9050 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9061 legal_class_expr_9061);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 32%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9061 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9061%nat ltac:(vm_compute;tauto))as H9061.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9062 legal_class_expr_9062);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 33%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9062 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9061.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 6)(from_N 6 51))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9062 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9063 legal_class_expr_9063);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 34%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9063 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9063%nat ltac:(vm_compute;tauto))as H9063.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9064 legal_class_expr_9064);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 35%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9064 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9063.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 14)(from_N 14 8243))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9064 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9065 legal_class_expr_9065);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 36%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9065 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9065%nat ltac:(vm_compute;tauto))as H9065.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9066 legal_class_expr_9066);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 37%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9066 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9065.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 14)(from_N 14 12339))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9066 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9067 legal_class_expr_9067);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 38%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9067 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9067%nat ltac:(vm_compute;tauto))as H9067.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9068 legal_class_expr_9068);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 39%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9068 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9067.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 28723))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9068 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9069 legal_class_expr_9069);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 40%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9069 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9069%nat ltac:(vm_compute;tauto))as H9069.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9070 legal_class_expr_9070);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 41%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9070 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9069.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 24627))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9070 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9071 legal_class_expr_9071);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 42%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9071 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9071%nat ltac:(vm_compute;tauto))as H9071.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9072 legal_class_expr_9072);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 43%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9072 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9071.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 16435))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9072 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9073 legal_class_expr_9073);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 44%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9073 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9073%nat ltac:(vm_compute;tauto))as H9073.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9074 legal_class_expr_9074);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 45%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9074 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9073.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 13)(from_N 13 4147))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9074 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9075 legal_class_expr_9075);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 46%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9075 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9075%nat ltac:(vm_compute;tauto))as H9075.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9076 legal_class_expr_9076);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 47%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9076 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9075.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 20531))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9076 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9077 legal_class_expr_9077);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 48%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9077 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9077%nat ltac:(vm_compute;tauto))as H9077.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9078 legal_class_expr_9078);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 49%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9078 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9077.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 31)(from_N 31 1073741875))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9078 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9079 legal_class_expr_9079);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 50%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9079 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9079%nat ltac:(vm_compute;tauto))as H9079.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9080 legal_class_expr_9080);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 51%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9080 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9079.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 31)(from_N 31 1073762355))(Gval(Fuint(maxn 32 32))(andB instruction(from_N 32 4261441663)))=Some(Gval(Fuint 1)(legal_class_word_9080 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 9062%nat ltac:(vm_compute;tauto))as H9062.
pose proof(Values 9064%nat ltac:(vm_compute;tauto))as H9064.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9081 legal_class_expr_9081);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 52%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9081 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9062 H9064.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9062 instruction])(Gval(Fuint 1)[::legal_class_bit_9064 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9062 instruction || legal_class_bit_9064 instruction])).
destruct(legal_class_bit_9062 instruction),(legal_class_bit_9064 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9081%nat ltac:(vm_compute;tauto))as H9081.
pose proof(Values 9066%nat ltac:(vm_compute;tauto))as H9066.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9082 legal_class_expr_9082);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 53%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9082 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9081 H9066.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9081 instruction])(Gval(Fuint 1)[::legal_class_bit_9066 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9081 instruction || legal_class_bit_9066 instruction])).
destruct(legal_class_bit_9081 instruction),(legal_class_bit_9066 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9082%nat ltac:(vm_compute;tauto))as H9082.
pose proof(Values 9068%nat ltac:(vm_compute;tauto))as H9068.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9083 legal_class_expr_9083);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 54%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9083 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9082 H9068.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9082 instruction])(Gval(Fuint 1)[::legal_class_bit_9068 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9082 instruction || legal_class_bit_9068 instruction])).
destruct(legal_class_bit_9082 instruction),(legal_class_bit_9068 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9083%nat ltac:(vm_compute;tauto))as H9083.
pose proof(Values 9070%nat ltac:(vm_compute;tauto))as H9070.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9084 legal_class_expr_9084);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 55%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9084 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9083 H9070.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9083 instruction])(Gval(Fuint 1)[::legal_class_bit_9070 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9083 instruction || legal_class_bit_9070 instruction])).
destruct(legal_class_bit_9083 instruction),(legal_class_bit_9070 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9084%nat ltac:(vm_compute;tauto))as H9084.
pose proof(Values 9072%nat ltac:(vm_compute;tauto))as H9072.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9085 legal_class_expr_9085);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 56%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9085 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9084 H9072.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9084 instruction])(Gval(Fuint 1)[::legal_class_bit_9072 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9084 instruction || legal_class_bit_9072 instruction])).
destruct(legal_class_bit_9084 instruction),(legal_class_bit_9072 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9085%nat ltac:(vm_compute;tauto))as H9085.
pose proof(Values 9074%nat ltac:(vm_compute;tauto))as H9074.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9086 legal_class_expr_9086);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 57%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9086 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9085 H9074.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9085 instruction])(Gval(Fuint 1)[::legal_class_bit_9074 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9085 instruction || legal_class_bit_9074 instruction])).
destruct(legal_class_bit_9085 instruction),(legal_class_bit_9074 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9086%nat ltac:(vm_compute;tauto))as H9086.
pose proof(Values 9076%nat ltac:(vm_compute;tauto))as H9076.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9087 legal_class_expr_9087);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 58%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9087 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9086 H9076.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9086 instruction])(Gval(Fuint 1)[::legal_class_bit_9076 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9086 instruction || legal_class_bit_9076 instruction])).
destruct(legal_class_bit_9086 instruction),(legal_class_bit_9076 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9087%nat ltac:(vm_compute;tauto))as H9087.
pose proof(Values 9078%nat ltac:(vm_compute;tauto))as H9078.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9088 legal_class_expr_9088);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 59%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9088 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9087 H9078.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9087 instruction])(Gval(Fuint 1)[::legal_class_bit_9078 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9087 instruction || legal_class_bit_9078 instruction])).
destruct(legal_class_bit_9087 instruction),(legal_class_bit_9078 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9088%nat ltac:(vm_compute;tauto))as H9088.
pose proof(Values 9080%nat ltac:(vm_compute;tauto))as H9080.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9089 legal_class_expr_9089);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 60%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9089 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9088 H9080.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9088 instruction])(Gval(Fuint 1)[::legal_class_bit_9080 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9088 instruction || legal_class_bit_9080 instruction])).
destruct(legal_class_bit_9088 instruction),(legal_class_bit_9080 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9060%nat ltac:(vm_compute;tauto))as H9060.
pose proof(Values 9089%nat ltac:(vm_compute;tauto))as H9089.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9090 legal_class_expr_9090);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 61%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9090 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9060 H9089.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9060 instruction])(Gval(Fuint 1)[::legal_class_bit_9089 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9060 instruction || legal_class_bit_9089 instruction])).
destruct(legal_class_bit_9060 instruction),(legal_class_bit_9089 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9091 legal_class_expr_9091);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 62%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9091 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9091%nat ltac:(vm_compute;tauto))as H9091.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9092 legal_class_expr_9092);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 63%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9092 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9091.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 7)(from_N 7 111))(Gval(Fuint(maxn 32 7))(andB instruction(from_N 7 127)))=Some(Gval(Fuint 1)(legal_class_word_9092 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9093 legal_class_expr_9093);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 64%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9093 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9093%nat ltac:(vm_compute;tauto))as H9093.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9094 legal_class_expr_9094);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 65%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9094 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9093.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 7)(from_N 7 103))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9094 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9095 legal_class_expr_9095);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 66%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9095 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9095%nat ltac:(vm_compute;tauto))as H9095.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9096 legal_class_expr_9096);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 67%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9096 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9095.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 7)(from_N 7 99))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9096 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9097 legal_class_expr_9097);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 68%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9097 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9097%nat ltac:(vm_compute;tauto))as H9097.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9098 legal_class_expr_9098);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 69%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9098 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9097.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 13)(from_N 13 4195))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9098 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9099 legal_class_expr_9099);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 70%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9099 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9099%nat ltac:(vm_compute;tauto))as H9099.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9100 legal_class_expr_9100);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 71%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9100 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9099.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 16483))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9100 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9101 legal_class_expr_9101);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 72%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9101 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9101%nat ltac:(vm_compute;tauto))as H9101.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9102 legal_class_expr_9102);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 73%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9102 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9101.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 24675))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9102 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9103 legal_class_expr_9103);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 74%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9103 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9103%nat ltac:(vm_compute;tauto))as H9103.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9104 legal_class_expr_9104);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 75%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9104 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9103.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 20579))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9104 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9105 legal_class_expr_9105);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 76%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9105 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9105%nat ltac:(vm_compute;tauto))as H9105.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9106 legal_class_expr_9106);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 77%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9106 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9105.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 28771))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9106 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 9092%nat ltac:(vm_compute;tauto))as H9092.
pose proof(Values 9094%nat ltac:(vm_compute;tauto))as H9094.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9107 legal_class_expr_9107);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 78%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9107 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9092 H9094.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9092 instruction])(Gval(Fuint 1)[::legal_class_bit_9094 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9092 instruction || legal_class_bit_9094 instruction])).
destruct(legal_class_bit_9092 instruction),(legal_class_bit_9094 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9107%nat ltac:(vm_compute;tauto))as H9107.
pose proof(Values 9096%nat ltac:(vm_compute;tauto))as H9096.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9108 legal_class_expr_9108);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 79%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9108 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9107 H9096.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9107 instruction])(Gval(Fuint 1)[::legal_class_bit_9096 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9107 instruction || legal_class_bit_9096 instruction])).
destruct(legal_class_bit_9107 instruction),(legal_class_bit_9096 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9108%nat ltac:(vm_compute;tauto))as H9108.
pose proof(Values 9098%nat ltac:(vm_compute;tauto))as H9098.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9109 legal_class_expr_9109);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 80%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9109 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9108 H9098.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9108 instruction])(Gval(Fuint 1)[::legal_class_bit_9098 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9108 instruction || legal_class_bit_9098 instruction])).
destruct(legal_class_bit_9108 instruction),(legal_class_bit_9098 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9109%nat ltac:(vm_compute;tauto))as H9109.
pose proof(Values 9100%nat ltac:(vm_compute;tauto))as H9100.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9110 legal_class_expr_9110);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 81%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9110 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9109 H9100.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9109 instruction])(Gval(Fuint 1)[::legal_class_bit_9100 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9109 instruction || legal_class_bit_9100 instruction])).
destruct(legal_class_bit_9109 instruction),(legal_class_bit_9100 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9110%nat ltac:(vm_compute;tauto))as H9110.
pose proof(Values 9102%nat ltac:(vm_compute;tauto))as H9102.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9111 legal_class_expr_9111);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 82%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9111 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9110 H9102.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9110 instruction])(Gval(Fuint 1)[::legal_class_bit_9102 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9110 instruction || legal_class_bit_9102 instruction])).
destruct(legal_class_bit_9110 instruction),(legal_class_bit_9102 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9111%nat ltac:(vm_compute;tauto))as H9111.
pose proof(Values 9104%nat ltac:(vm_compute;tauto))as H9104.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9112 legal_class_expr_9112);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 83%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9112 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9111 H9104.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9111 instruction])(Gval(Fuint 1)[::legal_class_bit_9104 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9111 instruction || legal_class_bit_9104 instruction])).
destruct(legal_class_bit_9111 instruction),(legal_class_bit_9104 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9112%nat ltac:(vm_compute;tauto))as H9112.
pose proof(Values 9106%nat ltac:(vm_compute;tauto))as H9106.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9113 legal_class_expr_9113);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 84%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9113 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9112 H9106.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9112 instruction])(Gval(Fuint 1)[::legal_class_bit_9106 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9112 instruction || legal_class_bit_9106 instruction])).
destruct(legal_class_bit_9112 instruction),(legal_class_bit_9106 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9090%nat ltac:(vm_compute;tauto))as H9090.
pose proof(Values 9113%nat ltac:(vm_compute;tauto))as H9113.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9114 legal_class_expr_9114);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 85%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9114 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9090 H9113.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9090 instruction])(Gval(Fuint 1)[::legal_class_bit_9113 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9090 instruction || legal_class_bit_9113 instruction])).
destruct(legal_class_bit_9090 instruction),(legal_class_bit_9113 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9115 legal_class_expr_9115);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 86%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9115 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9115%nat ltac:(vm_compute;tauto))as H9115.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9116 legal_class_expr_9116);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 87%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9116 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9115.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 2)(from_N 2 3))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9116 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9117 legal_class_expr_9117);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 88%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9117 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9117%nat ltac:(vm_compute;tauto))as H9117.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9118 legal_class_expr_9118);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 89%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9118 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9117.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 13)(from_N 13 4099))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9118 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9119 legal_class_expr_9119);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 90%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9119 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9119%nat ltac:(vm_compute;tauto))as H9119.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9120 legal_class_expr_9120);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 91%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9120 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9119.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 14)(from_N 14 8195))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9120 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9121 legal_class_expr_9121);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 92%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9121 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9121%nat ltac:(vm_compute;tauto))as H9121.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9122 legal_class_expr_9122);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 93%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9122 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9121.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 16387))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9122 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9123 legal_class_expr_9123);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 94%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9123 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9123%nat ltac:(vm_compute;tauto))as H9123.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9124 legal_class_expr_9124);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 95%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9124 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9123.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 15)(from_N 15 20483))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9124 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9125 legal_class_expr_9125);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 96%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9125 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9125%nat ltac:(vm_compute;tauto))as H9125.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9126 legal_class_expr_9126);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 97%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9126 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9125.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 6)(from_N 6 35))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9126 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9127 legal_class_expr_9127);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 98%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9127 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9127%nat ltac:(vm_compute;tauto))as H9127.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9128 legal_class_expr_9128);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 99%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9128 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9127.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 13)(from_N 13 4131))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9128 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 44%nat ltac:(vm_compute;tauto))as H44.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9129 legal_class_expr_9129);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 100%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9129 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H44.
cbn [legal_class_value].
reflexivity. }
destruct index as[|index].
{
pose proof(Values 9129%nat ltac:(vm_compute;tauto))as H9129.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9130 legal_class_expr_9130);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 101%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9130 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9129.
cbn [legal_class_value].
change(eval_binop(Bcomp Beq)(Gval(Fuint 14)(from_N 14 8227))(Gval(Fuint(maxn 32 15))(andB instruction(from_N 15 28799)))=Some(Gval(Fuint 1)(legal_class_word_9130 instruction))).
rewrite redirect_mask_decode. reflexivity. }
destruct index as[|index].
{
pose proof(Values 9116%nat ltac:(vm_compute;tauto))as H9116.
pose proof(Values 9118%nat ltac:(vm_compute;tauto))as H9118.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9131 legal_class_expr_9131);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 102%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9131 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9116 H9118.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9116 instruction])(Gval(Fuint 1)[::legal_class_bit_9118 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9116 instruction || legal_class_bit_9118 instruction])).
destruct(legal_class_bit_9116 instruction),(legal_class_bit_9118 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9131%nat ltac:(vm_compute;tauto))as H9131.
pose proof(Values 9120%nat ltac:(vm_compute;tauto))as H9120.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9132 legal_class_expr_9132);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 103%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9132 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9131 H9120.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9131 instruction])(Gval(Fuint 1)[::legal_class_bit_9120 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9131 instruction || legal_class_bit_9120 instruction])).
destruct(legal_class_bit_9131 instruction),(legal_class_bit_9120 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9132%nat ltac:(vm_compute;tauto))as H9132.
pose proof(Values 9122%nat ltac:(vm_compute;tauto))as H9122.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9133 legal_class_expr_9133);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 104%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9133 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9132 H9122.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9132 instruction])(Gval(Fuint 1)[::legal_class_bit_9122 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9132 instruction || legal_class_bit_9122 instruction])).
destruct(legal_class_bit_9132 instruction),(legal_class_bit_9122 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9133%nat ltac:(vm_compute;tauto))as H9133.
pose proof(Values 9124%nat ltac:(vm_compute;tauto))as H9124.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9134 legal_class_expr_9134);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 105%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9134 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9133 H9124.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9133 instruction])(Gval(Fuint 1)[::legal_class_bit_9124 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9133 instruction || legal_class_bit_9124 instruction])).
destruct(legal_class_bit_9133 instruction),(legal_class_bit_9124 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9134%nat ltac:(vm_compute;tauto))as H9134.
pose proof(Values 9126%nat ltac:(vm_compute;tauto))as H9126.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9135 legal_class_expr_9135);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 106%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9135 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9134 H9126.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9134 instruction])(Gval(Fuint 1)[::legal_class_bit_9126 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9134 instruction || legal_class_bit_9126 instruction])).
destruct(legal_class_bit_9134 instruction),(legal_class_bit_9126 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9135%nat ltac:(vm_compute;tauto))as H9135.
pose proof(Values 9128%nat ltac:(vm_compute;tauto))as H9128.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9136 legal_class_expr_9136);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 107%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9136 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9135 H9128.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9135 instruction])(Gval(Fuint 1)[::legal_class_bit_9128 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9135 instruction || legal_class_bit_9128 instruction])).
destruct(legal_class_bit_9135 instruction),(legal_class_bit_9128 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9136%nat ltac:(vm_compute;tauto))as H9136.
pose proof(Values 9130%nat ltac:(vm_compute;tauto))as H9130.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9137 legal_class_expr_9137);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 108%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9137 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9136 H9130.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9136 instruction])(Gval(Fuint 1)[::legal_class_bit_9130 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9136 instruction || legal_class_bit_9130 instruction])).
destruct(legal_class_bit_9136 instruction),(legal_class_bit_9130 instruction);reflexivity. }
destruct index as[|index].
{
pose proof(Values 9114%nat ltac:(vm_compute;tauto))as H9114.
pose proof(Values 9137%nat ltac:(vm_compute;tauto))as H9137.
eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes 9138 legal_class_expr_9138);[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes 109%nat);reflexivity| |exact Step].
intros site. cbn [legal_class_expr_9138 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite H9114 H9137.
cbn [legal_class_value].
change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_9114 instruction])(Gval(Fuint 1)[::legal_class_bit_9137 instruction])=Some(Gval(Fuint 1)[::legal_class_bit_9114 instruction || legal_class_bit_9137 instruction])).
destruct(legal_class_bit_9114 instruction),(legal_class_bit_9137 instruction);reflexivity. }
lia. Qed.
(* Semantic history composition. *)
Lemma legal_class_rank_positive index : (index<110)%coq_nat ->(0<legal_class_rank(9029+index)%nat)%coq_nat.
Proof. intro Bound. do 110(destruct index as[|index];[vm_compute;lia|]);lia. Qed.
Lemma legal_class_dependency_rank index dep : (index<110)%coq_nat ->List.In dep(legal_class_dependencies(9029+index)%nat) ->
 dep=44%nat \/exists prior,(prior<110)%coq_nat /\dep=(9029+prior)%nat /\(legal_class_rank dep<legal_class_rank(9029+index)%nat)%coq_nat.
Proof. intros Bound.
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9029%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 0%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9031%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 2%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9033%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 4%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9035%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 6%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9037%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 8%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9039%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 10%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9041%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 12%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9043%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 14%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9045%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 16%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9047%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 18%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9049%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 20%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9030%nat;9032%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 1%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 3%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9051%nat;9034%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 22%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 5%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9052%nat;9036%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 23%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 7%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9053%nat;9038%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 24%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 9%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9054%nat;9040%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 25%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 11%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9055%nat;9042%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 26%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 13%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9056%nat;9044%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 27%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 15%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9057%nat;9046%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 28%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 17%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9058%nat;9048%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 29%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 19%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9059%nat;9050%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 30%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 21%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9061%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 32%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9063%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 34%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9065%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 36%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9067%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 38%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9069%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 40%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9071%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 42%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9073%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 44%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9075%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 46%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9077%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 48%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9079%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 50%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9062%nat;9064%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 33%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 35%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9081%nat;9066%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 52%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 37%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9082%nat;9068%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 53%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 39%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9083%nat;9070%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 54%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 41%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9084%nat;9072%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 55%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 43%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9085%nat;9074%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 56%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 45%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9086%nat;9076%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 57%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 47%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9087%nat;9078%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 58%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 49%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9088%nat;9080%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 59%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 51%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9060%nat;9089%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 31%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 60%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9091%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 62%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9093%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 64%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9095%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 66%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9097%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 68%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9099%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 70%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9101%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 72%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9103%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 74%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9105%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 76%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9092%nat;9094%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 63%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 65%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9107%nat;9096%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 78%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 67%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9108%nat;9098%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 79%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 69%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9109%nat;9100%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 80%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 71%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9110%nat;9102%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 81%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 73%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9111%nat;9104%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 82%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 75%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9112%nat;9106%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 83%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 77%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9090%nat;9113%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 61%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 84%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9115%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 86%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9117%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 88%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9119%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 90%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9121%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 92%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9123%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 94%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9125%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 96%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9127%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 98%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::44%nat])in H.
destruct H as[H|H]. { subst dep. left;reflexivity. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9129%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 100%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9116%nat;9118%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 87%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 89%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9131%nat;9120%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 102%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 91%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9132%nat;9122%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 103%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 93%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9133%nat;9124%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 104%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 95%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9134%nat;9126%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 105%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 97%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9135%nat;9128%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 106%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 99%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9136%nat;9130%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 107%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 101%nat;vm_compute;repeat split;lia. }
contradiction. }
destruct index as[|index]. { intro H.
change(List.In dep [::9114%nat;9137%nat])in H.
destruct H as[H|H]. { subst dep. right;exists 85%nat;vm_compute;repeat split;lia. }
destruct H as[H|H]. { subst dep. right;exists 108%nat;vm_compute;repeat split;lia. }
contradiction. }
lia. Qed.
Theorem legal_class_nodes_history invalid history (limit start:nat) instruction :
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 44(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time index,(index<110)%coq_nat ->(Nat.add start(legal_class_rank(9029+index)%nat)<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find(N.of_nat(9029+index)%nat)(history time)=Some(legal_class_value(9029+index)%nat instruction).
Proof.
 intros Instruction Steps time. induction time as[|time IH];intros index Bound Lower Upper.
 - pose proof(legal_class_rank_positive index Bound). lia.
 - eapply(legal_class_step index invalid(history time)(history(S time))instruction Bound);[|apply Steps;lia].
   intros dep Member. destruct(legal_class_dependency_rank index dep Bound Member)as[Root|[prior[Prior[Same Rank]]]].
   + subst dep. exact(Instruction time ltac:(pose proof(legal_class_rank_positive index Bound);lia)ltac:(lia)).
   + subst dep. apply IH;lia.
Qed.
Definition legal_instruction_classes : seq(N*N) := [::(28799,19);(28799,8211);(28799,12307);(28799,28691);(28799,24595);(28799,16403);(4261441663,4115);(4261441663,20499);(4261441663,1073762323);(127,55);(127,23);(4261441663,51);(4261441663,8243);(4261441663,12339);(4261441663,28723);(4261441663,24627);(4261441663,16435);(4261441663,4147);(4261441663,20531);(4261441663,1073741875);(4261441663,1073762355);(127,111);(28799,103);(28799,99);(28799,4195);(28799,16483);(28799,24675);(28799,20579);(28799,28771);(28799,3);(28799,4099);(28799,8195);(28799,16387);(28799,20483);(28799,35);(28799,4131);(28799,8227)].
Definition legal_instruction_classified instruction := exists mask code,List.In(mask,code)legal_instruction_classes /\N.land(to_N instruction)mask=code.
Lemma legal_class_bit_member instruction :legal_class_bit_9138 instruction=true ->legal_instruction_classified instruction.
Proof. unfold legal_class_bit_9138, legal_class_bit_9137, legal_class_bit_9136, legal_class_bit_9135, legal_class_bit_9134, legal_class_bit_9133, legal_class_bit_9132, legal_class_bit_9131, legal_class_bit_9114, legal_class_bit_9113, legal_class_bit_9112, legal_class_bit_9111, legal_class_bit_9110, legal_class_bit_9109, legal_class_bit_9108, legal_class_bit_9107, legal_class_bit_9090, legal_class_bit_9089, legal_class_bit_9088, legal_class_bit_9087, legal_class_bit_9086, legal_class_bit_9085, legal_class_bit_9084, legal_class_bit_9083, legal_class_bit_9082, legal_class_bit_9081, legal_class_bit_9060, legal_class_bit_9059, legal_class_bit_9058, legal_class_bit_9057, legal_class_bit_9056, legal_class_bit_9055, legal_class_bit_9054, legal_class_bit_9053, legal_class_bit_9052, legal_class_bit_9051.
intro H. repeat rewrite Bool.orb_true_iff in H.
assert (C9030:legal_class_bit_9030 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,19. split;[apply(List.nth_error_In legal_instruction_classes 0%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9032:legal_class_bit_9032 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,8211. split;[apply(List.nth_error_In legal_instruction_classes 1%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9034:legal_class_bit_9034 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,12307. split;[apply(List.nth_error_In legal_instruction_classes 2%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9036:legal_class_bit_9036 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,28691. split;[apply(List.nth_error_In legal_instruction_classes 3%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9038:legal_class_bit_9038 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,24595. split;[apply(List.nth_error_In legal_instruction_classes 4%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9040:legal_class_bit_9040 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,16403. split;[apply(List.nth_error_In legal_instruction_classes 5%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9042:legal_class_bit_9042 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,4115. split;[apply(List.nth_error_In legal_instruction_classes 6%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9044:legal_class_bit_9044 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,20499. split;[apply(List.nth_error_In legal_instruction_classes 7%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9046:legal_class_bit_9046 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,1073762323. split;[apply(List.nth_error_In legal_instruction_classes 8%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9048:legal_class_bit_9048 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 127,55. split;[apply(List.nth_error_In legal_instruction_classes 9%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9050:legal_class_bit_9050 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 127,23. split;[apply(List.nth_error_In legal_instruction_classes 10%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9062:legal_class_bit_9062 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,51. split;[apply(List.nth_error_In legal_instruction_classes 11%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9064:legal_class_bit_9064 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,8243. split;[apply(List.nth_error_In legal_instruction_classes 12%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9066:legal_class_bit_9066 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,12339. split;[apply(List.nth_error_In legal_instruction_classes 13%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9068:legal_class_bit_9068 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,28723. split;[apply(List.nth_error_In legal_instruction_classes 14%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9070:legal_class_bit_9070 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,24627. split;[apply(List.nth_error_In legal_instruction_classes 15%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9072:legal_class_bit_9072 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,16435. split;[apply(List.nth_error_In legal_instruction_classes 16%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9074:legal_class_bit_9074 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,4147. split;[apply(List.nth_error_In legal_instruction_classes 17%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9076:legal_class_bit_9076 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,20531. split;[apply(List.nth_error_In legal_instruction_classes 18%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9078:legal_class_bit_9078 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,1073741875. split;[apply(List.nth_error_In legal_instruction_classes 19%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9080:legal_class_bit_9080 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 4261441663,1073762355. split;[apply(List.nth_error_In legal_instruction_classes 20%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9092:legal_class_bit_9092 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 127,111. split;[apply(List.nth_error_In legal_instruction_classes 21%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9094:legal_class_bit_9094 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,103. split;[apply(List.nth_error_In legal_instruction_classes 22%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9096:legal_class_bit_9096 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,99. split;[apply(List.nth_error_In legal_instruction_classes 23%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9098:legal_class_bit_9098 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,4195. split;[apply(List.nth_error_In legal_instruction_classes 24%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9100:legal_class_bit_9100 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,16483. split;[apply(List.nth_error_In legal_instruction_classes 25%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9102:legal_class_bit_9102 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,24675. split;[apply(List.nth_error_In legal_instruction_classes 26%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9104:legal_class_bit_9104 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,20579. split;[apply(List.nth_error_In legal_instruction_classes 27%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9106:legal_class_bit_9106 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,28771. split;[apply(List.nth_error_In legal_instruction_classes 28%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9116:legal_class_bit_9116 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,3. split;[apply(List.nth_error_In legal_instruction_classes 29%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9118:legal_class_bit_9118 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,4099. split;[apply(List.nth_error_In legal_instruction_classes 30%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9120:legal_class_bit_9120 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,8195. split;[apply(List.nth_error_In legal_instruction_classes 31%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9122:legal_class_bit_9122 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,16387. split;[apply(List.nth_error_In legal_instruction_classes 32%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9124:legal_class_bit_9124 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,20483. split;[apply(List.nth_error_In legal_instruction_classes 33%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9126:legal_class_bit_9126 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,35. split;[apply(List.nth_error_In legal_instruction_classes 34%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9128:legal_class_bit_9128 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,4131. split;[apply(List.nth_error_In legal_instruction_classes 35%nat);reflexivity|apply N.eqb_eq;exact Match]. }
assert (C9130:legal_class_bit_9130 instruction=true ->legal_instruction_classified instruction). { intro Match. exists 28799,8227. split;[apply(List.nth_error_In legal_instruction_classes 36%nat);reflexivity|apply N.eqb_eq;exact Match]. }
tauto. Qed.
Require Import LegalBooleanCone LegalAssumptionNodes FormalTypedNodeEquation.
Lemma legal_class_active_negation invalid old result :
 VM.find 42 old=Some(Gval(Fuint 1)[::true]) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 9028 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Active Step. eapply formal_combinational_known_node;
 [exact legal_bool_9028_position|exact legal_bool_9028_safe|exact legal_bool_9028_nonregister| |reflexivity|exact Step].
 cbn [legal_bool_9028_expr eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Active. reflexivity.
Qed.

Theorem legal_active_instruction_classified_history invalid history (limit start time:nat) instruction :
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 44(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (Nat.add start 16<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 42(history(Nat.sub time 2))=Some(Gval(Fuint 1)[::true]) ->
 VM.find 9139(history time)=Some(Gval(Fuint 1)[::true]) ->
 legal_instruction_classified instruction.
Proof.
 intros Instruction Steps Lower Upper Active Legal.
 destruct time as[|[|time]];try lia.
 cbn [Nat.sub] in Active. rewrite Nat.sub_0_r in Active.
 assert (Negated:VM.find 9028(history(S time))=Some(Gval(Fuint 1)[::false])).
 { apply(legal_class_active_negation invalid(history time)(history(S time)) Active). apply Steps;lia. }
 assert (Class:VM.find 9138(history(S time))=Some(Gval(Fuint 1)[::legal_class_bit_9138 instruction])).
 { exact(legal_class_nodes_history invalid history limit start instruction Instruction Steps(S time)109%nat ltac:(lia) ltac:(change(Nat.add start 15<=S time)%coq_nat;lia)ltac:(lia)). }
 rewrite(legal_equation_9139 invalid(history(S time))(history(S time))(history(S(S time)))(Steps(S time)ltac:(lia)))in Legal.
 cbn [legal_expr_9139 eval_hfexpr_with_memory eval_href_with_memory] in Legal.
 rewrite Negated Class in Legal.
 apply legal_class_bit_member. destruct(legal_class_bit_9138 instruction);[reflexivity|discriminate Legal].
Qed.

Require Import FormalDeclaredWireCheck.
Local Transparent flat_statements flat_memories.
Definition legal_input_nodes := [::(9000,(@Eref VarOrder.T (@Eid VarOrder.T 101)));(9001,(@Eref VarOrder.T (@Eid VarOrder.T 9000)));(9002,(@Evalidif VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 9001))));(9146,(@Eref VarOrder.T (@Eid VarOrder.T 111)));(9154,(@Eref VarOrder.T (@Eid VarOrder.T 9146)));(9156,(@Eref VarOrder.T (@Eid VarOrder.T 9002)))].
Definition legal_input_offsets := [::9773%nat;0%nat;0%nat;143%nat;7%nat;1%nat].
Lemma legal_input_positions :select_node_offsets legal_input_offsets flat_statements=Some legal_input_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma legal_input_safety :selected_node_safety flat_memories flat_statements legal_input_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Lemma legal_input_wire_101_checked :declared_wire_check flat_memories flat_statements 78 8690 101 7750 32=true.
Proof. vm_compute;reflexivity. Qed.
Lemma legal_input_wire_101 invalid old result word :size word=32%nat ->VM.find 7750 old=Some(Gval(Fuint 32)word) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 101 result=Some(Gval(Fuint 32)word).
Proof. intros Size Source Step. eapply declared_wire_checked_value;[exact legal_input_wire_101_checked|exact Source| |exact Step].
change (Some (Gval (Fuint 32) (zext_to 32 (take 32 word))) = Some (Gval (Fuint 32) word)).
rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity. Qed.
Lemma legal_input_wire_111_checked :declared_wire_check flat_memories flat_statements 88 8690 111 7956 1=true.
Proof. vm_compute;reflexivity. Qed.
Lemma legal_input_wire_111 invalid old result word :size word=1%nat ->VM.find 7956 old=Some(Gval(Fuint 1)word) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 111 result=Some(Gval(Fuint 1)word).
Proof. intros Size Source Step. eapply declared_wire_checked_value;[exact legal_input_wire_111_checked|exact Source| |exact Step].
change (Some (Gval (Fuint 1) (zext_to 1 (take 1 word))) = Some (Gval (Fuint 1) word)).
rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity. Qed.
Lemma legal_input_wire_42_checked :declared_wire_check flat_memories flat_statements 19 9940 42 9154 1=true.
Proof. vm_compute;reflexivity. Qed.
Lemma legal_input_wire_42 invalid old result word :size word=1%nat ->VM.find 9154 old=Some(Gval(Fuint 1)word) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 42 result=Some(Gval(Fuint 1)word).
Proof. intros Size Source Step. eapply declared_wire_checked_value;[exact legal_input_wire_42_checked|exact Source| |exact Step].
change (Some (Gval (Fuint 1) (zext_to 1 (take 1 word))) = Some (Gval (Fuint 1) word)).
rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity. Qed.
Lemma legal_input_wire_44_checked :declared_wire_check flat_memories flat_statements 21 9940 44 9156 32=true.
Proof. vm_compute;reflexivity. Qed.
Lemma legal_input_wire_44 invalid old result word :size word=32%nat ->VM.find 9156 old=Some(Gval(Fuint 32)word) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 44 result=Some(Gval(Fuint 32)word).
Proof. intros Size Source Step. eapply declared_wire_checked_value;[exact legal_input_wire_44_checked|exact Source| |exact Step].
change (Some (Gval (Fuint 32) (zext_to 32 (take 32 word))) = Some (Gval (Fuint 32) word)).
rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma legal_input_node_9000 invalid old result word : VM.find 101 old=Some(Gval(Fuint 32)word) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 9000 result=Some(Gval(Fuint 32)word).
Proof. intros Source Step.
eapply(reference_redirect_ground_step legal_input_offsets legal_input_nodes 9000 (@Eref VarOrder.T (@Eid VarOrder.T 101)));[exact legal_input_positions|exact legal_input_safety|apply(List.nth_error_In legal_input_nodes 0);reflexivity| |exact Step].
intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. Qed.
Lemma legal_input_node_9001 invalid old result word : VM.find 9000 old=Some(Gval(Fuint 32)word) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 9001 result=Some(Gval(Fuint 32)word).
Proof. intros Source Step.
eapply(reference_redirect_ground_step legal_input_offsets legal_input_nodes 9001 (@Eref VarOrder.T (@Eid VarOrder.T 9000)));[exact legal_input_positions|exact legal_input_safety|apply(List.nth_error_In legal_input_nodes 1);reflexivity| |exact Step].
intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. Qed.
Lemma legal_input_node_9002 invalid old result word : VM.find 9001 old=Some(Gval(Fuint 32)word) ->VM.find 42 old=Some(Gval(Fuint 1)[::true]) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 9002 result=Some(Gval(Fuint 32)word).
Proof. intros Source Active Step.
eapply(reference_redirect_ground_step legal_input_offsets legal_input_nodes 9002 (@Evalidif VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 9001))));[exact legal_input_positions|exact legal_input_safety|apply(List.nth_error_In legal_input_nodes 2);reflexivity| |exact Step].
intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Active Source. unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Source. reflexivity. Qed.
Lemma legal_input_node_9146 invalid old result word : VM.find 111 old=Some(Gval(Fuint 1)word) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 9146 result=Some(Gval(Fuint 1)word).
Proof. intros Source Step.
eapply(reference_redirect_ground_step legal_input_offsets legal_input_nodes 9146 (@Eref VarOrder.T (@Eid VarOrder.T 111)));[exact legal_input_positions|exact legal_input_safety|apply(List.nth_error_In legal_input_nodes 3);reflexivity| |exact Step].
intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. Qed.
Lemma legal_input_node_9154 invalid old result word : VM.find 9146 old=Some(Gval(Fuint 1)word) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 9154 result=Some(Gval(Fuint 1)word).
Proof. intros Source Step.
eapply(reference_redirect_ground_step legal_input_offsets legal_input_nodes 9154 (@Eref VarOrder.T (@Eid VarOrder.T 9146)));[exact legal_input_positions|exact legal_input_safety|apply(List.nth_error_In legal_input_nodes 4);reflexivity| |exact Step].
intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. Qed.
Lemma legal_input_node_9156 invalid old result word : VM.find 9002 old=Some(Gval(Fuint 32)word) ->formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 9156 result=Some(Gval(Fuint 32)word).
Proof. intros Source Step.
eapply(reference_redirect_ground_step legal_input_offsets legal_input_nodes 9156 (@Eref VarOrder.T (@Eid VarOrder.T 9002)));[exact legal_input_positions|exact legal_input_safety|apply(List.nth_error_In legal_input_nodes 5);reflexivity| |exact Step].
intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. Qed.
Require Import ExceptionPCSourceRegisters FormalCheckerValidNodes FormalCheckerValidOutput FormalStallHistory FormalCheckerResetConnections FormalCheckerValidStability.
Lemma legal_checker_source_after_five invalid s0 s1 s2 s3 s4 s5 :
 VM.find 7947 s0=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7765 s0=Some(Gval(Fuint 1)[::false]) ->
 VM.find 65 s0=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements=Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements=Some s5 ->
 VM.find 7956 s5=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Bubble Stall Reset S1 S2 S3 S4 S5.
 assert(A:VM.find 7948 s1=Some(Gval(Fuint 1)[::false])).
 { rewrite(checker_valid_equation_7948 invalid s0 s0 s1 S1).
 cbn[checker_valid_expr_7948 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Bubble Stall. reflexivity. }
 assert(B:VM.find 7949 s1=Some(Gval(Fuint 1)[::false])).
 { rewrite(checker_valid_equation_7949 invalid s0 s0 s1 S1).
 cbn[checker_valid_expr_7949 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Reset. reflexivity. }
 assert(C:VM.find 7950 s2=Some(Gval(Fuint 1)[::false])).
 { rewrite(checker_valid_equation_7950 invalid s1 s1 s2 S2).
 cbn[checker_valid_expr_7950 eval_hfexpr_with_memory eval_href_with_memory]. rewrite A B. reflexivity. }
 assert(D:VM.find 7951 s3=Some(Gval(Fuint 1)[::false])).
 { rewrite(checker_valid_equation_7951 invalid s2 s2 s3 S3).
 cbn[checker_valid_expr_7951 eval_hfexpr_with_memory eval_href_with_memory]. exact C. }
 assert(E:VM.find 7952 s4=Some(Gval(Fuint 1)[::true])).
 { rewrite(checker_valid_equation_7952 invalid s3 s3 s4 S4).
 cbn[checker_valid_expr_7952 eval_hfexpr_with_memory eval_href_with_memory]. rewrite D. reflexivity. }
 eapply valid_node_7956;[|reflexivity|exact S5].
 cbn[valid_expr_7956 eval_hfexpr_with_memory eval_href_with_memory]. exact E.
Qed.
Lemma legal_checker_source_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 7947(history limit)=Some(Gval(Fuint 1)[::false]) ->
 forall time,(11<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 7956(history time)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Steps Resets Bubble time Lower Upper.
 set(t:=Nat.sub time 5).
 assert(T:time=S(S(S(S(S t))))). { unfold t;lia. }
 assert(T6:(6<=t)%coq_nat). {unfold t;lia. }
 assert(B:VM.find 7947(history t)=Some(Gval(Fuint 1)[::false])).
 { rewrite(flat_register_history_same invalid history limit 7947 formal_checker_bubble_register Steps t ltac:(lia)).
 rewrite(flat_register_history_same invalid history limit 7947 formal_checker_bubble_register Steps limit ltac:(lia))in Bubble. exact Bubble. }
 assert(Stall:VM.find 7765(history t)=Some(Gval(Fuint 1)[::false])).
 { set(j:=Nat.sub t 6). assert(J:t=S(S(S(S(S(S j))))))by(unfold j;lia).
 rewrite J. eapply(stall_after_six invalid(history j)(history(S j))(history(S(S j)))(history(S(S(S j))))(history(S(S(S(S j)))))(history(S(S(S(S(S j))))))(history(S(S(S(S(S(S j)))))))false);
 [apply Resets;lia|apply Steps;lia|apply Steps;lia|apply Steps;lia|apply Steps;lia|apply Steps;lia|apply Steps;lia]. }
 assert(Reset:VM.find 65(history t)=Some(Gval(Fuint 1)[::false])).
 { set(j:=Nat.sub t 2). assert(J:t=S(S j))by(unfold j;lia). rewrite J.
 eapply(reset_connection_65_transfer invalid(history(S j))(history(S j))(history(S(S j)))false).
 - eapply(reset_connection_24_transfer invalid(history j)(history j)(history(S j))false);[apply Resets;lia|apply Steps;lia].
 - apply Steps;lia. }
 rewrite T. eapply legal_checker_source_after_five;[exact B|exact Stall|exact Reset|apply Steps;lia|apply Steps;lia|apply Steps;lia|apply Steps;lia|apply Steps;lia].
Qed.
Lemma legal_input_active_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7956(history t)=Some(Gval(Fuint 1)[::true])) ->
 forall time,(15<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 42(history time)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Steps Source [|[|[|[|time]]]] Lower Upper;try lia.
 eapply(legal_input_wire_42 invalid(history(S(S(S(time)))))(history(S(S(S(S(time))))))[::true]);[reflexivity| |apply Steps;lia].
 eapply(legal_input_node_9154 invalid(history(S(S(time))))(history(S(S(S(time)))))[::true]);[|apply Steps;lia].
 eapply(legal_input_node_9146 invalid(history(S(time)))(history(S(S(time))))[::true]);[|apply Steps;lia].
 eapply(legal_input_wire_111 invalid(history(time))(history(S(time)))[::true]);[reflexivity|apply Source;lia|apply Steps;lia].
Qed.
Lemma legal_input_instruction_history invalid history limit instruction :size instruction=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(15<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 42(history t)=Some(Gval(Fuint 1)[::true])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)) ->
 forall time,(21<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 44(history time)=Some(Gval(Fuint 32)instruction).
Proof.
 intros Size Steps Active Instruction [|[|[|[|[|[|time]]]]]] Lower Upper;try lia.
 eapply(legal_input_wire_44 invalid(history(S(S(S(S(S(time)))))))(history(S(S(S(S(S(S(time))))))))instruction);[exact Size| |apply Steps;lia].
 eapply(legal_input_node_9156 invalid(history(S(S(S(S(time))))))(history(S(S(S(S(S(time)))))))instruction);[|apply Steps;lia].
 eapply(legal_input_node_9002 invalid(history(S(S(S(time)))))(history(S(S(S(S(time))))))instruction);[|apply Active;lia|apply Steps;lia].
 eapply(legal_input_node_9001 invalid(history(S(S(time))))(history(S(S(S(time)))))instruction);[|apply Steps;lia].
 eapply(legal_input_node_9000 invalid(history(S(time)))(history(S(S(time))))instruction);[|apply Steps;lia].
 eapply(legal_input_wire_101 invalid(history(time))(history(S(time)))instruction);[exact Size|apply Instruction;lia|apply Steps;lia].
Qed.
Require Import FormalInstructionResetCycle FormalResetPreparation LegalNoTrapHistory FormalLocalHistory.
Theorem legal_active_commit_instruction_classified_history invalid history limit time instruction :size instruction=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 7947(history limit)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(history limit)=Some(Gval(Fuint 32)instruction) ->
 (37<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 9139(history time)=Some(Gval(Fuint 1)[::true]) ->legal_instruction_classified instruction.
Proof.
 intros Size Steps Resets Bubble Instruction Lower Upper Legal.
 assert(Source:forall t,(11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7956(history t)=Some(Gval(Fuint 1)[::true])).
 { exact(legal_checker_source_history invalid history limit Steps Resets Bubble). }
 assert(Active:forall t,(15<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 42(history t)=Some(Gval(Fuint 1)[::true])).
 { exact(legal_input_active_history invalid history limit Steps Source). }
 assert(Word:forall t,(t<=limit)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Bound. destruct(instruction_register_shape 7750 ltac:(vm_compute;reflexivity))as[Safe Present].
 rewrite(flat_register_history_same invalid history limit 7750 Present Steps t Bound).
 rewrite(flat_register_history_same invalid history limit 7750 Present Steps limit ltac:(lia))in Instruction. exact Instruction. }
 apply(legal_active_instruction_classified_history invalid history limit 21 time instruction).
 - exact(legal_input_instruction_history invalid history limit instruction Size Steps Active Word).
 - exact Steps.
 - change(37<=time)%coq_nat. exact Lower.
 - exact Upper.
 - apply Active;lia.
 - exact Legal.
Qed.
Require Import LegalInstructionAssumption ObservedLegalNoTrap.
Theorem legal_active_commit_instruction_classified_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7947(top_environment observed)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->size instruction=32%nat ->
 legal_instruction_classified instruction.
Proof.
 intros Observe Legal Reset Bubble Instruction Size.
 destruct(observed_legal_instruction_history memory inputs k observed Observe Legal Reset)
 as[committed[initial[history[Run[Prepare[First[Last[Steps Class]]]]]]]].
 assert(InitialReset:VM.find 1(history 0%nat)=Some(Gval(Fuint 1)[::false])).
 { rewrite First. destruct(top_reset_prepared(Some committed)_ initial _ Reset Prepare)as[env[Env Value]].
 unfold top_environment. rewrite Env. exact Value. }
 eapply(legal_active_commit_instruction_classified_history _ history 9259 9255 instruction Size Steps).
 - intros t Bound. exact(legal_local_reset_history _ history 9259 false Steps InitialReset t Bound).
 - rewrite Last. exact Bubble.
 - rewrite Last. exact Instruction.
 - vm_compute;lia.
 - vm_compute;lia.
 - exact Class.
Qed.

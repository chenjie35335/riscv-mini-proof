Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine DUTRedirectDecode LoadTypeCorrespondence.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_instruction_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(1885,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1886,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; false; false; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1885))));(1888,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(1889,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 26) [::true; true; false; false; true; true; false; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1888))));(1893,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(1894,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 26) [::true; true; false; false; true; true; false; false; false; false; false; false; false; true; true; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1893))));(1898,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(1899,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 26) [::true; true; false; false; true; true; false; false; false; false; false; false; true; false; true; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1898))));(1903,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(1904,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 26) [::true; true; false; false; true; true; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1903))));(1908,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(1909,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 26) [::true; true; false; false; true; true; false; false; false; false; false; false; true; true; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1908))));(1913,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(1914,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 26) [::true; true; false; false; true; true; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1913))));(1918,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(1919,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 26) [::true; true; false; false; true; true; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1918))));(1923,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(1924,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 26) [::true; true; false; false; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1923))));(1928,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1929,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1928))));(1932,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true])));(1933,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1932))));(1936,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true])));(1937,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 21) [::true; true; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1936))));(1940,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1941,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; false; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1940))));(1945,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1946,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; false; true; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1945))));(1950,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1951,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::true; true; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1950))));(1957,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1958,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1957))));(1961,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1962,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1961))));(1965,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1966,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1965))));(1969,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1970,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1969))));(1973,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1974,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1973))));(1979,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1980,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1979))));(1985,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1986,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1985))));(1991,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1992,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1991))));(1997,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(1998,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; false; true; true; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1997))));(2003,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(2004,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2003))));(2009,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(2010,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2009))));(2013,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2014,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 31) [::true; true; false; false; true; true; false; false; false; false; false; false; true; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2013))));(2018,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2019,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 31) [::true; true; false; false; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2018))));(2023,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2024,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2023))));(2028,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2029,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; true; true; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2028))));(2033,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2034,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2033))));(2038,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2039,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2038))));(2043,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2044,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2043))));(2048,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2049,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; true; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2048))));(2053,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2054,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2053))));(2058,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2059,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::true; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2058))));(2063,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2064,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 31) [::true; true; false; false; true; false; false; false; false; false; false; false; true; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2063))));(2067,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2068,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2067))));(2071,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; true; true; true; true; true; true; true])));(2072,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2071))));(2075,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(2076,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2075))));(2079,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(2080,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2079))));(2083,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(2084,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2083))));(2087,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(2088,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2087))));(2091,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(2092,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2091))));(2095,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])));(2096,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2095))));(2356,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 7) [::true; true; true; true; true; true; true])));(2357,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; true; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2356))));(2471,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 7) [::true; true; true; true; true; true; true])));(2472,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2471))));(2474,(@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 7) [::true; true; true; true; true; true; true])));(2475,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::true; true; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 2474))))].
Definition reference_instruction_offsets := [::1964%nat;0%nat;1%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;2%nat;0%nat;2%nat;0%nat;2%nat;0%nat;3%nat;0%nat;3%nat;0%nat;5%nat;0%nat;2%nat;0%nat;2%nat;0%nat;2%nat;0%nat;2%nat;0%nat;4%nat;0%nat;4%nat;0%nat;4%nat;0%nat;4%nat;0%nat;4%nat;0%nat;4%nat;0%nat;2%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;3%nat;0%nat;2%nat;0%nat;2%nat;0%nat;2%nat;0%nat;2%nat;0%nat;2%nat;0%nat;2%nat;0%nat;2%nat;0%nat;2%nat;0%nat;259%nat;0%nat;113%nat;0%nat;1%nat;0%nat].
Definition reference_instruction_guards : seq VarOrder.T := [::2096;2092;2088;2084;2080;2076;2072;2068;2064;2475;2472;2059;2054;2049;2044;2039;2034;2029;2024;2019;2014;2357;2010;2004;1998;1992;1986;1980;1974;1970;1966;1962;1958;1886;1951;1946;1941;1937;1933;1929;1924;1919;1914;1909;1904;1899;1894;1889].
Definition reference_instruction_codes : seq N := [::19;8211;12307;28691;24595;16403;4115;20499;1073762323;55;23;51;8243;12339;28723;24627;16435;4147;20531;1073741875;1073762355;111;103;99;4195;16483;24675;20579;28771;3;4099;8195;16387;20483;35;4131;8227;1048691;115;15;33554483;33558579;33562675;33566771;33570867;33574963;33579059;33583155].
Definition reference_instruction_code_widths : seq nat := [::5%nat;14%nat;14%nat;15%nat;15%nat;15%nat;13%nat;15%nat;31%nat;6%nat;5%nat;6%nat;14%nat;14%nat;15%nat;15%nat;15%nat;13%nat;15%nat;31%nat;31%nat;7%nat;7%nat;7%nat;13%nat;15%nat;15%nat;15%nat;15%nat;2%nat;13%nat;14%nat;15%nat;15%nat;6%nat;13%nat;14%nat;21%nat;7%nat;4%nat;26%nat;26%nat;26%nat;26%nat;26%nat;26%nat;26%nat;26%nat].
Definition reference_instruction_masks : seq N := [::28799;28799;28799;28799;28799;28799;4261441663;4261441663;4261441663;127;127;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;127;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;4294967295;4294967295;28799;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663].
Definition reference_instruction_mask_widths : seq nat := [::15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;32%nat;32%nat;32%nat;7%nat;7%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;7%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;32%nat;32%nat;15%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat].
Lemma reference_instruction_positions : select_node_offsets reference_instruction_offsets flat_statements = Some reference_instruction_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_instruction_safety : selected_node_safety flat_memories flat_statements reference_instruction_offsets flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_instruction_guard row := nth 0 reference_instruction_guards row.
Definition reference_instruction_code row := nth 0 reference_instruction_codes row.
Definition reference_instruction_code_width row := nth 0%nat reference_instruction_code_widths row.
Definition reference_instruction_mask row := nth 0 reference_instruction_masks row.
Definition reference_instruction_mask_width row := nth 0%nat reference_instruction_mask_widths row.
Definition reference_instruction_mask_expression (row:nat) := @Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint (reference_instruction_mask_width row)) (from_N (reference_instruction_mask_width row) (reference_instruction_mask row))).
Definition reference_instruction_guard_expression row := @Eprim_binop VarOrder.T (Bcomp Beq)
 (@Econst VarOrder.T (Fuint (reference_instruction_code_width row)) (from_N (reference_instruction_code_width row) (reference_instruction_code row)))
 (@Eref VarOrder.T (@Eid VarOrder.T (reference_instruction_guard row - 1))).
Lemma reference_instruction_decode_certificates row : (row < 48)%coq_nat ->
 List.In (reference_instruction_guard row - 1,reference_instruction_mask_expression row) reference_instruction_nodes /\
 List.In (reference_instruction_guard row,reference_instruction_guard_expression row) reference_instruction_nodes /\
 to_N (from_N (reference_instruction_code_width row) (reference_instruction_code row)) = reference_instruction_code row /\
 to_N (from_N (reference_instruction_mask_width row) (reference_instruction_mask row)) = reference_instruction_mask row.
Proof.
 intro Row.
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 88%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 89%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 86%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 87%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 84%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 85%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 82%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 83%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 80%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 81%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 78%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 79%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 76%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 77%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 74%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 75%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 72%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 73%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 94%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 95%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 92%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 93%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 70%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 71%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 68%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 69%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 66%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 67%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 64%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 65%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 62%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 63%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 60%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 61%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 58%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 59%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 56%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 57%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 54%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 55%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 52%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 53%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 90%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 91%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 50%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 51%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 48%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 49%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 46%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 47%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 44%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 45%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 42%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 43%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 40%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 41%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 38%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 39%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 36%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 37%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 34%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 35%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 32%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 33%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 30%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 31%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 0%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 1%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 28%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 29%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 26%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 27%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 24%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 25%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 22%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 23%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 20%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 21%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 18%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 19%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 16%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 17%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 14%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 15%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 12%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 13%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 10%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 11%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 8%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 9%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 6%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 7%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 4%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 5%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 destruct row as [|row].
 { split.
 - apply (List.nth_error_In reference_instruction_nodes 2%nat);vm_compute;reflexivity.
 - split.
 + apply (List.nth_error_In reference_instruction_nodes 3%nat);vm_compute;reflexivity.
 + split;vm_compute;reflexivity. }
 lia.
Qed.
Theorem reference_instruction_decode_history invalid history limit instruction row :
 (row < 48)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= limit)%coq_nat -> VM.find 1884 (history i) = Some (Gval (Fuint 32) instruction)) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (reference_instruction_guard row) (history time) = Some (Gval (Fuint 1) [::N.eqb (reference_instruction_code row) (N.land (to_N instruction) (reference_instruction_mask row))]).
Proof.
 intros Row Steps Instruction [|[|time]] Lower Upper;try lia.
 destruct (reference_instruction_decode_certificates row Row) as [MC [GC [Code MaskValue]]].
 assert (Mask : VM.find (reference_instruction_guard row - 1) (history (S time)) = Some (Gval (Fuint (maxn 32 (reference_instruction_mask_width row))) (andB instruction (from_N (reference_instruction_mask_width row) (reference_instruction_mask row))))).
 { eapply (reference_redirect_ground_step reference_instruction_offsets reference_instruction_nodes _ (reference_instruction_mask_expression row));
 [exact reference_instruction_positions|exact reference_instruction_safety|exact MC| |apply Steps;lia].
 intros site. unfold reference_instruction_mask_expression. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (Instruction time ltac:(lia)) size_from_N ltnn. unfold zext_to. rewrite size_from_N subnn. unfold zext. rewrite zeros0 cats0. reflexivity. }
 eapply (reference_redirect_ground_step reference_instruction_offsets reference_instruction_nodes _ (reference_instruction_guard_expression row));
 [exact reference_instruction_positions|exact reference_instruction_safety|exact GC| |apply Steps;lia].
 intros site. unfold reference_instruction_guard_expression. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite size_from_N ltnn. unfold zext_to. rewrite size_from_N subnn. unfold zext. rewrite zeros0 cats0 Mask.
 rewrite (redirect_mask_decode instruction (from_N (reference_instruction_mask_width row) (reference_instruction_mask row)) (from_N (reference_instruction_code_width row) (reference_instruction_code row)) 32 (reference_instruction_mask_width row) (reference_instruction_code_width row)) Code MaskValue N.eqb_sym. reflexivity.
Qed.

Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceRedirectSpine FormalSuccessfulNodeEvaluation SelectedNodeSafety FormalTypedNodeEquation ScalarSinkTypes DUTRedirectDecode.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ReferenceImmediateTypes.
(* Generated rs1 type DAG. *)
Definition reference_rs1_ids : seq VarOrder.T := [::1890;1891;1892;1895;1896;1897;1900;1901;1902;1905;1906;1907;1910;1911;1912;1915;1916;1917;1920;1921;1922;1925;1926;1927;1930;1931;1934;1935;1938;1939;1942;1943;1944;1947;1948;1949;1952;1953;1954;1955;1956;1959;1960;1963;1964;1967;1968;1971;1972;1975;1976;1977;1978;1981;1982;1983;1984;1987;1988;1989;1990;1993;1994;1995;1996;1999;2000;2001;2002;2005;2006;2007;2008;2011;2012;2015;2016;2017;2020;2021;2022;2025;2026;2027;2030;2031;2032;2035;2036;2037;2040;2041;2042;2045;2046;2047;2050;2051;2052;2055;2056;2057;2060;2061;2062;2065;2066;2069;2070;2073;2074;2077;2078;2081;2082;2085;2086;2089;2090;2093;2094;2097;2098;2099;2100;2101;2102;2103;2104;2105;2106;2107;2108;2109;2110;2111;2112;2113;2114;2115;2116;2117;2118;2119;2120;2121;2122;2123;2124;2125;2126;2127;2128;2129;2130;2131;2132;2133;2134;2135;2136;2137;2138;2139;2140;2141;2142;2143;2144;2145].
Definition reference_rs1_widths : seq nat := [::25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;31%nat;25%nat;20%nat;5%nat;31%nat;25%nat;20%nat;5%nat;31%nat;25%nat;20%nat;5%nat;31%nat;25%nat;20%nat;5%nat;31%nat;25%nat;20%nat;5%nat;31%nat;25%nat;20%nat;5%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;25%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;20%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat].
Definition reference_rs1_ranks : seq nat := [::1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;3%nat;4%nat;1%nat;2%nat;3%nat;4%nat;1%nat;2%nat;3%nat;4%nat;1%nat;2%nat;3%nat;4%nat;1%nat;2%nat;3%nat;4%nat;1%nat;2%nat;3%nat;4%nat;1%nat;2%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;21%nat;22%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat;48%nat;49%nat].
Definition reference_rs1_groups : seq nat := [::0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Definition reference_rs1_expressions : seq (hfexpr VarOrder.T) := [::reference_control_expr_1890;reference_control_expr_1891;reference_control_expr_1892;reference_control_expr_1895;reference_control_expr_1896;reference_control_expr_1897;reference_control_expr_1900;reference_control_expr_1901;reference_control_expr_1902;reference_control_expr_1905;reference_control_expr_1906;reference_control_expr_1907;reference_control_expr_1910;reference_control_expr_1911;reference_control_expr_1912;reference_control_expr_1915;reference_control_expr_1916;reference_control_expr_1917;reference_control_expr_1920;reference_control_expr_1921;reference_control_expr_1922;reference_control_expr_1925;reference_control_expr_1926;reference_control_expr_1927;reference_control_expr_1930;reference_control_expr_1931;reference_control_expr_1934;reference_control_expr_1935;reference_control_expr_1938;reference_control_expr_1939;reference_control_expr_1942;reference_control_expr_1943;reference_control_expr_1944;reference_control_expr_1947;reference_control_expr_1948;reference_control_expr_1949;reference_control_expr_1952;reference_control_expr_1953;reference_control_expr_1954;reference_control_expr_1955;reference_control_expr_1956;reference_control_expr_1959;reference_control_expr_1960;reference_control_expr_1963;reference_control_expr_1964;reference_control_expr_1967;reference_control_expr_1968;reference_control_expr_1971;reference_control_expr_1972;reference_control_expr_1975;reference_control_expr_1976;reference_control_expr_1977;reference_control_expr_1978;reference_control_expr_1981;reference_control_expr_1982;reference_control_expr_1983;reference_control_expr_1984;reference_control_expr_1987;reference_control_expr_1988;reference_control_expr_1989;reference_control_expr_1990;reference_control_expr_1993;reference_control_expr_1994;reference_control_expr_1995;reference_control_expr_1996;reference_control_expr_1999;reference_control_expr_2000;reference_control_expr_2001;reference_control_expr_2002;reference_control_expr_2005;reference_control_expr_2006;reference_control_expr_2007;reference_control_expr_2008;reference_control_expr_2011;reference_control_expr_2012;reference_control_expr_2015;reference_control_expr_2016;reference_control_expr_2017;reference_control_expr_2020;reference_control_expr_2021;reference_control_expr_2022;reference_control_expr_2025;reference_control_expr_2026;reference_control_expr_2027;reference_control_expr_2030;reference_control_expr_2031;reference_control_expr_2032;reference_control_expr_2035;reference_control_expr_2036;reference_control_expr_2037;reference_control_expr_2040;reference_control_expr_2041;reference_control_expr_2042;reference_control_expr_2045;reference_control_expr_2046;reference_control_expr_2047;reference_control_expr_2050;reference_control_expr_2051;reference_control_expr_2052;reference_control_expr_2055;reference_control_expr_2056;reference_control_expr_2057;reference_control_expr_2060;reference_control_expr_2061;reference_control_expr_2062;reference_control_expr_2065;reference_control_expr_2066;reference_control_expr_2069;reference_control_expr_2070;reference_control_expr_2073;reference_control_expr_2074;reference_control_expr_2077;reference_control_expr_2078;reference_control_expr_2081;reference_control_expr_2082;reference_control_expr_2085;reference_control_expr_2086;reference_control_expr_2089;reference_control_expr_2090;reference_control_expr_2093;reference_control_expr_2094;reference_control_expr_2097;reference_control_expr_2098;reference_control_expr_2099;reference_control_expr_2100;reference_control_expr_2101;reference_control_expr_2102;reference_control_expr_2103;reference_control_expr_2104;reference_control_expr_2105;reference_control_expr_2106;reference_control_expr_2107;reference_control_expr_2108;reference_control_expr_2109;reference_control_expr_2110;reference_control_expr_2111;reference_control_expr_2112;reference_control_expr_2113;reference_control_expr_2114;reference_control_expr_2115;reference_control_expr_2116;reference_control_expr_2117;reference_control_expr_2118;reference_control_expr_2119;reference_control_expr_2120;reference_control_expr_2121;reference_control_expr_2122;reference_control_expr_2123;reference_control_expr_2124;reference_control_expr_2125;reference_control_expr_2126;reference_control_expr_2127;reference_control_expr_2128;reference_control_expr_2129;reference_control_expr_2130;reference_control_expr_2131;reference_control_expr_2132;reference_control_expr_2133;reference_control_expr_2134;reference_control_expr_2135;reference_control_expr_2136;reference_control_expr_2137;reference_control_expr_2138;reference_control_expr_2139;reference_control_expr_2140;reference_control_expr_2141;reference_control_expr_2142;reference_control_expr_2143;reference_control_expr_2144;reference_control_expr_2145].
Definition reference_rs1_dependencies : seq (seq VarOrder.T) := [::[::1884];[::1890];[::1891];[::1884];[::1895];[::1896];[::1884];[::1900];[::1901];[::1884];[::1905];[::1906];[::1884];[::1910];[::1911];[::1884];[::1915];[::1916];[::1884];[::1920];[::1921];[::1884];[::1925];[::1926];[::1884];[::1930];[::1884];[::1934];[::1884];[::1938];[::1884];[::1942];[::1943];[::1884];[::1947];[::1948];[::1884];[::1952];[::1953];[::1884];[::1955];[::1884];[::1959];[::1884];[::1963];[::1884];[::1967];[::1884];[::1971];[::1884];[::1975];[::1976];[::1977];[::1884];[::1981];[::1982];[::1983];[::1884];[::1987];[::1988];[::1989];[::1884];[::1993];[::1994];[::1995];[::1884];[::1999];[::2000];[::2001];[::1884];[::2005];[::2006];[::2007];[::1884];[::2011];[::1884];[::2015];[::2016];[::1884];[::2020];[::2021];[::1884];[::2025];[::2026];[::1884];[::2030];[::2031];[::1884];[::2035];[::2036];[::1884];[::2040];[::2041];[::1884];[::2045];[::2046];[::1884];[::2050];[::2051];[::1884];[::2055];[::2056];[::1884];[::2060];[::2061];[::1884];[::2065];[::1884];[::2069];[::1884];[::2073];[::1884];[::2077];[::1884];[::2081];[::1884];[::2085];[::1884];[::2089];[::1884];[::2093];[::1884];[::2097];[::2098];[::2094;2099];[::2090;2100];[::2086;2101];[::2082;2102];[::2078;2103];[::2074;2104];[::2070;2105];[::2066;2106];[::2062;2107];[::2057;2108];[::2052;2109];[::2047;2110];[::2042;2111];[::2037;2112];[::2032;2113];[::2027;2114];[::2022;2115];[::2017;2116];[::2012;2117];[::2008;2118];[::2002;2119];[::1996;2120];[::1990;2121];[::1984;2122];[::1978;2123];[::1972;2124];[::1968;2125];[::1964;2126];[::1960;2127];[::1956;2128];[::1954;2129];[::1949;2130];[::1944;2131];[::1939;2132];[::1935;2133];[::1931;2134];[::1927;2135];[::1922;2136];[::1917;2137];[::1912;2138];[::1907;2139];[::1902;2140];[::1897;2141];[::1892;2142];[::2143];[::2144]].
Definition reference_rs1_node i := nth 0 reference_rs1_ids i.
Definition reference_rs1_width i := nth 0%nat reference_rs1_widths i.
Definition reference_rs1_rank i := nth 0%nat reference_rs1_ranks i.
Definition reference_rs1_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) reference_rs1_expressions i.
Definition reference_rs1_refs i := nth [::] reference_rs1_dependencies i.
Definition reference_rs1_width_of node := if node == 1884 then 32%nat else reference_rs1_width (index node reference_rs1_ids).
Definition reference_rs1_nodes i := match nth 2%nat reference_rs1_groups i with O => reference_control_0_nodes | S O => reference_control_1_nodes | _ => reference_control_2_nodes end.
Definition reference_rs1_offsets i := match nth 2%nat reference_rs1_groups i with O => reference_control_0_offsets | S O => reference_control_1_offsets | _ => reference_control_2_offsets end.
Lemma reference_rs1_plan i : (i < 170)%coq_nat ->
 immediate_expression_check reference_rs1_width_of (reference_rs1_expression i) = Some (reference_rs1_width i,reference_rs1_refs i) /\ (0 < reference_rs1_rank i)%coq_nat.
Proof. intro Bound. do 170 (destruct i as [|i];[split;[vm_compute;reflexivity|vm_compute;lia]|]);lia. Qed.
Lemma reference_rs1_member i : (i < 170)%coq_nat ->
 List.In (reference_rs1_node i,reference_rs1_expression i) (reference_rs1_nodes i).
Proof. intro Bound.
 destruct i as [|i];[exact reference_control_member_1890|].
 destruct i as [|i];[exact reference_control_member_1891|].
 destruct i as [|i];[exact reference_control_member_1892|].
 destruct i as [|i];[exact reference_control_member_1895|].
 destruct i as [|i];[exact reference_control_member_1896|].
 destruct i as [|i];[exact reference_control_member_1897|].
 destruct i as [|i];[exact reference_control_member_1900|].
 destruct i as [|i];[exact reference_control_member_1901|].
 destruct i as [|i];[exact reference_control_member_1902|].
 destruct i as [|i];[exact reference_control_member_1905|].
 destruct i as [|i];[exact reference_control_member_1906|].
 destruct i as [|i];[exact reference_control_member_1907|].
 destruct i as [|i];[exact reference_control_member_1910|].
 destruct i as [|i];[exact reference_control_member_1911|].
 destruct i as [|i];[exact reference_control_member_1912|].
 destruct i as [|i];[exact reference_control_member_1915|].
 destruct i as [|i];[exact reference_control_member_1916|].
 destruct i as [|i];[exact reference_control_member_1917|].
 destruct i as [|i];[exact reference_control_member_1920|].
 destruct i as [|i];[exact reference_control_member_1921|].
 destruct i as [|i];[exact reference_control_member_1922|].
 destruct i as [|i];[exact reference_control_member_1925|].
 destruct i as [|i];[exact reference_control_member_1926|].
 destruct i as [|i];[exact reference_control_member_1927|].
 destruct i as [|i];[exact reference_control_member_1930|].
 destruct i as [|i];[exact reference_control_member_1931|].
 destruct i as [|i];[exact reference_control_member_1934|].
 destruct i as [|i];[exact reference_control_member_1935|].
 destruct i as [|i];[exact reference_control_member_1938|].
 destruct i as [|i];[exact reference_control_member_1939|].
 destruct i as [|i];[exact reference_control_member_1942|].
 destruct i as [|i];[exact reference_control_member_1943|].
 destruct i as [|i];[exact reference_control_member_1944|].
 destruct i as [|i];[exact reference_control_member_1947|].
 destruct i as [|i];[exact reference_control_member_1948|].
 destruct i as [|i];[exact reference_control_member_1949|].
 destruct i as [|i];[exact reference_control_member_1952|].
 destruct i as [|i];[exact reference_control_member_1953|].
 destruct i as [|i];[exact reference_control_member_1954|].
 destruct i as [|i];[exact reference_control_member_1955|].
 destruct i as [|i];[exact reference_control_member_1956|].
 destruct i as [|i];[exact reference_control_member_1959|].
 destruct i as [|i];[exact reference_control_member_1960|].
 destruct i as [|i];[exact reference_control_member_1963|].
 destruct i as [|i];[exact reference_control_member_1964|].
 destruct i as [|i];[exact reference_control_member_1967|].
 destruct i as [|i];[exact reference_control_member_1968|].
 destruct i as [|i];[exact reference_control_member_1971|].
 destruct i as [|i];[exact reference_control_member_1972|].
 destruct i as [|i];[exact reference_control_member_1975|].
 destruct i as [|i];[exact reference_control_member_1976|].
 destruct i as [|i];[exact reference_control_member_1977|].
 destruct i as [|i];[exact reference_control_member_1978|].
 destruct i as [|i];[exact reference_control_member_1981|].
 destruct i as [|i];[exact reference_control_member_1982|].
 destruct i as [|i];[exact reference_control_member_1983|].
 destruct i as [|i];[exact reference_control_member_1984|].
 destruct i as [|i];[exact reference_control_member_1987|].
 destruct i as [|i];[exact reference_control_member_1988|].
 destruct i as [|i];[exact reference_control_member_1989|].
 destruct i as [|i];[exact reference_control_member_1990|].
 destruct i as [|i];[exact reference_control_member_1993|].
 destruct i as [|i];[exact reference_control_member_1994|].
 destruct i as [|i];[exact reference_control_member_1995|].
 destruct i as [|i];[exact reference_control_member_1996|].
 destruct i as [|i];[exact reference_control_member_1999|].
 destruct i as [|i];[exact reference_control_member_2000|].
 destruct i as [|i];[exact reference_control_member_2001|].
 destruct i as [|i];[exact reference_control_member_2002|].
 destruct i as [|i];[exact reference_control_member_2005|].
 destruct i as [|i];[exact reference_control_member_2006|].
 destruct i as [|i];[exact reference_control_member_2007|].
 destruct i as [|i];[exact reference_control_member_2008|].
 destruct i as [|i];[exact reference_control_member_2011|].
 destruct i as [|i];[exact reference_control_member_2012|].
 destruct i as [|i];[exact reference_control_member_2015|].
 destruct i as [|i];[exact reference_control_member_2016|].
 destruct i as [|i];[exact reference_control_member_2017|].
 destruct i as [|i];[exact reference_control_member_2020|].
 destruct i as [|i];[exact reference_control_member_2021|].
 destruct i as [|i];[exact reference_control_member_2022|].
 destruct i as [|i];[exact reference_control_member_2025|].
 destruct i as [|i];[exact reference_control_member_2026|].
 destruct i as [|i];[exact reference_control_member_2027|].
 destruct i as [|i];[exact reference_control_member_2030|].
 destruct i as [|i];[exact reference_control_member_2031|].
 destruct i as [|i];[exact reference_control_member_2032|].
 destruct i as [|i];[exact reference_control_member_2035|].
 destruct i as [|i];[exact reference_control_member_2036|].
 destruct i as [|i];[exact reference_control_member_2037|].
 destruct i as [|i];[exact reference_control_member_2040|].
 destruct i as [|i];[exact reference_control_member_2041|].
 destruct i as [|i];[exact reference_control_member_2042|].
 destruct i as [|i];[exact reference_control_member_2045|].
 destruct i as [|i];[exact reference_control_member_2046|].
 destruct i as [|i];[exact reference_control_member_2047|].
 destruct i as [|i];[exact reference_control_member_2050|].
 destruct i as [|i];[exact reference_control_member_2051|].
 destruct i as [|i];[exact reference_control_member_2052|].
 destruct i as [|i];[exact reference_control_member_2055|].
 destruct i as [|i];[exact reference_control_member_2056|].
 destruct i as [|i];[exact reference_control_member_2057|].
 destruct i as [|i];[exact reference_control_member_2060|].
 destruct i as [|i];[exact reference_control_member_2061|].
 destruct i as [|i];[exact reference_control_member_2062|].
 destruct i as [|i];[exact reference_control_member_2065|].
 destruct i as [|i];[exact reference_control_member_2066|].
 destruct i as [|i];[exact reference_control_member_2069|].
 destruct i as [|i];[exact reference_control_member_2070|].
 destruct i as [|i];[exact reference_control_member_2073|].
 destruct i as [|i];[exact reference_control_member_2074|].
 destruct i as [|i];[exact reference_control_member_2077|].
 destruct i as [|i];[exact reference_control_member_2078|].
 destruct i as [|i];[exact reference_control_member_2081|].
 destruct i as [|i];[exact reference_control_member_2082|].
 destruct i as [|i];[exact reference_control_member_2085|].
 destruct i as [|i];[exact reference_control_member_2086|].
 destruct i as [|i];[exact reference_control_member_2089|].
 destruct i as [|i];[exact reference_control_member_2090|].
 destruct i as [|i];[exact reference_control_member_2093|].
 destruct i as [|i];[exact reference_control_member_2094|].
 destruct i as [|i];[exact reference_control_member_2097|].
 destruct i as [|i];[exact reference_control_member_2098|].
 destruct i as [|i];[exact reference_control_member_2099|].
 destruct i as [|i];[exact reference_control_member_2100|].
 destruct i as [|i];[exact reference_control_member_2101|].
 destruct i as [|i];[exact reference_control_member_2102|].
 destruct i as [|i];[exact reference_control_member_2103|].
 destruct i as [|i];[exact reference_control_member_2104|].
 destruct i as [|i];[exact reference_control_member_2105|].
 destruct i as [|i];[exact reference_control_member_2106|].
 destruct i as [|i];[exact reference_control_member_2107|].
 destruct i as [|i];[exact reference_control_member_2108|].
 destruct i as [|i];[exact reference_control_member_2109|].
 destruct i as [|i];[exact reference_control_member_2110|].
 destruct i as [|i];[exact reference_control_member_2111|].
 destruct i as [|i];[exact reference_control_member_2112|].
 destruct i as [|i];[exact reference_control_member_2113|].
 destruct i as [|i];[exact reference_control_member_2114|].
 destruct i as [|i];[exact reference_control_member_2115|].
 destruct i as [|i];[exact reference_control_member_2116|].
 destruct i as [|i];[exact reference_control_member_2117|].
 destruct i as [|i];[exact reference_control_member_2118|].
 destruct i as [|i];[exact reference_control_member_2119|].
 destruct i as [|i];[exact reference_control_member_2120|].
 destruct i as [|i];[exact reference_control_member_2121|].
 destruct i as [|i];[exact reference_control_member_2122|].
 destruct i as [|i];[exact reference_control_member_2123|].
 destruct i as [|i];[exact reference_control_member_2124|].
 destruct i as [|i];[exact reference_control_member_2125|].
 destruct i as [|i];[exact reference_control_member_2126|].
 destruct i as [|i];[exact reference_control_member_2127|].
 destruct i as [|i];[exact reference_control_member_2128|].
 destruct i as [|i];[exact reference_control_member_2129|].
 destruct i as [|i];[exact reference_control_member_2130|].
 destruct i as [|i];[exact reference_control_member_2131|].
 destruct i as [|i];[exact reference_control_member_2132|].
 destruct i as [|i];[exact reference_control_member_2133|].
 destruct i as [|i];[exact reference_control_member_2134|].
 destruct i as [|i];[exact reference_control_member_2135|].
 destruct i as [|i];[exact reference_control_member_2136|].
 destruct i as [|i];[exact reference_control_member_2137|].
 destruct i as [|i];[exact reference_control_member_2138|].
 destruct i as [|i];[exact reference_control_member_2139|].
 destruct i as [|i];[exact reference_control_member_2140|].
 destruct i as [|i];[exact reference_control_member_2141|].
 destruct i as [|i];[exact reference_control_member_2142|].
 destruct i as [|i];[exact reference_control_member_2143|].
 destruct i as [|i];[exact reference_control_member_2144|].
 destruct i as [|i];[exact reference_control_member_2145|].
 lia.
Qed.
Lemma reference_rs1_predecessors i node : (i < 170)%coq_nat -> List.In node (reference_rs1_refs i) ->
 node = 1884 \/ exists j, (j < i)%coq_nat /\ (j < 170)%coq_nat /\ reference_rs1_node j = node /\ reference_rs1_width_of node = reference_rs1_width j /\ (reference_rs1_rank j < reference_rs1_rank i)%coq_nat.
Proof.
 intro Bound.
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 0%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 1%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 4%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 7%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 10%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 13%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 16%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 19%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 21%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 22%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 24%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 26%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 28%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 30%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 31%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 33%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 34%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 36%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 37%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 39%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 41%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 43%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 45%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 47%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 49%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 50%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 51%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 53%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 54%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 55%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 57%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 58%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 59%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 62%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 63%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 65%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 66%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 67%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 69%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 70%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 71%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 73%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 75%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 76%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 78%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 79%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 81%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 82%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 84%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 85%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 87%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 88%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 90%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 91%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 93%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 94%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 96%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 97%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 99%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 100%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 102%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 103%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 105%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 107%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 109%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 111%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 113%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 115%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 117%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 119%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 121%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 122%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 120%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 123%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 118%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 124%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 116%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 125%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 114%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 126%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 112%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 127%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 110%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 128%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 108%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 129%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 106%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 130%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 104%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 131%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 101%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 132%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 98%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 133%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 95%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 134%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 92%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 135%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 89%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 136%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 86%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 137%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 83%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 138%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 80%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 139%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 77%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 140%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 74%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 141%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 72%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 142%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 68%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 143%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 64%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 144%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 60%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 145%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 56%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 146%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 52%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 147%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 48%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 148%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 46%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 149%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 44%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 150%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 42%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 151%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 40%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 152%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 38%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 153%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 35%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 154%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 32%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 155%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 29%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 156%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 27%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 157%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 25%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 158%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 23%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 159%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 20%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 160%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 17%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 161%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 14%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 162%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 11%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 163%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 8%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 164%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 5%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 165%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 2%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 166%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 167%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs1_refs reference_rs1_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 168%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 lia.
Qed.
Theorem reference_rs1_node_type_step i invalid old result : (i < 170)%coq_nat ->
 (forall site value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (reference_rs1_expression i) old old = Some value -> type_of_val value = Gtyp (Fuint (reference_rs1_width i))) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (reference_rs1_node i) result = Some value /\ type_of_val value = Gtyp (Fuint (reference_rs1_width i)).
Proof.
 intros Bound Shape Step.
 assert (Position : select_node_offsets (reference_rs1_offsets i) flat_statements = Some (reference_rs1_nodes i)).
 { unfold reference_rs1_offsets,reference_rs1_nodes;destruct (nth 2%nat reference_rs1_groups i) as [|[|g]];[exact reference_control_0_positions|exact reference_control_1_positions|exact reference_control_2_positions]. }
 assert (Safety : selected_node_safety flat_memories flat_statements (reference_rs1_offsets i) flat_statements = true).
 { unfold reference_rs1_offsets;destruct (nth 2%nat reference_rs1_groups i) as [|[|g]];[exact reference_control_0_safety|exact reference_control_1_safety|exact reference_control_2_safety]. }
 destruct (selected_node_safe_position flat_memories flat_statements (reference_rs1_offsets i) flat_statements (reference_rs1_nodes i) _ _ Position Safety (reference_rs1_member i Bound)) as [count [tail [Pos [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Pos Step) as [value Eval]. rewrite add0n in Eval.
 exists value. split;[eapply formal_combinational_known_node;[exact Pos|exact Safe|exact Nonreg|exact Eval|eapply Shape;exact Eval|exact Step]|eapply Shape;exact Eval].
Qed.
Theorem reference_rs1_types_history invalid history limit start :
 (forall t, (t < limit)%coq_nat -> formal_value_iter invalid flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (forall t, (start <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 1884 (history t) = Some value /\ type_of_val value = Gtyp (Fuint 32)) ->
 forall i, (i < 170)%coq_nat -> forall t, (Nat.add start (reference_rs1_rank i) <= t)%coq_nat -> (t <= limit)%coq_nat ->
 exists value, VM.find (reference_rs1_node i) (history t) = Some value /\ type_of_val value = Gtyp (Fuint (reference_rs1_width i)).
Proof.
 intros Steps Source i. induction i using lt_wf_ind. intros Bound [|t] Lower Upper.
 - pose proof (proj2 (reference_rs1_plan i Bound));lia.
 - eapply reference_rs1_node_type_step;[exact Bound| |apply Steps;lia].
   intros site value Eval. eapply immediate_expression_check_sound;[exact (proj1 (reference_rs1_plan i Bound))| |exact Eval].
   intros node Member. destruct (reference_rs1_predecessors i node Bound Member) as [->|[j [Before [J [Node [Width Rank]]]]]].
   + change (exists value, VM.find 1884 (history t) = Some value /\ type_of_val value = Gtyp (Fuint 32)).
     apply Source;[pose proof (proj2 (reference_rs1_plan i Bound));lia|lia].
   + rewrite Width. rewrite <- Node. apply (H j Before J t);lia.
Qed.

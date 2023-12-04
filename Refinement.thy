theory Refinement
  imports (*"Collections.Refine_Dflt_Only_ICF"*) "Refine_Monadic.Refine_Monadic" LayerMaintenance
begin

subsection \<open>PathFinding\<close>

context Graph
begin
definition pathFindingRefine :: "node \<Rightarrow> path nres" where
  "pathFindingRefine s \<equiv> do {
    (p, _) \<leftarrow> WHILE (\<lambda>(p, u). outgoing u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> SPEC (\<lambda>e. e \<in> outgoing u);
      let p = p @ [e];
      let u = snd e;
      RETURN (p, u)
    }) ([], s);
    RETURN p
  }"

find_theorems "WHILE\<^sub>T" (* TODO *)
find_theorems wellorder_class

definition pathFinding_invar :: "node \<Rightarrow> (path \<times> node) \<Rightarrow> bool" where
  "pathFinding_invar s \<equiv> \<lambda>(p, u). isPath s p u"

lemma pathFinding_invar_step:
  "\<lbrakk>e \<in> outgoing u; pathFinding_invar s (p, u)\<rbrakk> \<Longrightarrow> pathFinding_invar s (p @ [e], snd e)"
  unfolding pathFinding_invar_def by (auto simp: isPath_tail outgoing_def)

lemma pathFinding_finds_maximal_path: "pathFindingRefine s \<le> SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
  unfolding pathFindingRefine_def
  apply (intro WHILE_rule[where I="pathFinding_invar s"] refine_vcg)
    apply (auto intro: pathFinding_invar_step)
  unfolding pathFinding_invar_def by auto
end \<comment> \<open>Graph\<close>

context ST_Graph
begin
(* TODO useful? then move *)
lemma stl_no_outD: "stl.outgoing u = {} \<Longrightarrow> u = t \<or> u \<notin> stl.V"
  using only_t_without_stl_outgoing by blast


find_theorems "(?A :: _ nres) \<le> ?B \<Longrightarrow> ?B \<le> ?C \<Longrightarrow> ?A \<le> ?C"
thm SPEC_trans
thm nrec.leq_trans


find_theorems "SPEC ?A \<le> SPEC ?B"
thm SPEC_rule
thm iSPEC_rule
(* TODO why are there two? *)

lemma pathFinding_finds_st_path:
  assumes "connected s t"
  shows "stl.pathFindingRefine s \<le> SPEC (\<lambda>p. isPath s p t)"
proof (rule nrec.leq_trans[OF stl.pathFinding_finds_maximal_path], rule SPEC_rule)
  fix p
  assume "\<exists>u. stl.outgoing u = {} \<and> stl.isPath s p u"
  then obtain u where NO_OUT: "stl.outgoing u = {}" and PATH: "stl.isPath s p u" by blast
  then have "u = t \<or> u \<notin> stl.V" using stl_no_outD by simp
  with PATH show "isPath s p t"
  proof (elim disjE)
    assume "u \<notin> stl.V"
    with PATH have "u = s" "p = []"
      using stl.acyclic stl.isCycle_def
      by (metis stl.connected_def stl.distinct_nodes_in_V_if_connected(2))+
    with NO_OUT have "s = t \<or> s \<notin> stl.V" using stl_no_outD by blast
    with assms have "s = t"
      using stl.distinct_nodes_in_V_if_connected stl_maintains_st_connected by blast
    with \<open>p = []\<close> show ?thesis by simp
  qed (auto intro: stl_sub_c.sg_paths_are_base_paths)
qed (* TODO prettify *)
end \<comment> \<open>ST_Graph\<close>

subsubsection \<open>Total correctness\<close>

context Distance_Bounded_Graph
begin

definition pathFindingRefine' :: "node \<Rightarrow> path nres" where
  "pathFindingRefine' s \<equiv> do {
    (p, _) \<leftarrow> WHILE\<^sub>T\<^bsup>pathFinding_invar s\<^esup> (\<lambda>(p, u). outgoing u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> SPEC (\<lambda>e. e \<in> outgoing u);
      let p = p @ [e];
      let u = snd e;
      RETURN (p, u)
    }) ([], s);
    RETURN p
  }"

(* definition custom_wf :: "(path \<times> path) set" where "custom_wf \<equiv> {(p1, p2) |p1 p2. length p1 \<le> length p2}" *)
definition custom_wf :: "(path \<times> path) set"
  where "custom_wf \<equiv> {(p1, p2) |p1 p2. (\<exists>u v. isPath u p1 v) \<and> (\<exists>u v. isPath u p2 v) \<and> length p1 > length p2}"

thm wf_def
thm wf_measure
thm wf_subset
find_theorems "_ \<Longrightarrow> wf ?x"
find_consts "'a rel \<Rightarrow> 'a list rel"
find_consts "'a rel \<Rightarrow> 'b rel \<Rightarrow> ('a \<times> 'b) rel"
thm lex_prod_def
find_consts "('a \<times> 'b) \<Rightarrow> ('b \<times> 'a)"
thm prod.swap_def
thm inv_image_def

(*lemma "wf custom_wf"
proof (rule wfUNIVI)
  fix P x
  assume "\<forall>x. (\<forall>y. (y, x) \<in> custom_wf \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P x"
  proof
  apply (rule wfUNIVI)

lemma pathFinding_finds_maximal_path': "pathFindingRefine' s \<le> SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
  unfolding pathFindingRefine'_def
  apply (intro refine_vcg)
     apply (subgoal_tac "wf (inv_image finite_psubset fst)", assumption)
    (*apply (auto intro: pathFinding_invar_step)*)
  unfolding pathFinding_invar_def (*by auto*)*)

end






\<comment> \<open>PathFinding\<close>

subsection \<open>RightPass\<close>

definition removeEdge :: "_ graph \<Rightarrow> edge \<Rightarrow> _ graph" where
  "removeEdge c e \<equiv> c(e := 0)"

definition removeEdges :: "_ graph \<Rightarrow> edge set \<Rightarrow> _ graph" where
  "removeEdges c R \<equiv> \<lambda>e. if e \<in> R then 0 else c e"

context Graph
begin
lemma removeEdges_subgraph: "isSubgraph (removeEdges c S) c"
  unfolding removeEdges_def isSubgraph_def by presburger

lemma removeEdges_E: "Graph.E (removeEdges c S) = E - S"
  unfolding removeEdges_def Graph.E_def by auto
end

(* TODO refine removeEdges and use the refined version *)

(* This is the exact definition, using the edge set*)
definition rightPassRefine_original :: "_ graph \<Rightarrow> edge set \<Rightarrow> (_ graph) nres" where
  "rightPassRefine_original c Q \<equiv> do {
    (c, _) \<leftarrow> WHILE (\<lambda>(c, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      e \<leftarrow> SPEC (\<lambda>e. e \<in> Q);
      let Q = Q - {e};
      let v = snd e;
      if Graph.incoming c v = {} then do {
        let R = Graph.outgoing c v;
        let Q = Q \<union> R;
        let c = removeEdges c R;
        RETURN (c, Q)}
      else RETURN (c, Q)
    }) (c, Q);
    RETURN c
  }"

text \<open>This definition is slightly adapted in that it works on the set of edge tails,
      instead of on the edges themselves.\<close>
definition rightPassRefine :: "_ graph \<Rightarrow> node set \<Rightarrow> (_ graph) nres" where
  "rightPassRefine c Q \<equiv> do {
    (c, _) \<leftarrow> WHILE (\<lambda>(c, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      u \<leftarrow> SPEC (\<lambda>u. u \<in> Q);
      let Q = Q - {u};
      if Graph.incoming c u = {} then do {
        let R = Graph.outgoing c u;
        let Q = Q \<union> (snd ` R);
        let c = removeEdges c R;
        RETURN (c, Q)}
      else RETURN (c, Q)
    }) (c, Q);
    RETURN c
  }"

(* TODO check which definition is better *)

definition rightPass_invar :: "_ graph \<Rightarrow> node \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool"
  where "rightPass_invar c s \<equiv> \<lambda>(c', Q). isSubgraph c' c
                                \<and> s \<notin> Q
                                \<and> (\<forall>u v. Graph.connected c s u \<longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v))
                                \<and> (\<forall>u \<in> Graph.V c' - Q - {s}. Graph.incoming c' u \<noteq> {})"

lemma (in Graph) rightPassRefine_step:
  assumes S_NO_IN: "incoming s = {}"
    and "u \<in> Q"
    and U_NO_IN: "Graph.incoming c' u = {}"
    and INVAR: "rightPass_invar c s (c', Q)"
  shows "rightPass_invar c s (removeEdges c' (Graph.outgoing c' u), Q - {u} \<union> snd ` Graph.outgoing c' u)"
  unfolding rightPass_invar_def
proof (clarify, intro conjI)
  interpret g': Graph c' .
  interpret g'': Graph "removeEdges c' (g'.outgoing u)" .
  from INVAR have SUB: "isSubgraph c' c"
    and "s \<notin> Q"
    and S_CON: "\<And>u v. connected s u \<Longrightarrow> g'.connected s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> g'.V - Q - {s}. g'.incoming  u \<noteq> {}"
    unfolding rightPass_invar_def by simp_all

  show "isSubgraph (removeEdges c' (g'.outgoing u)) c"
    using g'.removeEdges_subgraph SUB subgraph.order_trans by blast

  show "s \<notin> Q - {u} \<union> snd ` g'.outgoing u"
  proof -
    from S_NO_IN SUB have "g'.incoming s = {}" unfolding Graph.incoming_def
      using Subgraph.E_ss Subgraph.intro by blast
    then have "s \<notin> snd ` g'.outgoing u" unfolding g'.incoming_def g'.outgoing_def by fastforce
    with \<open>s \<notin> Q\<close> show "?thesis" by blast
  qed

  show "(\<forall>v w. connected s v \<longrightarrow> g''.connected s v \<and> (removeEdges c' (g'.outgoing u)) (v, w) = c (v, w))"
  proof (clarify, intro conjI)
    from \<open>u \<in> Q\<close> \<open>s \<notin> Q\<close> have "u \<noteq> s" by blast
    fix v w
    assume "connected s v"
    then have CON': "g'.connected s v" and C'_EQ_C: "c' (v, w) = c (v, w)" using S_CON by simp_all
    then obtain p where PATH': "g'.isPath s p v" unfolding g'.connected_def by blast
    with \<open>u \<noteq> s\<close> U_NO_IN have "u \<notin> set (g'.pathVertices s p)"
      by (metis g'.distinct_nodes_have_in_out_if_connected(2) g'.connected_def g'.pathVertices_fwd g'.split_path_at_vertex)
    with PATH' have "set p \<inter> g'.outgoing u = {}"
      using g'.outgoing_edges_not_on_path g'.pathVertices_fwd by fastforce
    with PATH' have "g''.isPath s p v" unfolding Graph.isPath_alt using g'.removeEdges_E by blast
    then show "g''.connected s v" using g''.connected_def by blast

    from \<open>u \<noteq> s\<close> CON' U_NO_IN have "u \<noteq> v" using g'.distinct_nodes_have_in_out_if_connected(2) by blast
    then have "removeEdges c' (g'.outgoing u) (v, w) = c' (v, w)"
      unfolding g'.outgoing_def removeEdges_def by simp
    then show "removeEdges c' (g'.outgoing u) (v, w) = c (v, w)" using C'_EQ_C by simp
  qed

  show "(\<forall>v \<in> g''.V - (Q - {u} \<union> snd ` g'.outgoing u) - {s}. g''.incoming v \<noteq> {})"
  proof clarsimp (* TODO can you remove lemmas from clarify? *)
    fix v
    assume "v \<in> g''.V" "v \<noteq> s" "v \<notin> snd ` g'.outgoing u" "v \<in> Q \<longrightarrow> v = u" "g''.incoming v = {}"
    from \<open>v \<in> g''.V\<close> have "v \<in> g'.V"
      using g'.removeEdges_subgraph Subgraph.V_ss Subgraph.intro by blast
    have "v \<notin> Q"
    proof
      assume "v \<in> Q"
      with \<open>v \<in> Q \<longrightarrow> v = u\<close> have "v = u" by blast
      (* NOTE: \<open>g''.incoming v = {}\<close> is not needed, since we could get it from U_NO_IN, might be more elegant, but also more verbose *)
      with \<open>v \<in> g''.V\<close> \<open>g''.incoming v = {}\<close> obtain w where "(u, w) \<in> g''.E"
        unfolding g''.incoming_def by (auto elim: g''.vertex_cases)
      then show False using g'.removeEdges_E g'.outgoing_alt by fastforce
    qed
    with \<open>v \<in> g'.V\<close> \<open>v \<noteq> s\<close> NODE_HAS_IN obtain u' where "(u', v) \<in> g'.E" unfolding g'.incoming_def by blast
    with \<open>v \<notin> snd ` g'.outgoing u\<close> have "(u', v) \<in> g''.E" using g'.removeEdges_E by blast
    with \<open>g''.incoming v = {}\<close> show False unfolding g''.incoming_def by blast
  qed
qed

context Distance_Bounded_Graph
begin

lemma rightPassRefine_final:
  assumes SUB: "isSubgraph c' c"
    and S_CON: "\<And>u v. connected s u \<Longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> Graph.V c' - {s}. Graph.incoming c' u \<noteq> {}"
  shows "rightPassAbstract c s = c'"
proof (intro subgraph.order_antisym, unfold isSubgraph_def, clarsimp_all)
  fix u v
  assume "rightPassAbstract c s (u, v) \<noteq> 0"
  with S_CON show "rightPassAbstract c s (u, v) = c' (u, v)"
    using rightPassAbstract_nz_iff S_Graph.rp_is_c_if_s_connected by metis
next
  interpret g': Distance_Bounded_Graph c' b
    using SUB Subgraph.intro Subgraph.sg_Distance_Bounded Distance_Bounded_Graph_axioms by blast
  fix u v
  assume "c' (u, v) \<noteq> 0"
  then have "u \<in> g'.V" unfolding Graph.V_def Graph.E_def by blast
  obtain w where W_CON: "g'.connected w u" and W_NO_IN: "g'.incoming w = {}" using g'.obtain_front_terminal_connected by blast
  from W_CON \<open>u \<in> g'.V\<close> have "w \<in> g'.V" by (meson g'.connected_inV_iff)
  with W_NO_IN NODE_HAS_IN have "w = s" by blast
  with W_CON have "rightPassAbstract c s (u, v) = c (u, v)"
    using SUB Subgraph.intro Subgraph.sg_connected_remains_base_connected S_Graph.rp_is_c_if_s_connected by blast
  also from SUB \<open>c' (u, v) \<noteq> 0\<close> have "... = c' (u, v)" unfolding isSubgraph_def by metis
  finally show "c' (u, v) = rightPassAbstract c s (u, v)" by simp
qed (* TODO cleanup *)

theorem rightPassRefine_correct:
  assumes S_NO_IN: "incoming s = {}"
    and Q_START: "s \<notin> Q" "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}"
  shows "rightPassRefine c Q \<le> RETURN (rightPassAbstract c s)"
  unfolding rightPassRefine_def
proof (intro WHILE_rule[where I="rightPass_invar c s"] refine_vcg, clarsimp_all)
  show "rightPass_invar c s (c, Q)" unfolding rightPass_invar_def using Q_START by blast
next
  fix c' :: "'capacity graph"
  fix Q u
  assume step_assms: "rightPass_invar c s (c', Q)" "u \<in> Q"
  then have SUB: "isSubgraph c' c"
    and "s \<notin> Q"
    and S_CON: "\<forall>u v. connected s u \<longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> Graph.V c' - Q - {s}. Graph.incoming c' u \<noteq> {}"
    unfolding rightPass_invar_def by simp_all
  then show "Graph.incoming c' u \<noteq> {} \<Longrightarrow> rightPass_invar c s (c', Q - {u})"
    unfolding rightPass_invar_def by blast

  from S_NO_IN step_assms show "Graph.incoming c' u = {} \<Longrightarrow> rightPass_invar c s (removeEdges c' (Graph.outgoing c' u), Q - {u} \<union> snd ` Graph.outgoing c' u)"
    using rightPassRefine_step by simp
next
  fix c' :: "'capacity  graph"
  assume "rightPass_invar c s (c', {})"
  then show "rightPassAbstract c s = c'" unfolding rightPass_invar_def using rightPassRefine_final by simp
qed
end






thm wf_def
thm wf_measure
thm wf_subset
find_theorems "_ \<Longrightarrow> wf ?x"
find_consts "'a rel \<Rightarrow> 'a list rel"
find_consts "'a rel \<Rightarrow> 'b rel \<Rightarrow> ('a \<times> 'b) rel"
thm lex_prod_def
find_consts "('a \<times> 'b) \<Rightarrow> ('b \<times> 'a)"
thm prod.swap_def
thm inv_image_def

(*definition rightPassRefine' :: "_ graph \<Rightarrow> node set \<Rightarrow> (_ graph) nres" where
  "rightPassRefine' c Q \<equiv> do {
    (c, _) \<leftarrow> WHILE\<^sub>T\<^bsup>rightPass_invar c s\<^esup> (\<lambda>(c, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      u \<leftarrow> SPEC (\<lambda>u. u \<in> Q);
      let Q = Q - {u};
      if Graph.incoming c u = {} then do {
        let R = Graph.outgoing c u;
        let Q = Q \<union> (snd ` R);
        let c = removeEdges c R;
        RETURN (c, Q)}
      else RETURN (c, Q)
    }) (c, Q);
    RETURN c
  }"*)

definition rightPassRefine' :: "_ graph \<Rightarrow> node set \<Rightarrow> (_ graph) nres" where
  "rightPassRefine' c Q \<equiv> do {
    (c, _) \<leftarrow> WHILET (\<lambda>(c, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      u \<leftarrow> SPEC (\<lambda>u. u \<in> Q);
      let Q = Q - {u};
      if Graph.incoming c u = {} then do {
        let R = Graph.outgoing c u;
        let Q = Q \<union> (snd ` R);
        let c = removeEdges c R;
        RETURN (c, Q)}
      else RETURN (c, Q)
    }) (c, Q);
    RETURN c
  }"

definition tmp_wf :: "(_ graph \<times> node set) rel"
  where "tmp_wf \<equiv> {(x, y). isTrueSubgraph x y} <*lex*> finite_psubset" (* TODO replace emptyset *)

interpretation subgraph: wellorder isSubgraph isTrueSubgraph sorry
thm subgraph.wf

lemma tmp_wf_wf: "wf tmp_wf" unfolding tmp_wf_def (*by (auto intro: subgraph.wf)*)
  apply (intro wf_lex_prod)
   apply (rule subgraph.wf)
  apply (rule wf_finite_psubset)
  done

(* TODO *)
locale Finite_Bounded_Graph = Finite_Graph + Distance_Bounded_Graph
(*Finite_Graph c + Distance_Bounded_Graph c b
  for c :: "'capacity::linordered_idom graph" and b*)
begin
theorem rightPassRefine'_correct:
  assumes S_NO_IN: "incoming s = {}"
    and Q_START: "s \<notin> Q" "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}"
  shows "rightPassRefine' c Q \<le> RETURN (rightPassAbstract c s)"
  unfolding rightPassRefine'_def
proof (intro WHILET_rule[where I="rightPass_invar c s"] refine_vcg, clarsimp_all)
  show "wf tmp_wf" by (rule tmp_wf_wf) oops

end


\<comment> \<open>RightPass\<close>

end
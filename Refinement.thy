theory Refinement
  imports "Refine_Monadic.Refine_Monadic" LayerMaintenance
begin

subsection \<open>PathFinding\<close>

context Graph
begin
definition pathFindingRefine_partial :: "node \<Rightarrow> path nres" where
  "pathFindingRefine_partial s \<equiv> do {
    (p, _) \<leftarrow> WHILE (\<lambda>(p, u). outgoing u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> SPEC (\<lambda>e. e \<in> outgoing u);
      let p = p @ [e];
      let u = snd e;
      RETURN (p, u)
    }) ([], s);
    RETURN p
  }"

definition pathFinding_invar :: "node \<Rightarrow> (path \<times> node) \<Rightarrow> bool" where
  "pathFinding_invar s \<equiv> \<lambda>(p, u). isPath s p u"

lemma pathFinding_finds_maximal_path: "pathFindingRefine_partial s \<le> SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
  unfolding pathFindingRefine_partial_def
  apply (intro WHILE_rule[where I="pathFinding_invar s"] refine_vcg)
  unfolding pathFinding_invar_def outgoing_def by (auto simp: isPath_append_edge)
end \<comment> \<open>Graph\<close>

subsubsection \<open>Total correctness\<close>

context Distance_Bounded_Graph
begin

(* TODO useful? then move *)
lemma in_outgoingD: "(u', v) \<in> outgoing u \<Longrightarrow> (u, v) \<in> E \<and> u' = u" unfolding outgoing_def by blast

definition pathFindingRefine_total :: "node \<Rightarrow> path nres" where
  "pathFindingRefine_total s \<equiv> do {
    (p, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(p, u). outgoing u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> SPEC (\<lambda>e. e \<in> outgoing u);
      let p = p @ [e];
      let u = snd e;
      RETURN (p, u)
    }) ([], s);
    RETURN p
  }"

definition bounded_path_measure :: "path rel" where "bounded_path_measure \<equiv> measure (\<lambda>p. b - length p)"

lemma pathFinding_total_correct: "pathFindingRefine_total s \<le> SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
  unfolding pathFindingRefine_total_def
proof (intro WHILET_rule[where I="pathFinding_invar s"] refine_vcg, clarsimp_all dest!: in_outgoingD)
  show "wf (inv_image bounded_path_measure fst)" unfolding bounded_path_measure_def by blast
next
  fix p u v
  assume STEP: "pathFinding_invar s (p, u)" "(u, v) \<in> E"
  then have "isPath s p u" and PATH': "isPath s (p @ [(u, v)]) v"
    unfolding pathFinding_invar_def by (simp_all add: isPath_append_edge)
  then have "((p @ [(u, v)]), p) \<in> bounded_path_measure" unfolding bounded_path_measure_def
    using path_length_bounded by fastforce
  with PATH' show "pathFinding_invar s (p @ [(u, v)], v) \<and> ((p @ [(u, v)], v), p, u) \<in> inv_image bounded_path_measure fst"
    unfolding pathFinding_invar_def by simp
qed (auto simp: pathFinding_invar_def)

end \<comment> \<open>Distance_Bounded_Graph\<close>

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

lemma back_terminal_s_path_is_st_path:
  "stl.outgoing u = {} \<Longrightarrow> stl.connected s t\<Longrightarrow> stl.isPath s p u \<Longrightarrow> stl.isPath s p t"
proof (drule stl_no_outD, elim disjE)
  assume PATH: "stl.isPath s p u" and CON: "stl.connected s t" and "u \<notin> stl.V"
  then have "s \<notin> stl.V" "p = []"
    using stl.acyclic stl.isCycle_def
    by (metis stl.connected_def stl.distinct_nodes_in_V_if_connected(2))+
  with PATH CON show "stl.isPath s p t"
    using Graph.distinct_nodes_in_V_if_connected(1) Graph.isPath.simps(1) by blast
qed (auto intro: stl_sub_c.sg_paths_are_base_paths) (* TODO cleanup *)

lemma pathFinding_partial_finds_st_path:
  assumes "connected s t"
  shows "stl.pathFindingRefine_partial s \<le> SPEC (\<lambda>p. isPath s p t)"
  apply (rule nrec.leq_trans[OF stl.pathFinding_finds_maximal_path], rule SPEC_rule)
  using stl_maintains_st_connected[OF \<open>connected s t\<close>] back_terminal_s_path_is_st_path stl_sub_c.sg_paths_are_base_paths by blast
(* TODO cleanup *)
end \<comment> \<open>ST_Graph\<close>

(* TODO refactor into new locale *)
locale TMPLoc = ST_Graph + Distance_Bounded_Graph
begin
lemma pathFinding_total_finds_st_path:
  assumes "connected s t"
  shows "stl.pathFindingRefine_total s \<le> SPEC (\<lambda>p. isPath s p t)"
  apply (rule nrec.leq_trans[OF stl.pathFinding_total_correct], rule SPEC_rule)
  using stl_maintains_st_connected[OF \<open>connected s t\<close>] back_terminal_s_path_is_st_path stl_sub_c.sg_paths_are_base_paths by blast
end

\<comment> \<open>PathFinding\<close>



subsection \<open>RightPass\<close>

definition removeEdge :: "_ graph \<Rightarrow> edge \<Rightarrow> _ graph" where
  "removeEdge c e \<equiv> c(e := 0)"

definition removeEdges :: "_ graph \<Rightarrow> edge set \<Rightarrow> _ graph" where
  "removeEdges c R \<equiv> \<lambda>e. if e \<in> R then 0 else c e"

context Graph
begin
lemma removeEdges_E: "Graph.E (removeEdges c S) = E - S"
  unfolding removeEdges_def Graph.E_def by auto

lemma removeEdges_sg: "isSubgraph (removeEdges c S) c"
  unfolding removeEdges_def isSubgraph_def by presburger

lemma removeEdges_psg: "\<exists>e. e \<in> S \<inter> E \<Longrightarrow> isProperSubgraph (removeEdges c S) c"
  unfolding isProperSubgraph_def using removeEdges_sg 
  by (simp add: Graph.E_def' removeEdges_def)
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
definition rightPassRefine_partial :: "_ graph \<Rightarrow> node set \<Rightarrow> (_ graph) nres" where
  "rightPassRefine_partial c Q \<equiv> do {
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

definition rightPass_partial_invar :: "_ graph \<Rightarrow> node \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool"
  where "rightPass_partial_invar c s \<equiv> \<lambda>(c', Q). isSubgraph c' c
                                \<and> s \<notin> Q
                                \<and> (\<forall>u v. Graph.connected c s u \<longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v))
                                \<and> (\<forall>u \<in> Graph.V c' - Q - {s}. Graph.incoming c' u \<noteq> {})"


(* TODO check use of c''_def / Q'_def *)
lemma (in Graph) rightPassRefine_partial_step:
  assumes S_NO_IN: "incoming s = {}"
    and "u \<in> Q"
    and U_NO_IN: "Graph.incoming c' u = {}"
    and INVAR: "rightPass_partial_invar c s (c', Q)"
  defines "c'' \<equiv> removeEdges c' (Graph.outgoing c' u)"
    and "Q' \<equiv> Q - {u} \<union> snd ` Graph.outgoing c' u"
  shows "rightPass_partial_invar c s (c'', Q')"
  (*shows "rightPass_partial_invar c s (removeEdges c' (Graph.outgoing c' u), Q - {u} \<union> snd ` Graph.outgoing c' u)"
    (is "rightPass_partial_invar c s (?c'', ?Q')")*)
  unfolding rightPass_partial_invar_def
proof (clarify, intro conjI)
  interpret g': Graph c' .
  interpret g'': Graph c'' .
  from INVAR have SUB: "isSubgraph c' c"
    and "s \<notin> Q"
    and S_CON: "\<And>u v. connected s u \<Longrightarrow> g'.connected s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> g'.V - Q - {s}. g'.incoming  u \<noteq> {}"
    unfolding rightPass_partial_invar_def by simp_all

  show "isSubgraph c'' c" unfolding c''_def
    using g'.removeEdges_sg SUB subgraph.order_trans by blast

  show "s \<notin> Q'"
  proof -
    from S_NO_IN SUB have "g'.incoming s = {}" unfolding Graph.incoming_def
      using Subgraph.E_ss Subgraph.intro by blast
    then have "s \<notin> snd ` g'.outgoing u" unfolding g'.incoming_def g'.outgoing_def by fastforce
    with \<open>s \<notin> Q\<close> show "?thesis" unfolding Q'_def by blast
  qed

  show "(\<forall>v w. connected s v \<longrightarrow> g''.connected s v \<and> c'' (v, w) = c (v, w))"
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
    with PATH' have "g''.isPath s p v" unfolding Graph.isPath_alt c''_def using g'.removeEdges_E by blast
    then show "g''.connected s v" using g''.connected_def by blast

    from \<open>u \<noteq> s\<close> CON' U_NO_IN have "u \<noteq> v" using g'.distinct_nodes_have_in_out_if_connected(2) by blast
    then have "c'' (v, w) = c' (v, w)"
      unfolding g'.outgoing_def removeEdges_def c''_def by simp
    then show "c'' (v, w) = c (v, w)" using C'_EQ_C by simp
  qed

  show "(\<forall>v \<in> g''.V - Q' - {s}. g''.incoming v \<noteq> {})" unfolding Q'_def
  proof clarsimp (* TODO can you remove lemmas from clarify? *)
    fix v
    assume "v \<in> g''.V" "v \<noteq> s" "v \<notin> snd ` g'.outgoing u" "v \<in> Q \<longrightarrow> v = u" "g''.incoming v = {}"
    from \<open>v \<in> g''.V\<close> have "v \<in> g'.V" unfolding c''_def
      using g'.removeEdges_sg Subgraph.V_ss Subgraph.intro by blast
    have "v \<notin> Q"
    proof
      assume "v \<in> Q"
      with \<open>v \<in> Q \<longrightarrow> v = u\<close> have "v = u" by blast
      (* NOTE: \<open>g''.incoming v = {}\<close> is not needed, since we could get it from U_NO_IN, might be more elegant, but also more verbose *)
      with \<open>v \<in> g''.V\<close> \<open>g''.incoming v = {}\<close> obtain w where "(u, w) \<in> g''.E"
        unfolding g''.incoming_def by (auto elim: g''.vertex_cases)
      then show False unfolding c''_def using g'.removeEdges_E g'.outgoing_alt by fastforce
    qed
    with \<open>v \<in> g'.V\<close> \<open>v \<noteq> s\<close> NODE_HAS_IN obtain u' where "(u', v) \<in> g'.E" unfolding g'.incoming_def by blast
    with \<open>v \<notin> snd ` g'.outgoing u\<close> have "(u', v) \<in> g''.E" unfolding c''_def using g'.removeEdges_E by blast
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

theorem rightPassRefine_partial_correct:
  assumes S_NO_IN: "incoming s = {}"
    and Q_START: "s \<notin> Q" "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}"
  shows "rightPassRefine_partial c Q \<le> RETURN (rightPassAbstract c s)"
  unfolding rightPassRefine_partial_def
proof (intro WHILE_rule[where I="rightPass_partial_invar c s"] refine_vcg, clarsimp_all)
  show "rightPass_partial_invar c s (c, Q)" unfolding rightPass_partial_invar_def using Q_START by blast
next
  fix c' Q u
  assume step_assms: "rightPass_partial_invar c s (c', Q)" "u \<in> Q"
  then show "Graph.incoming c' u \<noteq> {} \<Longrightarrow> rightPass_partial_invar c s (c', Q - {u})"
    unfolding rightPass_partial_invar_def by blast

  let ?c'' = "removeEdges c' (Graph.outgoing c' u)"
  let ?Q' = "Q - {u} \<union> snd ` Graph.outgoing c' u"
  from S_NO_IN step_assms show "Graph.incoming c' u = {} \<Longrightarrow> rightPass_partial_invar c s (?c'', ?Q')"
    using rightPassRefine_partial_step by simp
next
  fix c'
  assume "rightPass_partial_invar c s (c', {})"
  then show "rightPassAbstract c s = c'" unfolding rightPass_partial_invar_def using rightPassRefine_final by simp
qed
end

subsubsection \<open>Total correctness\<close>

definition rightPassRefine_total :: "_ graph \<Rightarrow> node set \<Rightarrow> (_ graph) nres" where
  "rightPassRefine_total c Q \<equiv> do {
    (c, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(c, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
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

definition finiteProperSubgraph :: "_ graph rel"
  where "finiteProperSubgraph \<equiv> {(c', c). Proper_Subgraph c' c \<and> Finite_Graph c}"

lemma wf_finiteProperSubgraph: "wf finiteProperSubgraph"
proof (rule wf_subset)
  show "wf (inv_image finite_psubset Graph.E)" by simp
  show "finiteProperSubgraph \<subseteq> inv_image finite_psubset Graph.E"
    unfolding finiteProperSubgraph_def inv_image_def finite_psubset_def
    using Proper_Subgraph.E_pss Finite_Graph.finite_E by blast
qed

definition GraphWorkingSet_rel :: "(_ graph \<times> _ set) rel"
  where "GraphWorkingSet_rel \<equiv> finiteProperSubgraph <*lex*> finite_psubset"

lemma wf_GraphWorkingSet_rel: "wf GraphWorkingSet_rel" unfolding GraphWorkingSet_rel_def
  using wf_finiteProperSubgraph by auto

definition rightPass_total_invar :: "_ graph \<Rightarrow> node \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool"
  where "rightPass_total_invar c s \<equiv> \<lambda>(c', Q). rightPass_partial_invar c s (c', Q)
                                \<and> finite Q"

(* TODO does this make sense?
interpretation subgraph: wellorder isSubgraph isProperSubgraph sorry
thm subgraph.wf
*)


lemma (in Finite_Graph) rightPassRefine_total_step:
  assumes S_NO_IN: "incoming s = {}"
    and "u \<in> Q"
    and U_NO_IN: "Graph.incoming c' u = {}"
    and T_INVAR: "rightPass_total_invar c s (c', Q)"
  defines "c'' \<equiv> removeEdges c' (Graph.outgoing c' u)"
    and "Q' \<equiv> Q - {u} \<union> snd ` Graph.outgoing c' u"
  shows "rightPass_total_invar c s (c'', Q') \<and> ((c'', Q'), (c', Q)) \<in> GraphWorkingSet_rel"
  unfolding rightPass_total_invar_def
proof (clarify, intro conjI)
  from T_INVAR have P_INVAR: "rightPass_partial_invar c s (c', Q)" and "finite Q"
    unfolding rightPass_total_invar_def by auto
  then interpret g': Finite_Graph c' unfolding rightPass_partial_invar_def Finite_Graph_def
    using Subgraph.V_ss Subgraph.intro finite_V finite_subset by fast

  from S_NO_IN \<open>u \<in> Q\<close> U_NO_IN P_INVAR show "rightPass_partial_invar c s (c'', Q')"
    unfolding c''_def Q'_def by (rule rightPassRefine_partial_step)

  from \<open>finite Q\<close> show "finite Q'" unfolding Q'_def by blast

  show "((c'', Q'), c', Q) \<in> GraphWorkingSet_rel"
  proof (cases "g'.outgoing u = {}")
    case True
    then have "c'' = c'" unfolding c''_def removeEdges_def by simp
    moreover from True have "Q' = Q - {u}" unfolding Q'_def by simp
    moreover note \<open>u \<in> Q\<close> \<open>finite Q\<close>
    ultimately show ?thesis unfolding GraphWorkingSet_rel_def by auto
  next
    case False
    then have "Proper_Subgraph c'' c'" unfolding c''_def
      using g'.removeEdges_psg g'.outgoing_edges Proper_Subgraph.intro by blast
    then show ?thesis unfolding GraphWorkingSet_rel_def finiteProperSubgraph_def
      using g'.Finite_Graph_axioms by simp
  qed
qed

locale Finite_Bounded_Graph = Finite_Graph + Distance_Bounded_Graph
begin
theorem rightPassRefine_total_correct:
  assumes S_NO_IN: "incoming s = {}"
    and Q_START: "s \<notin> Q" "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}" "finite Q"
  shows "rightPassRefine_total c Q \<le> RETURN (rightPassAbstract c s)"
  unfolding rightPassRefine_total_def
proof (intro WHILET_rule[where I="rightPass_total_invar c s"] refine_vcg, clarsimp_all)
  show "wf GraphWorkingSet_rel" by (rule wf_GraphWorkingSet_rel)
next
  show "rightPass_total_invar c s (c, Q)" unfolding rightPass_partial_invar_def rightPass_total_invar_def
    using Q_START by blast
next
  fix c' Q u
  assume step_assms: "rightPass_total_invar c s (c', Q)" "u \<in> Q"
  then have SUB: "isSubgraph c' c"
    and "s \<notin> Q"
    and S_CON: "\<forall>u v. connected s u \<longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> Graph.V c' - Q - {s}. Graph.incoming c' u \<noteq> {}"
    and "finite Q"
    unfolding rightPass_total_invar_def rightPass_partial_invar_def by simp_all
  with \<open>u \<in> Q\<close> show "Graph.incoming c' u \<noteq> {} \<Longrightarrow> rightPass_total_invar c s (c', Q - {u}) \<and> ((c', Q - {u}), (c', Q)) \<in> GraphWorkingSet_rel"
    by (auto simp: rightPass_total_invar_def rightPass_partial_invar_def GraphWorkingSet_rel_def)

  let ?c'' = "removeEdges c' (Graph.outgoing c' u)"
  let ?Q' = "Q - {u} \<union> snd ` Graph.outgoing c' u"
  from S_NO_IN step_assms show "Graph.incoming c' u = {} \<Longrightarrow> rightPass_total_invar c s (?c'', ?Q') \<and> ((?c'', ?Q'), (c', Q)) \<in> GraphWorkingSet_rel"
    using rightPassRefine_total_step by blast
next
  fix c'
  assume "rightPass_total_invar c s (c', {})"
  then show "rightPassAbstract c s = c'" unfolding rightPass_total_invar_def rightPass_partial_invar_def
    using rightPassRefine_final by simp
qed

end


\<comment> \<open>RightPass\<close>

end
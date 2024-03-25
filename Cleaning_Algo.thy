theory Cleaning_Algo
  imports LayerMaintenance Graph_Transpose Refine_Imperative_HOL.Sepref_Foreach
begin

subsection \<open>PathFinding\<close>

context Graph
begin
definition pathFindingRefine_partial :: "node \<Rightarrow> path nres" where
  "pathFindingRefine_partial s \<equiv> do {
    (p, _) \<leftarrow> WHILE (\<lambda>(p, u). outgoing u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> RES (outgoing u);
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
  apply (refine_vcg WHILE_rule[where I="pathFinding_invar s"])
  unfolding pathFinding_invar_def outgoing_def by (auto simp: isPath_append_edge)
end \<comment> \<open>Graph\<close>

subsubsection \<open>Total correctness\<close>

definition (in Graph) pathFindingRefine_total :: "node \<Rightarrow> path nres" where
  "pathFindingRefine_total s \<equiv> do {
    (p, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(p, u). outgoing u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> RES (outgoing u);
      let p = p @ [e];
      let u = snd e;
      RETURN (p, u)
    }) ([], s);
    RETURN p
  }"

context Distance_Bounded_Graph
begin
(* TODO redo with bounded measure *)
term "measure (\<lambda>p. b - length p)"
thm wf_bounded_measure

(*definition bounded_path_measure :: "path rel" where "bounded_path_measure \<equiv> measure (\<lambda>p. b - length p)"
definition bounded_path_measure' where "bounded_path_measure \<equiv> measure (\<lambda>p. b - length p)"
term bounded_path_measure
term "pathFindingRefine_total s"
term "SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
term b
thm WHILET_rule*)

lemma pathFinding_total_correct:
  "pathFindingRefine_total s \<le> SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
  unfolding pathFindingRefine_total_def
  apply (refine_vcg WHILET_rule[where
          R="inv_image (measure (\<lambda>p. b - length p)) fst"
          and I="pathFinding_invar s"])
unfolding pathFinding_invar_def outgoing_def apply (auto intro: isPath_append_edge)
  by (metis Distance_Bounded_Graph_def Graph.dist_suc Graph.isPath_distD diff_less_mono2 lessI less_eq_Suc_le local.Distance_Bounded_Graph_axioms)
(* TODO fix this *)

(*  apply (refine_vcg WHILET_rule[where I="pathFinding_invar s" and R="inv_image bounded_path_measure fst"])
      apply (auto simp:pathFinding_invar_def bounded_path_measure_def dest!: in_outgoingD)[]
     apply (auto simp:pathFinding_invar_def bounded_path_measure_def dest!: in_outgoingD)[]
    defer
  defer
apply (auto simp:pathFinding_invar_def bounded_path_measure_def dest!: in_outgoingD)[]*)
(*
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
*)

end \<comment> \<open>Distance_Bounded_Graph\<close>

(* TODO maybe redo this using recursion *)
thm REC_def

(* TODO is it possible to skip the check whether outgoing u = {} and instead rely on the FAIL we'd get from RES (outgoing u)? *)
definition (in Graph) greedy_st_path_finding :: "node \<Rightarrow> node \<Rightarrow> (path option) nres" where
  "greedy_st_path_finding s t \<equiv> do {
    if s = t
      then RETURN (Some [])
      else do {
        (p, _, found, _) \<leftarrow> WHILE\<^sub>T
          (\<lambda>(_, _, _, brk). \<not> brk)
          (\<lambda>(p, u, _, _). do {
            if (outgoing u = {})
              then RETURN (p, u, False, True)
            else do {
              e \<leftarrow> RES (outgoing u);
              let p = p @ [e];
              let u = snd e;
              let found = (u = t);
              RETURN (p, u, found, found)}})
          ([], s, False, s \<notin> V);
        RETURN (if found then Some p else None)}}"


context ST_Layer_Graph
begin
(* TODO prettify *)
lemma greedy_st_path_finding_correct: "greedy_st_path_finding s t \<le> SELECT (\<lambda>p. isPath s p t)"
  unfolding greedy_st_path_finding_def SELECT_as_SPEC
  apply (refine_vcg WHILET_rule[where R="inv_image (greater_bounded (min_dist s t)) (length \<circ> fst)"
          and I="\<lambda>(p, u, found, brk). isPath s p u \<and> found = (u = t) \<and> (brk = (outgoing u = {}))"])
               apply clarsimp_all
  using isEmpty_def no_outgoingD outgoing_edges s_in_V_if_nonempty apply blast
     apply (fastforce intro: isPath_append_edge)
    apply (metis Graph.connected_append_edge Graph.connected_refl Graph.distinct_nodes_in_V_if_connected(2) Graph.in_outgoingD no_outgoingD obtain_back_terminal_connected)
  using b_length_paths_are_terminal(2) le_antisym path_length_bounded apply fastforce
  by (metis Graph.connected_def Graph.distinct_nodes_in_V_if_connected(2) Graph.empty_connected no_outgoingD s_in_V_if_nonempty)
end


(*context ST_Graph
begin
lemma back_terminal_s_path_is_st_path:
  "stl.outgoing u = {} \<Longrightarrow> stl.connected s t\<Longrightarrow> stl.isPath s p u \<Longrightarrow> stl.isPath s p t"
proof (drule stl.no_outgoingD, elim disjE)
  assume PATH: "stl.isPath s p u" and CON: "stl.connected s t" and "u \<notin> stl.V"
  then have "s \<notin> stl.V" "p = []"
    using stl.acyclic stl.isCycle_def
    by (metis stl.connected_def stl.distinct_nodes_in_V_if_connected(2))+
  with PATH CON show "stl.isPath s p t"
    using Graph.distinct_nodes_in_V_if_connected(1) Graph.isPath.simps(1) by blast
qed (auto intro: stl_sub_c.sg_paths_are_base_paths) (* TODO cleanup *)

thm order_trans
thm nrec.leq_trans

lemma pathFinding_partial_finds_st_path:
  assumes "connected s t"
  shows "stl.pathFindingRefine_partial s \<le> SPEC (\<lambda>p. isPath s p t)"
  apply (rule order_trans[OF stl.pathFinding_finds_maximal_path], rule SPEC_rule)
  using stl_maintains_st_connected[OF \<open>connected s t\<close>] back_terminal_s_path_is_st_path stl_sub_c.sg_paths_are_base_paths by blast
(* TODO cleanup *)
end \<comment> \<open>ST_Graph\<close>

locale TMPLoc = ST_Graph + Distance_Bounded_Graph
begin
lemma pathFinding_total_finds_st_path:
  assumes "connected s t"
  shows "stl.pathFindingRefine_total s \<le> SPEC (\<lambda>p. isPath s p t)"
proof -
  note stl.pathFinding_total_correct
  also have "SPEC (\<lambda>p. \<exists>u. stl.outgoing u = {} \<and> stl.isPath s p u) \<le> SPEC (\<lambda>p. isPath s p t)"
    apply (rule SPEC_rule)
    using stl_maintains_st_connected[OF \<open>connected s t\<close>] back_terminal_s_path_is_st_path stl_sub_c.sg_paths_are_base_paths by blast
  finally show ?thesis .
qed
end*)

context ST_Layer_Graph
begin
lemma pathFinding_partial_finds_st_path:
  "s \<in> V \<Longrightarrow> pathFindingRefine_partial s \<le> SPEC (\<lambda>p. isPath s p t)"
  apply (intro order_trans[OF pathFinding_finds_maximal_path] SPEC_rule)
  using back_terminal_path_is_t_path by blast

lemma pathFinding_total_finds_st_path:
  "s \<in> V \<Longrightarrow> pathFindingRefine_total s \<le> SPEC (\<lambda>p. isPath s p t)"
  apply (intro order_trans[OF pathFinding_total_correct] SPEC_rule)
  using back_terminal_path_is_t_path by blast
end

\<comment> \<open>PathFinding\<close>

definition removeEdge :: "_ graph \<Rightarrow> edge \<Rightarrow> _ graph" where
  "removeEdge c e \<equiv> c(e := 0)"

definition removeEdges :: "_ graph \<Rightarrow> edge set \<Rightarrow> _ graph" where
  "removeEdges c R \<equiv> \<lambda>e. if e \<in> R then 0 else c e"

context Graph
begin
lemma removeEdges_E: "Graph.E (removeEdges c S) = E - S"
  unfolding removeEdges_def Graph.E_def by auto

lemma removeEdges_sg: "Subgraph (removeEdges c S) c"
  unfolding removeEdges_def by fastforce

lemma removeEdges_psg: "\<exists>e. e \<in> S \<inter> E \<Longrightarrow> Proper_Subgraph (removeEdges c S) c"
  using removeEdges_sg
  by (metis Diff_iff IntD1 IntD2 removeEdges_E subgraph.dual_order.not_eq_order_implies_strict)
end

(* TODO refine removeEdges and use the refined version *)


subsection \<open>RightPass\<close>
(* This is the exact definition, using the edge set*)
definition rightPassRefine_original :: "_ graph \<Rightarrow> edge set \<Rightarrow> (_ graph) nres" where
  "rightPassRefine_original c Q \<equiv> do {
    (c, _) \<leftarrow> WHILE (\<lambda>(_, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      e \<leftarrow> RES Q;
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
(* TODO swap tuple *)
definition rightPassRefine_partial :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "rightPassRefine_partial Q c \<equiv> do {
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
  where "rightPass_partial_invar c s \<equiv> \<lambda>(c', Q). Subgraph c' c
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
  from INVAR have SUB: "Subgraph c' c"
    and "s \<notin> Q"
    and S_CON: "\<And>u v. connected s u \<Longrightarrow> g'.connected s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> g'.V - Q - {s}. g'.incoming  u \<noteq> {}"
    unfolding rightPass_partial_invar_def by simp_all

  show "Subgraph c'' c" unfolding c''_def
    using g'.removeEdges_sg SUB subgraph.order_trans by blast

  show "s \<notin> Q'"
  proof -
    from S_NO_IN SUB have "g'.incoming s = {}" unfolding Graph.incoming_def
      using Subgraph.E'_ss by fast
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
    with PATH' have "g'.outgoing u \<inter> set p = {}"
      using g'.outgoing_edges_not_on_path g'.pathVertices_fwd by simp
    with PATH' have "g''.isPath s p v" unfolding Graph.isPath_alt c''_def using g'.removeEdges_E by blast
    then show "g''.connected s v" using g''.connected_def by blast

    from \<open>u \<noteq> s\<close> CON' U_NO_IN have "u \<noteq> v" using g'.distinct_nodes_have_in_out_if_connected(2) by blast
    then have "c'' (v, w) = c' (v, w)"
      unfolding g'.outgoing_def removeEdges_def c''_def by simp
    then show "c'' (v, w) = c (v, w)" using C'_EQ_C by simp
  qed

  show "(\<forall>v \<in> g''.V - Q' - {s}. g''.incoming v \<noteq> {})" unfolding Q'_def
  proof clarsimp
    fix v
    assume "v \<in> g''.V" "v \<noteq> s" "v \<notin> snd ` g'.outgoing u" "v \<in> Q \<longrightarrow> v = u" "g''.incoming v = {}"
    from \<open>v \<in> g''.V\<close> have "v \<in> g'.V" unfolding c''_def
      using g'.removeEdges_sg Subgraph.V_ss by fast
    have "v \<notin> Q"
    proof
      assume "v \<in> Q"
      with \<open>v \<in> Q \<longrightarrow> v = u\<close> have "v = u" by blast
      moreover from U_NO_IN have "g''.incoming u = {}" unfolding c''_def Graph.incoming_def
        using g'.removeEdges_E by auto
      moreover note \<open>v \<in> g''.V\<close>
      ultimately obtain w where "(u, w) \<in> g''.E"
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

thm subgraph.order_antisym
lemma rightPassRefine_final:
  assumes SUB: "Subgraph c' c"
    and S_CON: "\<And>u v. connected s u \<Longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> Graph.V c' - {s}. Graph.incoming c' u \<noteq> {}"
  shows "right_pass s c = c'"
proof (intro subgraph.order_antisym Subgraph_edgeI)
  fix u v
  assume "right_pass s c (u, v) \<noteq> 0"
  with S_CON show "c' (u, v) = right_pass s c (u, v)"
    using right_pass_nz_iff S_Graph.rp_is_c_if_s_connected by metis
next
  interpret g': Distance_Bounded_Graph c' b
    using SUB Subgraph.sg_Distance_Bounded Distance_Bounded_Graph_axioms by blast
  fix u v
  assume "c' (u, v) \<noteq> 0"
  then have "u \<in> g'.V" unfolding Graph.V_def Graph.E_def by blast
  obtain w where W_CON: "g'.connected w u" and W_NO_IN: "g'.incoming w = {}" using g'.obtain_front_terminal_connected by blast
  from W_CON \<open>u \<in> g'.V\<close> have "w \<in> g'.V" by (meson g'.connected_inV_iff)
  with W_NO_IN NODE_HAS_IN have "w = s" by blast
  with W_CON have "right_pass s c (u, v) = c (u, v)"
    using SUB Subgraph.sg_connected_remains_base_connected S_Graph.rp_is_c_if_s_connected by fastforce
  also from SUB \<open>c' (u, v) \<noteq> 0\<close> have "... = c' (u, v)" by (metis Subgraph.c'_sg_c_old)
  finally show "right_pass s c (u, v) = c' (u, v)" by simp
qed (* TODO cleanup *)

theorem rightPassRefine_partial_correct:
  assumes S_NO_IN: "incoming s = {}"
    and Q_START: "s \<notin> Q" "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}"
  shows "rightPassRefine_partial Q c \<le> RETURN (right_pass s c)"
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
  then show "right_pass s c = c'" unfolding rightPass_partial_invar_def using rightPassRefine_final by simp
qed
end

subsubsection \<open>Total correctness\<close>

definition right_pass_refine :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "right_pass_refine Q c \<equiv> do {
    (c, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(_, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      u \<leftarrow> RES Q;
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
    using Proper_Subgraph.E'_pss Finite_Graph.finite_E by blast
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


lemma (in Finite_Graph) right_pass_refine_step:
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
    using Subgraph.V_ss finite_V finite_subset by fast

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

context Finite_Bounded_Graph
begin
theorem right_pass_refine_correct:
  assumes S_NO_IN: "incoming s = {}"
    and Q_START: "s \<notin> Q" "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}" "finite Q"
  shows "right_pass_refine Q c \<le> RETURN (right_pass s c)"
  unfolding right_pass_refine_def
proof (intro WHILET_rule[where I="rightPass_total_invar c s"] refine_vcg, clarsimp_all)
  show "wf GraphWorkingSet_rel" by (rule wf_GraphWorkingSet_rel)
next
  show "rightPass_total_invar c s (c, Q)" unfolding rightPass_partial_invar_def rightPass_total_invar_def
    using Q_START apply clarify (* TODO *) by blast
next
  fix c' Q u
  assume step_assms: "rightPass_total_invar c s (c', Q)" "u \<in> Q"
  then show "Graph.incoming c' u \<noteq> {} \<Longrightarrow> rightPass_total_invar c s (c', Q - {u}) \<and> ((c', Q - {u}), (c', Q)) \<in> GraphWorkingSet_rel"
    by (auto simp: rightPass_total_invar_def rightPass_partial_invar_def GraphWorkingSet_rel_def)

  let ?c'' = "removeEdges c' (Graph.outgoing c' u)"
  let ?Q' = "Q - {u} \<union> snd ` Graph.outgoing c' u"
  from S_NO_IN step_assms show "Graph.incoming c' u = {} \<Longrightarrow> rightPass_total_invar c s (?c'', ?Q') \<and> ((?c'', ?Q'), (c', Q)) \<in> GraphWorkingSet_rel"
    using right_pass_refine_step by blast
next
  fix c'
  assume "rightPass_total_invar c s (c', {})"
  then show "right_pass s c = c'" unfolding rightPass_total_invar_def rightPass_partial_invar_def
    using rightPassRefine_final by simp
qed

end

\<comment> \<open>RightPass\<close>

subsection \<open>LeftPass\<close>
(* TODO swap tuple *)
definition left_pass_refine :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "left_pass_refine Q c \<equiv> do {
    (c, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(_, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      u \<leftarrow> RES Q;
      let Q = Q - {u};
      if Graph.outgoing c u = {} then do {
        let L = Graph.incoming c u;
        let Q = Q \<union> (fst ` L);
        let c = removeEdges c L;
        RETURN (c, Q)}
      else RETURN (c, Q)
    }) (c, Q);
    RETURN c
  }"

context Finite_Bounded_Graph
begin
interpretation Dual_Graph_Algorithms "left_pass_refine Q" "right_pass_refine Q"
proof
  fix c :: "('capacity::linordered_idom) graph"
  note[refine_dref_RELATES] = RELATESI[of transpose_graph_rel]
  show "left_pass_refine Q c \<le> \<Down> transpose_graph_rel (right_pass_refine Q (transpose_graph c))"
    unfolding right_pass_refine_def left_pass_refine_def
    apply refine_rcg
    apply refine_dref_type
    by (auto simp: transpose_graph_rel_def removeEdges_def)

  show "right_pass_refine Q c \<le> \<Down> transpose_graph_rel (left_pass_refine Q (transpose_graph c))"
    unfolding right_pass_refine_def left_pass_refine_def
    apply refine_rcg
    apply refine_dref_type
    by (auto simp: transpose_graph_rel_def removeEdges_def)
qed

(* TODO cleanup proof *)
theorem left_pass_refine_correct:
  assumes T_NO_OUT: "outgoing t = {}"
    and Q_START: "t \<notin> Q" "\<forall>u \<in> V - Q - {t}. outgoing u \<noteq> {}" "finite Q"
  shows "left_pass_refine Q c \<le> RETURN (left_pass t c)"
  apply (intro transfer_return[where ret'="right_pass t"])
   apply (fastforce simp: right_pass_def left_pass_def)
  apply (intro Finite_Bounded_Graph.right_pass_refine_correct)
  using assms Finite_Bounded_Graph_axioms by (auto simp: converse_empty_simp)
  (*by (metis converse_converse converse_empty)*)
end

lemmas nfoldli_to_fold =
  foldli_eq_nfoldli[where c="\<lambda>_. True", symmetric, unfolded foldli_foldl foldl_conv_fold]

context Graph
begin

(* TODO impl *)
text \<open>See EdmondsKarp_Impl.augment_edge\<close>
definition subtract_edge :: "edge \<Rightarrow> 'capacity \<Rightarrow> _ graph" where
  "subtract_edge e cap \<equiv> c(e := c e - cap)"

text \<open>This is essentially the same as EdmondsKarp_Impl.resCap_cf_impl, except it works on any graph,
      not just the residual graph.\<close>
definition path_cap_algo :: "path \<Rightarrow> 'capacity nres" where
  "path_cap_algo p \<equiv> case p of
    [] \<Rightarrow> RETURN 0
  | (e # p) \<Rightarrow> nfoldli p (\<lambda>_. True) (\<lambda>e cap. RETURN (min (c e) cap)) (c e)"

definition subtract_path_algo :: "path \<Rightarrow> _ graph nres" where
  "subtract_path_algo p \<equiv> do {
    cap \<leftarrow> path_cap_algo p;
    c' \<leftarrow> nfoldli p (\<lambda>_. True) (\<lambda>e c'. RETURN (Graph.subtract_edge c' e cap)) c;
    RETURN c'
  }"


lemma path_cap_algo_correct: "path_cap_algo p = RETURN (if p = [] then 0 else pathCap p)"
  unfolding path_cap_algo_def pathCap_alt
  apply (simp split: list.split add: nfoldli_to_fold)
  by (metis (no_types, lifting) Min.set_eq_fold fold_map fun_comp_eq_conv list.set_map list.simps(15))

lemma subtract_path_algo_correct_aux:
  "distinct p \<Longrightarrow> fold (\<lambda>e c'. Graph.subtract_edge c' e cap) p c = (\<lambda>(u, v). if (u, v) \<in> set p then c (u, v) - cap else c (u, v))"
  unfolding Graph.subtract_edge_def by (induction p arbitrary: c) auto

lemma subtract_path_algo_correct:
  assumes "distinct p"
  shows "subtract_path_algo p \<le> RETURN (subtract_path p)"
  unfolding subtract_path_algo_def subtract_path_def
  apply (simp split: list.splits add: nfoldli_to_fold path_cap_algo_correct)
  using assms subtract_path_algo_correct_aux by simp

end

find_theorems Graph.pathVertices
find_theorems Graph.pathVertices_fwd

(* TODO invert *)
definition inner_path_vertices_algo :: "path \<Rightarrow> node list nres" where
  "inner_path_vertices_algo p \<equiv> case p of
    [] \<Rightarrow> RETURN []
  | (_ # p) \<Rightarrow> nfoldli p (\<lambda>_. True) (\<lambda>e us. RETURN (us @ [fst e])) []"

term butlast
term tl
find_theorems butlast tl
thm nfoldli_to_fold
context Graph
begin

find_theorems pathVertices "(@)"
find_theorems pathVertices_fwd "(@)"
thm pathVertices.induct
find_theorems name:induct "(@)"

thm rev_induct
thm pathVertices_alt
thm pathVertices.elims
thm pathVertices.simps

lemma inner_path_vertices_algo_correct:
  "inner_path_vertices_algo p = RETURN (tl (butlast (pathVertices u p)))"
proof (cases p)
  case Nil
  then show ?thesis unfolding inner_path_vertices_algo_def by auto
next
  case (Cons _ p')
  then show ?thesis
  proof (induction p' arbitrary: p rule: rev_induct)
    case Nil
    then show ?case unfolding inner_path_vertices_algo_def by auto
  next
    case (snoc x xs)
    then show ?case
      unfolding inner_path_vertices_algo_def
      apply (auto simp: nfoldli_to_fold elim: pathVertices.elims)
      by (smt (z3) Graph.pathVertices.simps(1) list.simps(8) list.simps(9) list_e_eq_lel(2) map_append pathVertices_alt snoc_eq_iff_butlast)
  qed
qed
end





definition cleaning_algo :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "cleaning_algo Q c \<equiv> do {
    c \<leftarrow> right_pass_refine Q c;
    c \<leftarrow> left_pass_refine Q c;
    RETURN c}"

context Finite_Bounded_Graph
begin
thm right_pass_refine_correct
thm left_pass_refine_correct
find_theorems "Distance_Bounded_Graph c"

lemma cleaning_algo_correct:
  assumes S_PROPS: "incoming s = {}" "outgoing s \<noteq> {}"
    and T_PROPS: "outgoing t = {}" "incoming t \<noteq> {}"
    and Q_START: "s \<notin> Q" "t \<notin> Q" "\<forall>u \<in> V - Q - {s, t}. incoming u \<noteq> {} \<and> outgoing u \<noteq> {}" "finite Q"
  shows "cleaning_algo Q c \<le> RETURN (cleaning s t c)"
  unfolding cleaning_algo_def
proof (refine_vcg, simp)
  have "right_pass_refine Q c \<le> RETURN (right_pass s c)"
    using assms by (blast intro: right_pass_refine_correct)
  also have "... \<le> SPEC (\<lambda>ca. left_pass_refine Q ca \<le> RES {cleaning s t c})"
  proof simp
    interpret Subgraph "right_pass s c" c using right_pass_Subgraph .
    have "left_pass_refine Q (right_pass s c) \<le> RETURN (left_pass t (right_pass s c))" (* TODO prettify *)
      apply (intro Finite_Bounded_Graph.left_pass_refine_correct)
          prefer 3 using assms apply simp
         prefer 4 using assms apply simp
        prefer 2 subgoal
        using \<open>outgoing t = {}\<close>
        unfolding Graph.outgoing_def Graph.E_def right_pass_def by simp
      unfolding Finite_Bounded_Graph_def apply auto[1]
      using edges_ss g'.Finite_Graph_EI rev_finite_subset apply blast
      using Distance_Bounded_Graph_axioms apply (rule sg_Distance_Bounded)
      sorry






    also have "... \<le> RES {cleaning s t c}"
      by (simp add: ST_Graph.left_right_pass_is_cleaning)
    finally show "left_pass_refine Q (right_pass s c) \<le> RES {cleaning s t c}" .
  qed
  finally show "right_pass_refine Q c \<le> SPEC (\<lambda>ca. left_pass_refine Q ca \<le> RES {cleaning s t c})" .
qed
end
end
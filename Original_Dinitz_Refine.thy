theory Original_Dinitz_Refine
  imports Original_Dinitz_Algo
begin
text \<open>This theory takes the abstract definition of the Original Dinitz algorithm and refines
      it towards a concrete version. The goal here is not yet to arrive at an executable version,
      but to refine it as much as possible without choosing a particular datatype representation
      or execution framework. The functions will thus still include simple, but not necessarily
      executable, primitives such as set operations.\<close>

subsection \<open>Primitives\<close>
subsubsection \<open>Edge Deletion\<close>
definition deleteEdge :: "_ graph \<Rightarrow> edge \<Rightarrow> _ graph" where
  "deleteEdge c e \<equiv> c(e := 0)"

(* TODO executable version *)
definition deleteEdges :: "_ graph \<Rightarrow> edge set \<Rightarrow> _ graph" where
  "deleteEdges c R \<equiv> \<lambda>e. if e \<in> R then 0 else c e"

context Graph
begin
lemma deleteEdges_E: "Graph.E (deleteEdges c S) = E - S"
  unfolding deleteEdges_def Graph.E_def by auto

lemma deleteEdges_sg: "Subgraph (deleteEdges c S) c"
  unfolding deleteEdges_def by fastforce

lemma removeEdges_psg: "\<exists>e. e \<in> S \<inter> E \<Longrightarrow> Proper_Subgraph (deleteEdges c S) c"
  using deleteEdges_sg
  by (metis Diff_iff IntD1 IntD2 deleteEdges_E subgraph.dual_order.not_eq_order_implies_strict)
end
\<comment> \<open>Edge Removal\<close>
\<comment> \<open>Primitives\<close>

subsection \<open>Pathfinding\<close>

text \<open>Used primitives:
  - RES (outgoing u) / checking outgoing u for emptiness
  - checking whether s is a vertex
  - list append\<close>
(* TODO version using Cons rather than append *)
(* TODO maybe redo this using recursion *)
thm REC_def
definition (in Graph) greedyPathFinding :: "node \<Rightarrow> node \<Rightarrow> (path option) nres" where
  "greedyPathFinding s t \<equiv> do {
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

(* TODO prettify *)
lemma (in Dual_Layer_Graph) greedyPathFinding_correct:
  "greedyPathFinding s t \<le> SELECT (\<lambda>p. isPath s p t)"
  unfolding greedyPathFinding_def SELECT_as_SPEC
  apply (refine_vcg WHILET_rule[where R="inv_image (greater_bounded (min_dist s t)) (length \<circ> fst)"
          and I="\<lambda>(p, u, found, brk). isPath s p u \<and> found = (u = t) \<and> (brk = (outgoing u = {}))"])
               apply clarsimp_all
  using isEmpty_def no_outgoingD outgoing_edges s_in_V_if_nonempty apply blast
     apply (fastforce intro: isPath_append_edge)
    apply (metis Graph.connected_append_edge Graph.connected_refl Graph.distinct_nodes_in_V_if_connected(2) Graph.in_outgoingD no_outgoingD obtain_back_terminal_connected)
  using b_length_paths_are_terminal(2) le_antisym path_length_bounded apply fastforce
  by (metis Graph.connected_def Graph.distinct_nodes_in_V_if_connected(2) Graph.empty_connected no_outgoingD s_in_V_if_nonempty)

\<comment> \<open>Pathfinding\<close>

subsection \<open>Cleaning\<close>
subsubsection \<open>Right Pass\<close>

text \<open>This definition is slightly adapted in that it works on the set of edge tails,
      instead of on the edges themselves.\<close>
text \<open>Used primitives:
  - working set operation: adding elements, removing element, checking for emptiness
  - graph operations: checking incoming for emptiness, getting set of outgoing edges
  - delete_edges\<close>
definition rightPassRefine :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "rightPassRefine Q c \<equiv> do {
    (_, c) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(Q, _). Q \<noteq> {})
      (\<lambda>(Q, c). do {
        u \<leftarrow> RES Q;
        let Q = Q - {u};
        if Graph.incoming c u = {}
          then do {
            let R = Graph.outgoing c u;
            let Q = Q \<union> (snd ` R);
            let c = deleteEdges c R;
            RETURN (Q, c)}
          else RETURN (Q, c)})
      (Q, c);
    RETURN c
  }"

definition rightPassInvar :: "_ graph \<Rightarrow> node \<Rightarrow> (node set \<times>_ graph) \<Rightarrow> bool"
  where "rightPassInvar c s \<equiv> \<lambda>(Q, c'). Subgraph c' c
                                \<and> s \<notin> Q
                                \<and> (\<forall>u v. Graph.connected c s u \<longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v))
                                \<and> (\<forall>u \<in> Graph.V c' - Q - {s}. Graph.incoming c' u \<noteq> {})
                                \<and> finite Q"


definition finiteProperSubgraph :: "_ graph rel"
  where "finiteProperSubgraph \<equiv> {(c', c). Proper_Subgraph c' c \<and> Finite_Graph c}"

lemma wf_finiteProperSubgraph: "wf finiteProperSubgraph"
proof (rule wf_subset)
  show "wf (inv_image finite_psubset Graph.E)" by simp
  show "finiteProperSubgraph \<subseteq> inv_image finite_psubset Graph.E"
    unfolding finiteProperSubgraph_def inv_image_def finite_psubset_def
    using Proper_Subgraph.E'_pss Finite_Graph.finite_E by blast
qed

definition graphWorkingSetRel :: "(_ set \<times> _ graph) rel"
  where "graphWorkingSetRel \<equiv> inv_image (finiteProperSubgraph <*lex*> finite_psubset) prod.swap"

lemma wf_graphWorkingSetRel: "wf graphWorkingSetRel" unfolding graphWorkingSetRel_def
  using wf_finiteProperSubgraph by auto

lemma (in Finite_Graph) rightPassRefine_step:
  assumes S_NO_IN: "incoming s = {}"
    and "u \<in> Q"
    and U_NO_IN: "Graph.incoming c' u = {}"
    and INVAR: "rightPassInvar c s (Q, c')"
  defines "c'' \<equiv> deleteEdges c' (Graph.outgoing c' u)"
    and "Q' \<equiv> Q - {u} \<union> snd ` Graph.outgoing c' u"
  shows "rightPassInvar c s (Q', c'') \<and> ((Q', c''), (Q, c')) \<in> graphWorkingSetRel"
  unfolding rightPassInvar_def
proof (clarify, intro conjI)
  from INVAR have "Subgraph c' c"
    and "s \<notin> Q"
    and S_CON: "\<And>u v. connected s u \<Longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> Graph.V c' - Q - {s}. Graph.incoming c' u \<noteq> {}"
    unfolding rightPassInvar_def by auto
  then interpret Subgraph c' c by simp





  interpret g': Graph c' .
  interpret g'': Graph c'' .

  term g'.connected
  term "Graph.connected c'"
  term c'
  term c
  term c''
  from INVAR have SUB: "Subgraph c' c" unfolding rightPassInvar_def by simp
  from INVAR have SUB: "s \<notin> Q" unfolding rightPassInvar_def by simp
  from INVAR have S_CON: "\<And>u v. connected s u \<Longrightarrow> g'.connected s u \<and> c' (u, v) = c (u, v)"


  from INVAR have SUB: "Subgraph c' c"
    and "s \<notin> Q"
    and S_CON: "\<And>u v. connected s u \<Longrightarrow> g'.connected s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> g'.V - Q - {s}. g'.incoming  u \<noteq> {}"
    unfolding rightPass_partial_invar_def by simp_all


  oops


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
interpretation subgraph: wellorder isSubgraph isProperSubgraph oops
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

end
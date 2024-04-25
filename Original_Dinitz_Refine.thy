theory Original_Dinitz_Refine
  imports Original_Dinitz_Algo Graph_Transpose Refine_Imperative_HOL.Sepref_Foreach
begin
text \<open>This theory takes the abstract definition of the Original Dinitz algorithm and refines
      it towards a concrete version. The goal here is not yet to arrive at an executable version,
      but to refine it as much as possible without choosing a particular datatype representation
      or execution framework. The functions will thus still include simple, but not necessarily
      executable, primitives such as set operations.\<close>

(* TODO *)
interpretation Refine_Monadic_Syntax .

text \<open>For several refinement proofs in this theory, we need an additional pattern for refine_dref_type\<close>
lemma RELATESI_in_spec(*[refine_dref_pattern]*):
  "RELATES R \<Longrightarrow> S \<le> (spec x. (x, y) \<in> R) \<Longrightarrow> S \<le> (spec x. (x, y) \<in> R)" .

lemmas nfoldli_to_fold =
  foldli_eq_nfoldli[where c="\<lambda>_. True", symmetric, unfolded foldli_foldl foldl_conv_fold]

(* TODO remove notation *)
term Ref.update
(*no_notation Ref.update ("_ := _")*)

subsection \<open>Primitives\<close>
definition deleteEdge :: "edge \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "deleteEdge e c \<equiv> c(e := 0)"

text \<open>See EdmondsKarp_Impl.augment_edge\<close>
definition subtractEdge :: "edge \<Rightarrow> ('capacity::linordered_idom) \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "subtractEdge e cap c \<equiv> c(e := c e - cap)"

definition (in Graph) transferEdge :: "edge \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "transferEdge e c' \<equiv> c'(e := c e)"
\<comment> \<open>Primitives\<close>

subsection \<open>Deleting a set of edges\<close>
definition deleteEdges :: "edge set \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "deleteEdges R c \<equiv> \<lambda>e. if e \<in> R then 0 else c e"

definition deleteEdgesRefine :: "edge set \<Rightarrow> _ graph \<Rightarrow> _ graph nres" where
  "deleteEdgesRefine R c \<equiv> FOREACH R (RETURN \<circ>\<circ> deleteEdge) c"

lemma deleteEdgesRefine_correct: "finite R \<Longrightarrow> deleteEdgesRefine R c \<le> RETURN (deleteEdges R c)"
  unfolding deleteEdgesRefine_def
  apply (refine_vcg FOREACH_rule[where I="\<lambda>R' c'. \<forall>e. e \<notin> R' \<longrightarrow> c' e = deleteEdges R c e"])
  by (auto simp: deleteEdges_def deleteEdge_def)

context Graph
begin
lemma deleteEdges_E: "Graph.E (deleteEdges S c) = E - S"
  unfolding deleteEdges_def Graph.E_def by auto

lemma deleteEdges_sg: "Subgraph (deleteEdges S c) c"
  unfolding deleteEdges_def by fastforce

lemma removeEdges_psg: "\<exists>e. e \<in> S \<inter> E \<Longrightarrow> Proper_Subgraph (deleteEdges S c) c"
  using deleteEdges_sg
  by (metis Diff_iff IntD1 IntD2 deleteEdges_E subgraph.dual_order.not_eq_order_implies_strict)
end
\<comment> \<open>Deleting a set of edges\<close>

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

subsection \<open>Subtracting a path\<close>
text \<open>Here, we refine subtraction of a path from a graph. Note that, with the current primitives
      (especially subtractEdge) being mere definitions, we technically do not yet need to use the
      monadic framework at all. Instead of nfoldli, we could simply use fold or similar predefined
      functions (e.g. arg_min_list), which are already executable. However, if in a later step we
      use a refinement of subtractEdge that requires the monadic framework, we would then have to
      redefine the entire subtractPathRefine definition, instead of just proofing refinement of the
      primitive and transferring correctness. Thus, we use nfoldli here, even though it is not yet
      strictly required.\<close>
context Graph
begin
text \<open>This is essentially the same as EdmondsKarp_Impl.resCap_cf_impl, except it works on any graph,
      not just the residual graph.\<close>
definition pathCapRefine :: "path \<Rightarrow> 'capacity nres" where
  "pathCapRefine p \<equiv> case p of
    [] \<Rightarrow> RETURN 0
  | (e # p) \<Rightarrow> nfoldli p (\<lambda>_. True) (\<lambda>e cap. RETURN (min (c e) cap)) (c e)"

definition subtractPathRefine :: "path \<Rightarrow> _ graph nres" where
  "subtractPathRefine p \<equiv> do {
    cap \<leftarrow> pathCapRefine p;
    c' \<leftarrow> nfoldli p (\<lambda>_. True) (\<lambda>e c'. RETURN (subtractEdge e cap c')) c;
    RETURN c'
  }"

lemma pathCapRefine_correct: "pathCapRefine p = RETURN (if p = [] then 0 else pathCap p)"
  unfolding pathCapRefine_def pathCap_alt
  apply (simp split: list.split add: nfoldli_to_fold)
  by (metis (no_types, lifting) Min.set_eq_fold fold_map fun_comp_eq_conv list.set_map list.simps(15))

lemma subtractPathRefine_correct_aux:
  "distinct p \<Longrightarrow> fold (\<lambda>e c'. subtractEdge e cap c') p c = (\<lambda>(u, v). if (u, v) \<in> set p then c (u, v) - cap else c (u, v))"
  unfolding subtractEdge_def by (induction p arbitrary: c) auto

lemma subtractPathRefine_correct:
  assumes "distinct p"
  shows "subtractPathRefine p \<le> RETURN (subtract_path p)"
  unfolding subtractPathRefine_def subtract_path_def
  apply (simp split: list.splits add: nfoldli_to_fold pathCapRefine_correct)
  using assms subtractPathRefine_correct_aux by simp
end
\<comment> \<open>Subtracting a path\<close>

subsection \<open>Inner vertices of a path\<close>
text \<open>This definition is very similar to the existing setup of pathVertices, but easier to work with,
      as we do not need to declare the first vertex.
      Note that in contrast to the section concerning path subtraction, we stay purely functional
      here and do not use the monadic framework. The reason is that we do not use any primitives
      that may later need to be refined into monadic results, all work we do on lists can be done
      purely functionally.\<close>

fun innerPathVertices :: "path \<Rightarrow> node list" where
  "innerPathVertices p = (case p of
    [] \<Rightarrow> []
  | (_ # p') \<Rightarrow> map fst p')"

lemma innerPathVertices_correct: "innerPathVertices p = tl (butlast (Graph.pathVertices u p))"
  by (auto split: list.split simp: Graph.pathVertices.simps(1) Graph.pathVertices_alt)
\<comment> \<open>Inner vertices of a path\<close>

subsection \<open>Cleaning\<close>
subsubsection \<open>Right Pass\<close>

text \<open>This definition slightly deviates from the one presented in Dinitz's original paper, in that
      it works on the set of edge tails, instead of on the edges themselves. Also note that we refer
      to this intermediate version with an uptick, as we will later use a more concrete version.\<close>

text \<open>Used primitives:
  - working set operation: adding elements, removing element, checking for emptiness
  - graph operations: checking incoming for emptiness, getting set of outgoing edges
  - delete_edges\<close>
definition rightPassRefine' :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "rightPassRefine' Q c \<equiv> do {
    (_, c) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(Q, _). Q \<noteq> {})
      (\<lambda>(Q, c). do {
        u \<leftarrow> RES Q;
        let Q = Q - {u};
        if Graph.incoming c u = {}
          then do {
            let R = Graph.outgoing c u;
            ASSERT (finite R);
            let Q = Q \<union> (snd ` R);
            let c = deleteEdges R c;
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
  defines "c'' \<equiv> deleteEdges (Graph.outgoing c' u) c'"
    and "Q' \<equiv> Q - {u} \<union> snd ` Graph.outgoing c' u"
  shows "rightPassInvar c s (Q', c'') \<and> ((Q', c''), (Q, c')) \<in> graphWorkingSetRel \<and> finite (Graph.outgoing c' u)"
  unfolding rightPassInvar_def
proof (clarify, intro conjI)
  from INVAR have "Subgraph c' c"
    and "s \<notin> Q"
    and S_CON: "\<And>u v. connected s u \<Longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> Graph.V c' - Q - {s}. Graph.incoming c' u \<noteq> {}"
    and "finite Q"
    unfolding rightPassInvar_def by auto
  then interpret Subgraph c' c by simp
  interpret g'': Graph c'' .

  show "Subgraph c'' c" unfolding c''_def
    using Subgraph_axioms g'.deleteEdges_sg subgraph.order.trans by blast

  show "s \<notin> Q'"
  proof -
    from S_NO_IN have "g'.incoming s = {}" unfolding Graph.incoming_def
      using E'_ss by fast
    then have "s \<notin> snd ` g'.outgoing u" unfolding g'.incoming_def g'.outgoing_def by fastforce
    with \<open>s \<notin> Q\<close> show "?thesis" unfolding Q'_def by blast
  qed

  show "\<forall>v w. connected s v \<longrightarrow> g''.connected s v \<and> c'' (v, w) = c (v, w)"
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
    with PATH' have "g''.isPath s p v" unfolding Graph.isPath_alt c''_def using g'.deleteEdges_E by blast
    then show "g''.connected s v" using g''.connected_def by blast

    from \<open>u \<noteq> s\<close> CON' U_NO_IN have "u \<noteq> v" using g'.distinct_nodes_have_in_out_if_connected(2) by blast
    then have "c'' (v, w) = c' (v, w)"
      unfolding g'.outgoing_def deleteEdges_def c''_def by simp
    then show "c'' (v, w) = c (v, w)" using C'_EQ_C by simp
  qed

  show "(\<forall>v \<in> g''.V - Q' - {s}. g''.incoming v \<noteq> {})" unfolding Q'_def
  proof clarsimp
    fix v
    assume "v \<in> g''.V" "v \<noteq> s" "v \<notin> snd ` g'.outgoing u" "v \<in> Q \<longrightarrow> v = u" "g''.incoming v = {}"
    from \<open>v \<in> g''.V\<close> have "v \<in> g'.V" unfolding c''_def
      using g'.deleteEdges_sg Subgraph.V_ss by fast
    have "v \<notin> Q"
    proof
      assume "v \<in> Q"
      with \<open>v \<in> Q \<longrightarrow> v = u\<close> have "v = u" by blast
      moreover from U_NO_IN have "g''.incoming u = {}" unfolding c''_def Graph.incoming_def
        using g'.deleteEdges_E by auto
      moreover note \<open>v \<in> g''.V\<close>
      ultimately obtain w where "(u, w) \<in> g''.E"
        unfolding g''.incoming_def by (auto elim: g''.vertex_cases)
      then show False unfolding c''_def using g'.deleteEdges_E g'.outgoing_alt by fastforce
    qed
    with \<open>v \<in> g'.V\<close> \<open>v \<noteq> s\<close> NODE_HAS_IN obtain u' where "(u', v) \<in> g'.E" unfolding g'.incoming_def by blast
    with \<open>v \<notin> snd ` g'.outgoing u\<close> have "(u', v) \<in> g''.E" unfolding c''_def using g'.deleteEdges_E by blast
    with \<open>g''.incoming v = {}\<close> show False unfolding g''.incoming_def by blast
  qed

  interpret g': Finite_Graph c' unfolding Finite_Graph_def
    using V_ss finite_V finite_subset by blast

  from \<open>finite Q\<close> show "finite Q'" unfolding Q'_def by blast

  show "((Q', c''), Q, c') \<in> graphWorkingSetRel"
  proof (cases "g'.outgoing u = {}")
    case True
    then have "c'' = c'" unfolding c''_def deleteEdges_def by simp
    moreover from True have "Q' = Q - {u}" unfolding Q'_def by simp
    moreover note \<open>u \<in> Q\<close> \<open>finite Q\<close>
    ultimately show ?thesis unfolding graphWorkingSetRel_def by auto
  next
    case False
    then have "Proper_Subgraph c'' c'" unfolding c''_def
      using g'.removeEdges_psg g'.outgoing_edges Proper_Subgraph.intro by blast
    then show ?thesis unfolding graphWorkingSetRel_def finiteProperSubgraph_def
      using g'.Finite_Graph_axioms by simp
  qed

  show "finite (g'.outgoing u)" by blast
qed

lemma (in Distance_Bounded_Graph) rightPassRefine_final:
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

(* TODO remove right_pass, instead use locale *)
theorem (in Finite_Bounded_Graph) rightPassRefine'_correct:
  assumes S_NO_IN: "incoming s = {}"
    and Q_START: "s \<notin> Q" "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}" "finite Q"
  shows "rightPassRefine' Q c \<le> RETURN (right_pass s c)"
  unfolding rightPassRefine'_def
proof (refine_vcg WHILET_rule[where I="rightPassInvar c s" and R=graphWorkingSetRel], clarsimp_all)
  show "wf graphWorkingSetRel" by (rule wf_graphWorkingSetRel)
next
  show "rightPassInvar c s (Q, c)" unfolding rightPassInvar_def using Q_START by fastforce
next
  fix c' Q u
  assume step_assms: "rightPassInvar c s (Q, c')" "u \<in> Q"
  {
    assume "Graph.incoming c' u \<noteq> {}"
    with step_assms show "rightPassInvar c s (Q - {u}, c')" "((Q - {u}, c'), (Q, c')) \<in> graphWorkingSetRel"
      by (auto simp: rightPassInvar_def graphWorkingSetRel_def)
  }

  let ?c'' = "deleteEdges (Graph.outgoing c' u) c'"
  let ?Q' = "Q - {u} \<union> snd ` Graph.outgoing c' u"
  assume "Graph.incoming c' u = {}"
  with S_NO_IN step_assms show "rightPassInvar c s (?Q', ?c'')" "((?Q', ?c''), (Q, c')) \<in> graphWorkingSetRel" "finite (Graph.outgoing c' u)"
    using rightPassRefine_step by auto
next
  fix c'
  assume "rightPassInvar c s ({}, c')"
  then show "right_pass s c = c'" unfolding rightPassInvar_def
    using rightPassRefine_final by simp
qed

text \<open>We introduce a further refinement that replaces the abstract deletion of edges with the
      algorithmic version that only requires the primitive operation of deleting a single edge.\<close>

text \<open>Used primitives:
  - working set operation: adding elements, removing element, checking for emptiness
  - graph operations: checking incoming for emptiness, getting set of outgoing edges, deleting an edge\<close>
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
            c \<leftarrow> deleteEdgesRefine R c;
            RETURN (Q, c)}
          else RETURN (Q, c)})
      (Q, c);
    RETURN c
  }"

lemma (in Finite_Graph) rightPassRefine'_refine:
  notes [refine_dref_pattern] = RELATESI_in_spec
  shows "rightPassRefine Q c \<le> \<Down> Id (rightPassRefine' Q c)"
  unfolding rightPassRefine_def rightPassRefine'_def
  apply refine_rcg
         apply refine_dref_type
  by (auto simp: RES_sng_eq_RETURN intro: deleteEdgesRefine_correct)

theorem (in Finite_Bounded_Graph) rightPassRefine_correct:
  assumes S_NO_IN: "incoming s = {}"
    and Q_START: "s \<notin> Q" "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}" "finite Q"
  shows "rightPassRefine Q c \<le> RETURN (right_pass s c)"
  using rightPassRefine'_correct rightPassRefine'_refine assms
  by (meson conc_trans_additional(5))
\<comment> \<open>Right Pass\<close>

subsubsection \<open>Left Pass\<close>
text \<open>Used primitives:
  - working set operation: adding elements, removing element, checking for emptiness
  - graph operations: checking outgoing for emptiness, getting set of incoming edges, deleting an edge\<close>
definition leftPassRefine :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "leftPassRefine Q c \<equiv> do {
    (_, c) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(Q, _). Q \<noteq> {})
      (\<lambda>(Q, c). do {
        u \<leftarrow> RES Q;
        let Q = Q - {u};
        if Graph.outgoing c u = {}
          then do {
            let L = Graph.incoming c u;
            let Q = Q \<union> (fst ` L);
            c \<leftarrow> deleteEdgesRefine L c;
            RETURN (Q, c)}
          else RETURN (Q, c)})
      (Q, c);
    RETURN c
  }"

context Finite_Bounded_Graph
begin
interpretation Dual_Graph_Algorithms "leftPassRefine Q" "rightPassRefine Q"
proof
  interpret Dual_Graph_Algorithms "deleteEdgesRefine S" "deleteEdgesRefine (S\<inverse>)" for S
  proof
    show "\<And>c. deleteEdgesRefine S c \<le> \<Down> transpose_graph_rel (deleteEdgesRefine (S\<inverse>) (c\<^sup>T))"
      unfolding deleteEdgesRefine_def
      apply (refine_rcg FOREACH_refine_rcg[where \<alpha>="prod.swap"])
      by (fastforce simp: deleteEdge_def)+

    show "\<And>c. deleteEdgesRefine (S\<inverse>) c \<le> \<Down> transpose_graph_rel (deleteEdgesRefine S (c\<^sup>T))"
      unfolding deleteEdgesRefine_def
      apply (refine_rcg FOREACH_refine_rcg[where \<alpha>="prod.swap"])
      by (fastforce simp: deleteEdge_def)+
  qed

  fix c :: "('capacity::linordered_idom) graph"
  note[refine_dref_RELATES] = RELATESI[of transpose_graph_rel]
  show "leftPassRefine Q c \<le> \<Down> transpose_graph_rel (rightPassRefine Q (transpose_graph c))"
    unfolding rightPassRefine_def leftPassRefine_def
    apply refine_rcg
           apply refine_dref_type
    by (fastforce simp: conc_simp)+

  show "rightPassRefine Q c \<le> \<Down> transpose_graph_rel (leftPassRefine Q (transpose_graph c))"
    unfolding rightPassRefine_def leftPassRefine_def
    apply refine_rcg
           apply refine_dref_type
    by (fastforce simp: conc_simp)+
qed

(* TODO cleanup proof *)
theorem leftPassRefine_correct:
  assumes T_NO_OUT: "outgoing t = {}"
    and Q_START: "t \<notin> Q" "\<forall>u \<in> V - Q - {t}. outgoing u \<noteq> {}" "finite Q"
  shows "leftPassRefine Q c \<le> RETURN (left_pass t c)"
  apply (intro transfer_return[where ret'="right_pass t"])
   apply (fastforce simp: right_pass_def left_pass_def)
  apply (intro Finite_Bounded_Graph.rightPassRefine_correct)
  using assms Finite_Bounded_Graph_axioms by (auto simp: converse_empty_simp)
end

\<comment> \<open>Left Pass\<close>

subsubsection \<open>Cleaning Algorithm\<close>

definition cleaningRefine :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "cleaningRefine Q c \<equiv> do {
    c \<leftarrow> rightPassRefine Q c;
    c \<leftarrow> leftPassRefine Q c;
    RETURN c}"

lemma (in Finite_Bounded_Graph) cleaning_algo_correct:
  assumes S_NO_IN: "incoming s = {}"
    and T_NO_OUT: "outgoing t = {}"
    and Q_START: "s \<notin> Q" "t \<notin> Q" "\<forall>u \<in> V - Q - {s, t}. incoming u \<noteq> {} \<and> outgoing u \<noteq> {}" "finite Q"
  shows "cleaningRefine Q c \<le> RETURN (cleaning s t c)"
  unfolding cleaningRefine_def
proof (refine_vcg, simp)
  from T_NO_OUT \<open>\<forall>u \<in> V - Q - {s, t}. incoming u \<noteq> {} \<and> outgoing u \<noteq> {}\<close> have "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}"
    by (cases "incoming t = {}") (auto simp: incoming_def outgoing_def V_def)
  with assms have "rightPassRefine Q c \<le> RETURN (right_pass s c)"
    by (blast intro: rightPassRefine_correct)
  also have "... \<le> SPEC (\<lambda>ca. leftPassRefine Q ca \<le> RES {cleaning s t c})"
  proof simp
    interpret Subgraph "right_pass s c" c using right_pass_Subgraph .
    have "leftPassRefine Q (right_pass s c) \<le> RETURN (left_pass t (right_pass s c))" (* TODO prettify *)
      apply (intro Finite_Bounded_Graph.leftPassRefine_correct)
          prefer 3 using assms apply simp
         prefer 4 using assms apply simp
        prefer 2 subgoal
        using \<open>outgoing t = {}\<close>
        unfolding Graph.outgoing_def Graph.E_def right_pass_def by simp
      unfolding Finite_Bounded_Graph_def apply auto[1]
      using edges_ss g'.Finite_Graph_EI rev_finite_subset apply blast
      using Distance_Bounded_Graph_axioms apply (rule sg_Distance_Bounded)
    proof
      fix u
      assume "u \<in> V' - Q - {t}"
      then have "outgoing u \<noteq> {}" (* TODO prettify *)
      proof (cases "outgoing s = {}")
        case True
        with S_NO_IN have "s \<notin> V" unfolding incoming_def outgoing_def V_def by blast
        then have "s \<notin> V'" using V_ss by blast
        with \<open>u \<in> V' - Q - {t}\<close> have "u \<noteq> s" by blast
        with assms \<open>u \<in> V' - Q - {t}\<close> show ?thesis using V_ss by blast
      next
        case False
        with \<open>u \<in> V' - Q - {t}\<close> show ?thesis using assms V_ss by auto
      qed
      then obtain v where "(u, v) \<in> E" by fast

      from \<open>u \<in> V' - Q - {t}\<close> have "u \<in> V'" by blast
      then have "connected s u" unfolding g'.V_def
        using S_Graph.rp_edges_s_connected connected_append_edge edge'_if_edge by blast
      with \<open>(u, v) \<in> E\<close> have "(u, v) \<in> E'"
        using S_Graph.s_connected_edges_remain by blast
      then show "g'.outgoing u \<noteq> {}" unfolding g'.outgoing_def by blast
    qed
    also have "... \<le> RES {cleaning s t c}"
      by (simp add: ST_Graph.left_right_pass_is_cleaning)
    finally show "leftPassRefine Q (right_pass s c) \<le> RES {cleaning s t c}" .
  qed
  finally show "rightPassRefine Q c \<le> SPEC (\<lambda>ca. leftPassRefine Q ca \<le> RES {cleaning s t c})" .
qed

\<comment> \<open>Cleaning Algorithm\<close>

\<comment> \<open>Cleaning\<close>


subsection \<open>Extended BFS\<close>
text \<open>In this section, we present an extended version of breadth-first search, which builds a graph
      consisting of all shortest paths starting at a source node, instead of only a single shortest
      path to a specified destination.

      While we loosely follow the verified implementation of BFS developed for the implementation
      of Edmonds-Karp, there are multiple significant differences. First, unlike standard BFS, we
      care about the capacity of edges as we build a graph instead of a path. Second, we use two
      working sets, since we need to distinguish between nodes in the graph that were added in the
      current phase (which are still eligible edge endpoints) and older nodes. Third, the setup
      based on a single predecessor for each node does not work here as we do not necessarily have
      a tree.\<close>

subsubsection \<open>Transferring edges to another graph\<close>
context Graph
begin
definition transferEdges :: "edge set \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "transferEdges S c' = (\<lambda>e. if e \<in> S then c e else c' e)"

definition transferEdgesRefine :: "edge set \<Rightarrow> _ graph \<Rightarrow> _ graph nres" where
  "transferEdgesRefine S c' \<equiv> foreach S (\<lambda>e c'. RETURN (transferEdge e c')) c'"

lemma transferEdge_alt: "transferEdge e c' = (\<lambda>e'. if e' = e then c e' else c' e')"
  unfolding transferEdge_def by fastforce

definition transferEdgesRefineInvar :: "edge set \<Rightarrow> _ graph \<Rightarrow> edge set \<Rightarrow> _ graph \<Rightarrow> bool" where
  "transferEdgesRefineInvar S c' it c'' \<equiv> c'' = (\<lambda>e. if e \<in> S - it then c e else c' e)"

lemma transferEdgesRefine_correct:
  "finite S \<Longrightarrow> transferEdgesRefine S c' \<le> RETURN (transferEdges S c')"
  unfolding transferEdgesRefine_def transferEdges_def
  apply (refine_vcg FOREACH_rule[where I="transferEdgesRefineInvar S c'"])
  unfolding transferEdgesRefineInvar_def transferEdge_alt by fastforce+

lemma transferEdges_capcomp:
  "CapacityCompatibleGraphs c' c \<Longrightarrow> CapacityCompatibleGraphs (transferEdges S c') c"
  unfolding transferEdges_def
  by unfold_locales (simp add: CapacityCompatibleGraphs.cap_compatible)

lemma transferEdges_E: "Graph.E (transferEdges S c') = Graph.E c' - S \<union> (S \<inter> E)"
  unfolding Graph.E_def transferEdges_def by auto

lemma transferEdges_ss_E: "S \<subseteq> E \<Longrightarrow> Graph.E (transferEdges S c') = Graph.E c' \<union> S"
  using transferEdges_E by blast
end

interpretation transferEdges_dual:
  Dual_Graph_Algorithms "Graph.transferEdgesRefine c S" "Graph.transferEdgesRefine (c\<^sup>T) (prod.swap ` S)" for c S
  unfolding Graph.transferEdgesRefine_def
  apply (intro Dual_Graph_AlgorithmsI)
  apply (all \<open>refine_rcg FOREACH_refine_rcg[where \<alpha>="prod.swap"]\<close>)
  by (auto simp: transpose_graph_rel_def Graph.transferEdge_def)
\<comment> \<open>Transferring edges to another graph\<close>

subsubsection \<open>Extended Breadth First Search phase\<close>

text \<open>NOTE: For the correctness proofs, we need "V_i = Graph.V c' \<union> s", that is, we need to assure
      that the source node is contained in this vertex set. This is a consequence of the graph
      model, where nodes without edges cannot exists, which results in the graph being empty during
      the first iteration even though s is within distance 0 of itself.
      If we merely had "V_i = Graph.V c'" (making it unnecessary to pass V_i as a separate parameter),
      then if there were a self loop of s, the first phase iteration would add s to the queue for
      the next iteration (as it is an outgoing neighbor of s and not contained in the graph),
      violating the invariant.\<close>

context Graph
begin
(* TODO here we directly use the refined version of transferEdges, where in rightPass we first
  use the abstract version and refine later. Unify! *)
definition ebfsPhase :: "node set \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfsPhase V\<^sub>i c' Q \<equiv> foreach Q
    (\<lambda>u (c', Q'). do {
      let S = E `` {u} - V\<^sub>i;
      c' \<leftarrow> transferEdgesRefine ({u} \<times> S) c';
      let Q' = Q' \<union> S;
      RETURN (c', Q')
    })
    (c', {})"

definition ebfsPhaseInvar :: "node \<Rightarrow> nat \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfsPhaseInvar s n c\<^sub>i Q \<equiv> \<lambda>(c', Q').
    CapacityCompatibleGraphs c' c
    \<and> Graph.E c' = Graph.E c\<^sub>i \<union> E \<inter> (exactDistNodes n s - Q) \<times> Q'
    \<and> Q' = exactDistNodes (Suc n) s \<inter> E `` (exactDistNodes n s - Q)"

lemma ebfsPhase_initial:
  assumes "Bounded_Source_Shortest_Path_Union c' c s V n"
  shows "ebfsPhaseInvar s n c' (exactDistNodes n s) (c', {})"
  unfolding ebfsPhaseInvar_def
proof (intro case_prodI conjI)
  from assms interpret Bounded_Source_Shortest_Path_Union c' c s V n .
  show "CapacityCompatibleGraphs c' c" by intro_locales
qed (simp_all)

lemma ebfs_phase_final:
  assumes BSPU: "Bounded_Source_Shortest_Path_Union c\<^sub>i c s V n"
    and INVAR: "ebfsPhaseInvar s n c\<^sub>i {} (c', Q')"
  shows "Bounded_Source_Shortest_Path_Union c' c s V (Suc n) \<and> Q' = exactDistNodes (Suc n) s"
proof
  from INVAR have "CapacityCompatibleGraphs c' c"
    and E'_EQ: "Graph.E c' = Graph.E c\<^sub>i \<union> E \<inter> exactDistNodes n s \<times> Q'"
    and Q'_EQ: "Q' = exactDistNodes (Suc n) s \<inter> E `` exactDistNodes n s"
    unfolding ebfsPhaseInvar_def by auto
  then interpret CapacityCompatibleGraphs c' c by simp
  from BSPU interpret g\<^sub>i: Bounded_Source_Shortest_Path_Union c\<^sub>i c s V n .

  have "exactDistNodes (Suc n) s \<subseteq> E `` exactDistNodes n s"
  proof
    fix v
    assume "v \<in> exactDistNodes (Suc n) s"
    then obtain p where "isShortestPath s p v" "length p = Suc n" unfolding exactDistNodes_def
      by (fastforce elim: obtain_shortest_path simp: isShortestPath_min_dist_def)
    then obtain u p\<^sub>u where "isShortestPath s p\<^sub>u u" "length p\<^sub>u = n" "(u, v) \<in> E"
      by (metis isShortestPath_min_dist_def min_dist_suc obtain_shortest_path connected_def)
    then show "v \<in> E `` exactDistNodes n s" unfolding exactDistNodes_def isShortestPath_min_dist_def
      using isPath_rtc connected_edgeRtc by fastforce
  qed
  with Q'_EQ show "Q' = exactDistNodes (Suc n) s" by blast
  with E'_EQ have E'_EQ: "E' = g\<^sub>i.E' \<union> E \<inter> exactDistNodes n s \<times> exactDistNodes (Suc n) s"
    by simp

  show "Bounded_Source_Shortest_Path_Union c' c s V (Suc n)"
  proof (unfold_locales, intro pair_set_eqI)
    fix u v
    assume "(u, v) \<in> E'"
    then consider (OLD) "(u, v) \<in> g\<^sub>i.E'"
      | (NEW) "(u, v) \<in> E \<inter> exactDistNodes n s \<times> exactDistNodes (Suc n) s"
      using E'_EQ by blast
    then show "(u, v) \<in> \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t \<and> length p \<le> Suc n}"
    proof cases
      case OLD
      then have "(u, v) \<in> \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t \<and> length p \<le> n}"
        by (simp add: g\<^sub>i.bounded_shortest_s_path_union)
      then show ?thesis by fastforce
    next
      case NEW
      then have "connected s u" "Suc (min_dist s u) = min_dist s v" "(u, v) \<in> E" "min_dist s v = Suc n"
        unfolding exactDistNodes_def by auto
      then obtain p where SP: "isShortestPath s (p @ [(u, v)]) v"
        using obtain_shortest_path shortestPath_append_edge by meson
      with \<open>min_dist s v = Suc n\<close> have "length p = n" unfolding isShortestPath_min_dist_def by simp
      moreover note SP \<open>(u, v) \<in> E\<close>
      ultimately show ?thesis using V_def by fastforce
    qed
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t \<and> length p \<le> Suc n}"
    then obtain t p where "(u, v) \<in> set p" "isShortestPath s p t" "length p \<le> Suc n" by blast
    then obtain p' where SP: "isShortestPath s (p' @ [(u, v)]) v" and LEN: "length p' \<le> n"
      by (fastforce dest: split_list split_shortest_path_around_edge)
    then have "(u, v) \<in> E" by (simp add: isPath_append isShortestPath_def)
    from LEN consider (LEN_LE) "length p' < n" | (LEN_EQ) "length p' = n" by linarith
    then show "(u, v) \<in> E'"
    proof cases
      case LEN_LE
      with \<open>(u, v) \<in> E\<close> have "length (p' @ [(u, v)]) \<le> n" "v \<in> V"
        unfolding V_def by auto
      with SP show ?thesis using E'_EQ unfolding g\<^sub>i.bounded_shortest_s_path_union by fastforce
    next
      case LEN_EQ
      with SP have "v \<in> exactDistNodes (Suc n) s"
        unfolding exactDistNodes_def isShortestPath_min_dist_def connected_def by auto
      moreover from SP LEN_EQ have "u \<in> exactDistNodes n s"
        using split_shortest_path unfolding exactDistNodes_def isShortestPath_min_dist_def connected_def
        by fastforce
      moreover note \<open>(u, v) \<in> E\<close>
      ultimately show ?thesis using E'_EQ by blast
    qed
  qed
qed

context
  fixes s
  assumes FINITE_REACHABLE: "finite (reachableNodes s)"
begin
(* TODO necessary? *)
(*
lemma finite_if_spu(*[intro]*): "Source_Shortest_Path_Union c' c s T \<Longrightarrow> Finite_Graph c'"
proof
  assume "Source_Shortest_Path_Union c' c s T"
  then interpret Source_Shortest_Path_Union c' c s T .
  have "Graph.V c' \<subseteq> reachableNodes s"
    unfolding reachableNodes_def using sg_connected_remains_base_connected by blast
  then show "finite (Graph.V c')" using FINITE_REACHABLE finite_subset by blast
qed
*)

lemma ebfs_phase_step:
  assumes BSPU: "Bounded_Source_Shortest_Path_Union c\<^sub>i c s V n"
    and Q: "u \<in> Q" "Q \<subseteq> exactDistNodes n s"
    and INVAR: "ebfsPhaseInvar s n c\<^sub>i Q (c', Q')"
  defines "S \<equiv> E `` {u} - (Graph.V c\<^sub>i \<union> {s})"
  shows "transferEdgesRefine ({u} \<times> S) c' \<le> (spec c''. ebfsPhaseInvar s n c\<^sub>i (Q - {u}) (c'', Q' \<union> S))"
proof -
  from Q have "connected s u" unfolding exactDistNodes_def by blast
  then have "E `` {u} \<subseteq> reachableNodes s"
    unfolding reachableNodes_def using connected_append_edge by blast
  with FINITE_REACHABLE have "finite S" unfolding S_def using finite_subset by blast
  then have "transferEdgesRefine ({u} \<times> S) c' \<le> return (transferEdges ({u} \<times> S) c')"
    using transferEdgesRefine_correct by simp
  also have "... \<le> (spec c''. ebfsPhaseInvar s n c\<^sub>i (Q - {u}) (c'', Q' \<union> S))"
    unfolding ebfsPhaseInvar_def
  proof (clarify, refine_vcg)
    from INVAR have "CapacityCompatibleGraphs c' c"
      and E'_EQ: "Graph.E c' = Graph.E c\<^sub>i \<union> E \<inter> (exactDistNodes n s - Q) \<times> Q'"
      and Q'_EQ: "Q' = exactDistNodes (Suc n) s \<inter> E `` (exactDistNodes n s - Q)"
      unfolding ebfsPhaseInvar_def by auto
    then interpret CapacityCompatibleGraphs c' c by simp

    show "CapacityCompatibleGraphs (transferEdges ({u} \<times> S) c') c"
      using \<open>CapacityCompatibleGraphs c' c\<close> transferEdges_capcomp by blast

    interpret g\<^sub>i: Graph c\<^sub>i .
    from Q have "E `` {u} \<subseteq> boundedReachableNodes (Suc n) s"
      unfolding boundedReachableNodes_alt using exactDistNodes_reachable_ss by blast
    with BSPU have S_alt: "S = exactDistNodes (Suc n) s \<inter> E `` {u}"
      unfolding S_def exactDistNodes_alt using BSPU_V'_boundedReachable by blast
    with Q Q'_EQ show "Q' \<union> S = exactDistNodes (Suc n) s \<inter> E `` (exactDistNodes n s - (Q - {u}))"
      by blast

    have "{u} \<times> S \<subseteq> E" unfolding S_def by blast
    then have "Graph.E (transferEdges ({u} \<times> S) c') = g\<^sub>i.E \<union> E \<inter> ((exactDistNodes n s - Q) \<times> Q' \<union> {u} \<times> S)"
      using transferEdges_ss_E E'_EQ by blast
    also have "... = g\<^sub>i.E \<union> E \<inter> (exactDistNodes n s - (Q - {u})) \<times> (Q' \<union> S)"
      unfolding S_alt Q'_EQ using Q by blast
    finally show "Graph.E (transferEdges ({u} \<times> S) c') = g\<^sub>i.E \<union> E \<inter> (exactDistNodes n s - (Q - {u})) \<times> (Q' \<union> S)" .
  qed
  finally show ?thesis .
qed

lemma ebfs_phase_correct:
  assumes BSPU: "Bounded_Source_Shortest_Path_Union c' c s V n"
  shows "ebfsPhase (Graph.V c' \<union> {s}) c' (exactDistNodes n s) \<le> SPEC (\<lambda>(c'', Q'). Bounded_Source_Shortest_Path_Union c'' c s V (Suc n) \<and> Q' = exactDistNodes (Suc n) s)"
  unfolding ebfsPhase_def
  apply (refine_vcg FOREACH_rule[where I="ebfsPhaseInvar s n c'"])
  using FINITE_REACHABLE finite_subset exactDistNodes_reachable_ss boundedReachableNodes_ss apply meson
  using BSPU ebfsPhase_initial ebfs_phase_step ebfs_phase_final by simp_all
end
end

\<comment> \<open>Extended Breadth First Search phase\<close>

subsubsection \<open>Extended Breadth First Search Outer Loop\<close>
context Graph
begin
(* TODO the n exists only for analysis purposes, can we remove it? *)
(* TODO curry *)
(* TODO update V\<^sub>i by adding Q instead of recomputing it *)
definition ebfs :: "node \<Rightarrow> _ graph nres" where
  "ebfs s \<equiv> do {
    (c', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q, _). Q \<noteq> {})
      (\<lambda>(c', Q, n). do {
        let V\<^sub>i = Graph.V c' \<union> {s};
        (c', Q') \<leftarrow> ebfsPhase V\<^sub>i c' Q;
        RETURN (c', Q', Suc n)
      })
      ((\<lambda>_. 0), {s}, 0);
    RETURN c'
  }"

definition ebfsInvar :: "node \<Rightarrow> (_ graph \<times> node set \<times> nat) \<Rightarrow> bool" where
  "ebfsInvar s \<equiv> \<lambda>(c', Q, n).
    Bounded_Source_Shortest_Path_Union c' c s V n
    \<and> Q = exactDistNodes n s"

lemma ebfs_final:
  assumes INVAR: "ebfsInvar s (c', {}, n)"
  shows "Source_Shortest_Path_Union c' c s V"
proof -
  from INVAR interpret Bounded_Source_Shortest_Path_Union c' c s V n unfolding ebfsInvar_def by blast

  show ?thesis
  proof (unfold_locales, intro equalityI subsetI)
    fix e
    assume "e \<in> \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t}"
    then obtain p t where P: "e \<in> set p" "t \<in> V" "isShortestPath s p t" by blast
    have "length p < n"
    proof (rule ccontr)
      assume "\<not> length p < n"
      with P obtain p' u where "isShortestPath s p' u" "length p' = n"
        using split_list_min_len split_shortest_path by (metis not_le)
      then have "u \<in> exactDistNodes n s"
        unfolding exactDistNodes_def isShortestPath_min_dist_def connected_def by auto
      with INVAR show False unfolding ebfsInvar_def by simp
    qed
    with P show "e \<in> E'" using bounded_shortest_s_path_union by fastforce
  qed (auto simp: bounded_shortest_s_path_union)
qed

context
  fixes s
  assumes FINITE_REACHABLE: "finite (reachableNodes s)"
begin
thm ebfs_phase_correct[OF FINITE_REACHABLE]
thm greater_bounded_def
term greater_bounded
find_consts "('a \<times> 'b \<times> 'c) \<Rightarrow> 'c"
value "(snd \<circ> snd) ((1::nat), (2::nat), (3::nat))"
term inv_image
term less_than_bool
find_consts "(nat \<times> nat) set"
thm greater_bounded_Suc_iff
find_theorems "_ \<Longrightarrow> _ \<le> SPEC _"
thm SPEC_rule
find_theorems pathVertices reachableNodes
find_theorems pathVertices isSimplePath
thm pathVertices_fwd
thm distinct_card
find_theorems pathVertices length

(* TODO fix this hot mess *)
lemma ebfs_step:
  assumes INVAR: "ebfsInvar s (c', Q, n)" and Q: "Q \<noteq> {}"
  shows "ebfsPhase (Graph.V c' \<union> {s}) c' Q \<le> SPEC (\<lambda>(c'', Q'). ebfsInvar s (c'', Q', Suc n) \<and> Suc n \<le> card (reachableNodes s))"
proof -
  from INVAR have "ebfsPhase (Graph.V c' \<union> {s}) c' Q \<le> SPEC (\<lambda>(c'', Q'). Bounded_Source_Shortest_Path_Union c'' c s V (Suc n) \<and> Q' = exactDistNodes (Suc n) s)"
    using ebfs_phase_correct[OF FINITE_REACHABLE] unfolding ebfsInvar_def by blast
  also have "... \<le> SPEC (\<lambda>(c'', Q'). ebfsInvar s (c'', Q', Suc n) \<and> Suc n \<le> card (reachableNodes s))"
  proof (auto simp: ebfsInvar_def)
    from INVAR Q obtain p u where "isShortestPath s p u" "length p = n"
      unfolding ebfsInvar_def exactDistNodes_def
      using obtain_shortest_path isShortestPath_min_dist_def by simp metis
    then have "card (set (pathVertices s p)) = Suc n" apply (auto dest!: shortestPath_is_simple simp: isSimplePath_def)
      using length_pathVertices_eq distinct_card by fastforce (* TODO *)
    with \<open>isShortestPath s p u\<close>[THEN shortestPath_is_path, THEN pathVertices_reachable] show "Suc n \<le> card (reachableNodes s)"
      by (metis FINITE_REACHABLE card_mono)
  qed
  finally show ?thesis .
qed

theorem ebfs_correct: "ebfs s \<le> (spec c'. Source_Shortest_Path_Union c' c s V)"
  unfolding ebfs_def
  apply (refine_vcg WHILET_rule[where I="ebfsInvar s"
      and R="inv_image (greater_bounded (card (reachableNodes s))) (snd \<circ> snd)"])

  apply blast

  subgoal
    unfolding ebfsInvar_def exactDistNodes_def
    apply auto
    apply unfold_locales
    unfolding Graph.E_def
    by auto

  using ebfs_step ebfs_final by simp_all
end
end
\<comment> \<open>Extended Breadth First Search Outer Loop\<close>

subsubsection \<open>Backward EBFS\<close>
context Graph
begin
definition ebfsBackward :: "node \<Rightarrow> _ graph nres" where
  "ebfsBackward t \<equiv> do {
    (c', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q, _). Q \<noteq> {})
      (\<lambda>(c', Q, n). do {
        let V\<^sub>i = (Graph.V c' \<union> {t});
        (c', Q') \<leftarrow> foreach Q
          (\<lambda>u (c', Q'). do {
            let S = E\<inverse> `` {u} - V\<^sub>i;
            c' \<leftarrow> transferEdgesRefine (S \<times> {u}) c';
            let Q' = Q' \<union> S;
            RETURN (c', Q')
          })
          (c', {});
        RETURN (c', Q', Suc n)
      })
      ((\<lambda>_. 0), {t}, 0);
    RETURN c'
  }"


(* TODO improve *)
lemma dual_ebfs: "Dual_Graph_Algorithms (swap_args2 Graph.ebfsBackward u) (swap_args2 Graph.ebfs u)"
proof (intro Dual_Graph_AlgorithmsI, unfold swap_args2_def)
  fix c' :: "('capacity'::linordered_idom) graph"
  note[refine_dref_RELATES] = RELATESI[of transpose_graph_rel]
  show "Graph.ebfsBackward c' u \<le> \<Down> transpose_graph_rel (Graph.ebfs (c'\<^sup>T) u)"
    unfolding Graph.ebfsBackward_def Graph.ebfs_def Graph.ebfsPhase_def
    apply (refine_rcg FOREACH_refine_rcg[where \<alpha>=id], refine_dref_type)
            apply (all \<open>(auto simp: transpose_graph_rel_def; fail)?\<close>)
    apply (simp add: transferEdges_dual.conc_simp)
    by (simp add: transpose_graph_rel_def product_swap)

  show "Graph.ebfs c' u \<le> \<Down> transpose_graph_rel (Graph.ebfsBackward (c'\<^sup>T) u)"
    unfolding Graph.ebfsBackward_def Graph.ebfs_def Graph.ebfsPhase_def
    apply (refine_rcg FOREACH_refine_rcg[where \<alpha>=id])
            apply refine_dref_type
            apply (all \<open>(auto simp: transpose_graph_rel_def; fail)?\<close>)
    apply (simp add: transferEdges_dual.conc_simp)
    by (simp add: transpose_graph_rel_def product_swap)
qed

(* TODO simplify and extract *)
lemma dual_spu: "Target_Shortest_Path_Union c' c (Graph.V c) t = Source_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t (Graph.V (c\<^sup>T))"
proof
  assume "Target_Shortest_Path_Union c' c (Graph.V c) t"
  then interpret spu: Target_Shortest_Path_Union c' c "Graph.V c" t .
  show "Source_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t (Graph.V (c\<^sup>T))"
  proof
    show "\<And>u v. (c'\<^sup>T) (u, v) = 0 \<or> (c\<^sup>T) (u, v) = 0 \<or> (c'\<^sup>T) (u, v) = (c\<^sup>T) (u, v)"
      using spu.cap_compatible by simp
    show "Graph.E (c'\<^sup>T) = \<Union> {set p |p. \<exists>ta. ta \<in> Graph.V (c\<^sup>T) \<and> Graph.isShortestPath (c\<^sup>T) t p ta}"
    proof (simp, intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> spu.E'\<inverse>"
      then obtain s p where "(v, u) \<in> set p" "s \<in> V" "isShortestPath s p t"
        using spu.shortest_t_path_union by blast
      then have "(u, v) \<in> set (transpose_path p)" "isShortestPath s (transpose_path (transpose_path p)) t"
        by auto
      with \<open>s \<in> V\<close> show "(u, v) \<in> \<Union> {set p |p. \<exists>ta. ta \<in> V \<and> isShortestPath ta (transpose_path p) t}"
        by blast
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. \<exists>ta. ta \<in> V \<and> isShortestPath ta (transpose_path p) t}"
      then show "(u, v) \<in> spu.E'\<inverse>" using spu.shortest_t_path_union by fastforce
    qed
  qed
next
  assume "Source_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t (Graph.V (c\<^sup>T))"
  then interpret spu: Source_Shortest_Path_Union "c'\<^sup>T" "c\<^sup>T" t "Graph.V c" by simp
  show "Target_Shortest_Path_Union c' c (Graph.V c) t"
  proof
    show "\<And>u v. c' (u, v) = 0 \<or> c (u, v) = 0 \<or> c' (u, v) = c (u, v)"
      using spu.cap_compatible by simp
    show "Graph.E c' = \<Union> {set p |p. \<exists>s. s \<in> Graph.V c \<and> Graph.isShortestPath c s p t}"
    proof (intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> Graph.E c'"
      then obtain s p where "(v, u) \<in> set p" "s \<in> V" "spu.isShortestPath t p s"
        using spu.shortest_s_path_union by fastforce
      then show "(u, v) \<in> \<Union> {set p |p. \<exists>s. s \<in> Graph.V c \<and> Graph.isShortestPath c s p t}"
        by fastforce
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. \<exists>s. s \<in> Graph.V c \<and> Graph.isShortestPath c s p t}"
      then obtain s p where "(u, v) \<in> set p" "s \<in> Graph.V c" "Graph.isShortestPath c s p t"
        by blast
      then have "(v, u) \<in> set (transpose_path p)" "spu.isShortestPath t (transpose_path p) s" by auto
      with \<open>s \<in> Graph.V c\<close> have "(v, u) \<in> spu.E'" using spu.shortest_s_path_union by blast
      then show "(u, v) \<in> Graph.E c'" by simp
    qed
  qed
qed

theorem (in Graph) ebfsBackward_correct:
  assumes FINITE_REACHED_FROM: "finite {u. connected u t}"
  shows "ebfsBackward t \<le> (spec c'. Target_Shortest_Path_Union c' c V t)"
proof -
  interpret Dual_Graph_Algorithms "swap_args2 Graph.ebfsBackward t" "swap_args2 Graph.ebfs t"
    using dual_ebfs .
  have "swap_args2 Graph.ebfsBackward t c \<le> (spec c'. Target_Shortest_Path_Union c' c V t)"
    (*using dual_spu apply (auto elim!: transfer_spec)*)
    (*thm dual_spu[THEN transfer_spec]*)
    (*thm transfer_spec[OF dual_spu]*)
  proof (intro transfer_spec[where spec'="\<lambda>c c'. Source_Shortest_Path_Union c' c t (Graph.V c)"])
    show "\<And>c c'. Target_Shortest_Path_Union c' c (Graph.V c) t = Source_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t (Graph.V (c\<^sup>T))"
      using Graph.dual_spu .
    thm Graph.ebfs_correct
    from FINITE_REACHED_FROM have "finite (Graph.reachableNodes (c\<^sup>T) t)"
      unfolding Graph.reachableNodes_def by simp
    then show "swap_args2 Graph.ebfs t (c\<^sup>T) \<le> (spec c'. Source_Shortest_Path_Union c' (c\<^sup>T) t (Graph.V (c\<^sup>T)))"
      using Graph.ebfs_correct by fastforce
  qed
  then show ?thesis by simp
qed
end
\<comment> \<open>Backward EBFS\<close>

subsubsection \<open>Building a dual layering\<close>
context Graph
begin
(* TODO bounded version *)
definition buildDualLayering :: "node \<Rightarrow> node \<Rightarrow> _ graph nres" where
  "buildDualLayering s t \<equiv> do {
    sl \<leftarrow> ebfs s;
    stl \<leftarrow> Graph.ebfsBackward sl t;
    RETURN stl
  }"
end

(* TODO is Finite_Graph really what we want? *)
context Finite_Graph
begin
lemma buildDualLayering_correct:
  "buildDualLayering s t \<le> (spec c'. Dual_Shortest_Path_Union c' c s t)"
  unfolding buildDualLayering_def
proof (refine_vcg, simp)
  have "reachableNodes s \<subseteq> V \<union> {s}"
    using Graph.distinct_nodes_in_V_if_connected(2) reachableNodes_def by auto
  then have "finite (reachableNodes s)" using finite_V by (simp add: finite_subset)
  then have "ebfs s \<le> (spec sl. Source_Shortest_Path_Union sl c s V)" by (rule ebfs_correct)
  also have "... \<le> (spec sl. Graph.ebfsBackward sl t \<le> (spec c'. Dual_Shortest_Path_Union c' c s t))"
  proof (rule SPEC_rule)
    fix c'
    assume "Source_Shortest_Path_Union c' c s V"
    then interpret Source_Shortest_Path_Union c' c s V .

    have "{u. g'.connected u t} \<subseteq> V' \<union> {t}"
      using g'.distinct_nodes_in_V_if_connected by auto
    then have "finite {u. g'.connected u t}" using finite_V V_ss by (simp add: finite_subset)
    then have "g'.ebfsBackward t \<le> (spec c''. Target_Shortest_Path_Union c'' c' V' t)"
      by (rule g'.ebfsBackward_correct)
    also from \<open>Source_Shortest_Path_Union c' c s V\<close> have "... \<le> (spec c''. Dual_Shortest_Path_Union c'' c s t)"
      using SPEC_rule ST_SPU_dualI by metis
    finally show "g'.ebfsBackward t \<le> (spec c''. Dual_Shortest_Path_Union c'' c s t)" .
  qed
  finally show "ebfs s \<le> (spec sl. Graph.ebfsBackward sl t \<le> (spec c'. Dual_Shortest_Path_Union c' c s t))" .
qed
end
\<comment> \<open>Building a dual layering\<close>
\<comment> \<open>Extended BFS\<close>


























subsection \<open>Dinitz phase refinement\<close>





(* TODO *)
end



context NFlow
begin

section \<open>Experiment\<close>
definition test1 :: "_ flow nres" where
  "test1 \<equiv> do {
    (f', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, _, brk). \<not> brk)
      (\<lambda>(f', stl, _). do {
            stl \<leftarrow> Graph.subtract_path_algo stl [(0, 0)];
            RETURN (f', stl, False)
          })
      (f, c, False);
    RETURN f'}"
definition test2 :: "_ flow nres" where
  "test2 \<equiv> do {
    (f', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, _, brk). \<not> brk)
      (\<lambda>(f', stl, _). do {
            stl \<leftarrow> return (Graph.subtract_path stl [(0, 0)]);
            RETURN (f', stl, False)
          })
      (f, c, False);
    RETURN f'}"

thm refine_dref_pattern
(* TODO find out which rule leads to the spec term, which in turn means dref_type cannot infer relation type *)
lemma "test1 \<le> \<Down> Id test2"
  unfolding test1_def test2_def
  apply refine_rcg
         apply refine_dref_type
      apply clarsimp_all
  oops
\<comment> \<open>Experiment\<close>





(* TODO *)
(*declare fun_relI[refine del]*)
lemma RELATESI_workaround[refine_dref_pattern]:
  "RELATES R \<Longrightarrow> S \<le> (spec x. (x, y) \<in> R) \<Longrightarrow> S \<le> (spec x. (x, y) \<in> R)" .


thm build_st_layering_correct
  Dual_Layer_Graph.greedyPathFinding_correct
  subtract_path_algo_correct
  Graph.inner_path_vertices_algo_correct
  Finite_Bounded_Graph.cleaning_algo_correct

(* TODO cleanup assertions *)

(*
definition dinitz_phase_assert_invar :: "(_ flow \<times> _ graph \<times> bool) \<Rightarrow> bool" where
  "dinitz_phase_assert_invar \<equiv> \<lambda>(f', stl, brk).
    NFlow c s t f'
    \<and> Bounded_ST_Shortest_Path_Union stl (cf_of f') s t (cf.min_dist s t)
    \<and> (Graph.connected (cf_of f') s t \<longrightarrow> cf.min_dist s t \<le> Graph.min_dist (cf_of f') s t)
    \<and> (brk \<longrightarrow> \<not> Graph.connected stl s t)"

definition dinitz_phase_assert :: "_ flow nres" where
  "dinitz_phase_assert \<equiv> do {
    stl \<leftarrow> (spec c'. ST_Shortest_Path_Union c' cf s t);
    (f', _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>dinitz_phase_assert_invar\<^esup>
      (\<lambda>(_, _, brk). \<not> brk)
      (\<lambda>(f', stl, _). do {
        p' \<leftarrow> select p. Graph.isPath stl s p t;
        case p' of
          None \<Rightarrow> RETURN (f', stl, True)
        | Some p \<Rightarrow> do {
            assert (Graph.isPath stl s p t);
            assert (ST_Shortest_Path_Union stl (cf_of f') s t);
            Q_ls \<leftarrow> return (tl (butlast (Graph.pathVertices s p)));
            assert (set Q_ls = set (Graph.pathVertices s p) - {s, t});
            stl' \<leftarrow> return (Graph.subtract_path stl p);
            assert (Contained_Graph stl' stl \<and> Graph.E stl \<subseteq> Graph.E stl' \<union> set p);
            stl' \<leftarrow> return (cleaning s t stl');
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl', False)
          }})
      (f, stl, False);
    RETURN f'}"
*)

definition dinitz_phase_assert_invar :: "(_ flow \<times> _ graph \<times> bool \<times> bool) \<Rightarrow> bool" where
  "dinitz_phase_assert_invar \<equiv> \<lambda>(f', stl, brk, changed).
    NFlow c s t f'
    \<and> Bounded_ST_Shortest_Path_Union stl (cf_of f') s t (cf.min_dist s t)
    \<and> (Graph.connected (cf_of f') s t \<longrightarrow> cf.min_dist s t \<le> Graph.min_dist (cf_of f') s t)
    \<and> (brk \<longrightarrow> \<not> Graph.connected stl s t)
    \<and> (val \<le> Flow.val c s f')
    \<and> (changed \<longleftrightarrow> f' \<noteq> f)
    \<and> (changed \<longrightarrow> cf.connected s t)" (* \<and> (changed \<and> brk \<longrightarrow> cf.connected s t)" *)

(* TODO can this be simplified to just changed \<longleftrightarrow> val < val'? *)
lemma dinitz_phase_assert_invar_alt:
  "dinitz_phase_assert_invar = (\<lambda>(f', stl, brk, changed).
    dinitz_phase_invar (f', stl)
    \<and> (brk \<longrightarrow> \<not> Graph.connected stl s t)
    \<and> (val \<le> Flow.val c s f')
    \<and> (changed \<longleftrightarrow> f' \<noteq> f)
    \<and> (changed \<longrightarrow> cf.connected s t))" (* TODO does this work? *)
  unfolding dinitz_phase_invar_def dinitz_phase_assert_invar_def by simp

definition dinitz_phase_assert :: "(_ flow \<times> bool) nres" where
  "dinitz_phase_assert \<equiv> do {
    stl \<leftarrow> (spec c'. ST_Shortest_Path_Union c' cf s t);
    (f', _, _, changed) \<leftarrow> WHILE\<^sub>T\<^bsup>dinitz_phase_assert_invar\<^esup>
      (\<lambda>(_, _, brk, _). \<not> brk)
      (\<lambda>(f', stl, _, changed). do {
        p' \<leftarrow> select p. Graph.isPath stl s p t;
        case p' of
          None \<Rightarrow> RETURN (f', stl, True, changed)
        | Some p \<Rightarrow> do {
            assert (Graph.isPath stl s p t);
            assert (ST_Shortest_Path_Union stl (cf_of f') s t);
            Q_ls \<leftarrow> return (tl (butlast (Graph.pathVertices s p)));
            assert (set Q_ls = set (Graph.pathVertices s p) - {s, t});
            stl' \<leftarrow> return (Graph.subtract_path stl p);
            assert (Contained_Graph stl' stl \<and> Graph.E stl \<subseteq> Graph.E stl' \<union> set p);
            stl' \<leftarrow> return (cleaning s t stl');
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl', False, True)
          }})
      (f, stl, False, False);
    RETURN (f', changed)}"

(* TODO comment about val needed for changed inequality *)

(* TODO use this in phase step *)
lemma stu_if_invar_and_path:
  assumes INVAR: "dinitz_phase_invar (f', stl)"
    and PATH: "Graph.isPath stl s p t"
  shows "ST_Shortest_Path_Union stl (cf_of f') s t"
proof -
  from INVAR interpret f': NFlow c s t f' unfolding dinitz_phase_invar_def by blast

  have BOUND_EQ: "cf.min_dist s t = f'.cf.min_dist s t"
  proof -
    from INVAR interpret Bounded_ST_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
      unfolding dinitz_phase_invar_def by simp
    show ?thesis
    proof (intro antisym)
      from PATH INVAR show "cf.min_dist s t \<le> f'.cf.min_dist s t"
        unfolding dinitz_phase_invar_def Graph.connected_def
        using sg_paths_are_base_paths by blast
      from PATH show "f'.cf.min_dist s t \<le> cf.min_dist s t" (* TODO fix proof *)
      using f'.cf.isShortestPath_min_dist_def path_length_bounded shortest_path_transfer (* by simp *)
      by (metis Bounded_Shortest_Path_Union.obtain_close_ST Bounded_Shortest_Path_Union_axioms emptyE g'.isEmpty_def g'.isPath_bwd_cases min_dist_transfer s_in_V_if_nonempty singleton_iff t_not_s)
    qed
  qed
  with INVAR show "ST_Shortest_Path_Union stl (f'.cf) s t"
    unfolding dinitz_phase_invar_def using min_st_dist_bound by fastforce
qed

lemma dinitz_phase_assert_step:
  fixes f' stl changed
  assumes PATH: "Graph.isPath stl s p t"
      and INVAR: "dinitz_phase_assert_invar (f', stl, False, changed)"
  defines "aug_f' \<equiv> NFlow.augment c f' (NPreflow.augmentingFlow c f' p)"
      and "stl' \<equiv> cleaning s t (Graph.subtract_path stl p)"
    shows "dinitz_phase_assert_invar (aug_f', stl', False, True) \<and> Graph.E stl' \<subset> Graph.E stl \<and> finite (Graph.E stl)"
proof -
  have "Flow.val c s f' < Flow.val c s aug_f'"
  proof -
    from INVAR interpret f': NFlow c s t f' unfolding dinitz_phase_assert_invar_def by blast
    from INVAR PATH interpret stu: ST_Shortest_Path_Union stl "cf_of f'" s t
      unfolding dinitz_phase_assert_invar_alt using stu_if_invar_and_path by blast

    have "Flow f'.cf s t (f'.augmentingFlow p)"
      apply (intro f'.augFlow_resFlow)
      unfolding f'.isAugmentingPath_def
      using PATH f'.cf.isShortestPath_alt stu.shortest_path_transfer by blast
    moreover have "0 < Flow.val f'.cf s (f'.augmentingFlow p)"
      by (simp add: Graph.shortestPath_is_path Graph.shortestPath_is_simple PATH f'.augFlow_val f'.isAugmentingPath_def f'.resCap_gzero_aux stu.shortest_path_transfer)
    ultimately show ?thesis unfolding aug_f'_def using f'.augment_flow_value by simp
  qed
  with PATH INVAR show ?thesis unfolding dinitz_phase_assert_invar_alt aug_f'_def stl'_def
    using dinitz_phase_step (* TODO prettify *)
    apply auto
    apply (meson Graph.connected_def ST_Shortest_Path_Union.st_connected_iff stu_if_invar_and_path)
    by blast+
qed




definition "dinitz_phase_assert_wf_rel \<equiv> inv_image
  (less_than_bool <*lex*> finite_psubset)
  (\<lambda>(_, stl, brk, _). (\<not>brk, Graph.E stl))"


find_theorems Graph.E Graph.subtract_path
find_theorems Graph.E Graph.subtract_graph
thm Graph.subtract_graph_untouched_edges

lemma dinitz_phase_assert_correct:
  "dinitz_phase_assert \<le> SPEC (\<lambda>(f', changed). res_dist_increasing_flow f' \<and> changed = (f' \<noteq> f) \<and> (changed \<longrightarrow> cf.connected s t))"
  unfolding dinitz_phase_assert_def
  apply (refine_vcg WHILEIT_rule[where R=dinitz_phase_assert_wf_rel])
                      apply (all \<open>(clarsimp; fail)?\<close>)
            apply (simp add: dinitz_phase_assert_wf_rel_def wf_lex_prod)
            apply (simp add: dinitz_phase_assert_invar_def NFlow_axioms min_st_dist_bound)
           defer defer defer
  apply (simp add: Graph.subtract_path_alt) using Graph.subtract_graph_untouched_edges apply (metis (no_types, lifting) Graph.isPath_alt Graph.path_induced_graph_edges Int_Un_eq(4) Int_absorb1 Int_commute Un_Diff_cancel2 cf.isPath.simps(1) set_eq_subset t_not_s)
          apply (simp add: dinitz_phase_assert_step)
          apply (simp add: dinitz_phase_assert_step dinitz_phase_assert_wf_rel_def)
        apply (simp add: dinitz_phase_assert_invar_alt Graph.connected_def)
       apply (simp add: dinitz_phase_assert_wf_rel_def)
      apply (clarsimp simp: dinitz_phase_assert_invar_alt dinitz_phase_final)
      apply (simp add: dinitz_phase_assert_invar_alt)
  apply (clarsimp simp: dinitz_phase_assert_invar_alt)
proof clarsimp_all oops
  fix f' stl p changed
  interpret cf': Graph "cf_of f'" .
  assume INVAR: "dinitz_phase_assert_invar (f', stl, False, changed)" and PATH: "Graph.isPath stl s p t"
  then show "ST_Shortest_Path_Union stl (cf_of f') s t"
    unfolding dinitz_phase_assert_invar_alt using stu_if_invar_and_path by blast
  then interpret ST_Shortest_Path_Union stl "cf_of f'" s t .

  from INVAR interpret f': NFlow c s t f' unfolding dinitz_phase_assert_invar_def by blast
  interpret g': Nonnegative_Graph stl
    using f'.cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast
  (* TODO replace this with a simple 'have', need some way to use sublocale relations *)
  interpret subt_pos_cont: Pos_Contained_Graph "g'.subtract_path p" stl
    unfolding g'.subtract_path_alt
    using g'.path_induced_graph_pos_contained Pos_Contained_Graph.subtract_le_contained by blast
  show "Contained_Graph (g'.subtract_path p ) stl" by intro_locales

  from PATH have "pathVertices s p = s # (tl (pathVertices s p))"
    by (simp add: Graph.pathVertices_fwd pathVertices_fwd_def)
  moreover from PATH have "pathVertices s p = butlast (pathVertices s p) @ [t]"
    by (metis Graph.isPath_bwd_cases Graph.isPath_tail Graph.pathVertices_alt snoc_eq_iff_butlast' t_not_s)
  ultimately have "pathVertices s p = s # (tl (butlast (pathVertices s p))) @ [t]"
    by (metis butlast_tl empty_append_eq_id snoc_eq_iff_butlast' t_not_s tl_last)
      (* TODO simplify, probably need to show s, t \<notin> tl (butlast (pathVertices s p)) *)
  then show "set (tl (butlast (pathVertices s p))) = set (pathVertices s p) - {s, t}"
    by (smt (verit, ccfv_threshold) Diff_insert0 Graph.isSimplePath_fwd Graph.pathVertices_fwd PATH Un_Diff_Int Un_insert_right distinct.simps(2) distinct_append empty_set insertCI insert_Diff1 list.simps(15) paths_are_simple set_append sup_bot.right_neutral)
qed

definition dinitz_phase_concrete :: "(_ flow \<times> bool) nres" where
  "dinitz_phase_concrete \<equiv> do {
    stl \<leftarrow> cf.build_st_layering s t;
    (f', _, _, changed) \<leftarrow> WHILE\<^sub>T\<^bsup>dinitz_phase_assert_invar\<^esup>
      (\<lambda>(_, _, brk, _). \<not> brk)
      (\<lambda>(f', stl, _, changed). do {
        p' \<leftarrow> Graph.greedy_st_path_finding stl s t;
        case p' of
          None \<Rightarrow> RETURN (f', stl, True, changed)
        | Some p \<Rightarrow> do {
            assert (Graph.isPath stl s p t);
            assert (ST_Shortest_Path_Union stl (cf_of f') s t);
            Q_ls \<leftarrow> inner_path_vertices_algo p;
            assert (set Q_ls = set (Graph.pathVertices s p) - {s, t});
            stl' \<leftarrow> Graph.subtract_path_algo stl p;
            assert (Contained_Graph stl' stl \<and> Graph.E stl \<subseteq> Graph.E stl' \<union> set p);
            stl' \<leftarrow> cleaning_algo (set Q_ls) stl';
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl', False, True)
          }})
      (f, stl, False, False);
    RETURN (f', changed)}"





find_theorems Graph.pathVertices set
find_theorems Graph.pathVertices_fwd set
find_theorems Graph.pathVertices
thm Graph.pathVertices_append

(*
lemma (in Graph) aux: "u \<notin> set (pathVertices s p) \<Longrightarrow> (u, v) \<notin> set p"
  by (induction p arbitrary: s) auto(*TODO*)
lemma (in Graph) aux2: "u \<notin> set (pathVertices s p) \<Longrightarrow> (v, u) \<notin> set p"
  apply (induction p arbitrary: s)
   apply simp
  apply simp sledgehammer
  apply (induction p arbitrary: s rule: rev_induct)
   apply simp
  apply (simp add: Graph.pathVertices_append) apply auto
  by (induction p arbitrary: s) auto(*TODO*)*)



lemma dinitz_phase_concrete_refine: "dinitz_phase_concrete \<le> \<Down> Id dinitz_phase_assert"
  unfolding dinitz_phase_concrete_def dinitz_phase_assert_def
  apply refine_rcg
            apply refine_dref_type
           apply clarsimp_all
  using cf.build_st_layering_correct apply simp
proof -
  fix f' stl changed
  assume "dinitz_phase_assert_invar (f', stl, False, changed)"
  then interpret bstu: Bounded_ST_Shortest_Path_Union stl "cf_of f'" s t "cf.min_dist s t"
    unfolding dinitz_phase_assert_invar_def by blast
  show "Graph.greedy_st_path_finding stl s t \<le> (select p. Graph.isPath stl s p t)"
    using bstu.greedy_st_path_finding_correct .
next
  fix f' stl p
  assume "ST_Shortest_Path_Union stl (cf_of f') s t"
  then interpret stu: ST_Shortest_Path_Union stl "cf_of f'" s t .

  assume "Graph.isPath stl s p t"
  then have SP: "Graph.isPath stl s p t" by blast
  
  show "inner_path_vertices_algo p \<le> RES {tl (butlast (Graph.pathVertices s p))}"
    using inner_path_vertices_algo_correct by (simp add: RES_sng_eq_RETURN)

  from SP show "Graph.subtract_path_algo stl p \<le> RES {Graph.subtract_path stl p}"
    using stu.g'.isSPath_distinct stu.paths_are_simple stu.g'.subtract_path_algo_correct
    by (metis RES_sng_eq_RETURN)

  thm Finite_Bounded_Graph.cleaning_algo_correct
  fix stl'
  assume "Contained_Graph stl' stl" "Graph.E stl \<subseteq> Graph.E stl' \<union> set p"
  show "cleaning_algo (set (Graph.pathVertices s p) - {s, t}) stl' \<le> RES {cleaning s t stl'}"
  proof (unfold RES_sng_eq_RETURN, intro Finite_Bounded_Graph.cleaning_algo_correct)
    show "s \<notin> set (Graph.pathVertices s p) - {s, t}"
      "t \<notin> set (Graph.pathVertices s p) - {s, t}"
      "finite (set (Graph.pathVertices s p) - {s, t})"
      by auto
    from \<open>Contained_Graph stl' stl\<close> show "Finite_Bounded_Graph stl' (stu.layer t)" unfolding Finite_Bounded_Graph_def
      by (meson Finite_Graph.intro Graph.Efin_imp_Vfin Contained_Graph.edges_ss Contained_Graph.cont_Distance_Bounded cfE_of_finite infinite_super stu.Distance_Bounded_Graph_axioms stu.E'_ss)
    from \<open>Contained_Graph stl' stl\<close> show "Graph.incoming stl' s = {}"
      by (metis Graph.isShortestPath_min_dist_def SP Contained_Graph.cont_incoming_ss bot.extremum_uniqueI stu.b_length_paths_are_terminal(1) stu.path_is_shortest)
      (*by (metis Subgraph.incoming_ss Subgraph_axioms incoming_s_empty subset_empty)*)
    from \<open>Contained_Graph stl' stl\<close> show "Graph.outgoing stl' t = {}"
      by (metis Diff_empty Diff_eq_empty_iff Graph.distinct_nodes_in_V_if_connected(2) Contained_Graph.cont_outgoing_ss stu.no_outgoingD stu.obtain_back_terminal_connected)
      (*by (metis Subgraph.outgoing_ss Subgraph_axioms outgoing_t_empty subset_empty)*)
    from \<open>Graph.E stl \<subseteq> Graph.E stl' \<union> set p\<close> show "\<forall>u\<in>Graph.V stl' - (set (Graph.pathVertices s p) - {s, t}) - {s, t}. Graph.incoming stl' u \<noteq> {} \<and> Graph.outgoing stl' u \<noteq> {}"
    proof auto (* TODO *)
      fix v
      assume "v \<in> Graph.V stl'"
      then have "v \<in> Graph.V stl" using Contained_Graph.vertices_ss[OF \<open>Contained_Graph stl' stl\<close>] by blast
      moreover assume "v \<noteq> s" "v \<noteq> t"
      ultimately obtain u w where IN_OUT: "(u, v) \<in> Graph.E stl" "(v, w) \<in> Graph.E stl"
        by (metis Graph.isPath_bwd_cases Graph.isPath_fwd_cases stu.g'.connected_def stu.st_connected)
      
      assume "v \<notin> set (Graph.pathVertices s p)"
      with \<open>Graph.isPath stl s p t\<close> have "v \<notin> set (Graph.pathVertices_fwd s p)"
        by (simp add: stu.g'.pathVertices_fwd)
      from IN_OUT have "(u, v) \<notin> set p" "(v, w) \<notin> set p" using stu.g'.adjacent_edges_not_on_path[OF \<open>Graph.isPath stl s p t\<close> \<open>v \<notin> set (Graph.pathVertices_fwd s p)\<close>]
        unfolding stu.g'.adjacent_def stu.g'.incoming_def stu.g'.outgoing_def by auto
      with \<open>Graph.E stl \<subseteq> Graph.E stl' \<union> set p\<close> IN_OUT have "(u, v) \<in> Graph.E stl'" "(v, w) \<in> Graph.E stl'" by auto
      then show "Graph.incoming stl' v = {} \<Longrightarrow> False" "Graph.outgoing stl' v = {} \<Longrightarrow> False"
        unfolding Graph.incoming_def Graph.outgoing_def by auto
    qed
  qed
qed

lemma dinitz_phase_concrete_correct: "dinitz_phase_concrete \<le> SPEC (\<lambda>(f', changed). res_dist_increasing_flow f' \<and> changed = (f' \<noteq> f) \<and> (changed \<longrightarrow> cf.connected s t))"
  using dinitz_phase_concrete_refine dinitz_phase_assert_correct by simp
end

context Network
begin
(* TODO rework using changed flag *)
definition dinitz_concrete :: "_ flow nres" where
  "dinitz_concrete \<equiv> do {
    (f, _) \<leftarrow> WHILE\<^sub>T snd (NFlow.dinitz_phase_concrete c s t \<circ> fst) (\<lambda>_. 0, True);
    RETURN f}"

(*
definition dinitz_concrete_aux_rel where
  "dinitz_concrete_aux_rel \<equiv> {((f, m), f)|f m. m \<or> isMaxFlow f}"
term dinitz_concrete_aux_rel
thm dinitz_concrete_aux_rel_def

thm bind_refine
lemma dinitz_concrete_refine: "dinitz_concrete \<le> \<Down> Id dinitz"
  unfolding dinitz_concrete_def dinitz_def
  apply (refine_rcg bind_refine[where R'=dinitz_concrete_aux_rel])
  unfolding dinitz_concrete_aux_rel_def apply clarsimp_all
  defer using NFlow.dinitz_phase_concrete_refine apply clarsimp
*)
find_consts "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
term pred_prod


theorem dinitz_concrete_correct: "dinitz_concrete \<le> SPEC (\<lambda>f. isMaxFlow f)"
  unfolding dinitz_concrete_def
  apply (refine_vcg WHILET_rule[where I="\<lambda>(f', m). NFlow c s t f' \<and> (m \<or> isMaxFlow f')"
          and R="inv_image (less_than_bool <*lex*> res_dist_rel) prod.swap"])
      apply (fastforce simp: res_dist_wf)
     apply (clarsimp_all simp: NFlowI Network_axioms zero_is_flow)
proof -
  fix f
  assume "NFlow c s t f"
  then interpret NFlow c s t f .
  have "dinitz_phase_concrete \<le> SPEC (\<lambda>(f', changed). res_dist_increasing_flow f' \<and> changed = (f' \<noteq> f) \<and> (changed \<longrightarrow> cf.connected s t))"
    using dinitz_phase_concrete_correct .
  also have "... \<le> (spec s'. (case s' of (f', m) \<Rightarrow> NFlow c s t f' \<and> (m \<or> isMaxFlow f')) \<and> (prod.swap s', True, f) \<in> less_than_bool <*lex*> res_dist_rel)"
  proof (clarsimp, intro conjI)
    fix f'
    assume "res_dist_increasing_flow f'" and CON_IF_NEQ: "(f' \<noteq> f) \<longrightarrow> cf.connected s t"
    then show "NFlow c s t f'"
      unfolding res_dist_increasing_flow_def by simp
    then interpret n': NFlow c s t f' .
    from \<open>res_dist_increasing_flow f'\<close> have DIST: "n'.cf.connected s t \<longrightarrow> cf.min_dist s t < n'.cf.min_dist s t"
      unfolding res_dist_increasing_flow_def by simp
    with CON_IF_NEQ show "f' = f \<or> f' \<noteq> f \<and> (f', f) \<in> res_dist_rel" unfolding res_dist_rel_def by blast
    from CON_IF_NEQ show "f' = f \<longrightarrow> isMaxFlow f"
      using Graph.connected_def Graph.isSimplePath_fwd n'.fofu_III_I n'.fofu_II_III n'.isAugmentingPath_def DIST by blast
  qed 
  finally show "dinitz_phase_concrete \<le> (spec s'. (case s' of (f', m) \<Rightarrow> NFlow c s t f' \<and> (m \<or> isMaxFlow f')) \<and> (prod.swap s', True, f) \<in> less_than_bool <*lex*> res_dist_rel)" .
qed

(*
term SPEC
term "if changed then cf.connected s t \<and> res_dist_increasing_flow f' else \<not> cf.connected s t \<and> (f' = f))"
lemma (in NFlow) dinitz_phase_concrete_correct_if:
  "dinitz_phase_concrete \<le> SPEC (\<lambda>(f', changed).
    (if changed then cf.connected s t \<and> res_dist_increasing_flow f' else \<not> cf.connected s t \<and> (f' = f)))"


res_dist_increasing_flow f' \<and> changed = (cf.connected s t \<and> f' \<noteq> f))"
  sorry*)



(*
term "inv_image (less_than_bool <*lex*> res_dist_rel) prod.swap"
theorem dinitz_concrete_correct: "dinitz_concrete \<le> SPEC (\<lambda>f. isMaxFlow f)"
  unfolding dinitz_concrete_def
  apply (refine_vcg WHILET_rule[where I="\<lambda>(f', m). NFlow c s t f' \<and> (m \<or> isMaxFlow f')"
          and R="inv_image (less_than_bool <*lex*> res_dist_rel) prod.swap"])
      apply (fastforce simp: res_dist_wf)
     apply (simp add: NFlowI Network_axioms zero_is_flow)
    apply simp
   defer apply simp

proof clarsimp
  fix f
  assume "NFlow c s t f"
  then interpret n: NFlow c s t f .
  thm n.dinitz_phase_concrete_correct
  have "n.dinitz_phase_concrete \<le> SPEC (\<lambda>(f', changed). n.res_dist_increasing_flow f' \<and> changed = (f' \<noteq> f))"
    using n.dinitz_phase_concrete_correct .
  also have "... \<le> (spec s'. (case s' of (f', m) \<Rightarrow> NFlow c s t f' \<and> (m \<or> isMaxFlow f')) \<and> (prod.swap s', True, f) \<in> less_than_bool <*lex*> res_dist_rel)"
  proof (clarsimp, intro conjI)
    fix f'
    assume "n.res_dist_increasing_flow f'"
    then show "NFlow c s t f'"
      unfolding n.res_dist_increasing_flow_def by simp
    then interpret n': NFlow c s t f' .
    from \<open>n.res_dist_increasing_flow f'\<close> have DIST: "n'.cf.connected s t \<longrightarrow> n.cf.min_dist s t < n'.cf.min_dist s t"
      unfolding n.res_dist_increasing_flow_def by simp

    then show "NFlow c s t f' \<and> (f' = f \<longrightarrow> isMaxFlow f) \<and> (f' = f \<or> f' \<noteq> f \<and> (f', f) \<in> res_dist_rel)"
      unfolding n.res_dist_increasing_flow_def apply auto
        apply (meson Graph.connected_def Graph.isSimplePath_fwd n.ford_fulkerson(1) n.isAugmentingPath_def)
      unfolding res_dist_rel_def apply auto oops


      thm res_dist_rel_def

theorem dinitz_concrete_correct: "dinitz_concrete \<le> SPEC (\<lambda>f. isMaxFlow f)"
  unfolding dinitz_concrete_def
  apply (refine_vcg WHILET_rule[where I="\<lambda>(f', m). NFlow c s t f' \<and> (m \<or> isMaxFlow f')"
          and R="inv_image (less_than_bool <*lex*> res_dist_rel) prod.swap"])
      apply (fastforce simp: res_dist_wf)
     apply (simp add: NFlowI Network_axioms zero_is_flow)
    apply simp
   defer apply simp

proof clarsimp
  fix f
  assume "NFlow c s t f"
  then interpret n: NFlow c s t f .
  thm n.dinitz_phase_concrete_correct'
  have "n.dinitz_phase_concrete \<le> SPEC (\<lambda>(f', changed). n.res_dist_increasing_flow f' \<and> (changed \<longleftrightarrow> n.val < Flow.val c s f'))"
    using n.dinitz_phase_concrete_correct' sorry
  also have "... \<le> (spec s'. (case s' of (f', m) \<Rightarrow> NFlow c s t f' \<and> (m \<or> isMaxFlow f')) \<and> (prod.swap s', True, f) \<in> less_than_bool <*lex*> res_dist_rel)"
  proof (clarsimp, intro conjI)
    fix f'
    assume "n.res_dist_increasing_flow f'"
    then show "NFlow c s t f'"
      unfolding n.res_dist_increasing_flow_def by simp
    then interpret n': NFlow c s t f' .

    from \<open>n.res_dist_increasing_flow f'\<close> have DIST: "n'.cf.connected s t \<longrightarrow> n.cf.min_dist s t < n'.cf.min_dist s t"
      unfolding n.res_dist_increasing_flow_def by simp
    then show "n.val < n'.val \<or> isMaxFlow f'" apply auto
       apply (simp add: n'.ford_fulkerson(1) Graph.connected_def Graph.isSimplePath_fwd n'.isAugmentingPath_def)
      sorry

    from DIST show "n.val < n'.val \<longrightarrow> (f', f) \<in> res_dist_rel"
      unfolding res_dist_rel_def
      apply auto
      by (meson Graph.connected_def Graph.isSimplePath_fwd isMaxFlow_def less_le_not_le n'.Flow_axioms n.fofu_III_I n.fofu_II_III n.isAugmentingPath_def)+

    oops

theorem dinitz_concrete_correct: "dinitz_concrete \<le> SPEC (\<lambda>f. isMaxFlow f)"
  unfolding dinitz_concrete_def
  apply (refine_vcg WHILET_rule[where I="\<lambda>(f', m). NFlow c s t f' \<and> (m \<or> isMaxFlow f')"
          and R="inv_image (less_than_bool <*lex*> res_dist_rel) prod.swap"])
      apply (fastforce simp: res_dist_wf)
     apply (simp add: NFlowI Network_axioms zero_is_flow)
    apply simp
   defer apply simp

proof clarsimp
  fix f
  assume "NFlow c s t f"
  then interpret n: NFlow c s t f .
  thm n.dinitz_phase_concrete_correct'
  have "n.dinitz_phase_concrete \<le> SPEC (\<lambda>(f', changed). n.res_dist_increasing_flow f' \<and> (changed \<or> f' = f \<and> isMaxFlow f))"
    using n.dinitz_phase_concrete_correct' .
  also have "... \<le> (spec s'. (case s' of (f', m) \<Rightarrow> NFlow c s t f' \<and> (m \<or> isMaxFlow f')) \<and> (prod.swap s', True, f) \<in> less_than_bool <*lex*> res_dist_rel)"
  proof (clarsimp, intro conjI)
    fix f'
    assume "n.res_dist_increasing_flow f'"
    then show "NFlow c s t f'"
      unfolding n.res_dist_increasing_flow_def by simp
    then interpret n': NFlow c s t f' .

    from \<open>n.res_dist_increasing_flow f'\<close> have DIST: "n'.cf.connected s t \<longrightarrow> n.cf.min_dist s t < n'.cf.min_dist s t"
      unfolding n.res_dist_increasing_flow_def by simp
    then show "n.val < n'.val \<or> isMaxFlow f'" apply auto
       apply (simp add: n'.ford_fulkerson(1) Graph.connected_def Graph.isSimplePath_fwd n'.isAugmentingPath_def)
      sorry

    from DIST show "n.val < n'.val \<longrightarrow> (f', f) \<in> res_dist_rel"
      unfolding res_dist_rel_def
      apply auto
      by (meson Graph.connected_def Graph.isSimplePath_fwd isMaxFlow_def less_le_not_le n'.Flow_axioms n.fofu_III_I n.fofu_II_III n.isAugmentingPath_def)+

      oops*)
end
end
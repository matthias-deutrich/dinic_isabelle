theory Original_Dinitz_Components
  imports Graph_Transpose
    Graph_Restriction
    Network_Utils
begin

interpretation Refine_Monadic_Syntax .

lemma nfoldli_to_fold: "nfoldli l (\<lambda>_. True) (\<lambda>x s. return (f x s)) s = return (fold f l s)"
  by (induction l arbitrary: s) auto

subsection \<open>Primitives\<close>
definition deleteEdge :: "edge \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "deleteEdge e c \<equiv> c(e := 0)"

text \<open>See EdmondsKarp_Impl.augment_edge\<close>
definition subtractEdge :: "edge \<Rightarrow> ('capacity::linordered_idom) \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "subtractEdge e cap c \<equiv> c(e := c e - cap)"

definition (in Graph) transferEdge :: "edge \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "transferEdge e c' \<equiv> c'(e := c e)"
\<comment> \<open>Primitives\<close>






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
  "transferEdgesRefine S c' \<equiv> foreach S (return \<circ>\<circ> transferEdge) c'"

lemma transferEdge_alt: "transferEdge e c' = (\<lambda>e'. if e' = e then c e' else c' e')"
  unfolding transferEdge_def by fastforce

definition transferEdgesRefineInvar :: "edge set \<Rightarrow> _ graph \<Rightarrow> edge set \<Rightarrow> _ graph \<Rightarrow> bool" where
  "transferEdgesRefineInvar S c' it c'' \<equiv> c'' = (\<lambda>e. if e \<in> S - it then c e else c' e)"

lemma transferEdgesRefine_correct:
  "finite S \<Longrightarrow> transferEdgesRefine S c' \<le> return (transferEdges S c')"
  unfolding transferEdgesRefine_def transferEdges_def
  apply (refine_vcg FOREACH_rule[where I="transferEdgesRefineInvar S c'"])
  unfolding transferEdgesRefineInvar_def transferEdge_alt by fastforce+

lemma transferEdges_capcomp:
  "Capacity_Compatible c' c \<Longrightarrow> Capacity_Compatible (transferEdges S c') c"
  unfolding transferEdges_def
  by unfold_locales (simp add: Capacity_Compatible.cap_compatible)

lemma transferEdges_E: "Graph.E (transferEdges S c') = Graph.E c' - S \<union> (S \<inter> E)"
  unfolding Graph.E_def transferEdges_def by auto

lemma transferEdges_ss_E: "S \<subseteq> E \<Longrightarrow> Graph.E (transferEdges S c') = Graph.E c' \<union> S"
  using transferEdges_E by blast
end

interpretation transferEdges_symmetric:
  Symmetric_Graph_Algorithms "Graph.transferEdgesRefine c S" "Graph.transferEdgesRefine (c\<^sup>T) (prod.swap ` S)" for c S
  unfolding Graph.transferEdgesRefine_def
  apply (intro Symmetric_Graph_AlgorithmsI)
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
definition ebfsPhase :: "node set \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfsPhase V\<^sub>i c' Q \<equiv> foreach Q
    (\<lambda>u (c', Q'). do {
      let S = E `` {u} - V\<^sub>i;
      c' \<leftarrow> transferEdgesRefine ({u} \<times> S) c';
      let Q' = Q' \<union> S;
      return (c', Q')
    })
    (c', {})"

definition ebfsPhaseInvar :: "node \<Rightarrow> nat \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfsPhaseInvar s n c\<^sub>i Q \<equiv> \<lambda>(c', Q').
    Capacity_Compatible c' c
    \<and> Graph.E c' = Graph.E c\<^sub>i \<union> E \<inter> (exactDistNodes n s - Q) \<times> Q'
    \<and> Q' = exactDistNodes (Suc n) s \<inter> E `` (exactDistNodes n s - Q)"
end

context Bounded_Source_Shortest_Path_Union
begin
lemma ebfsPhase_initial: "ebfsPhaseInvar s n c' (exactDistNodes n s) (c', {})"
  unfolding ebfsPhaseInvar_def by simp intro_locales

lemma ebfs_phase_final:
  assumes INVAR: "ebfsPhaseInvar s b c' {} (c'', Q')"
  shows "Bounded_Source_Shortest_Path_Union c'' c s (Suc b) \<and> Q' = exactDistNodes (Suc b) s"
proof
  interpret g'': Graph c'' .
  from INVAR have "Capacity_Compatible c'' c"
    and E'_EQ: "Graph.E c'' = Graph.E c' \<union> E \<inter> exactDistNodes b s \<times> Q'"
    and Q'_EQ: "Q' = exactDistNodes (Suc b) s \<inter> E `` exactDistNodes b s"
    unfolding ebfsPhaseInvar_def by auto
  then interpret cap_comp: Capacity_Compatible c'' c by simp

  have "exactDistNodes (Suc b) s \<subseteq> E `` exactDistNodes b s"
  proof
    fix v
    assume "v \<in> exactDistNodes (Suc b) s"
    then obtain p where "isShortestPath s p v" "length p = Suc b" unfolding exactDistNodes_def
      by (fastforce elim: obtain_shortest_path simp: isShortestPath_min_dist_def)
    then obtain u p\<^sub>u where "isShortestPath s p\<^sub>u u" "length p\<^sub>u = b" "(u, v) \<in> E"
      by (metis isShortestPath_min_dist_def min_dist_suc obtain_shortest_path connected_def)
    then show "v \<in> E `` exactDistNodes b s" unfolding exactDistNodes_def isShortestPath_min_dist_def
      using isPath_rtc connected_edgeRtc by fastforce
  qed
  with Q'_EQ show "Q' = exactDistNodes (Suc b) s" by blast
  with E'_EQ have E'_EQ: "g''.E = E' \<union> E \<inter> exactDistNodes b s \<times> exactDistNodes (Suc b) s"
    by simp

  show "Bounded_Source_Shortest_Path_Union c'' c s (Suc b)"
  proof (unfold_locales, intro pair_set_eqI)
    fix u v
    assume "(u, v) \<in> g''.E"
    then consider (OLD) "(u, v) \<in> E'"
      | (NEW) "(u, v) \<in> E \<inter> exactDistNodes b s \<times> exactDistNodes (Suc b) s"
      using E'_EQ by blast
    then show "(u, v) \<in> \<Union> {set p |p. \<exists>t\<in>V. isBoundedShortestPath (Suc b) c s p t}"
    proof cases
      case OLD
      then show ?thesis
        using source_path_union unfolding isBoundedShortestPath_def by fastforce
    next
      case NEW
      then have "connected s u" "Suc (min_dist s u) = min_dist s v" "(u, v) \<in> E" "min_dist s v = Suc b"
        unfolding exactDistNodes_def by auto
      then obtain p where SP: "isShortestPath s (p @ [(u, v)]) v"
        using obtain_shortest_path shortestPath_append_edge by meson
      with \<open>min_dist s v = Suc b\<close> have "length p = b" unfolding isShortestPath_min_dist_def by simp
      moreover note SP \<open>(u, v) \<in> E\<close>
      ultimately show ?thesis unfolding V_def isBoundedShortestPath_def by fastforce
    qed
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. \<exists>t\<in>V. isBoundedShortestPath (Suc b) c s p t}"
    then obtain t p where "(u, v) \<in> set p" "isShortestPath s p t" "length p \<le> Suc b"
      unfolding isBoundedShortestPath_def by blast
    then obtain p' where SP: "isShortestPath s (p' @ [(u, v)]) v" and LEN: "length p' \<le> b"
      by (fastforce dest: split_list isShortestPath.split_around_edge)
    then have "(u, v) \<in> E" by (simp add: isPath_append isShortestPath_def)
    from LEN consider (LEN_LE) "length p' < b" | (LEN_EQ) "length p' = b" by linarith
    then show "(u, v) \<in> g''.E"
    proof cases
      case LEN_LE
      with \<open>(u, v) \<in> E\<close> have "length (p' @ [(u, v)]) \<le> b" "v \<in> V"
        unfolding V_def by auto
      with SP show ?thesis using E'_EQ unfolding source_path_union isBoundedShortestPath_def by fastforce
    next
      case LEN_EQ
      with SP have "v \<in> exactDistNodes (Suc b) s"
        unfolding exactDistNodes_def isShortestPath_min_dist_def connected_def by auto
      moreover from SP LEN_EQ have "u \<in> exactDistNodes b s"
        using split_shortest_path unfolding exactDistNodes_def isShortestPath_min_dist_def connected_def
        by fastforce
      moreover note \<open>(u, v) \<in> E\<close>
      ultimately show ?thesis using E'_EQ by blast
    qed
  qed
qed

context
  assumes FINITE_REACHABLE: "finite (reachableNodes s)"
begin
lemma ebfs_phase_step:
  assumes Q: "u \<in> Q" "Q \<subseteq> exactDistNodes b s"
    and INVAR: "ebfsPhaseInvar s b c' Q (c'', Q')"
  defines "S \<equiv> E `` {u} - (Graph.V c' \<union> {s})"
  shows "transferEdgesRefine ({u} \<times> S) c'' \<le> (spec c'''. ebfsPhaseInvar s b c' (Q - {u}) (c''', Q' \<union> S))"
proof -
  from Q have "connected s u" unfolding exactDistNodes_def by blast
  then have "E `` {u} \<subseteq> reachableNodes s"
    unfolding reachableNodes_def using connected_append_edge by blast
  with FINITE_REACHABLE have "finite S" unfolding S_def using finite_subset by blast
  then have "transferEdgesRefine ({u} \<times> S) c'' \<le> return (transferEdges ({u} \<times> S) c'')"
    using transferEdgesRefine_correct by simp
  also have "... \<le> (spec c'''. ebfsPhaseInvar s b c' (Q - {u}) (c''', Q' \<union> S))"
    unfolding ebfsPhaseInvar_def
  proof (clarify, refine_vcg)
    interpret g'': Graph c'' .
    from INVAR have "Capacity_Compatible c'' c"
      and E'_EQ: "Graph.E c'' = Graph.E c' \<union> E \<inter> (exactDistNodes b s - Q) \<times> Q'"
      and Q'_EQ: "Q' = exactDistNodes (Suc b) s \<inter> E `` (exactDistNodes b s - Q)"
      unfolding ebfsPhaseInvar_def by auto
    then interpret cap_comp: Capacity_Compatible c'' c by simp

    show "Capacity_Compatible (transferEdges ({u} \<times> S) c'') c"
      using \<open>Capacity_Compatible c'' c\<close> transferEdges_capcomp by blast
    from Q have "E `` {u} \<subseteq> boundedReachableNodes (Suc b) s"
      unfolding boundedReachableNodes_alt using exactDistNodes_reachable_ss by blast
    then have S_alt: "S = exactDistNodes (Suc b) s \<inter> E `` {u}"
      unfolding S_def exactDistNodes_alt using V'_boundedReachable by blast
    with Q Q'_EQ show "Q' \<union> S = exactDistNodes (Suc b) s \<inter> E `` (exactDistNodes b s - (Q - {u}))"
      by blast

    have "{u} \<times> S \<subseteq> E" unfolding S_def by blast
    then have "Graph.E (transferEdges ({u} \<times> S) c'') = E' \<union> E \<inter> ((exactDistNodes b s - Q) \<times> Q' \<union> {u} \<times> S)"
      using transferEdges_ss_E E'_EQ by blast
    also have "... = E' \<union> E \<inter> (exactDistNodes b s - (Q - {u})) \<times> (Q' \<union> S)"
      unfolding S_alt Q'_EQ using Q by blast
    finally show "Graph.E (transferEdges ({u} \<times> S) c'') = E' \<union> E \<inter> (exactDistNodes b s - (Q - {u})) \<times> (Q' \<union> S)" .
  qed
  finally show ?thesis .
qed

lemma ebfs_phase_correct:
  "ebfsPhase (Graph.V c' \<union> {s}) c' (exactDistNodes b s) \<le> SPEC (\<lambda>(c'', Q'). Bounded_Source_Shortest_Path_Union c'' c s (Suc b) \<and> Q' = exactDistNodes (Suc b) s)"
  unfolding ebfsPhase_def
  apply (refine_vcg FOREACH_rule[where I="ebfsPhaseInvar s b c'"])
  using FINITE_REACHABLE finite_subset exactDistNodes_reachable_ss boundedReachableNodes_ss apply meson
  using ebfsPhase_initial ebfs_phase_step ebfs_phase_final by simp_all
end
end
\<comment> \<open>Extended Breadth First Search phase\<close>

subsubsection \<open>Extended Breadth First Search Outer Loop\<close>
context Graph
begin
(* TODO curry *)

definition ebfs' :: "node \<Rightarrow> _ graph nres" where
  "ebfs' s \<equiv> do {
    (c', _, _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q, _, _). Q \<noteq> {})
      (\<lambda>(c', Q, V\<^sub>i, n). do {
        (c', Q') \<leftarrow> ebfsPhase V\<^sub>i c' Q;
        let V\<^sub>i = V\<^sub>i \<union> Q';
        return (c', Q', V\<^sub>i, Suc n)
      })
      ((\<lambda>_. 0), {s}, {s}, 0);
    return c'
  }"

definition ebfs'Invar :: "node \<Rightarrow> (_ graph \<times> node set \<times> node set \<times> nat) \<Rightarrow> bool" where
  "ebfs'Invar s \<equiv> \<lambda>(c', Q, V\<^sub>i, n).
    Bounded_Source_Shortest_Path_Union c' c s n
    \<and> Q = exactDistNodes n s
    \<and> V\<^sub>i = boundedReachableNodes n s"

lemma ebfs'_final:
  assumes INVAR: "ebfs'Invar s (c', {}, V\<^sub>i, n)"
  shows "Source_Shortest_Path_Union c' c s"
proof -
  from INVAR interpret Bounded_Source_Shortest_Path_Union c' c s n unfolding ebfs'Invar_def by blast

  show ?thesis
  proof (unfold_locales, intro equalityI subsetI)
    fix e
    assume "e \<in> \<Union> {set p |p. \<exists>t\<in>V. isShortestPath s p t}"
    then obtain p t where P: "e \<in> set p" "t \<in> V" "isShortestPath s p t" by blast
    have "length p < n"
    proof (rule ccontr)
      assume "\<not> length p < n"
      with P obtain p' u where "isShortestPath s p' u" "length p' = n"
        using split_list_min_len split_shortest_path by (metis not_le)
      then have "u \<in> exactDistNodes n s"
        unfolding exactDistNodes_def isShortestPath_min_dist_def connected_def by auto
      with INVAR show False unfolding ebfs'Invar_def by simp
    qed
    with P show "e \<in> E'" using source_path_union unfolding isBoundedShortestPath_def by fastforce
  qed (auto simp: source_path_union isBoundedShortestPath_def)
qed

context
  fixes s
  assumes FINITE_REACHABLE: "finite (reachableNodes s)"
begin

(* TODO fix this hot mess *)
lemma ebfs'_step:
  assumes INVAR: "ebfs'Invar s (c', Q, V\<^sub>i, n)" and Q: "Q \<noteq> {}"
  shows "ebfsPhase V\<^sub>i c' Q \<le> SPEC (\<lambda>(c'', Q'). ebfs'Invar s (c'', Q', V\<^sub>i \<union> Q', Suc n) \<and> Suc n \<le> card (reachableNodes s))"
proof -
  from INVAR have "Bounded_Source_Shortest_Path_Union c' c s n" and VI: "V\<^sub>i = boundedReachableNodes n s"
    unfolding ebfs'Invar_def by auto
  then interpret Bounded_Source_Shortest_Path_Union c' c s n by blast

  from VI have "ebfsPhase V\<^sub>i c' Q = ebfsPhase (Graph.V c' \<union> {s}) c' Q"
    using V'_boundedReachable by simp
  also from INVAR have "... \<le> SPEC (\<lambda>(c'', Q'). Bounded_Source_Shortest_Path_Union c'' c s (Suc n) \<and> Q' = exactDistNodes (Suc n) s)"
    using ebfs_phase_correct[OF FINITE_REACHABLE] unfolding ebfs'Invar_def by blast
  also have "... \<le> SPEC (\<lambda>(c'', Q'). ebfs'Invar s (c'', Q', V\<^sub>i \<union> Q', Suc n) \<and> Suc n \<le> card (reachableNodes s))"
  proof (intro SPEC_rule, clarify, intro conjI)
    from INVAR Q obtain p u where "isShortestPath s p u" "length p = n"
      unfolding ebfs'Invar_def exactDistNodes_def
      using obtain_shortest_path isShortestPath_min_dist_def by simp metis
    then have "card (set (pathVertices s p)) = Suc n" apply (auto dest!: shortestPath_is_simple simp: isSimplePath_def)
      using length_pathVertices_eq distinct_card by fastforce (* TODO *)
    with \<open>isShortestPath s p u\<close>[THEN shortestPath_is_path, THEN pathVertices_reachable] show "Suc n \<le> card (reachableNodes s)"
      by (metis FINITE_REACHABLE card_mono)
  qed (simp add: ebfs'Invar_def VI exactDistNodes_alt boundedReachableNodes_alt)
  finally show ?thesis .
qed

theorem ebfs'_correct: "ebfs' s \<le> (spec c'. Source_Shortest_Path_Union c' c s)"
  unfolding ebfs'_def
  apply (refine_vcg WHILET_rule[where I="ebfs'Invar s"
      and R="inv_image (greater_bounded (card (reachableNodes s))) (snd \<circ> snd \<circ> snd)"])

  apply blast

  subgoal
    unfolding ebfs'Invar_def exactDistNodes_def
    apply auto
    apply unfold_locales
    unfolding Graph.E_def isBoundedShortestPath_def
    by (auto simp: boundedReachableNodes_def)

  using ebfs'_step ebfs'_final by simp_all
end

definition ebfs :: "node \<Rightarrow> _ graph nres" where
  "ebfs s \<equiv> do {
    (c', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q, _). Q \<noteq> {})
      (\<lambda>(c', Q, V\<^sub>i). do {
        (c', Q') \<leftarrow> ebfsPhase V\<^sub>i c' Q;
        let V\<^sub>i = V\<^sub>i \<union> Q';
        return (c', Q', V\<^sub>i)
      })
      ((\<lambda>_. 0), {s}, {s});
    return c'
  }"

lemma ebfs_refine:
  notes [refine_dref_RELATES] = RELATESI[of "{((a, b, c), a, b, c, d) |a b c d. True}"]
  shows "ebfs s \<le> \<Down> Id (ebfs' s)"
  unfolding ebfs'_def ebfs_def
  apply refine_rcg
      apply refine_dref_type
  by auto

lemma ebfs_correct:
  "finite (reachableNodes s) \<Longrightarrow> ebfs s \<le> (spec c'. Source_Shortest_Path_Union c' c s)"
  using ebfs_refine ebfs'_correct conc_trans_additional(5) by blast
end
\<comment> \<open>Extended Breadth First Search Outer Loop\<close>

subsubsection \<open>Backward EBFS\<close>
definition (in Graph) ebfsBackward :: "node \<Rightarrow> _ graph nres" where
  "ebfsBackward t \<equiv> do {
    (c', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q, _). Q \<noteq> {})
      (\<lambda>(c', Q, V\<^sub>i). do {
        (c', Q') \<leftarrow> foreach Q
          (\<lambda>u (c', Q'). do {
            let S = E\<inverse> `` {u} - V\<^sub>i;
            c' \<leftarrow> transferEdgesRefine (S \<times> {u}) c';
            let Q' = Q' \<union> S;
            return (c', Q')
          })
          (c', {});
        let V\<^sub>i = V\<^sub>i \<union> Q';
        return (c', Q', V\<^sub>i)
      })
      ((\<lambda>_. 0), {t}, {t});
    return c'
  }"


(* TODO improve *)
lemma symmetric_ebfs: "Symmetric_Graph_Algorithms (swap_args2 Graph.ebfsBackward u) (swap_args2 Graph.ebfs u)"
proof (intro Symmetric_Graph_AlgorithmsI, unfold swap_args2_def)
  fix c' :: "('capacity'::linordered_idom) graph"
  note[refine_dref_RELATES] = RELATESI[of transpose_graph_rel]
  show "Graph.ebfsBackward c' u \<le> \<Down> transpose_graph_rel (Graph.ebfs (c'\<^sup>T) u)"
    unfolding Graph.ebfsBackward_def Graph.ebfs_def Graph.ebfsPhase_def
    apply (refine_rcg FOREACH_refine_rcg[where \<alpha>=id], refine_dref_type)
            apply (all \<open>(auto simp: transpose_graph_rel_def; fail)?\<close>)
    apply (simp add: transferEdges_symmetric.conc_simp)
    by (simp add: transpose_graph_rel_def product_swap)

  show "Graph.ebfs c' u \<le> \<Down> transpose_graph_rel (Graph.ebfsBackward (c'\<^sup>T) u)"
    unfolding Graph.ebfsBackward_def Graph.ebfs_def Graph.ebfsPhase_def
    apply (refine_rcg FOREACH_refine_rcg[where \<alpha>=id])
            apply refine_dref_type
            apply (all \<open>(auto simp: transpose_graph_rel_def; fail)?\<close>)
    apply (simp add: transferEdges_symmetric.conc_simp)
    by (simp add: transpose_graph_rel_def product_swap)
qed

(* TODO simplify and extract *)
lemma symmetric_spu: "Target_Shortest_Path_Union c' c t = Source_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t"
proof
  assume "Target_Shortest_Path_Union c' c t"
  then interpret Target_Shortest_Path_Union c' c t .
  show "Source_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t"
  proof
    show "\<And>e. (c'\<^sup>T) e = 0 \<or> (c\<^sup>T) e = 0 \<or> (c'\<^sup>T) e = (c\<^sup>T) e"
      using cap_compatible by fastforce
    show "Graph.E (c'\<^sup>T) = \<Union> {set p |p. \<exists>s \<in> Graph.V (c\<^sup>T). Graph.isShortestPath (c\<^sup>T) t p s}"
    proof (simp, intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> E'\<inverse>"
      then obtain s p where "(v, u) \<in> set p" "s \<in> V" "isShortestPath s p t"
        using target_path_union by blast
      then have "(u, v) \<in> set (transpose_path p)" "isShortestPath s (transpose_path (transpose_path p)) t"
        by auto
      with \<open>s \<in> V\<close> show "(u, v) \<in> \<Union> {set p |p. \<exists>s\<in>V. isShortestPath s (transpose_path p) t}"
        by blast
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. \<exists>s\<in>V. isShortestPath s (transpose_path p) t}"
      then show "(u, v) \<in> E'\<inverse>" using target_path_union by fastforce
    qed
  qed
next
  interpret Graph_Comparison c' c .
  assume "Source_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t"
  then interpret spu: Source_Shortest_Path_Union "c'\<^sup>T" "c\<^sup>T" t by simp
  show "Target_Shortest_Path_Union c' c t"
  proof
    show "\<And>e. c' e = 0 \<or> c e = 0 \<or> c' e = c e"
      using spu.cap_compatible by fastforce
    show "E' = \<Union> {set p |p. \<exists>s\<in>V. isShortestPath s p t}"
    proof (intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> E'"
      then obtain s p where "(v, u) \<in> set p" "s \<in> V" "spu.isShortestPath t p s"
        using spu.source_path_union by fastforce
      then show "(u, v) \<in> \<Union> {set p |p. \<exists>s\<in>V. isShortestPath s p t}"
        by fastforce
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. \<exists>s\<in>V. isShortestPath s p t}"
      then obtain s p where "(u, v) \<in> set p" "s \<in> V" "isShortestPath s p t"
        by blast
      then have "(v, u) \<in> set (transpose_path p)" "spu.isShortestPath t (transpose_path p) s" by auto
      with \<open>s \<in> V\<close> have "(v, u) \<in> spu.E'" using spu.source_path_union transpose_V by blast
      then show "(u, v) \<in> Graph.E c'" by simp
    qed
  qed
qed

lemma (in Graph) ebfsBackward_correct:
  assumes FINITE_REACHED_FROM: "finite {u. connected u t}"
  shows "ebfsBackward t \<le> (spec c'. Target_Shortest_Path_Union c' c t)"
proof -
  interpret Symmetric_Graph_Algorithms "swap_args2 Graph.ebfsBackward t" "swap_args2 Graph.ebfs t"
    using symmetric_ebfs .
  have "swap_args2 Graph.ebfsBackward t c \<le> (spec c'. Target_Shortest_Path_Union c' c t)"
  proof (intro transfer_spec[where abst'="\<lambda>c c'. Source_Shortest_Path_Union c' c t"])
    show "\<And>c c'. Target_Shortest_Path_Union c' c t = Source_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t "
      using symmetric_spu .
    from FINITE_REACHED_FROM have "finite (Graph.reachableNodes (c\<^sup>T) t)"
      unfolding Graph.reachableNodes_def by simp
    then show "swap_args2 Graph.ebfs t (c\<^sup>T) \<le> (spec c'. Source_Shortest_Path_Union c' (c\<^sup>T) t)"
      using Graph.ebfs_correct by fastforce
  qed
  then show ?thesis by simp
qed
\<comment> \<open>Backward EBFS\<close>

subsubsection \<open>Building a dual layering\<close>
context Graph
begin
(* TODO bounded version *)
definition buildDualLayering :: "node \<Rightarrow> node \<Rightarrow> _ graph nres" where
  "buildDualLayering s t \<equiv> do {
    sl \<leftarrow> ebfs s;
    stl \<leftarrow> Graph.ebfsBackward sl t;
    return stl
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
  then have "ebfs s \<le> (spec sl. Source_Shortest_Path_Union sl c s)" by (rule ebfs_correct)
  also have "... \<le> (spec sl. Graph.ebfsBackward sl t \<le> (spec c'. Dual_Shortest_Path_Union c' c s t))"
  proof (rule SPEC_rule)
    fix c'
    assume "Source_Shortest_Path_Union c' c s"
    then interpret Source_Shortest_Path_Union c' c s .

    have "{u. g'.connected u t} \<subseteq> V' \<union> {t}"
      using g'.distinct_nodes_in_V_if_connected by auto
    then have "finite {u. g'.connected u t}" using finite_V V_ss by (simp add: finite_subset)
    then have "g'.ebfsBackward t \<le> (spec c''. Target_Shortest_Path_Union c'' c' t)"
      by (rule g'.ebfsBackward_correct)
    also from \<open>Source_Shortest_Path_Union c' c s\<close> have "... \<le> (spec c''. Dual_Shortest_Path_Union c'' c s t)"
      using SPEC_rule Dual_Shortest_Path_Union_right_leftI by metis
    finally show "g'.ebfsBackward t \<le> (spec c''. Dual_Shortest_Path_Union c'' c s t)" .
  qed
  finally show "ebfs s \<le> (spec sl. Graph.ebfsBackward sl t \<le> (spec c'. Dual_Shortest_Path_Union c' c s t))" .
qed
end
\<comment> \<open>Building a dual layering\<close>
\<comment> \<open>Extended BFS\<close>

subsection \<open>Pathfinding\<close>

text \<open>Used primitives:
  - RES (outgoing u) / checking outgoing u for emptiness
  - checking whether s is a vertex
  - list Cons\<close>

definition (in Graph) greedyPathFinding :: "node \<Rightarrow> node \<Rightarrow> path option nres" where
  "greedyPathFinding s t \<equiv> do {
    if s = t
      then return (Some [])
      else do {
        (p, _, found, _) \<leftarrow> WHILE\<^sub>T
          (\<lambda>(_, _, _, brk). \<not> brk)
          (\<lambda>(p, u, _, _). do {
            if (incoming u = {})
              then return (p, u, False, True)
            else do {
              e \<leftarrow> RES (incoming u);
              let p = e # p;
              let u = fst e;
              let found = (u = s);
              return (p, u, found, found)}})
          ([], t, False, t \<notin> V);
        return (if found then Some p else None)}}"

(* TODO prettify *)
lemma (in Dual_Layer_Graph) greedyPathFinding_correct:
  "greedyPathFinding s t \<le> (select p. isPath s p t)"
  unfolding greedyPathFinding_def SELECT_as_SPEC
  apply (refine_vcg WHILET_rule[where R="inv_image (greater_bounded (min_dist s t)) (length \<circ> fst)"
          and I="\<lambda>(p, u, found, brk). isPath u p t \<and> found = (u = s) \<and> (brk = (incoming u = {}))"])
               apply clarsimp_all
  using isEmpty_def no_incomingD incoming_edges t_in_V_if_nonempty apply blast
     apply (simp add: incoming_def)
    apply (metis connected_inV_iff connected_prepend_edge ex_front_terminal_path in_incomingD isEmpty_def isPath.connected no_incomingD t_in_V_if_nonempty)
   apply (metis b_length_paths_are_terminal(1) le_antisym not_less_eq_eq path_length_bounded)
  by (metis Graph.distinct_nodes_have_in_out_if_connected(2) Graph.distinct_nodes_in_V_if_connected(1) isPath.connected no_incomingD)
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
    [] \<Rightarrow> return 0
  | (e # p) \<Rightarrow> nfoldli p (\<lambda>_. True) (\<lambda>e cap. return (min (c e) cap)) (c e)"

definition subtractPathRefine :: "path \<Rightarrow> _ graph nres" where
  "subtractPathRefine p \<equiv> do {
    cap \<leftarrow> pathCapRefine p;
    c' \<leftarrow> nfoldli p (\<lambda>_. True) (\<lambda>e c'. return (subtractEdge e cap c')) c;
    return c'
  }"

lemma pathCapRefine_correct: "pathCapRefine p = return (if p = [] then 0 else pathCap p)"
  unfolding pathCapRefine_def pathCap_alt
  apply (simp split: list.split add: nfoldli_to_fold)
  by (metis (no_types, lifting) Min.set_eq_fold fold_map fun_comp_eq_conv list.set_map list.simps(15))

lemma subtractPathRefine_correct_aux:
  "distinct p \<Longrightarrow> fold (\<lambda>e c'. subtractEdge e cap c') p c = (\<lambda>e. if e \<in> set p then c e - cap else c e)"
  unfolding subtractEdge_def by (induction p arbitrary: c) auto

lemma subtractPathRefine_correct:
  assumes "distinct p"
  shows "subtractPathRefine p = return (subtract_path p)"
  unfolding subtractPathRefine_def subtract_path_def
  apply (simp split: list.splits add: nfoldli_to_fold pathCapRefine_correct)
  using assms subtractPathRefine_correct_aux by simp
end

definition subtractSkewEdgeRefine :: "edge \<Rightarrow> ('capacity::linordered_idom) \<Rightarrow> _ graph \<Rightarrow> _ graph nres" where
  "subtractSkewEdgeRefine e cap c = do {
    c \<leftarrow> return (subtractEdge e cap c);
    c \<leftarrow> return (subtractEdge (prod.swap e) (- cap) c);
    return c
  }"

lemma subtractSkewEdgeRefine_correct:
  "subtractSkewEdgeRefine e cap c = return (subtractEdge (prod.swap e) (- cap) (subtractEdge e cap c))"
  unfolding subtractSkewEdgeRefine_def by simp
(*
lemma subtractSkewEdgeRefine_correct':
  "subtractSkewEdgeRefine e cap = (\<lambda> c. return (subtractEdge (prod.swap e) (- cap) (subtractEdge e cap c)))"
  unfolding subtractSkewEdgeRefine_def by simp*)

context Graph
begin
definition subtractSkewPathRefine :: "path \<Rightarrow> _ graph nres" where
  "subtractSkewPathRefine p \<equiv> do {
    cap \<leftarrow> pathCapRefine p;
    c' \<leftarrow> nfoldli p (\<lambda>_. True) (\<lambda>e c'. return (subtractEdge e cap c')) c;
    c' \<leftarrow> nfoldli p (\<lambda>_. True) (\<lambda>e c'. return (subtractEdge (prod.swap e) (- cap) c')) c';
    return c'
  }"

lemma subtractSkewPathRefine_correct_aux:
  "distinct p \<Longrightarrow> fold (\<lambda>e c'. subtractEdge (prod.swap e) cap c') p c = (\<lambda>e. if e \<in> (set p)\<inverse> then c e - cap else c e)"
  unfolding subtractEdge_def by (induction p arbitrary: c) auto

lemma subtractSkewPathRefine_correct:
  assumes "distinct p"
  shows "subtractSkewPathRefine p = return (subtract_skew_path p)"
  unfolding subtractSkewPathRefine_def subtract_skew_path_def
  by (auto split: list.splits simp: nfoldli_to_fold pathCapRefine_correct
      subtractPathRefine_correct_aux[OF assms] Graph.subtractSkewPathRefine_correct_aux[OF assms])

(*
definition subtractSkewPathRefine :: "path \<Rightarrow> _ graph nres" where
  "subtractSkewPathRefine p \<equiv> do {
    cap \<leftarrow> pathCapRefine p;
    c' \<leftarrow> nfoldli p (\<lambda>_. True) (\<lambda>e c'. subtractSkewEdgeRefine e cap c') c;
    return c'
  }"

thm nfoldli_to_fold
thm subtractSkewEdgeRefine_correct'
thm subtractSkewPathRefine_correct_aux
lemma subtractSkewPathRefine_correct:
  assumes "distinct p"
  shows "subtractSkewPathRefine p = return (subtract_skew_path p)"
  unfolding subtractSkewPathRefine_def subtract_skew_path_def
  thm subtractPathRefine_correct_aux[OF assms]
  thm Graph.subtractSkewPathRefine_correct_aux[OF assms]
  apply (simp split: list.splits add: nfoldli_to_fold subtractSkewEdgeRefine_correct pathCapRefine_correct)
  using Graph.subtractSkewPathRefine_correct_aux[OF assms] subtractPathRefine_correct_aux[OF assms] sledgehammer
  apply auto
  apply (simp add: Graph.subtractSkewPathRefine_correct_aux[OF assms])
  using subtractPathRefine_correct_aux[OF assms] Graph.subtractSkewPathRefine_correct_aux[OF assms]
  apply clarsimp
  apply auto
  apply (auto simp: Graph.subtractSkewPathRefine_correct_aux[OF assms])


  by (auto split: list.splits simp: nfoldli_to_fold pathCapRefine_correct
      subtractPathRefine_correct_aux[OF assms] Graph.subtractSkewPathRefine_correct_aux[OF assms])
*)
end
\<comment> \<open>Subtracting a path\<close>

subsection \<open>Cleaning\<close>

subsubsection \<open>Deleting a set of edges\<close>
definition deleteEdges :: "edge set \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "deleteEdges S c \<equiv> \<lambda>e. if e \<in> S then 0 else c e"

definition deleteEdgesRefine :: "edge set \<Rightarrow> _ graph \<Rightarrow> _ graph nres" where
  "deleteEdgesRefine S c \<equiv> foreach S (return \<circ>\<circ> deleteEdge) c"

lemma deleteEdgesRefine_correct: "finite R \<Longrightarrow> deleteEdgesRefine R c \<le> return (deleteEdges R c)"
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

subsubsection \<open>Right Pass\<close>

text \<open>This definition slightly deviates from the one presented in Dinitz's original paper, in that
      it works on the set of edge tails, instead of on the edges themselves.\<close>

text \<open>Used primitives:
  - working set operation: adding elements, removing element, checking for emptiness
  - graph operations: checking incoming for emptiness, getting set of outgoing edges, deleting an edge\<close>
definition rightPassRefine :: "node set \<Rightarrow> _ graph \<Rightarrow> _ graph nres" where
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
            return (Q, c)}
          else return (Q, c)})
      (Q, c);
    return c
  }"

(* TODO should be able to change the invariant to \<forall>u v. connected s u \<and> (u, v) \<in> E \<longrightarrow> (u, v) \<in> E'*)
definition rightPassInvar :: "_ graph \<Rightarrow> node \<Rightarrow> (node set \<times>_ graph) \<Rightarrow> bool" where
  "rightPassInvar c s \<equiv> \<lambda>(Q, c'). Subgraph c' c
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
    unfolding finiteProperSubgraph_def Proper_Subgraph_def inv_image_def finite_psubset_def
    using Proper_Subset_Graph.E_pss Finite_Graph.finite_E by blast
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
      using E_ss by fast
    then have "s \<notin> snd ` g'.outgoing u" unfolding g'.incoming_def g'.outgoing_def by fastforce
    with \<open>s \<notin> Q\<close> show ?thesis unfolding Q'_def by blast
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
      using g'.deleteEdges_sg Subgraph_def Subset_Graph.V_ss by fast
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

(* TODO is c' = c needed? *)
lemma (in Distance_Bounded_Graph) rightPassRefine_final:
  assumes SUB: "Subgraph c' c"
    and S_CON: "\<And>u v. connected s u \<Longrightarrow> Graph.connected c' s u \<and> c' (u, v) = c (u, v)"
    and NODE_HAS_IN: "\<forall>u \<in> Graph.V c' - {s}. Graph.incoming c' u \<noteq> {}"
  shows "Source_Path_Union c' c s"
proof -
  from SUB interpret Subgraph c' c .
  interpret g': Distance_Bounded_Graph c' b
    using sub_Distance_Bounded Distance_Bounded_Graph_axioms by blast
  show "Source_Path_Union c' c s"
  proof (unfold_locales, intro pair_set_eqI)
    fix u v
    assume EDGE: "(u, v) \<in> E'"
    then have "u \<in> V'" "v \<in> V'" unfolding g'.V_def by auto
    obtain w where W_CON: "g'.connected w u" and W_NO_IN: "g'.incoming w = {}"
      using g'.obtain_front_terminal_connected by blast
    with \<open>u \<in> V'\<close> have "w \<in> g'.V" by (meson g'.connected_inV_iff)
    with W_NO_IN NODE_HAS_IN have "w = s" by blast
    with W_CON S_CON obtain p where "isPath s p u" using isPath.connecting sub_connected by blast
    with EDGE have "isPath s (p @ [(u, v)]) v" by (simp add: edge'_if_edge isPath_append_edge)
    with \<open>v \<in> V'\<close> show "(u, v) \<in> \<Union> {set p |p. \<exists>t\<in>V. isPath s p t}"
      using vertex'_if_vertex by force
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. \<exists>t\<in>V. isPath s p t}"
    then obtain p p' t where "isPath s (p @ (u, v) # p') t" using split_list by fastforce
    then have "connected s u" "(u, v) \<in> E"
      using connected_def isPath.split_around_edge by blast+
    with S_CON show "(u, v) \<in> E'" unfolding Graph.E_def by simp
  qed
qed

lemma (in Finite_Bounded_Graph) rightPassRefine_correct:
  assumes S_NO_IN: "incoming s = {}"
    and Q_START: "s \<notin> Q" "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}" "finite Q"
  shows "rightPassRefine Q c \<le> (spec c'. Source_Path_Union c' c s)"
  unfolding rightPassRefine_def
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

  let ?Q' = "Q - {u} \<union> snd ` Graph.outgoing c' u"
  assume U_NO_IN: "Graph.incoming c' u = {}"

  (* TODO prettify using the right transitivity lemma *)
  have "deleteEdgesRefine (Graph.outgoing c' u) c' \<le> return (deleteEdges (Graph.outgoing c' u) c')"
    using S_NO_IN U_NO_IN rightPassRefine_step step_assms
    by (blast intro: deleteEdgesRefine_correct)
  also have "... \<le> (spec c''. rightPassInvar c s (?Q', c'') \<and> ((?Q', c''), Q, c') \<in> graphWorkingSetRel)"
    using S_NO_IN U_NO_IN rightPassRefine_step step_assms by simp
  finally show "deleteEdgesRefine (Graph.outgoing c' u) c' \<le> (spec c''. rightPassInvar c s (?Q', c'') \<and> ((?Q', c''), Q, c') \<in> graphWorkingSetRel)" .
next
  fix c'
  assume "rightPassInvar c s ({}, c')"
  then show "Source_Path_Union c' c s" unfolding rightPassInvar_def
    using rightPassRefine_final by simp
qed
\<comment> \<open>Right Pass\<close>

subsubsection \<open>Left Pass\<close>
text \<open>Used primitives:
  - working set operation: adding elements, removing element, checking for emptiness
  - graph operations: checking outgoing for emptiness, getting set of incoming edges, deleting an edge\<close>
definition leftPassRefine :: "node set \<Rightarrow> _ graph \<Rightarrow> _ graph nres" where
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
            return (Q, c)}
          else return (Q, c)})
      (Q, c);
    return c
  }"

(* TODO simplify and unify with dual_spu *)
lemma (in Graph) dual_pu: "Target_Path_Union c' c t = Source_Path_Union (c'\<^sup>T) (c\<^sup>T) t"
proof
  assume "Target_Path_Union c' c t"
  then interpret pu: Target_Path_Union c' c t .
  show "Source_Path_Union (c'\<^sup>T) (c\<^sup>T) t"
  proof
    show "\<And>e. (c'\<^sup>T) e = 0 \<or> (c\<^sup>T) e = 0 \<or> (c'\<^sup>T) e = (c\<^sup>T) e"
      using pu.cap_compatible by fastforce
    show "Graph.E (c'\<^sup>T) = \<Union> {set p |p. \<exists>s \<in> Graph.V (c\<^sup>T). Graph.isPath (c\<^sup>T) t p s}"
    proof (simp, intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> pu.E'\<inverse>"
      then obtain s p where "(v, u) \<in> set p" "s \<in> V" "isPath s p t"
        using pu.target_path_union by blast
      then have "(u, v) \<in> set (transpose_path p)" "isPath s (transpose_path (transpose_path p)) t"
        by auto
      with \<open>s \<in> V\<close> show "(u, v) \<in> \<Union> {set p |p. \<exists>s \<in> V. isPath s (transpose_path p) t}"
        by blast
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. \<exists>s \<in> V. isPath s (transpose_path p) t}"
      then show "(u, v) \<in> pu.E'\<inverse>" using pu.target_path_union by fastforce
    qed
  qed
next
  assume "Source_Path_Union (c'\<^sup>T) (c\<^sup>T) t"
  then interpret pu: Source_Path_Union "c'\<^sup>T" "c\<^sup>T" t by simp
  show "Target_Path_Union c' c t"
  proof
    show "\<And>e. c' e = 0 \<or> c e = 0 \<or> c' e = c e"
      using pu.cap_compatible by fastforce
    show "Graph.E c' = \<Union> {set p |p. \<exists>s \<in> V. Graph.isPath c s p t}"
    proof (intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> Graph.E c'"
      then obtain s p where "(v, u) \<in> set p" "s \<in> V" "pu.isPath t p s"
        using pu.source_path_union by fastforce
      then show "(u, v) \<in> \<Union> {set p |p. \<exists>s \<in> V. Graph.isPath c s p t}"
        by fastforce
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. \<exists>s \<in> V. Graph.isPath c s p t}"
      then obtain s p where "(u, v) \<in> set p" "s \<in> Graph.V c" "Graph.isPath c s p t"
        by blast
      then have "(v, u) \<in> set (transpose_path p)" "pu.isPath t (transpose_path p) s" by auto
      with \<open>s \<in> Graph.V c\<close> have "(v, u) \<in> pu.E'" using pu.source_path_union transpose_V by blast
      then show "(u, v) \<in> Graph.E c'" by simp
    qed
  qed
qed

context Finite_Bounded_Graph
begin
interpretation Symmetric_Graph_Algorithms "leftPassRefine Q" "rightPassRefine Q"
proof
  interpret Symmetric_Graph_Algorithms "deleteEdgesRefine S" "deleteEdgesRefine (S\<inverse>)" for S
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

thm transfer_return
thm transfer_spec



(* TODO cleanup proof *)
theorem leftPassRefine_correct:
  assumes T_NO_OUT: "outgoing t = {}"
    and Q_START: "t \<notin> Q" "\<forall>u \<in> V - Q - {t}. outgoing u \<noteq> {}" "finite Q"
  shows "leftPassRefine Q c \<le> (spec c'. Target_Path_Union c' c t)"
  apply (intro transfer_spec[where abst'="\<lambda>c c'. Source_Path_Union c' c t"])
  using Graph.dual_pu apply blast
  apply (intro Finite_Bounded_Graph.rightPassRefine_correct)
  using assms Finite_Bounded_Graph_axioms by (auto simp: converse_empty_simp)
end

\<comment> \<open>Left Pass\<close>

subsubsection \<open>Cleaning Algorithm on Working Set\<close>

definition cleaningSetRefine :: "node set \<Rightarrow> _ graph \<Rightarrow> _ graph nres" where
  "cleaningSetRefine Q c \<equiv> do {
    c \<leftarrow> rightPassRefine Q c;
    c \<leftarrow> leftPassRefine Q c;
    return c}"

lemma (in Finite_Bounded_Graph) cleaningSetRefine_correct:
  assumes S_NO_IN: "incoming s = {}"
    and T_NO_OUT: "outgoing t = {}"
    and Q_START: "s \<notin> Q" "t \<notin> Q" "\<forall>u \<in> V - Q - {s, t}. incoming u \<noteq> {} \<and> outgoing u \<noteq> {}" "finite Q"
  shows "cleaningSetRefine Q c \<le> (spec c'. Dual_Path_Union c' c s t)"
  unfolding cleaningSetRefine_def
proof (refine_vcg, simp)
  from T_NO_OUT \<open>\<forall>u \<in> V - Q - {s, t}. incoming u \<noteq> {} \<and> outgoing u \<noteq> {}\<close> have "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}"
    by (cases "incoming t = {}") (auto simp: incoming_def outgoing_def V_def)
  with assms have "rightPassRefine Q c \<le> (spec c'. Source_Path_Union c' c s)"
    by (blast intro: rightPassRefine_correct)
  also have "... \<le> (spec ca. leftPassRefine Q ca \<le> (spec c'. Dual_Path_Union c' c s t))"
  proof clarsimp
    fix c'
    assume "Source_Path_Union c' c s"
    then interpret Source_Path_Union c' c s .
    have "leftPassRefine Q c' \<le> (spec c''. Target_Path_Union c'' c' t)"
      apply (intro Finite_Bounded_Graph.leftPassRefine_correct)
          prefer 3 using assms apply simp
         prefer 4 using assms apply simp
        prefer 2 using \<open>outgoing t = {}\<close> outgoing_ss apply blast
      unfolding Finite_Bounded_Graph_def apply auto[1]
      using E_ss g'.Finite_Graph_EI rev_finite_subset apply blast
      using Distance_Bounded_Graph_axioms apply (rule sub_Distance_Bounded)
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
      then have "connected s u" unfolding g'.V_def using Graph.V_def obtain_connected_ST by blast
      with \<open>(u, v) \<in> E\<close> obtain p where "isPath s (p @ [(u, v)]) v" "v \<in> V"
        using connected_def isPath_append_edge V_def by blast
      then have "(u, v) \<in> E'"
        using Graph.isPath_tail ST_path_remains by blast
      then show "g'.outgoing u \<noteq> {}" unfolding g'.outgoing_def by blast
    qed
    also from \<open>Source_Path_Union c' c s\<close> have "... \<le> (spec c''. Dual_Path_Union c'' c s t)"
      by (auto intro: Dual_Path_Union_right_leftI)
    finally show "leftPassRefine Q c' \<le> (spec c''. Dual_Path_Union c'' c s t)" .
  qed
  finally show "rightPassRefine Q c \<le> (spec ca. leftPassRefine Q ca \<le> (spec c'. Dual_Path_Union c' c s t))" .
qed

\<comment> \<open>Cleaning Algorithm on Working Set\<close>

subsubsection \<open>Inner vertices of a path\<close>
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

lemma innerPathVertices_alt: "innerPathVertices p = tl (butlast (Graph.pathVertices u p))"
  by (auto split: list.split simp: Graph.pathVertices.simps(1) Graph.pathVertices_alt)
\<comment> \<open>Inner vertices of a path\<close>

subsubsection \<open>Cleaning Algorithm on Path\<close>
definition cleaningRefine :: "path \<Rightarrow> _ graph \<Rightarrow> _ graph nres" where
  "cleaningRefine p c \<equiv> cleaningSetRefine (set (innerPathVertices p)) c"

lemma (in Dual_Layer_Graph) cleaningRefine_correct:
  assumes "Finite_Graph c" "Contained_Graph c' c"
      and E_SUB: "E \<subseteq> Graph.E c' \<union> set p"
      and PATH: "isPath s p t"
    shows "cleaningRefine p c' \<le> (spec c''. Dual_Path_Union c'' c' s t)"
proof (unfold cleaningRefine_def, intro Finite_Bounded_Graph.cleaningSetRefine_correct)
  from assms interpret Finite_Graph c + Contained_Graph c' c by simp_all

  show "Finite_Bounded_Graph c' (layer t)"
    apply intro_locales
     apply (simp add: Finite_Graph_axioms sub_Finite_Graph)
    by (simp add: Distance_Bounded_Graph_axioms sub_Distance_Bounded)

  show "g'.incoming s = {}"
    by (metis Distance_Bounded_Graph.path_length_bounded Distance_Bounded_Graph_axioms Graph.isPath_distD Graph.min_dist_minD PATH b_length_paths_are_terminal(1) incoming_ss order_antisym subset_empty)

  show "g'.outgoing t = {}"
    by (metis Distance_Bounded_Graph.path_length_bounded Distance_Bounded_Graph_axioms Graph.isPath_distD Graph.min_dist_minD PATH b_length_paths_are_terminal(2) outgoing_ss order_antisym subset_empty)
    (*by (metis Graph.distinct_nodes_in_V_if_connected(2) no_outgoingD obtain_back_terminal_connected)*)

  (* TODO simplify *)
  have inner_V_alt: "set (innerPathVertices p) = set (pathVertices s p) - {s, t}"
  proof (cases "s = t")
    case True
    with PATH show ?thesis
      by (metis Diff_cancel Graph.pathVertices.simps(1) acyclic butlast.simps(1) butlast_tl empty_set innerPathVertices_alt insert_absorb2 isCycle_def list.sel(3) list.simps(15))
  next
    case False
    from PATH have "pathVertices s p = s # (tl (pathVertices s p))"
      by (simp add: Graph.pathVertices_fwd pathVertices_fwd_def)
    moreover from PATH have "pathVertices s p = butlast (pathVertices s p) @ [t]"
      by (metis Graph.isPath_bwd_cases Graph.isPath_tail Graph.pathVertices_alt snoc_eq_iff_butlast' False)
    ultimately have "pathVertices s p = s # (tl (butlast (pathVertices s p))) @ [t]"
      by (metis butlast_tl empty_append_eq_id snoc_eq_iff_butlast' False tl_last)
      (* TODO simplify, probably need to show s, t \<notin> tl (butlast (pathVertices s p)) *)
    then show ?thesis using innerPathVertices_alt
      by (smt (verit, ccfv_threshold) Diff_insert0 Graph.isSimplePath_fwd Graph.pathVertices_fwd PATH Un_Diff_Int Un_insert_right distinct.simps(2) distinct_append empty_set insertCI insert_Diff1 list.simps(15) paths_are_simple set_append sup_bot.right_neutral)
  qed

  show "s \<notin> set (innerPathVertices p)"
       "t \<notin> set (innerPathVertices p)"
       "finite (set (innerPathVertices p))"
    unfolding inner_V_alt by auto

  show "\<forall>u\<in>V' - set (innerPathVertices p) - {s, t}. g'.incoming u \<noteq> {} \<and> g'.outgoing u \<noteq> {}"
  proof (auto simp del: innerPathVertices.simps) (* TODO *)
    fix v
    assume "v \<in> V'"
    then have "v \<in> V" using V_ss by blast
    moreover assume NOT_ST: "v \<noteq> s" "v \<noteq> t"
    ultimately obtain u w where IN_OUT: "(u, v) \<in> E" "(v, w) \<in> E"
      using incoming_def outgoing_def by fastforce
    
    assume "v \<notin> set (innerPathVertices p)"
    with NOT_ST have "v \<notin> set (pathVertices s p)" using inner_V_alt by blast
    with PATH have "v \<notin> set (pathVertices_fwd s p)" using pathVertices_fwd by fastforce
    from IN_OUT have "(u, v) \<notin> set p" "(v, w) \<notin> set p"
      using adjacent_edges_not_on_path[OF PATH \<open>v \<notin> set (pathVertices_fwd s p)\<close>]
      unfolding adjacent_def incoming_def outgoing_def by auto
    with E_SUB IN_OUT have "(u, v) \<in> E'" "(v, w) \<in> E'" by auto
    then show "g'.incoming v = {} \<Longrightarrow> False" "g'.outgoing v = {} \<Longrightarrow> False"
      unfolding Graph.incoming_def Graph.outgoing_def by auto
  qed
qed
\<comment> \<open>Cleaning Algorithm on Path\<close>
\<comment> \<open>Cleaning\<close>

end
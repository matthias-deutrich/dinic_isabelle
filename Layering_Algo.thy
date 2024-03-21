theory Layering_Algo
  imports
    Cleaning_Algo
    EdmondsKarp_Maxflow.Augmenting_Path_BFS
begin

no_notation Heap_Monad.return ("return")

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

context Graph
begin

subsection \<open>Transferring edges to another graph\<close>

definition transfer_edge :: "edge \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "transfer_edge e c' \<equiv> c'(e := c e)"

lemma transfer_edge_alt: "transfer_edge e c' = (\<lambda>e'. if e' = e then c e' else c' e')"
  unfolding transfer_edge_def by fastforce

definition transfer_edges :: "edge set \<Rightarrow> _ graph \<Rightarrow> _ graph" where
  "transfer_edges S c' = (\<lambda>e. if e \<in> S then c e else c' e)"

definition transfer_edges_algo :: "edge set \<Rightarrow> _ graph \<Rightarrow> _ graph nres" where
  "transfer_edges_algo S c' \<equiv> foreach S (\<lambda>e c'. RETURN (transfer_edge e c')) c'"

definition transfer_edges_invar :: "edge set \<Rightarrow> _ graph \<Rightarrow> edge set \<Rightarrow> _ graph \<Rightarrow> bool" where
  "transfer_edges_invar S c' it c'' \<equiv> c'' = (\<lambda>e. if e \<in> S - it then c e else c' e)"

lemma transfer_edges_correct:
  "finite S \<Longrightarrow> transfer_edges_algo S c' \<le> RETURN (transfer_edges S c')"
  unfolding transfer_edges_algo_def transfer_edges_def
  apply (refine_vcg FOREACH_rule[where I="transfer_edges_invar S c'"])
  unfolding transfer_edges_invar_def transfer_edge_alt by fastforce+

lemma transfer_edges_capcomp:
  "CapacityCompatibleGraphs c' c \<Longrightarrow> CapacityCompatibleGraphs (transfer_edges S c') c"
  unfolding transfer_edges_def
  by unfold_locales (simp add: CapacityCompatibleGraphs.cap_compatible)

lemma transfer_edges_E: "Graph.E (transfer_edges S c') = Graph.E c' - S \<union> (S \<inter> E)"
  unfolding Graph.E_def transfer_edges_def by auto

lemma transfer_edges_ss_E: "S \<subseteq> E \<Longrightarrow> Graph.E (transfer_edges S c') = Graph.E c' \<union> S"
  using transfer_edges_E by blast
end

interpretation transfer_edges_dual:
  Dual_Graph_Algorithms "Graph.transfer_edges_algo c S" "Graph.transfer_edges_algo (c\<^sup>T) (prod.swap ` S)" for c S
  unfolding Graph.transfer_edges_algo_def
  apply (intro Dual_Graph_AlgorithmsI)
  apply (all \<open>refine_rcg FOREACH_refine_rcg[where \<alpha>="prod.swap"]\<close>)
  by (auto simp: transpose_graph_rel_def Graph.transfer_edge_def)
\<comment> \<open>Transferring edges to another graph\<close>

subsection \<open>Extended Breadth First Search phase\<close>

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
definition ebfs_phase :: "node set \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfs_phase V\<^sub>i c' Q \<equiv> foreach Q
    (\<lambda>u (c', Q'). do {
      let S = E `` {u} - V\<^sub>i;
      c' \<leftarrow> transfer_edges_algo ({u} \<times> S) c';
      let Q' = Q' \<union> S;
      RETURN (c', Q')
    })
    (c', {})"

definition ebfs_phase_invar :: "node \<Rightarrow> nat \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_phase_invar s n c\<^sub>i Q \<equiv> \<lambda>(c', Q').
    CapacityCompatibleGraphs c' c
    \<and> Graph.E c' = Graph.E c\<^sub>i \<union> E \<inter> (exactDistNodes n s - Q) \<times> Q'
    \<and> Q' = exactDistNodes (Suc n) s \<inter> E `` (exactDistNodes n s - Q)"

lemma ebfs_phase_initial:
  assumes "Bounded_S_Shortest_Path_Union c' c s V n"
  shows "ebfs_phase_invar s n c' (exactDistNodes n s) (c', {})"
  unfolding ebfs_phase_invar_def
proof (intro case_prodI conjI)
  from assms interpret Bounded_S_Shortest_Path_Union c' c s V n .
  show "CapacityCompatibleGraphs c' c" by intro_locales
qed (simp_all)

lemma ebfs_phase_final:
  assumes BSPU: "Bounded_S_Shortest_Path_Union c\<^sub>i c s V n"
    and INVAR: "ebfs_phase_invar s n c\<^sub>i {} (c', Q')"
  shows "Bounded_S_Shortest_Path_Union c' c s V (Suc n) \<and> Q' = exactDistNodes (Suc n) s"
proof
  from INVAR have "CapacityCompatibleGraphs c' c"
    and E'_EQ: "Graph.E c' = Graph.E c\<^sub>i \<union> E \<inter> exactDistNodes n s \<times> Q'"
    and Q'_EQ: "Q' = exactDistNodes (Suc n) s \<inter> E `` exactDistNodes n s"
    unfolding ebfs_phase_invar_def by auto
  then interpret CapacityCompatibleGraphs c' c by simp
  from BSPU interpret g\<^sub>i: Bounded_S_Shortest_Path_Union c\<^sub>i c s V n .

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

  show "Bounded_S_Shortest_Path_Union c' c s V (Suc n)"
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
lemma finite_if_spu(*[intro]*): "S_Shortest_Path_Union c' c s T \<Longrightarrow> Finite_Graph c'"
proof
  assume "S_Shortest_Path_Union c' c s T"
  then interpret S_Shortest_Path_Union c' c s T .
  have "Graph.V c' \<subseteq> reachableNodes s"
    unfolding reachableNodes_def using sg_connected_remains_base_connected by blast
  then show "finite (Graph.V c')" using FINITE_REACHABLE finite_subset by blast
qed

lemma ebfs_phase_step:
  assumes BSPU: "Bounded_S_Shortest_Path_Union c\<^sub>i c s V n"
    and Q: "u \<in> Q" "Q \<subseteq> exactDistNodes n s"
    and INVAR: "ebfs_phase_invar s n c\<^sub>i Q (c', Q')"
  defines "S \<equiv> E `` {u} - (Graph.V c\<^sub>i \<union> {s})"
  shows "transfer_edges_algo ({u} \<times> S) c' \<le> (spec c''. ebfs_phase_invar s n c\<^sub>i (Q - {u}) (c'', Q' \<union> S))"
proof -
  from Q have "connected s u" unfolding exactDistNodes_def by blast
  then have "E `` {u} \<subseteq> reachableNodes s"
    unfolding reachableNodes_def using connected_append_edge by blast
  with FINITE_REACHABLE have "finite S" unfolding S_def using finite_subset by blast
  then have "transfer_edges_algo ({u} \<times> S) c' \<le> return (transfer_edges ({u} \<times> S) c')"
    using transfer_edges_correct by simp
  also have "... \<le> (spec c''. ebfs_phase_invar s n c\<^sub>i (Q - {u}) (c'', Q' \<union> S))"
    unfolding ebfs_phase_invar_def
  proof (clarify, refine_vcg)
    from INVAR have "CapacityCompatibleGraphs c' c"
      and E'_EQ: "Graph.E c' = Graph.E c\<^sub>i \<union> E \<inter> (exactDistNodes n s - Q) \<times> Q'"
      and Q'_EQ: "Q' = exactDistNodes (Suc n) s \<inter> E `` (exactDistNodes n s - Q)"
      unfolding ebfs_phase_invar_def by auto
    then interpret CapacityCompatibleGraphs c' c by simp

    show "CapacityCompatibleGraphs (transfer_edges ({u} \<times> S) c') c"
      using \<open>CapacityCompatibleGraphs c' c\<close> transfer_edges_capcomp by blast

    interpret g\<^sub>i: Graph c\<^sub>i .
    from Q have "E `` {u} \<subseteq> boundedReachableNodes (Suc n) s"
      unfolding boundedReachableNodes_alt using exactDistNodes_reachable_ss by blast
    with BSPU have S_alt: "S = exactDistNodes (Suc n) s \<inter> E `` {u}"
      unfolding S_def exactDistNodes_alt using BSPU_V'_boundedReachable by blast
    with Q Q'_EQ show "Q' \<union> S = exactDistNodes (Suc n) s \<inter> E `` (exactDistNodes n s - (Q - {u}))"
      by blast

    have "{u} \<times> S \<subseteq> E" unfolding S_def by blast
    then have "Graph.E (transfer_edges ({u} \<times> S) c') = g\<^sub>i.E \<union> E \<inter> ((exactDistNodes n s - Q) \<times> Q' \<union> {u} \<times> S)"
      using transfer_edges_ss_E E'_EQ by blast
    also have "... = g\<^sub>i.E \<union> E \<inter> (exactDistNodes n s - (Q - {u})) \<times> (Q' \<union> S)"
      unfolding S_alt Q'_EQ using Q by blast
    finally show "Graph.E (transfer_edges ({u} \<times> S) c') = g\<^sub>i.E \<union> E \<inter> (exactDistNodes n s - (Q - {u})) \<times> (Q' \<union> S)" .
  qed
  finally show ?thesis .
qed

lemma ebfs_phase_correct:
  assumes BSPU: "Bounded_S_Shortest_Path_Union c' c s V n"
  shows "ebfs_phase (Graph.V c' \<union> {s}) c' (exactDistNodes n s) \<le> SPEC (\<lambda>(c'', Q'). Bounded_S_Shortest_Path_Union c'' c s V (Suc n) \<and> Q' = exactDistNodes (Suc n) s)"
  unfolding ebfs_phase_def
  apply (refine_vcg FOREACH_rule[where I="ebfs_phase_invar s n c'"])
  using FINITE_REACHABLE finite_subset exactDistNodes_reachable_ss boundedReachableNodes_ss apply meson
  using BSPU ebfs_phase_initial ebfs_phase_step ebfs_phase_final by simp_all
end



(*
definition ebfs :: "node \<Rightarrow> _ graph nres" where
  "ebfs s \<equiv> do {
    (c', _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q). Q \<noteq> {})
      (uncurry ebfs_phase)
      ((\<lambda>_. 0), {s});
    RETURN c'
  }"
*)

find_consts "'a \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b)"
term Pair


thm ebfs_phase_correct
(* TODO the n exists only for analysis purposes, can we remove it? *)
(* TODO curry *)
(* TODO update V\<^sub>i by adding Q instead of recomputing it *)
definition ebfs :: "node \<Rightarrow> _ graph nres" where
  "ebfs s \<equiv> do {
    (c', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q, _). Q \<noteq> {})
      (\<lambda>(c', Q, n). do {
        let V\<^sub>i = Graph.V c' \<union> {s};
        (c', Q') \<leftarrow> ebfs_phase V\<^sub>i c' Q;
        RETURN (c', Q', Suc n)
      })
      ((\<lambda>_. 0), {s}, 0);
    RETURN c'
  }"

definition ebfs_invar :: "node \<Rightarrow> (_ graph \<times> node set \<times> nat) \<Rightarrow> bool" where
  "ebfs_invar s \<equiv> \<lambda>(c', Q, n).
    Bounded_S_Shortest_Path_Union c' c s V n
    \<and> Q = exactDistNodes n s"

lemma ebfs_final:
  assumes INVAR: "ebfs_invar s (c', {}, n)"
  shows "S_Shortest_Path_Union c' c s V"
proof -
  from INVAR interpret Bounded_S_Shortest_Path_Union c' c s V n unfolding ebfs_invar_def by blast

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
      with INVAR show False unfolding ebfs_invar_def by simp
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
  assumes INVAR: "ebfs_invar s (c', Q, n)" and Q: "Q \<noteq> {}"
  shows "ebfs_phase (Graph.V c' \<union> {s}) c' Q \<le> SPEC (\<lambda>(c'', Q'). ebfs_invar s (c'', Q', Suc n) \<and> Suc n \<le> card (reachableNodes s))"
proof -
  from INVAR have "ebfs_phase (Graph.V c' \<union> {s}) c' Q \<le> SPEC (\<lambda>(c'', Q'). Bounded_S_Shortest_Path_Union c'' c s V (Suc n) \<and> Q' = exactDistNodes (Suc n) s)"
    using ebfs_phase_correct[OF FINITE_REACHABLE] unfolding ebfs_invar_def by blast
  also have "... \<le> SPEC (\<lambda>(c'', Q'). ebfs_invar s (c'', Q', Suc n) \<and> Suc n \<le> card (reachableNodes s))"
  proof (auto simp: ebfs_invar_def)
    from INVAR Q obtain p u where "isShortestPath s p u" "length p = n"
      unfolding ebfs_invar_def exactDistNodes_def
      using obtain_shortest_path isShortestPath_min_dist_def by simp metis
    then have "card (set (pathVertices s p)) = Suc n" apply (auto dest!: shortestPath_is_simple simp: isSimplePath_def)
      using length_pathVertices_eq distinct_card by fastforce (* TODO *)
    with \<open>isShortestPath s p u\<close>[THEN shortestPath_is_path, THEN pathVertices_reachable] show "Suc n \<le> card (reachableNodes s)"
      by (metis FINITE_REACHABLE card_mono)
  qed
  finally show ?thesis .
qed

theorem ebfs_correct: "ebfs s \<le> (spec c'. S_Shortest_Path_Union c' c s V)"
  unfolding ebfs_def
  apply (refine_vcg WHILET_rule[where I="ebfs_invar s"
      and R="inv_image (greater_bounded (card (reachableNodes s))) (snd \<circ> snd)"])

  apply blast

  subgoal
    unfolding ebfs_invar_def exactDistNodes_def
    apply auto
    apply unfold_locales
    unfolding Graph.E_def
    by auto

  using ebfs_step ebfs_final by simp_all
end









definition back_ebfs :: "node \<Rightarrow> _ graph nres" where
  "back_ebfs t \<equiv> do {
    (c', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q, _). Q \<noteq> {})
      (\<lambda>(c', Q, n). do {
        let V\<^sub>i = (Graph.V c' \<union> {t});
        (c', Q') \<leftarrow> foreach Q
          (\<lambda>u (c', Q'). do {
            let S = E\<inverse> `` {u} - V\<^sub>i;
            c' \<leftarrow> transfer_edges_algo (S \<times> {u}) c';
            let Q' = Q' \<union> S;
            RETURN (c', Q')
          })
          (c', {});
        RETURN (c', Q', Suc n)
      })
      ((\<lambda>_. 0), {t}, 0);
    RETURN c'
  }"

end

thm FOREACH_refine_rcg
thm FOREACH_refine
find_theorems FOREACH

(* TODO improve *)
lemma dual_ebfs: "Dual_Graph_Algorithms (swap_args2 Graph.back_ebfs u) (swap_args2 Graph.ebfs u)"
proof (intro Dual_Graph_AlgorithmsI, unfold swap_args2_def)
  fix c' :: "('capacity'::linordered_idom) graph"
  note[refine_dref_RELATES] = RELATESI[of transpose_graph_rel]
  show "Graph.back_ebfs c' u \<le> \<Down> transpose_graph_rel (Graph.ebfs (c'\<^sup>T) u)"
    unfolding Graph.back_ebfs_def Graph.ebfs_def Graph.ebfs_phase_def
    apply (refine_rcg FOREACH_refine_rcg[where \<alpha>=id], refine_dref_type)
            apply (all \<open>(auto simp: transpose_graph_rel_def; fail)?\<close>)
    apply (simp add: transfer_edges_dual.conc_simp)
    by (simp add: transpose_graph_rel_def product_swap)

  show "Graph.ebfs c' u \<le> \<Down> transpose_graph_rel (Graph.back_ebfs (c'\<^sup>T) u)"
    unfolding Graph.back_ebfs_def Graph.ebfs_def Graph.ebfs_phase_def
    apply (refine_rcg FOREACH_refine_rcg[where \<alpha>=id])
            apply refine_dref_type
            apply (all \<open>(auto simp: transpose_graph_rel_def; fail)?\<close>)
    apply (simp add: transfer_edges_dual.conc_simp)
    by (simp add: transpose_graph_rel_def product_swap)
qed

(* TODO simplify and extract *)
lemma dual_spu: "T_Shortest_Path_Union c' c (Graph.V c) t = S_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t (Graph.V (c\<^sup>T))"
proof
  assume "T_Shortest_Path_Union c' c (Graph.V c) t"
  then interpret T_Shortest_Path_Union c' c "Graph.V c" t .
  show "S_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t (Graph.V (c\<^sup>T))"
  proof
    show "\<And>u v. (c'\<^sup>T) (u, v) = 0 \<or> (c\<^sup>T) (u, v) = 0 \<or> (c'\<^sup>T) (u, v) = (c\<^sup>T) (u, v)"
      using cap_compatible by simp
    show "Graph.E (c'\<^sup>T) = \<Union> {set p |p. \<exists>ta. ta \<in> Graph.V (c\<^sup>T) \<and> Graph.isShortestPath (c\<^sup>T) t p ta}"
    proof (simp, intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> E'\<inverse>"
      then obtain s p where "(v, u) \<in> set p" "s \<in> V" "isShortestPath s p t"
        using shortest_t_path_union by blast
      then have "(u, v) \<in> set (transpose_path p)" "isShortestPath s (transpose_path (transpose_path p)) t"
        by auto
      with \<open>s \<in> V\<close> show "(u, v) \<in> \<Union> {set p |p. \<exists>ta. ta \<in> V \<and> isShortestPath ta (transpose_path p) t}"
        by blast
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. \<exists>ta. ta \<in> V \<and> isShortestPath ta (transpose_path p) t}"
      then show "(u, v) \<in> E'\<inverse>" using shortest_t_path_union by fastforce
    qed
  qed
next
  assume "S_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t (Graph.V (c\<^sup>T))"
  then interpret S_Shortest_Path_Union "c'\<^sup>T" "c\<^sup>T" t "Graph.V c" by simp
  show "T_Shortest_Path_Union c' c (Graph.V c) t"
  proof
    show "\<And>u v. c' (u, v) = 0 \<or> c (u, v) = 0 \<or> c' (u, v) = c (u, v)"
      using cap_compatible by simp
    show "Graph.E c' = \<Union> {set p |p. \<exists>s. s \<in> Graph.V c \<and> Graph.isShortestPath c s p t}"
    proof (intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> Graph.E c'"
      then obtain s p where "(v, u) \<in> set p" "s \<in> V" "isShortestPath t p s"
        using shortest_s_path_union by fastforce
      then show "(u, v) \<in> \<Union> {set p |p. \<exists>s. s \<in> Graph.V c \<and> Graph.isShortestPath c s p t}"
        by fastforce
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. \<exists>s. s \<in> Graph.V c \<and> Graph.isShortestPath c s p t}"
      then obtain s p where "(u, v) \<in> set p" "s \<in> Graph.V c" "Graph.isShortestPath c s p t"
        by blast
      then have "(v, u) \<in> set (transpose_path p)" "isShortestPath t (transpose_path p) s" by auto
      with \<open>s \<in> Graph.V c\<close> have "(v, u) \<in> E'" using shortest_s_path_union by blast
      then show "(u, v) \<in> Graph.E c'" by simp
    qed
  qed
qed

theorem (in Graph) back_ebfs_correct:
  assumes FINITE_REACHED_FROM: "finite {u. connected u t}"
  shows "back_ebfs t \<le> (spec c'. T_Shortest_Path_Union c' c V t)"
proof -
  interpret Dual_Graph_Algorithms "swap_args2 Graph.back_ebfs t" "swap_args2 Graph.ebfs t"
    using dual_ebfs .
  have "swap_args2 Graph.back_ebfs t c \<le> (spec c'. T_Shortest_Path_Union c' c V t)"
    (*using dual_spu apply (auto elim!: transfer_spec)*)
    (*thm dual_spu[THEN transfer_spec]*)
    (*thm transfer_spec[OF dual_spu]*)
  proof (intro transfer_spec[where spec'="\<lambda>c c'. S_Shortest_Path_Union c' c t (Graph.V c)"])
    show "\<And>c c'. T_Shortest_Path_Union c' c (Graph.V c) t = S_Shortest_Path_Union (c'\<^sup>T) (c\<^sup>T) t (Graph.V (c\<^sup>T))"
      using dual_spu .
    thm Graph.ebfs_correct
    from FINITE_REACHED_FROM have "finite (Graph.reachableNodes (c\<^sup>T) t)"
      unfolding Graph.reachableNodes_def by simp
    then show "swap_args2 Graph.ebfs t (c\<^sup>T) \<le> (spec c'. S_Shortest_Path_Union c' (c\<^sup>T) t (Graph.V (c\<^sup>T)))"
      using Graph.ebfs_correct by fastforce
  qed
  then show ?thesis by simp
qed

end
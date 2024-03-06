theory Layering_Algo
  imports
    Refinement
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

(* TODO make the successor function parametric or enable inverting graphs*)
definition invert_graph :: "_ graph \<Rightarrow> _ graph" where "invert_graph c \<equiv> c \<circ> prod.swap"

thm swap_swap
lemma invert_invert[simp]: "invert_graph (invert_graph c) = c"
  unfolding invert_graph_def by fastforce

(* TODO check whether such a thing exists *)
(* TODO still necessary? *)

(*
definition update_edge :: "'capacity graph \<Rightarrow> edge \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph" where
  "update_edge c e cap \<equiv> c(e := cap)"

lemma update_edge_apply: "update_edge c e cap e' = (if e' = e then cap else c e')"
  unfolding update_edge_def using fun_upd_apply .

(*
lemma update_edge_id[simp]: "update_edge c e cap e = cap"
  unfolding update_edge_def by simp
lemma update_edge_in_E_transfer[simp]: "e \<in> Graph.E (update_edge c' e (c e)) \<longleftrightarrow> e \<in> Graph.E c"
  unfolding Graph.E_def by simp
*)

lemma update_edge_Subgraph[intro]: "Subgraph c' c \<Longrightarrow> Subgraph (update_edge c' e (c e)) c"
  by (intro Subgraph_edgeI) (auto simp: update_edge_apply elim!: Subgraph.sg_cap_cases)

lemma update_edge_edgeset[simp]:
  "Graph.E (update_edge c e cap) = Graph.E c - {e} \<union> (if cap = 0 then {} else {e})"
  unfolding Graph.E_def by (auto simp: update_edge_apply)

(*
lemma update_edge_in_E_iff: "e \<in> Graph.E (update_edge c e cap) \<longleftrightarrow> cap \<noteq> 0"
  unfolding update_edge_def Graph.E_def by simp
*)
*)

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

\<comment> \<open>Transferring edges to another graph\<close>

subsection \<open>Extended Breadth First Search phase\<close>

(* TODO fix description *)
text \<open>NOTE: The phase algorithm does need to know the source node in order to avoid problems in
      cases where the source node has a self loop. This is a consequence of the graph model, where
      nodes without edges cannot exists, which results in the graph being empty during the first
      iteration even though s is within distance 0 of itself.
      If we did not explicitly exclude the source node from the set of relevant neighbours, then if
      there were a self loop of s, the first phase iteration would add s to the queue for the next
      iteration (as it is an outgoing neighbor of s and not contained in the graph), violating the
      invariant.
      The alternative would be to only proof correctness for graphs without a self loop of s,
      leading to a loss of generality.\<close>
(*
definition ebfs_phase :: "node \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfs_phase s c\<^sub>i Q \<equiv> foreach Q
    (\<lambda>u (c', Q). do {
      let S = E `` {u} - Graph.V c\<^sub>i - {s};
      c' \<leftarrow> transfer_edges_algo ({u} \<times> S) c';
      let Q = Q \<union> S;
      RETURN (c', Q)
    })
    (c\<^sub>i, {})"
*)

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
    then obtain t p where "(u, v) \<in> set p" (*"t \<in> V"*) "isShortestPath s p t" "length p \<le> Suc n" by blast
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
  (* TODO check where we can be more precise *)
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

    (*from BSPU interpret g\<^sub>i: Bounded_S_Shortest_Path_Union c\<^sub>i c s V n .*)
    interpret g\<^sub>i: Graph c\<^sub>i .
    have "S = exactDistNodes (Suc n) s \<inter> E `` {u}" unfolding S_def
    proof(intro equalityI; intro subsetI)
      fix v
      assume "v \<in> E `` {u} - (g\<^sub>i.V \<union> {s})"
      then have "(u, v) \<in> E" "v \<notin> (g\<^sub>i.V \<union> {s})" by auto
      with Q have "v \<in> boundedReachableNodes (Suc n) s"
        unfolding exactDistNodes_def boundedReachableNodes_def
        using connected_append_edge min_dist_succ by blast
      with \<open>(u, v) \<in> E\<close> \<open>v \<notin> (g\<^sub>i.V \<union> {s})\<close> show "v \<in> exactDistNodes (Suc n) s \<inter> E `` {u}"
        unfolding exactDistNodes_alt using BSPU_V'_boundedReachable[OF BSPU] by blast
    next
      fix v
      assume "v \<in> exactDistNodes (Suc n) s \<inter> E `` {u}"
      then have "v \<notin> boundedReachableNodes n s" "(u, v) \<in> E" "v \<noteq> s" unfolding exactDistNodes_alt
        using self_boundedReachable by auto
      then show "v \<in> E `` {u} - (g\<^sub>i.V \<union> {s})" using BSPU_V'_boundedReachable[OF BSPU] by blast
    qed
    with Q Q'_EQ show "Q' \<union> S = exactDistNodes (Suc n) s \<inter> E `` (exactDistNodes n s - (Q - {u}))"
      by blast

    (* TODO can we use any of the previous definitions for S or Q' \<union> S? *)

    have "E \<inter> {u} \<times> (Q' - S) = {}"
    proof auto (* TODO fix *)
      fix v
      assume "(u, v) \<in> E" "v \<in> Q'" "v \<notin> S"
      thm this[unfolded Q'_EQ S_def[unfolded BSPU_V'_boundedReachable[OF BSPU]]]
      then have "v \<in> boundedReachableNodes n s" unfolding S_def[unfolded BSPU_V'_boundedReachable[OF BSPU]] by simp
      with \<open>v \<in> Q'\<close> show False unfolding Q'_EQ exactDistNodes_def boundedReachableNodes_def by simp
    qed
    then have TMP: "E \<inter> ({u} \<times> (Q' \<union> S)) = E \<inter> {u} \<times> S" by blast

    have "E \<inter> (exactDistNodes n s - Q) \<times> (S - Q') = {}"
    proof auto (* TODO fix *)
      fix v w
      assume "(v, w) \<in> E" "v \<in> exactDistNodes n s" "v \<notin> Q" "w \<in> S" "w \<notin> Q'"
      thm this[unfolded Q'_EQ S_def[unfolded BSPU_V'_boundedReachable[OF BSPU]]] Q

      from \<open>w \<in> S\<close> Q have "w \<in> boundedReachableNodes (Suc n) s" unfolding S_def[unfolded BSPU_V'_boundedReachable[OF BSPU]] unfolding exactDistNodes_def boundedReachableNodes_def using min_dist_succ
        using \<open>S = exactDistNodes (Suc n) s \<inter> E `` {u}\<close> \<open>w \<in> S\<close> exactDistNodes_def by auto

      with \<open>w \<in> S\<close> have "w \<in> exactDistNodes (Suc n) s" unfolding S_def[unfolded BSPU_V'_boundedReachable[OF BSPU]] exactDistNodes_alt by blast
      with \<open>w \<notin> Q'\<close> have "w \<notin> E `` (exactDistNodes n s - Q)" unfolding Q'_EQ by simp
      with \<open>(v, w) \<in> E\<close> \<open>v \<in> exactDistNodes n s\<close> \<open>v \<notin> Q\<close> show False by auto
    qed
    then have TMP2: "E \<inter> ((exactDistNodes n s - Q) \<times> (Q' \<union> S)) = E \<inter> (exactDistNodes n s - Q) \<times> Q'" by blast

    have "{u} \<times> S \<subseteq> E" unfolding S_def by blast
    then have "Graph.E (transfer_edges ({u} \<times> S) c') = E' \<union> {u} \<times> S" using transfer_edges_ss_E by simp
    also have "... = g\<^sub>i.E \<union> E \<inter> (exactDistNodes n s - Q) \<times> Q' \<union> {u} \<times> S" using E'_EQ by simp
    also have "... = g\<^sub>i.E \<union> E \<inter> ((exactDistNodes n s - Q) \<times> Q' \<union> {u} \<times> S)" using \<open>{u} \<times> S \<subseteq> E\<close> by blast
    also have "... = g\<^sub>i.E \<union> E \<inter> ((exactDistNodes n s - Q) \<times> Q' \<union> (exactDistNodes n s - Q) \<times> S \<union> {u} \<times> S)" using TMP2 by blast
    also have "... = g\<^sub>i.E \<union> E \<inter> ((exactDistNodes n s - Q) \<times> Q' \<union> (exactDistNodes n s - Q) \<times> S \<union> {u} \<times> Q' \<union> {u} \<times> S)" using TMP by blast
    also have "... = g\<^sub>i.E \<union> E \<inter> (exactDistNodes n s - Q \<union> {u}) \<times> (Q' \<union> S)" by blast
    also have "... = g\<^sub>i.E \<union> E \<inter> (exactDistNodes n s - (Q - {u})) \<times> (Q' \<union> S)" using Q by blast
    finally show "Graph.E (transfer_edges ({u} \<times> S) c') = g\<^sub>i.E \<union> E \<inter> (exactDistNodes n s - (Q - {u})) \<times> (Q' \<union> S)" .
  qed
  finally show ?thesis .
qed

lemma ebfs_phase_correct:
  fixes c' Q n
  assumes BSPU: "Bounded_S_Shortest_Path_Union c' c s V n"
  shows "ebfs_phase (Graph.V c' \<union> {s}) c' (exactDistNodes n s) \<le> SPEC (\<lambda>(c'', Q'). Bounded_S_Shortest_Path_Union c'' c s V (Suc n) \<and> Q' = exactDistNodes (Suc n) s)"
  unfolding ebfs_phase_def
  apply (refine_vcg FOREACH_rule[where I="ebfs_phase_invar s n c'"])
  using FINITE_REACHABLE finite_subset exactDistNodes_reachable_ss boundedReachableNodes_ss apply meson
  using BSPU ebfs_phase_initial ebfs_phase_step ebfs_phase_final by simp_all
end











definition ebfs :: "node \<Rightarrow> _ graph nres" where
  "ebfs s \<equiv> do {
    (c', _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q). Q \<noteq> {})
      (uncurry ebfs_phase)
      ((\<lambda>_. 0), {s});
    RETURN c'
  }"


(* TODO the n exists only for analysis purposes, can we remove it? *)
definition ebfs' :: "node \<Rightarrow> _ graph nres" where
  "ebfs' s \<equiv> do {
    (c', _, _) \<leftarrow> WHILE
      (\<lambda>(_, Q, _). Q \<noteq> {})
      (uncurry ebfs_phase)
      ((\<lambda>_. 0), {s});
    RETURN c'
  }"

(*
thm WHILET_rule
thm FOREACH_rule
lemma ebfs_phase_correct: "ebfs_phase_invar s n Q c' \<Longrightarrow> ebfs_phase Q c' \<le> SPEC (uncurry (\<lambda>Q' c'. ebfs_phase_invar s (n + 1) Q' c'))"
thm FOREACH_rule[where I="ebfs_phase_invar s n"]
  unfolding ebfs_phase_def
  apply (refine_vcg FOREACH_rule[where I="ebfs_phase_invar s n"])
*)

(*definition ebfs_phase_invar :: *)

(*
definition ebfs_invar :: "node \<Rightarrow> nat \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_invar s n \<equiv> \<lambda>(c', Q).
    Bounded_S_Shortest_Path_Union c' c s V n
    \<and> Q = {u. connected s u \<and> min_dist s u = n + 1}"
*)

(* TODO use or remove *)
definition ebfs_invar' :: "node \<Rightarrow> (nat \<times> _ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_invar' s \<equiv> \<lambda>(n, c', Q).
    Bounded_S_Shortest_Path_Union c' c s V n
    \<and> Q = {u. connected s u \<and> min_dist s u = n + 1}"

definition ebfs_invar :: "node \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_invar s \<equiv> \<lambda>(c', Q). \<exists> n.
    Bounded_S_Shortest_Path_Union c' c s V n
    \<and> Q = {u. connected s u \<and> min_dist s u = n + 1}"

lemma ebfs_phase_correct': "ebfs_invar' s (n, c', Q) \<Longrightarrow> ebfs_phase c' Q \<le> SPEC (\<lambda>x. ebfs_invar' s (Suc n, x))" sorry

lemma ebfs_phase_correct: "ebfs_invar s (c', Q) \<Longrightarrow> ebfs_phase c' Q \<le> SPEC (\<lambda>x. ebfs_invar s x)" sorry

thm WHILE_rule
theorem ebfs'_correct: "ebfs' s \<le> (spec x. S_Shortest_Path_Union c' c s V)"
  unfolding ebfs'_def
  apply (refine_vcg WHILE_rule[where I="ebfs_invar s"])




  thm WHILE_rule[where I="ebfs_invar s" and f="uncurry ebfs_phase"]
  apply (rule WHILE_rule[where I="ebfs_invar s"])
  prefer 3
  apply refine_vcg
  apply (rule WHILE_rule)
  thm WHILE_rule
  thm WHILE_rule[where I="ebfs_invar s" and \<Phi>="\<lambda>c'. S_Shortest_Path_Union c' c s V"]
  sorry apply (refine_vcg WHILE_rule[where I="ebfs_invar s"])
end
end
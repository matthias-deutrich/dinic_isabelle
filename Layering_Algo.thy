theory Layering_Algo
  imports
    Refinement
    EdmondsKarp_Maxflow.Augmenting_Path_BFS
begin

subsection \<open>Extended BFS\<close>
text \<open>In this section, we present an extended version of breadth-first search, which builds a graph
      consisting of all shortest paths starting at a source node, instead of only a single shortest
      path to a specified destination.

      While we loosely follow the verified implementation of BFS developed for the implementation
      of Edmonds-Karp, there are multiple significant differences. First, unlike standard BFS, we
      care about the capacity of edges as we build a graph instead of a path. Second, we use two
      working sets, since we need to distinguish between nodes in the graph that were added in the
      current phase (which are still eligible edge endpoints) and older nodes.\<close>

(* TODO make the successor function parametric or enable inverting graphs*)
definition (in Graph) inverted where "inverted \<equiv> c \<circ> prod.swap"

thm swap_swap
lemma inverted_inverted[simp]: "Graph.inverted (Graph.inverted c) = c"
  unfolding Graph.inverted_def by fastforce

find_consts "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<times> 'a) \<Rightarrow> 'c"

(* TODO check whether such a thing exists *)
definition update_edge :: "'capacity graph \<Rightarrow> edge \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph" where
  "update_edge c e cap \<equiv> c(e := cap)"

context Graph
begin

definition ebfs_node :: "node \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfs_node u c' Q' \<equiv> do {
    let S = (E``{u}) - (Graph.V c' - Q');
    c' \<leftarrow> foreach S (\<lambda>v c'. RETURN (update_edge c' (u, v) (c (u, v)))) c';
    let Q' = Q' \<union> S;
    RETURN (c', Q')
  }"

definition ebfs_phase :: "_ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfs_phase c' Q \<equiv> foreach Q (\<lambda>u (c', Q'). ebfs_node u c' Q') (c', {})"

definition ebfs_phase_invar :: "node \<Rightarrow> nat \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_phase_invar s n Q \<equiv> \<lambda>(c', Q').
    S_Shortest_Path_Union c' c s (boundedReachableNodes (Suc n) s - Q)
    \<and> Q' = exactDistNodes (n + 2) s \<inter> {v. \<exists>u \<in> Graph.V c'. (u, v) \<in> E}"

lemma ebfs_phase_initial:
  assumes "S_Shortest_Path_Union c' c s (boundedReachableNodes n s)"
  shows "ebfs_phase_invar s n (exactDistNodes (Suc n) s) (c', {})"
  unfolding ebfs_phase_invar_def
proof (intro case_prodI conjI)
  show "S_Shortest_Path_Union c' c s (boundedReachableNodes (Suc n) s - exactDistNodes (Suc n) s)"
    using assms by (simp add: ebfs_phase_invar_def exactDistNodes_alt boundedReachableNodes_mono double_diff)

  have "\<And>v. \<exists>u \<in> Graph.V c'. (u, v) \<in> E \<Longrightarrow> v \<notin> exactDistNodes (n + 2) s"
  proof -
    interpret S_Shortest_Path_Union c' c s "boundedReachableNodes n s" using assms .

    fix v
    assume "\<exists>u \<in> Graph.V c'. (u, v) \<in> E"
    then obtain u where "u \<in> Graph.V c'" "(u, v) \<in> E" by blast
    then obtain t p\<^sub>s p\<^sub>t where "t \<in> boundedReachableNodes n s" "isShortestPath s (p\<^sub>s @ p\<^sub>t) t"
      and P2: "isShortestPath s p\<^sub>s u"
      by (blast elim: obtain_shortest_ST_paths)
    then have "length p\<^sub>s \<le> n" unfolding boundedReachableNodes_def isShortestPath_min_dist_def by simp
    with P2 \<open>(u, v) \<in> E\<close> have "min_dist s v \<le> Suc n"
      using isShortestPath_min_dist_def connected_def min_dist_succ by fastforce
    then show "v \<notin> exactDistNodes (n + 2) s" unfolding exactDistNodes_def by simp
  qed
  then show "{} = exactDistNodes (n + 2) s \<inter> {v. \<exists>u\<in>Graph.V c'. (u, v) \<in> E}" by blast
qed

lemma ebfs_phase_final: (* TODO switch order *)
  assumes "ebfs_phase_invar s n {} (c', Q')"
  shows "S_Shortest_Path_Union c' c s (boundedReachableNodes (Suc n) s) \<and> Q' = exactDistNodes (n + 2) s"
proof
  from assms show "S_Shortest_Path_Union c' c s (boundedReachableNodes (Suc n) s)"
    unfolding ebfs_phase_invar_def by simp
  then interpret S_Shortest_Path_Union c' c s "boundedReachableNodes (Suc n) s" . (* TODO necessary? *)

  from assms have "Q' = exactDistNodes (n + 2) s \<inter> {v. \<exists>u \<in> Graph.V c'. (u, v) \<in> E}"
    unfolding ebfs_phase_invar_def by simp
  moreover have "exactDistNodes (n + 2) s \<subseteq> {v. \<exists>u \<in> Graph.V c'. (u, v) \<in> E}"
  proof (* TODO prettify *)
    fix v
    assume "v \<in> exactDistNodes (n + 2) s"
    then obtain p where P: "isShortestPath s p v" "length p = n + 2" unfolding exactDistNodes_def
      by (metis (mono_tags) isShortestPath_min_dist_def mem_Collect_eq obtain_shortest_path)
    then obtain p\<^sub>u u where "p = p\<^sub>u @ [(u, v)]"
      by (metis Graph.isPath_bwd_cases add_2_eq_Suc' isShortestPath_def length_Suc_conv list.distinct(1))
    with P have "isShortestPath s p\<^sub>u u" "length p\<^sub>u = n + 1" "(u, v) \<in> E"
      using split_shortest_path_around_edge 
      by (metis Graph.isPath_tail add_Suc_right add_left_imp_eq length_append_singleton nat_1_add_1 plus_1_eq_Suc shortestPath_is_path)+
    then have "u \<in> boundedReachableNodes (Suc n) s" unfolding boundedReachableNodes_def
      by (metis connected_def Suc_eq_plus1 isShortestPath_def isShortestPath_min_dist_def mem_Collect_eq)
    then have "u \<in> V'"
      by (metis Graph.connected_edgeRtc Graph.connected_inV_iff Graph.distinct_nodes_in_V_if_connected(1) Graph.isPath_rtc Graph.isShortestPath_alt Graph.shortestPath_is_path Graph.simplePath_same_conv Suc_eq_plus1 \<open>isShortestPath s p\<^sub>u u\<close> \<open>length p\<^sub>u = n + 1\<close> insert_iff length_Suc_conv list.distinct(1) shortest_ST_path_remains)
    with \<open>(u, v) \<in> E\<close> show "v \<in> {v. \<exists>u\<in>V'. (u, v) \<in> E}" by blast
  qed
  ultimately show "Q' = exactDistNodes (n + 2) s" by blast
qed

lemma ebfs_phase_step:
  assumes "u \<in> Q" and "Q \<subseteq> exactDistNodes (Suc n) s" and "ebfs_phase_invar s n Q (c', Q')"
  shows "ebfs_node u c' Q' \<le> SPEC (ebfs_phase_invar s n (Q - {u}))"
  sorry

lemma ebfs_phase_correct:
  fixes s c' Q n
  assumes "finite (exactDistNodes (Suc n) s)"
    and "S_Shortest_Path_Union c' c s (boundedReachableNodes n s)"
  shows "ebfs_phase c' (exactDistNodes (Suc n) s) \<le> SPEC(\<lambda>(c'', Q'). S_Shortest_Path_Union c'' c s (boundedReachableNodes (Suc n) s) \<and> Q' = exactDistNodes (n + 2) s)"
  unfolding ebfs_phase_def
  apply (refine_vcg FOREACH_rule[where I="ebfs_phase_invar s n"])
  using assms ebfs_phase_initial ebfs_phase_step ebfs_phase_final by simp_all

thm FOREACH_rule
(* TODO somewhere we need the fact that the set of reachable nodes (from s) is finite *)

(* TODO is it better to remove any notion of Bounded locales from this part and rely entirely on restricted reachable sets? *)
(*
lemma ebfs_phase_correct:
  fixes s c' Q n
  assumes "Bounded_S_Shortest_Path_Union c' c s V n"
    and "Q = {u. connected s u \<and> min_dist s u = n + 1}"
    and "finite Q"
  shows "ebfs_phase c' Q \<le> SPEC(\<lambda>(c'', Q'). Bounded_S_Shortest_Path_Union c'' c s V (n + 1) \<and> Q' = {u. connected s u \<and> min_dist s u = n + 2})"
  unfolding ebfs_phase_def
  apply (rule FOREACH_rule, clarsimp_all)
proof (refine_vcg)
*)



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
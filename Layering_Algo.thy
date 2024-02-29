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
      current phase (which are still eligible edge endpoints) and older nodes. Third, the setup
      based on a single predecessor for each node does not work here as we do not necessarily have
      a tree.\<close>

(* TODO make the successor function parametric or enable inverting graphs*)
definition invert_graph :: "_ graph \<Rightarrow> _ graph" where "invert_graph c \<equiv> c \<circ> prod.swap"

thm swap_swap
lemma invert_invert[simp]: "invert_graph (invert_graph c) = c"
  unfolding invert_graph_def by fastforce

(* TODO check whether such a thing exists *)
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

context Graph
begin

(*
definition ebfs_node :: "node \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfs_node u c' Q' \<equiv> do {
    let S = (E``{u}) - (Graph.V c' - Q');
    c' \<leftarrow> foreach S (\<lambda>v c'. RETURN (update_edge c' (u, v) (c (u, v)))) c';
    let Q' = Q' \<union> S;
    RETURN (c', Q')
  }"
*)

find_consts "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set "
thm incoming_def
thm image_def
thm Image_def
term image
term Image
find_consts "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> 'a set"

(* TODO is there a prettier way to phrase "incoming v \<inter> (Graph.V c' \<times> {v})" ? *)

definition ebfs_node :: "node \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfs_node v c' Q' \<equiv> do {
    c' \<leftarrow> foreach (incoming v \<inter> (Graph.V c' \<times> {v})) (\<lambda>e c'. RETURN (update_edge c' e (c e))) c';
    let Q' = Q' \<union> (E``{v} - Graph.V c');
    RETURN (c', Q')
  }"

definition ebfs_node_invar :: "node \<Rightarrow> _ graph \<Rightarrow> edge set \<Rightarrow> _ graph \<Rightarrow> bool" where
  "ebfs_node_invar v c_init it c' \<equiv>
    Subgraph c' c
    \<and> Graph.E c' \<union> it = Graph.E c_init \<union> (incoming v \<inter> (Graph.V c_init \<times> {v}))"

definition ebfs_phase :: "_ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfs_phase c' Q \<equiv> foreach Q (\<lambda>u (c', Q'). ebfs_node u c' Q') (c', {})"

definition ebfs_phase_invar :: "node \<Rightarrow> nat \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_phase_invar s n Q \<equiv> \<lambda>(c', Q').
    S_Shortest_Path_Union c' c s (boundedReachableNodes (Suc n) s - Q)
    \<and> Q' = exactDistNodes (n + 2) s \<inter> {v. \<exists>u \<in> Graph.V c'. (u, v) \<in> E}"

lemma ebfs_node_final:
  assumes V_DIST: "v \<in> Q" "Q \<subseteq> exactDistNodes (Suc n) s" (* TODO what exactly do we need here? *)
    and NODE_INVAR: "ebfs_node_invar v c_init {} c'"
    and PHASE_INVAR: "ebfs_phase_invar s n Q (c_init, Q')"
  shows "ebfs_phase_invar s n (Q - {v}) (c', Q' \<union> (E `` {v} - Graph.V c'))"
  unfolding ebfs_phase_invar_def
proof (intro case_prodI conjI)
  from NODE_INVAR interpret Subgraph c' c unfolding ebfs_node_invar_def by blast

  from PHASE_INVAR interpret init: S_Shortest_Path_Union c_init c s "boundedReachableNodes (Suc n) s - Q"
    unfolding ebfs_phase_invar_def by blast

  thm assms[unfolded ebfs_node_invar_def ebfs_phase_invar_def, simplified]
  show "S_Shortest_Path_Union c' c s (boundedReachableNodes (Suc n) s - (Q - {v}))"
  proof (unfold_locales, intro equalityI; intro subsetI)
    fix e
    assume "e \<in> E'"
    then consider (old_edge) "e \<in> Graph.E c_init"
      | (new_edge) "e \<in> incoming v \<inter> Graph.V c_init \<times> {v}"
      using NODE_INVAR unfolding ebfs_node_invar_def by blast
    then show "e \<in> \<Union> {set p |p. \<exists>t. t \<in> boundedReachableNodes (Suc n) s - (Q - {v}) \<and> isShortestPath s p t}"
    proof cases
      case old_edge
      then obtain t p where "t \<in> boundedReachableNodes (Suc n) s - Q" "isShortestPath s p t" "e \<in> set p"
        using init.shortest_s_path_union by fast
      then show ?thesis by blast
    next
      case new_edge
      then obtain u where "u \<in> Graph.V c_init" "(u, v) \<in> E" and [simp]: "e = (u, v)"
        unfolding incoming_def Graph.V_def Graph.E_def by blast
      (*then obtain p where "isShortestPath s p u" "length p \<le> n" oops*)
      then show ?thesis sorry
    qed
  next
    fix e
    assume "e \<in> \<Union> {set p |p. \<exists>t. t \<in> boundedReachableNodes (Suc n) s - (Q - {v}) \<and> isShortestPath s p t}"
    then consider p t where "e \<in> set p" "t \<in> boundedReachableNodes (Suc n) s - Q" "isShortestPath s p t"
      | p where "e \<in> set p" "isShortestPath s p v" by blast
    then show "e \<in> E'"
    proof cases
      case 1
      then show ?thesis sorry
    next
      case 2
      then show ?thesis sorry
    qed
  qed

  (* TODO *)
  have "init.V' = V' - {v}" using NODE_INVAR unfolding ebfs_node_invar_def Graph.V_def sorry
  have "{v. \<exists>u\<in>init.V'. (u, v) \<in> E} \<union> (E `` {v}) = {v. \<exists>u\<in>V'. (u, v) \<in> E}"

  thm assms[unfolded ebfs_node_invar_def ebfs_phase_invar_def, simplified]
  have "Q' \<union> (E `` {v} - V') = exactDistNodes (n + 2) s \<inter> {v. \<exists>u\<in>init.V'. (u, v) \<in> E} \<union> (E `` {v} - V')"
    using PHASE_INVAR unfolding ebfs_phase_invar_def by fast
  also have "... = exactDistNodes (n + 2) s \<inter> {v. \<exists>u\<in>init.V'. (u, v) \<in> E} \<union> (E `` {v} - V')" sorry

  show "Q' \<union> (E `` {v} - V') = exactDistNodes (n + 2) s \<inter> {v. \<exists>u\<in>V'. (u, v) \<in> E}"
    using assms[unfolded ebfs_node_invar_def ebfs_phase_invar_def, simplified] oops
qed

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

lemma ebfs_phase_final:
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

context
  (* TODO check where we can be more precise *)
  fixes s
  assumes FINITE_REACHABLE: "finite (reachableNodes s)"
begin
lemma finite_if_spu[intro]: "S_Shortest_Path_Union c' c s T \<Longrightarrow> Finite_Graph c'"
proof
  assume "S_Shortest_Path_Union c' c s T"
  then interpret S_Shortest_Path_Union c' c s T .
  have "Graph.V c' \<subseteq> reachableNodes s"
    unfolding reachableNodes_def using sg_connected_remains_base_connected by blast
  then show "finite (Graph.V c')" using FINITE_REACHABLE finite_subset by blast
qed

lemma ebfs_node_step:
  assumes "e \<in> it" "it \<subseteq> incoming v \<inter> V' \<times> {v}" and INVAR: "ebfs_node_invar v c_init it c'"
  shows "ebfs_node_invar v c_init (it - {e}) (update_edge c' e (c e))"
proof -
  from assms have "c e \<noteq> 0"
    using Graph.incoming_edges Graph.E_def unfolding split_paired_all by blast
  with \<open>e \<in> it\<close> INVAR show ?thesis unfolding ebfs_node_invar_def by auto
qed

lemma ebfs_phase_step:
  assumes "u \<in> Q" and "Q \<subseteq> exactDistNodes (Suc n) s" and INVAR: "ebfs_phase_invar s n Q (c', Q')"
  shows "ebfs_node u c' Q' \<le> SPEC (ebfs_phase_invar s n (Q - {u}))"
proof -
  from INVAR interpret S_Shortest_Path_Union c' c s "boundedReachableNodes (Suc n) s - Q"
    unfolding ebfs_phase_invar_def by blast

  show ?thesis
  unfolding ebfs_node_def
  apply (refine_vcg FOREACH_rule[where I="ebfs_node_invar u c'"])
  using S_Shortest_Path_Union_axioms apply (blast intro: Finite_Graph.finite_V)
  using Subgraph_axioms apply (simp add: ebfs_node_invar_def) (* TODO can this work without the interpretation setup? *)
  using ebfs_node_step apply blast
  using ebfs_node_final assms by fast
qed
end

lemma ebfs_phase_correct:
  fixes s c' Q n
  assumes "finite (reachableNodes s)" (*"finite (exactDistNodes (Suc n) s)"*)
    and "S_Shortest_Path_Union c' c s (boundedReachableNodes n s)"
  shows "ebfs_phase c' (exactDistNodes (Suc n) s) \<le> SPEC(\<lambda>(c'', Q'). S_Shortest_Path_Union c'' c s (boundedReachableNodes (Suc n) s) \<and> Q' = exactDistNodes (n + 2) s)"
  unfolding ebfs_phase_def
  apply (refine_vcg FOREACH_rule[where I="ebfs_phase_invar s n"])
  using assms finite_subset apply (metis Diff_subset exactDistNodes_alt boundedReachableNodes_ss)
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
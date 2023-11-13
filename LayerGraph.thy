theory LayerGraph
  imports Subgraph
begin

definition s_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "s_layering c s \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.min_dist c s u + 1 = Graph.min_dist c s v then
      c (u, v)
    else
      0"

lemma s_layering_subgraph: "isSubgraph (s_layering c s) c"
  unfolding isSubgraph_def s_layering_def by simp

locale InducedSourceLayering = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
  assumes s_node[simp, intro!]: "s \<in> V"
begin

sublocale l: Graph "s_layering c s" .

sublocale l_sub: Subgraph "s_layering c s" c
  unfolding Subgraph_def by (rule s_layering_subgraph)

(* TODO check if this is a good idea, and if "connected s v" should also be a property *)
lemma l_edgeE[elim]:
  assumes "(u, v) \<in> l.E"
  obtains "(u, v) \<in> E"
    and "connected s u" "connected s v" "min_dist s u + 1 = min_dist s v"
proof
  from assms show "(u, v) \<in> E" using l_sub.E_ss by blast
  from assms have layering_not_z: "s_layering c s (u, v) \<noteq> 0" using l.E_def by blast
  then show "connected s u" unfolding s_layering_def by (smt case_prod_conv)
  then show "connected s v" using  \<open>(u, v) \<in> E\<close> by (rule connected_append_edge)
  from layering_not_z show "min_dist s u + 1 = min_dist s v" unfolding s_layering_def by (smt case_prod_conv)
qed

lemma l_edge_iff: "(u, v) \<in> l.E \<longleftrightarrow> (u, v) \<in> E \<and> connected s u \<and> min_dist s u + 1 = min_dist s v"
  using E_def' l.E_def' s_layering_def by (smt (verit, best) mem_Collect_eq prod.simps(2))

lemma l_vertices_connected_in_base: "u \<in> l.V \<Longrightarrow> connected s u" (* TODO necessary? *)
  unfolding l.V_def
  using connected_append_edge by blast

lemma shortest_s_path_remains_path:
  assumes "isShortestPath s p u"
  shows "l.isPath s p u"
proof -
  have "(set p) \<subseteq> l.E"
  proof clarify
    fix v w
    assume "(v, w) \<in> set p"
    with assms have "(v, w) \<in> E"
      using isPath_edgeset shortestPath_is_path by blast
    then show "(v, w) \<in> l.E"
      using isShortestPath_level_edge[OF assms \<open>(v, w) \<in> set p\<close>] l_edge_iff by simp
  qed
  moreover from assms have "isLinked s p u"
    using shortestPath_is_path isLinked_if_isPath by blast
  ultimately show "l.isPath s p u" using l.isPath_alt by simp
qed

lemma shortest_s_path_remains_shortest: "isShortestPath s p u \<Longrightarrow> l.isShortestPath s p u"
  using shortest_s_path_remains_path l_sub.shortest_paths_remain_if_contained by blast

lemma l_vertices_connected_in_l: "u \<in> l.V \<Longrightarrow> l.connected s u" unfolding l.connected_def
  using l_vertices_connected_in_base obtain_shortest_path shortest_s_path_remains_path by meson

(* TODO necessary? or reuse from LayerGraphExplicit *)
lemma l_path_adds_to_source_dist: "l.isPath u p v \<Longrightarrow> min_dist s u + length p = min_dist s v"
  by (induction rule: l.isPath_custom_induct) auto

(* TODO necessary? *)
(*lemma all_l_paths_are_shortest_in_base: "l.isPath s p u \<Longrightarrow> isShortestPath s p u"
proof (induction rule: l.isPath_custom_induct)
  case (SelfPath u)
  then show ?case unfolding isShortestPath_def by simp
next
  case (EdgePath u v p w)
  then show ?case sorry
qed*)


lemma connected_iff_in_layering: "s \<noteq> u \<Longrightarrow> connected s u \<longleftrightarrow> u \<in> l.V" (* TODO necessary? *)
proof
  assume "s \<noteq> u" "connected s u"
  then obtain p where "isShortestPath s p u" using obtain_shortest_path by blast
  then have "l.isPath s p u" by (rule shortest_s_path_remains_path)
  thm l.isPath_bwd_cases[OF \<open>l.isPath s p u\<close>] (* TODO remove *)
  with \<open>s \<noteq> u\<close> show "u \<in> l.V" using l.isPath_bwd_cases l.V_def by blast
next
  assume "u \<in> l.V"
  then show "connected s u" by (rule l_vertices_connected_in_base)
qed

theorem s_layering_is_shortest_s_paths_union:
  "isPathUnion (s_layering c s) (shortestSPaths s V)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> l.E"
  then have "connected s u" and min_dist_s: "min_dist s u + 1 = min_dist s v" by auto
  from \<open>connected s u\<close> obtain p where "isPath s p u" "length p = min_dist s u"
    using dist_def min_dist_is_dist by blast
  with \<open>(u, v) \<in> l.E\<close> min_dist_s have "isShortestPath s (p@[(u, v)]) v"
    using isShortestPath_min_dist_def isPath_append_edge by fastforce
  moreover from \<open>(u, v) \<in> l.E\<close> have "v \<in> V" using V_def by blast
  ultimately show "(u, v) \<in> \<Union> (set ` shortestSPaths s V)" unfolding shortestSPaths_def by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` shortestSPaths s V)"
  then obtain p v' where "isShortestPath s p v'" and "(u, v) \<in> set p"
    using shortestSPaths_def by auto
  then show "(u, v) \<in> l.E" using shortest_s_path_remains_path l.isPath_edgeset by blast
qed
end \<comment> \<open>InducedSourceLayering\<close>

definition s_t_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "s_t_layering c s t \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t \<and> Graph.min_dist c s u + 1 + Graph.min_dist c v t = Graph.min_dist c s t then
      c (u, v)
    else
      0"

lemma s_t_layering_subgraph: "isSubgraph (s_t_layering c s t) (s_layering c s)"
  unfolding isSubgraph_def
proof clarify
  fix u v
  assume 0: "s_t_layering c s t (u, v) \<noteq> 0"
  then have "s_t_layering c s t (u, v) = c (u, v)" "Graph.connected c s u" "Graph.connected c v t"
    "Graph.min_dist c s u + 1 + Graph.min_dist c v t = Graph.min_dist c s t"
    unfolding s_t_layering_def case_prod_conv by meson+
  then have "s_layering c s (u, v) = c (u, v)" unfolding s_layering_def
    by (smt (verit, best) Graph.min_dist_is_dist Graph.zero_cap_simp Suc_eq_plus1 case_prod_conv Graph.dist_suc Graph.min_dist_split(1))
  with \<open>s_t_layering c s t (u, v) = c (u, v)\<close> show "s_t_layering c s t (u, v) = s_layering c s (u, v)" by simp
qed (* TODO cleanup *)

locale InducedSourceTargetLayering = InducedSourceLayering c s for c :: "'capacity::linordered_idom graph" and s +
  fixes t :: node
  (* assumes t_node[simp, intro!]: "t \<in> V" *)
  (* assumes s_not_t[simp, intro!]: "s \<noteq> t" *) (* TODO check if necessary *)
begin

sublocale l': Graph "s_t_layering c s t" .

sublocale l'_sub_l: Subgraph "s_t_layering c s t" "s_layering c s" unfolding Subgraph_def
  using s_t_layering_subgraph .

sublocale l'_sub_c: Subgraph "s_t_layering c s t" c unfolding Subgraph_def
  using s_layering_subgraph s_t_layering_subgraph subgraph.order_trans by blast

lemma l'_edgeE:
  assumes "(u, v) \<in> l'.E"
  obtains "(u, v) \<in> E"
    and "connected s u" "connected s v"
    and "connected u t" "connected v t"
    and "min_dist s u + 1 + min_dist v t = min_dist s t"
proof
  from assms show "(u, v) \<in> E"
    by (smt (verit, best) E_def case_prod_conv l'.E_def' mem_Collect_eq s_t_layering_def)
  from assms show "connected s u"
    by (smt (verit) case_prod_conv l'.E_def' mem_Collect_eq s_t_layering_def)
  with \<open>(u, v) \<in> E\<close> show  "connected s v" using connected_append_edge by blast
  from assms have layering_not_z: "s_t_layering c s t (u, v) \<noteq> 0" using l'.E_def by blast
  then show "connected v t" unfolding s_t_layering_def by (smt case_prod_conv)
  with \<open>(u, v) \<in> E\<close> show "connected u t" by (rule connected_prepend_edge)
  from layering_not_z show "min_dist s u + 1 + min_dist v t = min_dist s t" unfolding s_t_layering_def case_prod_conv by meson
qed

lemma l'_edge_iff: "(u, v) \<in> l'.E \<longleftrightarrow> (u, v) \<in> E \<and> connected s u \<and> connected v t \<and> min_dist s u + 1 + min_dist v t = min_dist s t"
  using E_def' l'.E_def' s_t_layering_def by (smt (verit, ccfv_SIG) mem_Collect_eq prod.simps(2))

lemma obtain_shortest_st_path_via_edge:
  assumes "(u, v) \<in> l'.E"
  obtains p p' where "isShortestPath s (p @ (u, v) # p') t"
proof -
  from assms obtain p p' where "isShortestPath s p u" "isShortestPath v p' t"
    and "(u, v) \<in> E"  "min_dist s u + 1 + min_dist v t = min_dist s t"
    using l'_edgeE obtain_shortest_path by metis
  then have "isShortestPath s (p @ (u, v) # p') t" using isShortestPath_min_dist_def isPath_append by simp
  then show ?thesis using that by blast (* TODO prettify *)
qed
(* TODO currently, this is mostly used in conjunction with split_shortest_path_around_edge, make extra lemma? *)

lemma obtain_shortest_st_path_fragments:
  assumes "(u, v) \<in> l'.E"
  obtains p p' where "isShortestPath s p u" "isShortestPath u ((u, v) # p') t"
    and "isShortestPath s (p @ [(u, v)]) v" "isShortestPath v p' t"
  using obtain_shortest_st_path_via_edge[OF assms] split_shortest_path_around_edge by metis

(* TODO check if simp is a useful attribute, and if so, whether the order is reasonable *)
lemma l'_edge_increments_dist:
  assumes "(u, v) \<in> l'.E"
  shows "Suc (min_dist s u) = min_dist s v"
    and "Suc (min_dist v t) = min_dist u t" (*using assms tmp isShortestPath_min_dist_def by auto*)
(* TODO check how to write the conclusions. Using "+ 1" makes for a more readable property, but "Suc"
   might make for a safer simp rule *)
(*
  shows "min_dist s v = min_dist s u + 1" (is ?P1)
    and "min_dist u t = min_dist v t + 1" (is ?P2)
*)
  using obtain_shortest_st_path_fragments[OF assms] isShortestPath_min_dist_def by auto

lemma l'_edge_min_distsE:
  assumes "(u, v) \<in> l'.E"
  obtains "min_dist s v = min_dist s u + 1"
    and "min_dist u t = min_dist v t + 1"
  using assms l'_edge_increments_dist by simp
(* TODO find a better way to use this as an elim rule *)

lemma l'_path_adds_dist:
  assumes "l'.isPath u p v"
  shows "min_dist s u + length p = min_dist s v"
    and "min_dist v t + length p = min_dist u t"
  using assms by (induction rule: l'.isPath_custom_induct) (simp_all add: l'_edge_increments_dist[symmetric])

lemma l'_vertexE[elim]:
  assumes "u \<in> l'.V"
  obtains "u \<in> V"
    and "connected s u" "connected u t"
    and "min_dist s u + min_dist u t = min_dist s t"
proof
  from assms show "u \<in> V" using l'_sub_c.V_ss by blast
  from assms show "connected s u" "connected u t"
    using l'.V_def l'_edgeE by blast+
  from assms show "min_dist s u + min_dist u t = min_dist s t"
    by (rule l'.vertex_cases) (auto elim: l'_edgeE simp: l'_edge_increments_dist[symmetric]) (* TODO make this more concise *)
qed

lemma shortest_s_t_path_remains_path:
  assumes "isShortestPath s p t"
  shows "l'.isPath s p t"
proof -
  have "(set p) \<subseteq> l'.E"
  proof clarify
    fix v w
    assume "(v, w) \<in> set p"
    with assms have "(v, w) \<in> E" using isPath_edgeset shortestPath_is_path by blast
    then show "(v, w) \<in> l'.E"
      using isShortestPath_level_edge[OF assms \<open>(v, w) \<in> set p\<close>] l'_edge_iff by simp
  qed
  moreover from assms have "isLinked s p t"
    using shortestPath_is_path isLinked_if_isPath by blast
  ultimately show "l'.isPath s p t" using l'.isPath_alt by simp
qed

lemma l'_vertices_dual_connected_in_l': "u \<in> l'.V \<Longrightarrow> l'.connected s u \<and> l'.connected u t"
proof
  assume "u \<in> l'.V"
  then have "connected s u" "connected u t" "min_dist s u + min_dist u t = min_dist s t" by auto
  then obtain p p' where "isPath s p u" "isPath u p' t" "length p + length p' = min_dist s t"
    using obtain_shortest_path isShortestPath_min_dist_def by (metis (no_types, opaque_lifting))
  then have "isShortestPath s (p @ p') t" using isPath_append isShortestPath_min_dist_def by auto
  moreover from \<open>isPath s p u\<close> \<open>isPath u p' t\<close> have "isLinked s p u" "isLinked u p' t"
    using isLinked_if_isPath by auto
  ultimately show "l'.connected s u" "l'.connected u t" unfolding l'.connected_def
    using shortest_s_t_path_remains_path l'.isPath_alt l'.isPath_append by meson+
qed

lemma shortest_s_t_path_remains_shortest: "isShortestPath s p t \<Longrightarrow> l'.isShortestPath s p t"
  using shortest_s_path_remains_path shortest_s_t_path_remains_path l'_sub_c.shortest_paths_remain_if_contained by blast

theorem s_t_layering_is_shortest_s_t_paths_union:
  "isPathUnion (s_t_layering c s t) (shortestSTPaths s t)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> l'.E"
  then obtain p p' where "isShortestPath s (p @ (u, v) # p') t" by (rule obtain_shortest_st_path_via_edge)
  then show "(u, v) \<in> \<Union> (set ` shortestSTPaths s t)" unfolding shortestSTPaths_def by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` shortestSTPaths s t)"
  then obtain p where "isShortestPath s p t" and "(u, v) \<in> set p" using shortestSTPaths_def by auto
  then show "(u, v) \<in> l'.E" using shortest_s_t_path_remains_path l'.isPath_edgeset by blast
qed
end \<comment> \<open>InducedSourceTargetLayering\<close>

end
theory LayerGraph
imports Subgraph
begin

(* TODO check if this is necessary/helpful *)
locale LayerGraphExplicit = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
  fixes  layer :: "node \<Rightarrow> nat"
  assumes fully_connected: "\<forall>u \<in> V. connected s u"
  assumes s_in_layer_zero: "layer s = 0"
  assumes layered: "\<forall>(u, v) \<in> E. layer u + 1 = layer v"
begin
lemma path_ascends_layers[dest]: "isPath u p v \<Longrightarrow> layer v = layer u + length p"
proof (induction rule: isPath_custom_induct)
  case (SelfPath u)
  then show ?case by simp
next
  case (EdgePath u v p w)
  then show ?case using layered by fastforce
qed

lemma paths_unique_len: "\<lbrakk>isPath u p1 v; isPath u p2 v\<rbrakk> \<Longrightarrow> length p1 = length p2"
  by fastforce

definition unique_dist :: "node \<Rightarrow> node \<Rightarrow> nat"
  where "unique_dist u v = (THE d. dist u d v)"

lemma unique_dist_is_min_dist: "connected u v \<Longrightarrow> unique_dist u v = min_dist u v"
  unfolding unique_dist_def
proof (rule the_equality)
  assume "connected u v"
  then show "dist u (min_dist u v) v" unfolding connected_def min_dist_def dist_def
    by (smt (verit, best) LeastI) (* TODO prettify *)
next
  fix d
  show "dist u d v \<Longrightarrow> d = min_dist u v" unfolding min_dist_def dist_def using paths_unique_len
    by (smt (verit, best) LeastI) (* TODO prettify *)
qed
(* TODO check if these lemmata for uniqueness suffice *)

lemma s_node_for_nonempty: "V \<noteq> {} \<Longrightarrow> s \<in> V"
proof -
  assume "V \<noteq> {}"
  then obtain u where "u \<in> V" by blast
  with fully_connected obtain p where "isPath s p u" unfolding connected_def by blast
  then show "s \<in> V"
    using \<open>u \<in> V\<close> connected_inV_iff fully_connected by blast (* TODO prettify *)
qed

thm the_equality[symmetric]

lemma l_is_s_dist: "u \<in> V \<Longrightarrow> layer u = unique_dist s u"
proof -
  assume "u \<in> V"
  with fully_connected obtain p where "isPath s p u" unfolding connected_def by blast
  with path_ascends_layers s_in_layer_zero have "layer u = length p" by simp
  thm the_equality[symmetric]
  with \<open>isPath s p u\<close>  show "layer u = unique_dist s u" unfolding unique_dist_def dist_def
    by (smt (verit, del_insts) add_0 path_ascends_layers s_in_layer_zero the_equality) (* TODO prettify *)
qed

lemma only_s_in_layer_zero: "u \<in> V \<Longrightarrow> layer u = 0 \<Longrightarrow> u = s" (* TODO easier with prev lemma? *)
proof -
  assume "u \<in> V" "layer u = 0"
  then obtain p where "isPath s p u" using fully_connected connected_def by blast
  with \<open>layer u = 0\<close> s_in_layer_zero have "length p = 0" by fastforce
  with \<open>isPath s p u\<close> show "u = s" by simp
qed

lemma all_paths_are_shortest: "isPath u p v \<Longrightarrow> isShortestPath u p v" unfolding isShortestPath_def
  by (metis le_refl paths_unique_len)
end

(*
definition layering :: "_ graph \<Rightarrow> node \<Rightarrow> _ graph"
  where "layering c s \<equiv> \<lambda>(u, v).
    if Graph.min_dist c s u + 1 = Graph.min_dist c s v then
      c (u, v)
    else
      0"
*)

locale InducedLayeredGraph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
  assumes s_node[simp, intro!]: "s \<in> V"
begin

definition layering :: "'capacity graph"
  where "layering \<equiv> \<lambda>(u, v).
    if connected s u \<and> min_dist s u + 1 = min_dist s v then
      c (u, v)
    else
      0"

sublocale l: Graph layering .

sublocale l_sub: Subgraph layering c
  unfolding Subgraph_def isSubgraph_def layering_def by simp

(* TODO check if this is a good idea, and if "connected s v" should also be a property *)
lemma layer_edgeE[elim]:
  assumes "(u, v) \<in> l.E"
  obtains "(u, v) \<in> E" "connected s u" "connected s v" "min_dist s u + 1 = min_dist s v"
proof
  from assms show "(u, v) \<in> E" using l_sub.E_ss by blast
  from assms have layering_not_z: "layering (u, v) \<noteq> 0"
    using l.E_def by blast
  then show "connected s u" unfolding layering_def by (smt case_prod_conv)
  with \<open>(u, v) \<in> E\<close> show "connected s v" using connected_append_edge by blast
  from layering_not_z show "min_dist s u + 1 = min_dist s v" unfolding layering_def by (smt case_prod_conv)
qed

lemma layer_edge_iff: "(u, v) \<in> l.E \<longleftrightarrow> (u, v) \<in> E \<and> connected s u \<and> min_dist s u + 1 = min_dist s v"
  using E_def' l.E_def' layering_def by auto

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
      using isShortestPath_level_edge[OF assms \<open>(v, w) \<in> set p\<close>] layer_edge_iff by simp
  qed
  moreover from assms have "isLinked s p u"
    using shortestPath_is_path isLinked_if_isPath by blast
  ultimately show "l.isPath s p u" using l.isPath_alt by simp
qed

lemma shortest_s_path_remains_shortest: "isShortestPath s p u \<Longrightarrow> l.isShortestPath s p u"
  using shortest_s_path_remains_path l_sub.shortest_paths_remain_if_contained by blast

lemma tmp: "l.isShortestPath s p u \<Longrightarrow> isShortestPath s p u" sorry


sublocale l: LayerGraphExplicit "layering" s "min_dist s"
proof
  show "\<forall>u\<in>l.V. l.connected s u"
  proof
    fix u
    assume "u \<in> l.V"
    then have "connected s u" by (rule l_vertices_connected_in_base)
    then obtain p where "isShortestPath s p u" by (rule obtain_shortest_path)
    then have "l.isPath s p u" by (rule shortest_s_path_remains_path)
    then show "l.connected s u" unfolding l.connected_def by blast
  qed
next
  show "min_dist s s = 0" by (rule min_dist_z)
next
  show "\<forall>(u, v) \<in> l.E. min_dist s u + 1 = min_dist s v" using layer_edge_iff by blast
qed
(*
  by (metis (mono_tags, lifting) Graph.min_dist_z LayerGraphExplicit.intro case_prodI2 l.connected_def l_vertices_connected_in_base layer_edge_iff obtain_shortest_path shortest_s_path_remains_path)
*)

theorem connected_iff_in_layering: "s \<noteq> u \<Longrightarrow> connected s u \<longleftrightarrow> u \<in> l.V"
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
end

text \<open>Shortcut for the default way of starting an equality proof of edge sets.\<close>
lemma pair_set_eqI:
"\<lbrakk>\<And>a b. (a, b) \<in> A \<Longrightarrow> (a, b) \<in> B; \<And>a b. (a, b) \<in> B \<Longrightarrow> (a, b) \<in> A\<rbrakk> \<Longrightarrow> A = B"
  by (rule set_eqI, unfold split_paired_all, rule iffI)

section \<open>Path Union\<close>
definition isPathUnion :: "_ graph \<Rightarrow> path set \<Rightarrow> bool"
  where "isPathUnion c p_set \<equiv> Graph.E c = \<Union>(set ` p_set)"

context Graph
begin
definition allShortestPaths :: "node set \<Rightarrow> node set \<Rightarrow> path set"
  where "allShortestPaths s_set t_set \<equiv> {p. \<exists>s \<in> s_set. \<exists>t \<in> t_set. isShortestPath s p t}"

definition shortestSPaths :: "node \<Rightarrow> node set \<Rightarrow> path set"
  where "shortestSPaths s t_set \<equiv> {p. \<exists>t \<in> t_set. isShortestPath s p t}"

definition shortestSTPaths :: "node \<Rightarrow> node \<Rightarrow> path set"
  where "shortestSTPaths s t \<equiv> {p. isShortestPath s p t}"

lemma allShortestPaths_singleton_simps[simp]:
  "allShortestPaths {s} t_set = shortestSPaths s t_set"
  "shortestSPaths s {t} = shortestSTPaths s t"
  unfolding allShortestPaths_def shortestSPaths_def shortestSTPaths_def
  by simp_all

lemma graph_is_all_shortest_paths_union:
  assumes no_self_loop: "\<forall>u. (u, u) \<notin> E"
  shows "isPathUnion c (allShortestPaths V V)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> E"
  then have "u \<in> V" "v \<in> V" unfolding V_def by blast+
  moreover have "isShortestPath u [(u, v)] v"
  proof -
    from \<open>(u, v) \<in> E\<close> no_self_loop have "u \<noteq> v" by blast
    then have "\<forall>p'. isPath u p' v \<longrightarrow> length [(u, v)] \<le> length p'"
      using not_less_eq_eq by fastforce
    moreover from \<open>(u, v) \<in> E\<close> have "isPath u [(u, v)] v" by simp
    ultimately show ?thesis unfolding isShortestPath_def by simp
  qed
  ultimately show "(u, v) \<in> \<Union> (set ` allShortestPaths V V)" unfolding allShortestPaths_def by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` allShortestPaths V V)"
  then obtain p u' v' where "isShortestPath u' p v'" and "(u, v) \<in> set p"
    using allShortestPaths_def by auto
  then show "(u, v) \<in> E" using isPath_edgeset shortestPath_is_path by blast
qed
end


context InducedLayeredGraph
begin
lemma layer_graph_is_all_shortest_s_paths_union:
  assumes no_s_self_loop: "(s, s) \<notin> E" (* TODO check if needed *)
  shows "isPathUnion layering (shortestSPaths s V)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> l.E"
  thm layer_edge_iff
  then obtain p where "l.isPath s p v" "(u, v) \<in> set p" sorry
      (*apply (meson layer_edgeE obtain_shortest_path shortest_s_path_remains_path)*)
  then have "l.isShortestPath s p v" using l.all_paths_are_shortest by simp
  then show "(u, v) \<in> \<Union> (set ` shortestSPaths s V)" sorry
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` shortestSPaths s V)"
  then obtain p v' where "isShortestPath s p v'" and "(u, v) \<in> set p"
    using shortestSPaths_def by auto
  then show "(u, v) \<in> l.E" using shortest_s_path_remains_path l.isPath_edgeset by blast
qed
end


end
theory LayerGraph
  imports Subgraph
begin

subsection \<open>Layering from a source node\<close>

locale Generic_Layer_Graph = Graph +
  fixes layer
  assumes paths_ascend_layer: "isPath u p v \<Longrightarrow> layer v = layer u + length p"
begin
corollary dist_layer: "dist u d v \<Longrightarrow> layer v = layer u + d"
  unfolding dist_def using paths_ascend_layer by blast

lemma paths_unique_len: "\<lbrakk>isPath u p\<^sub>1 v; isPath u p\<^sub>2 v\<rbrakk> \<Longrightarrow> length p\<^sub>1 = length p\<^sub>2"
  by (fastforce dest: paths_ascend_layer)

corollary dist_unique: "\<lbrakk>dist u d\<^sub>1 v; dist u d\<^sub>2 v\<rbrakk> \<Longrightarrow> d\<^sub>1 = d\<^sub>2"
  unfolding dist_def using paths_unique_len by blast
end

locale S_Layer_Graph = Graph +
  fixes s
  assumes s_connected[intro]: "u \<in> V \<Longrightarrow> connected s u"
      and s_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist s u) = min_dist s v" (* TODO which direction is better for simp? *)
begin
abbreviation "layer \<equiv> min_dist s"
sublocale Generic_Layer_Graph c "min_dist s"
proof unfold_locales
  fix u p v
  assume "isPath u p v"
  then show "min_dist s v = min_dist s u + length p" by (induction rule: isPath_front_induct) auto
qed

(*
lemma path_ascends_layers: "isPath u p v \<Longrightarrow> min_dist s v = min_dist s u + length p"
  by (induction rule: isPath_front_induct) auto

corollary dist_layer: "dist u d v \<Longrightarrow> layer v = layer u + d"
  unfolding dist_def using path_ascends_layers by blast

lemma paths_unique_len: "\<lbrakk>isPath u p\<^sub>1 v; isPath u p\<^sub>2 v\<rbrakk> \<Longrightarrow> length p\<^sub>1 = length p\<^sub>2"
  by (fastforce dest: path_ascends_layers)

corollary dist_unique: "\<lbrakk>dist u d\<^sub>1 v; dist u d\<^sub>2 v\<rbrakk> \<Longrightarrow> d\<^sub>1 = d\<^sub>2"
  unfolding dist_def using paths_unique_len by blast
*)

lemma s_in_V_if_nonempty: "V \<noteq> {} \<Longrightarrow> s \<in> V"
  using connected_inV_iff by blast

lemma only_s_without_incoming[simp]: "\<lbrakk>u \<in> V; incoming u = {}\<rbrakk> \<Longrightarrow> u = s"
  using distinct_nodes_have_in_out_if_connected by blast

(*
lemma all_paths_are_shortest[intro]: "isPath u p v \<Longrightarrow> isShortestPath u p v"
  unfolding isShortestPath_def using paths_unique_len by (metis order_refl)
*)
end

subsubsection \<open>Building a source layering from an arbitrary graph\<close>

definition induced_s_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "induced_s_layering c s \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Suc (Graph.min_dist c s u) = Graph.min_dist c s v then
      c (u, v)
    else
      0"

lemma induced_s_layering_subgraph: "isSubgraph (induced_s_layering c s) c"
  unfolding isSubgraph_def induced_s_layering_def by simp

locale S_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
begin

sublocale sl: Graph "induced_s_layering c s" .

sublocale sl_sub: Subgraph "induced_s_layering c s" c
  unfolding Subgraph_def using induced_s_layering_subgraph .

(* TODO check if this is a good idea, and if "connected s v" should also be a property *)
(*lemma sl_edgeE(*[elim]*):
  assumes "(u, v) \<in> sl.E"
  obtains "(u, v) \<in> E"
    and "connected s u" "connected s v" "Suc (min_dist s u) = min_dist s v"
proof
  from assms show "(u, v) \<in> E" using sl_sub.E_ss by blast
  from assms have layering_not_z: "induced_s_layering c s (u, v) \<noteq> 0" using sl.E_def by blast
  then show "connected s u" unfolding induced_s_layering_def by (smt case_prod_conv)
  then show "connected s v" using  \<open>(u, v) \<in> E\<close> by (rule connected_append_edge)
  from layering_not_z show "Suc (min_dist s u) = min_dist s v" unfolding induced_s_layering_def by (clarify, meson)
qed*)

lemma sl_edgeD[dest]:
  assumes "(u, v) \<in> sl.E"
  shows "(u, v) \<in> E \<and> connected s u \<and> connected s v \<and> Suc (min_dist s u) = min_dist s v"
proof (intro conjI)
  from assms show "(u, v) \<in> E" using sl_sub.E_ss by blast
  from assms have layering_not_z: "induced_s_layering c s (u, v) \<noteq> 0" using sl.E_def by blast
  then show "connected s u" unfolding induced_s_layering_def by (smt case_prod_conv)
  then show "connected s v" using  \<open>(u, v) \<in> E\<close> by (rule connected_append_edge)
  from layering_not_z show "Suc (min_dist s u) = min_dist s v" unfolding induced_s_layering_def by (clarify, meson)
qed

lemma sl_edge_iff: "(u, v) \<in> sl.E \<longleftrightarrow> (u, v) \<in> E \<and> connected s u \<and> Suc (min_dist s u) = min_dist s v"
  unfolding induced_s_layering_def Graph.E_def by simp

lemma shortest_s_path_remains_path:
  "isShortestPath s p u \<Longrightarrow> sl.isPath s p u" unfolding sl.isPath_alt
proof
  assume SP: "isShortestPath s p u"
  then show "isLinked s p u"
    using shortestPath_is_path isLinked_if_isPath by blast
  show "(set p) \<subseteq> sl.E"
  proof clarify
    fix v w
    assume SET: "(v, w) \<in> set p"
    with SP have "(v, w) \<in> E" using isPath_edgeset shortestPath_is_path by blast
    moreover have "connected s v" "Suc (min_dist s v) = min_dist s w"
      using isShortestPath_level_edge[OF SP SET] by auto
    ultimately show "(v, w) \<in> sl.E" unfolding sl_edge_iff by simp
  qed
qed

lemma sl_s_path_is_shortest_base_path: "sl.isPath s p u \<Longrightarrow> isShortestPath s p u"
  apply (induction rule: sl.isPath_back_induct)
   apply (simp add: isShortestPath_def)
  by (auto intro: shortestPath_append)

lemma shortest_s_path_iff[simp]: "sl.isShortestPath s p u \<longleftrightarrow> isShortestPath s p u"
  by (auto intro:
        shortest_s_path_remains_path
        sl_sub.shortest_paths_remain_if_contained
        sl_s_path_is_shortest_base_path
        sl.shortestPath_is_path)

lemma min_s_dist_eq[simp]: "connected s u \<Longrightarrow> sl.min_dist s u = min_dist s u"
  using Graph.isShortestPath_min_dist_def shortest_s_path_iff obtain_shortest_path by metis

sublocale sl: S_Layer_Graph "induced_s_layering c s" s unfolding S_Layer_Graph_def sl.connected_def
  apply auto
  apply (elim sl.vertex_cases; drule sl_edgeD)
  apply (auto elim!: sl.vertex_cases dest: sl_edgeD)
   apply (elim obtain_shortest_path)
  apply (auto intro: shortest_s_path_remains_path)
  apply (auto intro!: shortest_s_path_remains_path elim: obtain_shortest_path)


  by (fastforce intro: shortest_s_path_remains_path elim: sl.vertex_cases obtain_shortest_path)

(*
sublocale sl: S_Layer_Graph "induced_s_layering c s" s unfolding S_Layer_Graph_def sl.connected_def
  by (fastforce intro: shortest_s_path_remains_path elim: sl.vertex_cases obtain_shortest_path)
*)

(*lemma connected_iff_in_layering: "s \<noteq> u \<Longrightarrow> connected s u \<longleftrightarrow> u \<in> sl.V" (* TODO necessary? *)
proof
  assume "s \<noteq> u" "connected s u"
  then obtain p where "isShortestPath s p u" using obtain_shortest_path by blast
  then have "sl.isPath s p u" by (rule shortest_s_path_remains_path)
  thm sl.isPath_bwd_cases[OF \<open>sl.isPath s p u\<close>] (* TODO remove *)
  with \<open>s \<noteq> u\<close> show "u \<in> sl.V" using sl.isPath_bwd_cases sl.V_def by blast
next
  assume "u \<in> sl.V"
  then show "connected s u" by (rule sl_vertices_connected_in_base)
qed*)

theorem induced_s_layering_is_shortest_s_paths_union:
  "isPathUnion (induced_s_layering c s) (shortestSPaths s V)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> sl.E"
  then have "connected s u" and min_dist_s: "min_dist s u + 1 = min_dist s v" by auto
  from \<open>connected s u\<close> obtain p where "isPath s p u" "length p = min_dist s u"
    using dist_def min_dist_is_dist by blast
  with \<open>(u, v) \<in> sl.E\<close> min_dist_s have "isShortestPath s (p@[(u, v)]) v"
    using isShortestPath_min_dist_def isPath_append_edge by fastforce
  moreover from \<open>(u, v) \<in> sl.E\<close> have "v \<in> V" using V_def by blast
  ultimately show "(u, v) \<in> \<Union> (set ` shortestSPaths s V)" unfolding shortestSPaths_def by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` shortestSPaths s V)"
  then obtain p v' where "isShortestPath s p v'" and "(u, v) \<in> set p"
    using shortestSPaths_def by auto
  then show "(u, v) \<in> sl.E" using shortest_s_path_remains_path sl.isPath_edgeset by blast
qed
end \<comment> \<open>S_Graph\<close>

subsection \<open>Layering from source to target node\<close>

locale T_Layer_Graph = Graph +
  fixes t
  assumes t_connected[intro]: "u \<in> V \<Longrightarrow> connected u t"
      and t_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist v t) = min_dist u t"
begin
lemma t_in_V_if_nonempty: "V \<noteq> {} \<Longrightarrow> t \<in> V"
  using connected_inV_iff by blast

lemma only_t_without_outgoing[simp]: "\<lbrakk>u \<in> V; outgoing u = {}\<rbrakk> \<Longrightarrow> u = t"
  using distinct_nodes_have_in_out_if_connected by blast
end

locale ST_Layer_Graph = Graph +
  fixes s t
  assumes s_connected[intro]: "u \<in> V \<Longrightarrow> connected s u"
      and t_connected[intro]: "u \<in> V \<Longrightarrow> connected u t"
      and st_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist s u + min_dist v t) = min_dist s t"
begin

lemma obtain_shortest_st_path_via_edge:
  assumes "(u, v) \<in> E"
  obtains p p' where "isShortestPath s (p @ (u, v) # p') t"
proof -
  from assms have "u \<in> V" "v \<in> V" unfolding V_def by auto
  then obtain p p' where "isShortestPath s p u" "isShortestPath v p' t"
    by (meson obtain_shortest_path s_connected t_connected)
  with assms have "isShortestPath s (p @ (u, v) # p') t"
    using isShortestPath_min_dist_def isPath_append by simp
  then show ?thesis using that by blast (* TODO prettify *)
qed

(*thm obtain_shortest_st_path_via_edge[THEN split_shortest_path_around_edge]*)

(*lemma obtain_shortest_st_path_fragments: (* TODO necessary? direct consequence of split_shortest_path_around_edge *)
  assumes "(u, v) \<in> E"
  obtains p p' where "isShortestPath s p u" "isShortestPath u ((u, v) # p') t"
    and "isShortestPath s (p @ [(u, v)]) v" "isShortestPath v p' t"
  using obtain_shortest_st_path_via_edge[OF assms] split_shortest_path_around_edge by metis*)

sublocale S_Layer_Graph unfolding S_Layer_Graph_def
  by (fastforce elim: obtain_shortest_st_path_via_edge dest: split_shortest_path_around_edge simp: isShortestPath_min_dist_def)

sublocale T_Layer_Graph unfolding T_Layer_Graph_def
  by (fastforce elim: obtain_shortest_st_path_via_edge dest: split_shortest_path_around_edge simp: isShortestPath_min_dist_def)
  (* by (auto intro: obtain_shortest_st_path_fragments simp: isShortestPath_min_dist_def) *)
end

definition st_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "st_layering c s t \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t \<and> Graph.min_dist c s u + 1 + Graph.min_dist c v t = Graph.min_dist c s t then
      c (u, v)
    else
      0"

lemma st_layering_subgraph: "isSubgraph (st_layering c s t) (induced_s_layering c s)"
  unfolding isSubgraph_def
proof clarify
  fix u v
  assume 0: "st_layering c s t (u, v) \<noteq> 0"
  then have "st_layering c s t (u, v) = c (u, v)" "Graph.connected c s u" "Graph.connected c v t"
    "Graph.min_dist c s u + 1 + Graph.min_dist c v t = Graph.min_dist c s t"
    unfolding st_layering_def case_prod_conv by meson+
  then have "induced_s_layering c s (u, v) = c (u, v)" unfolding induced_s_layering_def
    by (smt (verit, best) Graph.min_dist_is_dist Graph.zero_cap_simp Suc_eq_plus1 case_prod_conv Graph.dist_suc Graph.min_dist_split(1))
  with \<open>st_layering c s t (u, v) = c (u, v)\<close> show "st_layering c s t (u, v) = induced_s_layering c s (u, v)" by simp
qed (* TODO cleanup *)


locale T_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes t :: node

locale ST_Graph = S_Graph + T_Graph (*for c :: "'capacity::linordered_idom graph" and s t*)
begin

abbreviation "st_dist \<equiv> min_dist s t"

sublocale stl: Graph "st_layering c s t" .

sublocale stl_sub_sl: Subgraph "st_layering c s t" "induced_s_layering c s" unfolding Subgraph_def
  using st_layering_subgraph .

sublocale stl_sub_c: Subgraph "st_layering c s t" c unfolding Subgraph_def
  using induced_s_layering_subgraph st_layering_subgraph subgraph.order_trans by blast

lemma stl_edgeD[dest]:
  assumes "(u, v) \<in> stl.E"
  shows "(u, v) \<in> E \<and> connected s u \<and> connected s v \<and> connected u t \<and> connected v t
        \<and> min_dist s u + 1 + min_dist v t = min_dist s t"
proof (intro conjI)
  from assms show "(u, v) \<in> E"
    by (smt (verit, best) E_def case_prod_conv stl.E_def' mem_Collect_eq st_layering_def)
  from assms show "connected s u"
    by (smt (verit) case_prod_conv stl.E_def' mem_Collect_eq st_layering_def)
  with \<open>(u, v) \<in> E\<close> show  "connected s v" using connected_append_edge by blast
  from assms have layering_not_z: "st_layering c s t (u, v) \<noteq> 0" using stl.E_def by blast
  then show "connected v t" unfolding st_layering_def by (smt case_prod_conv)
  with \<open>(u, v) \<in> E\<close> show "connected u t" by (rule connected_prepend_edge)
  from layering_not_z show "min_dist s u + 1 + min_dist v t = min_dist s t" unfolding st_layering_def case_prod_conv by meson
qed

(*
lemma stl_edgeE:
  assumes "(u, v) \<in> stl.E"
  obtains "(u, v) \<in> E"
    and "connected s u" "connected s v"
    and "connected u t" "connected v t"
    and "min_dist s u + 1 + min_dist v t = min_dist s t"
proof
  from assms show "(u, v) \<in> E"
    by (smt (verit, best) E_def case_prod_conv stl.E_def' mem_Collect_eq st_layering_def)
  from assms show "connected s u"
    by (smt (verit) case_prod_conv stl.E_def' mem_Collect_eq st_layering_def)
  with \<open>(u, v) \<in> E\<close> show  "connected s v" using connected_append_edge by blast
  from assms have layering_not_z: "st_layering c s t (u, v) \<noteq> 0" using stl.E_def by blast
  then show "connected v t" unfolding st_layering_def by (smt case_prod_conv)
  with \<open>(u, v) \<in> E\<close> show "connected u t" by (rule connected_prepend_edge)
  from layering_not_z show "min_dist s u + 1 + min_dist v t = min_dist s t" unfolding st_layering_def case_prod_conv by meson
qed
*)

lemma stl_edge_iff: "(u, v) \<in> stl.E \<longleftrightarrow> (u, v) \<in> E \<and> connected s u \<and> connected v t \<and> Suc (min_dist s u + min_dist v t) = min_dist s t"
  unfolding st_layering_def Graph.E_def by simp

sublocale stl: ST_Layer_Graph "st_layering c s t" s t unfolding ST_Layer_Graph_def stl.connected_def
  apply safe
  apply (elim stl.vertex_cases)
  apply (auto elim!: stl.vertex_cases)
      apply (auto dest!: stl_edgeD)
  apply (auto intro!: shortest_s_path_remains_path stl_sub_sl.sg_paths_are_base_paths)

(*lemma obtain_shortest_st_path_via_edge: (* TRANSFERRED *)
  assumes "(u, v) \<in> stl.E"
  obtains p p' where "isShortestPath s (p @ (u, v) # p') t"
proof -
  from assms obtain p p' where "isShortestPath s p u" "isShortestPath v p' t"
    and "(u, v) \<in> E"  "min_dist s u + 1 + min_dist v t = min_dist s t"
    using stl_edgeE obtain_shortest_path by metis
  then have "isShortestPath s (p @ (u, v) # p') t" using isShortestPath_min_dist_def isPath_append by simp
  then show ?thesis using that by blast (* TODO prettify *)
qed
(* TODO currently, this is mostly used in conjunction with split_shortest_path_around_edge, make extra lemma? *)

lemma obtain_shortest_st_path_fragments: (* TRANSFERRED *)
  assumes "(u, v) \<in> stl.E"
  obtains p p' where "isShortestPath s p u" "isShortestPath u ((u, v) # p') t"
    and "isShortestPath s (p @ [(u, v)]) v" "isShortestPath v p' t"
  using obtain_shortest_st_path_via_edge[OF assms] split_shortest_path_around_edge by metis*)

(* TODO check if simp is a useful attribute, and if so, whether the order is reasonable *)
(*lemma stl_edge_increments_dist:
  assumes "(u, v) \<in> stl.E"
  shows "Suc (min_dist s u) = min_dist s v"
    and "Suc (min_dist v t) = min_dist u t" (*using assms tmp isShortestPath_min_dist_def by auto*)
(* TODO check how to write the conclusions. Using "+ 1" makes for a more readable property, but "Suc"
   might make for a safer simp rule *)
(*
  shows "min_dist s v = min_dist s u + 1" (is ?P1)
    and "min_dist u t = min_dist v t + 1" (is ?P2)
*)
  using obtain_shortest_st_path_fragments[OF assms] isShortestPath_min_dist_def by auto

lemma stl_edge_min_distsE:
  assumes "(u, v) \<in> stl.E"
  obtains "min_dist s v = min_dist s u + 1"
    and "min_dist u t = min_dist v t + 1"
  using assms stl_edge_increments_dist by simp*)
(* TODO find a better way to use this as an elim rule *)

lemma stl_path_adds_dist:
  assumes "stl.isPath u p v"
  shows "min_dist s u + length p = min_dist s v"
    and "min_dist v t + length p = min_dist u t"
  using assms by (induction rule: stl.isPath_front_induct) (simp_all add: stl_edge_increments_dist[symmetric])

lemma stl_vertexE[elim]:
  assumes "u \<in> stl.V"
  obtains "u \<in> V"
    and "connected s u" "connected u t"
    and "min_dist s u + min_dist u t = min_dist s t"
proof
  from assms show "u \<in> V" using stl_sub_c.V_ss by blast
  from assms show "connected s u" "connected u t"
    using stl.V_def stl_edgeE by blast+
  from assms show "min_dist s u + min_dist u t = min_dist s t"
    by (rule stl.vertex_cases) (auto elim: stl_edgeE simp: stl_edge_increments_dist[symmetric]) (* TODO make this more concise *)
qed

lemma shortest_st_path_remains_path:
  assumes "isShortestPath s p t"
  shows "stl.isPath s p t"
proof -
  have "(set p) \<subseteq> stl.E"
  proof clarify
    fix v w
    assume "(v, w) \<in> set p"
    with assms have "(v, w) \<in> E" using isPath_edgeset shortestPath_is_path by blast
    then show "(v, w) \<in> stl.E"
      using isShortestPath_level_edge[OF assms \<open>(v, w) \<in> set p\<close>] stl_edge_iff by simp
  qed
  moreover from assms have "isLinked s p t"
    using shortestPath_is_path isLinked_if_isPath by blast
  ultimately show "stl.isPath s p t" using stl.isPath_alt by simp
qed

corollary stl_maintains_st_connected: "connected s t \<Longrightarrow> stl.connected s t"
  using obtain_shortest_path shortest_st_path_remains_path stl.connected_def by metis

lemma stl_vertices_dual_connected_in_stl: "u \<in> stl.V \<Longrightarrow> stl.connected s u \<and> stl.connected u t"
proof
  assume "u \<in> stl.V"
  then have "connected s u" "connected u t" "min_dist s u + min_dist u t = min_dist s t" by auto
  then obtain p p' where "isPath s p u" "isPath u p' t" "length p + length p' = min_dist s t"
    using obtain_shortest_path isShortestPath_min_dist_def by (metis (no_types, opaque_lifting))
  then have "isShortestPath s (p @ p') t" using isPath_append isShortestPath_min_dist_def by auto
  moreover from \<open>isPath s p u\<close> \<open>isPath u p' t\<close> have "isLinked s p u" "isLinked u p' t"
    using isLinked_if_isPath by auto
  ultimately show "stl.connected s u" "stl.connected u t" unfolding stl.connected_def
    using shortest_st_path_remains_path stl.isPath_alt stl.isPath_append by meson+
qed

lemma shortest_st_path_remains_shortest: "isShortestPath s p t \<Longrightarrow> stl.isShortestPath s p t"
  using shortest_s_path_remains_path shortest_st_path_remains_path stl_sub_c.shortest_paths_remain_if_contained by blast

lemma only_s_without_stl_incoming: "u \<in> stl.V \<Longrightarrow> stl.incoming u = {} \<Longrightarrow> u = s"
  using stl_vertices_dual_connected_in_stl stl.distinct_nodes_have_in_out_if_connected by blast

lemma only_t_without_stl_outgoing: "u \<in> stl.V \<Longrightarrow> stl.outgoing u = {} \<Longrightarrow> u = t"
  using stl_vertices_dual_connected_in_stl stl.distinct_nodes_have_in_out_if_connected by blast

(* TODO necessary? *)
lemma only_s_paths_without_stl_incoming:
  "u \<in> stl.V \<Longrightarrow> stl.incoming u = {} \<Longrightarrow> stl.isPath u p v \<Longrightarrow> stl.isPath s p v"
  using only_s_without_stl_incoming by blast

lemma only_t_paths_without_stl_outgoing:
  "v \<in> stl.V \<Longrightarrow> stl.outgoing v = {} \<Longrightarrow> stl.isPath u p v \<Longrightarrow> stl.isPath u p t"
  using only_t_without_stl_outgoing by blast

theorem st_layering_is_shortest_st_paths_union:
  "isPathUnion (st_layering c s t) (shortestSTPaths s t)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> stl.E"
  then obtain p p' where "isShortestPath s (p @ (u, v) # p') t" by (rule obtain_shortest_st_path_via_edge)
  then show "(u, v) \<in> \<Union> (set ` shortestSTPaths s t)" unfolding shortestSTPaths_def by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` shortestSTPaths s t)"
  then obtain p where "isShortestPath s p t" and "(u, v) \<in> set p" using shortestSTPaths_def by auto
  then show "(u, v) \<in> stl.E" using shortest_st_path_remains_path stl.isPath_edgeset by blast
qed

lemma stl_path_length_bounded: "stl.isPath u p v \<Longrightarrow> length p \<le> min_dist s t"
  by (metis Graph.connected_def Graph.distinct_nodes_in_V_if_connected(1) ST_Graph.stl_path_adds_dist(2) ST_Graph.stl_vertexE add_cancel_right_right add_leD2 le_add2)
(* TODO cleanup using stl_path_adds_dist *)
(* TODO show finiteness *)
end \<comment> \<open>ST_Graph\<close>

(* TODO needed? *)
(*locale Bounded_ST_Graph = ST_Graph c s t + Distance_Bounded_Graph c b for c :: "'capacity::linordered_idom graph" and s t b*)

context ST_Graph
begin
sublocale stl: Distance_Bounded_Graph "st_layering c s t" "min_dist s t"
  unfolding Distance_Bounded_Graph_def
  using stl.dist_def stl_path_length_bounded by metis
end

end
theory LayerGraph
  imports Subgraph
begin



(* TODO can we somehow make this work? *)
(*
locale Generic_Layer_Graph' = Graph +
  (*fixes layer :: "node \<Rightarrow> 'l :: {one, plus}"*)
  fixes layer :: "node \<Rightarrow> int"
  assumes layer_edge[simp]: "(u, v) \<in> E \<Longrightarrow> layer v = layer u + 1"
begin
lemma path_ascends_layer: "isPath u p v \<Longrightarrow> layer v = layer u + int (length p)"
  by (induction rule: isPath_front_induct) auto

corollary dist_layer: "dist u d v \<Longrightarrow> layer v = layer u + int d"
  unfolding dist_def using path_ascends_layer by blast

lemma paths_unique_len: "\<lbrakk>isPath u p\<^sub>1 v; isPath u p\<^sub>2 v\<rbrakk> \<Longrightarrow> length p\<^sub>1 = length p\<^sub>2"
  by (fastforce dest: path_ascends_layer)

corollary dist_unique: "\<lbrakk>dist u d\<^sub>1 v; dist u d\<^sub>2 v\<rbrakk> \<Longrightarrow> d\<^sub>1 = d\<^sub>2"
  unfolding dist_def using paths_unique_len by blast

lemma path_is_shortest[intro]: "isPath u p v \<Longrightarrow> isShortestPath u p v"
  unfolding isShortestPath_def using paths_unique_len by (metis order_refl)
end
*)

subsection \<open>Layerings\<close>

locale Generic_Layer_Graph = Graph +
  fixes layer :: "node \<Rightarrow> nat"
  assumes layer_edge[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (layer u) = layer v"
begin
lemma path_ascends_layer: "isPath u p v \<Longrightarrow> layer v = layer u + length p"
  by (induction rule: isPath_front_induct) auto

corollary dist_layer: "dist u d v \<Longrightarrow> layer v = layer u + d"
  unfolding dist_def using path_ascends_layer by blast

lemma paths_unique_len: "\<lbrakk>isPath u p\<^sub>1 v; isPath u p\<^sub>2 v\<rbrakk> \<Longrightarrow> length p\<^sub>1 = length p\<^sub>2"
  by (fastforce dest: path_ascends_layer)

corollary dist_unique: "\<lbrakk>dist u d\<^sub>1 v; dist u d\<^sub>2 v\<rbrakk> \<Longrightarrow> d\<^sub>1 = d\<^sub>2"
  unfolding dist_def using paths_unique_len by blast

lemma path_is_shortest[intro]: "isPath u p v \<Longrightarrow> isShortestPath u p v"
  unfolding isShortestPath_def using paths_unique_len by (metis order_refl)
end

locale S_Layer_Graph = Graph +
  fixes s
  assumes s_connected[intro]: "u \<in> V \<Longrightarrow> connected s u"
      and s_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist s u) = min_dist s v" (* TODO which direction is better for simp? *)
begin
abbreviation "layer \<equiv> min_dist s"
sublocale Generic_Layer_Graph c "min_dist s" by unfold_locales simp

lemma s_in_V_if_nonempty: "V \<noteq> {} \<Longrightarrow> s \<in> V"
  using connected_inV_iff by blast

lemma only_s_without_incoming[simp]: "\<lbrakk>u \<in> V; incoming u = {}\<rbrakk> \<Longrightarrow> u = s"
  using distinct_nodes_have_in_out_if_connected by blast

corollary no_incomingD: "incoming u = {} \<Longrightarrow> u \<notin> V \<or> u = s" by simp

lemma front_terminal_path_is_s_path:
  "isPath u p v \<Longrightarrow> v \<in> V \<Longrightarrow> incoming u = {} \<Longrightarrow> isPath s p v"
  using connected_def connected_inV_iff no_incomingD by blast
end

locale T_Layer_Graph = Graph +
  fixes t
  assumes t_connected[intro]: "u \<in> V \<Longrightarrow> connected u t"
      and t_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist v t) = min_dist u t"
begin
lemma t_in_V_if_nonempty: "V \<noteq> {} \<Longrightarrow> t \<in> V"
  using connected_inV_iff by blast

lemma only_t_without_outgoing[simp]: "\<lbrakk>u \<in> V; outgoing u = {}\<rbrakk> \<Longrightarrow> u = t"
  using distinct_nodes_have_in_out_if_connected by blast

corollary no_outgoingD: "outgoing u = {} \<Longrightarrow> u \<notin> V \<or> u = t" by simp

lemma back_terminal_path_is_t_path:
  "isPath u p v \<Longrightarrow> u \<in> V \<Longrightarrow> outgoing v = {} \<Longrightarrow> isPath u p t"
  using connected_def connected_inV_iff no_outgoingD by blast
end

locale ST_Layer_Graph = Graph +
  fixes s t
  assumes st_connected: "u \<in> V \<Longrightarrow> connected s u \<and> connected u t"
      and st_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist s u + min_dist v t) = min_dist s t"
begin

lemma obtain_shortest_st_path_via_edge:
  assumes "(u, v) \<in> E"
  obtains p p' where "isShortestPath s (p @ (u, v) # p') t"
proof -
  from assms have "u \<in> V" "v \<in> V" unfolding V_def by auto
  then obtain p p' where "isShortestPath s p u" "isShortestPath v p' t"
    by (meson obtain_shortest_path st_connected)
  with assms have "isShortestPath s (p @ (u, v) # p') t"
    using isShortestPath_min_dist_def isPath_append by simp
  then show ?thesis using that by blast (* TODO prettify *)
qed (* TODO this idea is reused, can this be prevented? Maybe set this up as Intro for ST_Layer_Graph *)

sublocale S_Layer_Graph unfolding S_Layer_Graph_def
  by (fastforce elim: obtain_shortest_st_path_via_edge
                dest: split_shortest_path_around_edge st_connected
                simp: isShortestPath_min_dist_def)

sublocale T_Layer_Graph unfolding T_Layer_Graph_def
  by (fastforce elim: obtain_shortest_st_path_via_edge
                dest: split_shortest_path_around_edge st_connected
                simp: isShortestPath_min_dist_def)

lemma layer_bounded_by_t: "u \<in> V \<Longrightarrow> layer u \<le> layer t"
  using connected_by_dist dist_layer t_connected by fastforce

sublocale Distance_Bounded_Graph c "min_dist s t"
proof
  fix u v n
  assume DIST: "dist u n v"
  then show "n \<le> layer t"
  proof (cases "u = v")
    case True
    with DIST show ?thesis using dist_layer by fastforce
  next
    case False
    with DIST have "v \<in> V" using connected_distI distinct_nodes_in_V_if_connected(2) by blast
    with DIST show ?thesis using dist_layer layer_bounded_by_t by fastforce
  qed
qed
end

subsection \<open>Union of shortest path\<close>
(* TODO use CapacityCompatibleGraphs *)

locale Shortest_Path_Union = CapacityCompatibleGraphs +
  fixes S T
  assumes shortest_path_union: "E' = \<Union>{set p | p. \<exists>s t. s \<in> S \<and> t \<in> T \<and> g.isShortestPath s p t}"
begin
sublocale Subgraph
  using shortest_path_union g.isPath_edgeset g.shortestPath_is_path by unfold_locales blast

lemma edge_on_shortest_path:
  "(u, v) \<in> E' \<Longrightarrow> \<exists>s t p. s \<in> S \<and> t \<in> T \<and> g.isShortestPath s p t \<and> (u, v) \<in> set p"
  using shortest_path_union by blast

lemma obtain_shortest_ST_edge_path:
  assumes "(u, v) \<in> E'"
  obtains s t p p' where "s \<in> S" "t \<in> T" "g.isShortestPath s (p @ (u, v) # p') t"
  using assms by (metis edge_on_shortest_path in_set_conv_decomp)

lemma shortest_path_remains: "\<lbrakk>u \<in> S; v \<in> T; g.isShortestPath u p v\<rbrakk> \<Longrightarrow> g'.isShortestPath u p v" sorry (* TODO *)
end

locale S_Shortest_Path_Union = CapacityCompatibleGraphs + 
  fixes s T
  assumes shortest_s_path_union: "E' = \<Union>{set p | p. \<exists>t. t \<in> T \<and> g.isShortestPath s p t}"
begin
sublocale Subgraph
  using shortest_s_path_union g.isPath_edgeset g.shortestPath_is_path by unfold_locales blast

sublocale Shortest_Path_Union c' c "{s}" T
  by unfold_locales (simp add: shortest_s_path_union)

(* TODO can we improve on the latter two? *)
thm edge_on_shortest_path[simplified]
thm obtain_shortest_ST_edge_path[simplified]
thm shortest_path_remains[simplified]

lemma obtain_shortest_sT_edge_path:
  assumes "(u, v) \<in> E'"
  obtains t p p' where "t \<in> T" "g.isShortestPath s (p @ (u, v) # p') t"
  using assms by (blast elim: obtain_shortest_ST_edge_path)

sublocale S_Layer_Graph c' s sorry (* TODO *)
end

locale T_Shortest_Path_Union = CapacityCompatibleGraphs +
  fixes S t
  assumes shortest_t_path_union: "E' = \<Union>{set p | p. \<exists>s. s \<in> S \<and> g.isShortestPath s p t}"
begin
sublocale Subgraph
  using shortest_t_path_union g.isPath_edgeset g.shortestPath_is_path by unfold_locales blast

sublocale Shortest_Path_Union c' c S "{t}"
  by unfold_locales (simp add: shortest_t_path_union)

thm edge_on_shortest_path[simplified]

lemma obtain_shortest_St_edge_path:
  assumes "(u, v) \<in> E'"
  obtains s p p' where "s \<in> S" "g.isShortestPath s (p @ (u, v) # p') t"
  using assms by (blast elim: obtain_shortest_ST_edge_path)

sublocale T_Layer_Graph c' t sorry (* TODO *)
end

locale ST_Shortest_Path_Union = CapacityCompatibleGraphs +
  fixes s t
  assumes shortest_st_path_union: "E' = \<Union>{set p | p. g.isShortestPath s p t}"
begin
sublocale Subgraph
  using shortest_st_path_union g.isPath_edgeset g.shortestPath_is_path by unfold_locales blast

sublocale S_Shortest_Path_Union c' c s "{t}"
  by unfold_locales (simp add: shortest_st_path_union)

sublocale T_Shortest_Path_Union c' c "{s}" t
  by unfold_locales (simp add: shortest_st_path_union)

thm edge_on_shortest_path[simplified]

lemma obtain_shortest_st_edge_path: (* TODO this idea is once again reused *)
  assumes "(u, v) \<in> E'"
  obtains p p' where "g.isShortestPath s (p @ (u, v) # p') t"
  using assms by (blast elim: obtain_shortest_ST_edge_path)

sublocale ST_Layer_Graph c' s t sorry (* TODO, using obtain_shortest_st_edge_path, shortest_path_remains and then new Intro for ST_Layer_Edge *)
end

(* TODO move the following transfer properties to the shortest path union locales *)

interpretation ST_Shortest_Path_Union undefined undefined undefined undefined sorry

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
  using Subgraph_isSubgraphI induced_s_layering_subgraph .

lemma sl_edgeD[dest]:
  assumes "(u, v) \<in> sl.E"
  shows "(u, v) \<in> E \<and> connected s u \<and> connected s v \<and> Suc (min_dist s u) = min_dist s v"
proof (intro conjI)
  from assms show "(u, v) \<in> E" using sl_sub.E_ss by blast
  from assms have L_NOT_Z: "induced_s_layering c s (u, v) \<noteq> 0" using sl.E_def by blast
  then show "connected s u" unfolding induced_s_layering_def by (smt case_prod_conv)
  with \<open>(u, v) \<in> E\<close> show "connected s v" by (elim connected_append_edge)
  from L_NOT_Z show "Suc (min_dist s u) = min_dist s v" unfolding induced_s_layering_def by (smt case_prod_conv)
qed

lemma sl_edge_iff: "(u, v) \<in> sl.E \<longleftrightarrow> (u, v) \<in> E \<and> connected s u \<and> Suc (min_dist s u) = min_dist s v"
  unfolding induced_s_layering_def Graph.E_def by simp

lemma sl_shortest_s_path_remains_path:
  assumes SP: "isShortestPath s p u"
  shows "sl.isPath s p u"
  unfolding sl.isPath_alt
proof
  from SP show "isLinked s p u" using shortestPath_is_path isLinked_if_isPath by blast
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
  by (auto intro: shortestPath_append_edge)

lemma sl_shortest_s_path_iff[simp]: "sl.isShortestPath s p u \<longleftrightarrow> isShortestPath s p u"
proof
  assume "sl.isShortestPath s p u"
  then show "isShortestPath s p u"
    using sl.shortestPath_is_path sl_s_path_is_shortest_base_path by blast
next
  assume "isShortestPath s p u"
  then show "sl.isShortestPath s p u"
    using sl_shortest_s_path_remains_path sl_sub.shortest_paths_remain_if_contained by blast
qed

lemma sl_min_s_dist_eq: "connected s u \<Longrightarrow> sl.min_dist s u = min_dist s u"
  using Graph.isShortestPath_min_dist_def sl_shortest_s_path_iff obtain_shortest_path by metis

sublocale sl: S_Layer_Graph "induced_s_layering c s" s
proof
  fix u
  assume "u \<in> sl.V"
  then obtain p where "sl.isShortestPath s p u"
    by (fastforce elim: sl.vertex_cases obtain_shortest_path) (* TODO needs shortest_s_path, add if removed from simp *)
  then show "sl.connected s u"
    unfolding sl.connected_def using sl.shortestPath_is_path by blast
next
  fix u v
  assume "(u, v) \<in> sl.E"
  then show "Suc (sl.min_dist s u) = sl.min_dist s v" by (auto simp: sl_min_s_dist_eq)
qed

(* TODO review how to best transfer min_dist once st_graph enters the mix *)
(*lemma min_dist_eq[simp]:
  assumes CON: "sl.connected u v"
  shows "sl.min_dist u v = min_dist u v"
*)

theorem induced_s_layering_is_shortest_s_paths_union:
  "isPathUnion (induced_s_layering c s) (shortestSPaths s V)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> sl.E"
  then have "(u, v) \<in> E" "connected s u" and S_DIST: "Suc (min_dist s u) = min_dist s v" by auto
  from \<open>connected s u\<close> obtain p where "isShortestPath s p u" by (rule obtain_shortest_path)
  with \<open>(u, v) \<in> E\<close> S_DIST have "isShortestPath s (p @ [(u, v)]) v"
    by (intro shortestPath_append_edge)
  moreover from \<open>(u, v) \<in> E\<close> have "v \<in> V" using V_def by blast
  ultimately show "(u, v) \<in> \<Union> (set ` shortestSPaths s V)" unfolding shortestSPaths_def by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` shortestSPaths s V)"
  then obtain p v' where "isShortestPath s p v'" and "(u, v) \<in> set p"
    using shortestSPaths_def by auto
  then show "(u, v) \<in> sl.E" using sl_shortest_s_path_remains_path sl.isPath_edgeset by blast
qed
end \<comment> \<open>S_Graph\<close>

subsection \<open>Layering from source to target node\<close>


definition st_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "st_layering c s t \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t \<and> Suc (Graph.min_dist c s u + Graph.min_dist c v t) = Graph.min_dist c s t then
      c (u, v)
    else
      0"

lemma st_layering_subgraph: "isSubgraph (st_layering c s t) (induced_s_layering c s)"
  unfolding isSubgraph_def induced_s_layering_def st_layering_def
  apply (auto dest!: Graph.min_dist_is_dist intro!: Graph.zero_cap_simp)
  using Graph.dist_suc Graph.min_dist_split(1) by fastforce (* TODO prettify *)
(*
proof clarify
  fix u v
  assume 0: "st_layering c s t (u, v) \<noteq> 0"
  then have "st_layering c s t (u, v) = c (u, v)" "Graph.connected c s u" "Graph.connected c v t"
    "Graph.min_dist c s u + 1 + Graph.min_dist c v t = Graph.min_dist c s t"
    unfolding st_layering_def case_prod_conv by meson+
  then have "induced_s_layering c s (u, v) = c (u, v)" unfolding induced_s_layering_def
    by (smt (verit, best) Graph.min_dist_is_dist Graph.zero_cap_simp Suc_eq_plus1 case_prod_conv Graph.dist_suc Graph.min_dist_split(1))
  with \<open>st_layering c s t (u, v) = c (u, v)\<close> show "st_layering c s t (u, v) = induced_s_layering c s (u, v)" by simp
qed
*)

locale T_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes t :: node

locale ST_Graph = S_Graph + T_Graph
begin

abbreviation "st_dist \<equiv> min_dist s t"

sublocale stl: Graph "st_layering c s t" .

sublocale stl_sub_sl: Subgraph "st_layering c s t" "induced_s_layering c s"
  using Subgraph_isSubgraphI st_layering_subgraph .

sublocale stl_sub_c: Subgraph "st_layering c s t" c
  using induced_s_layering_subgraph st_layering_subgraph subgraph.order_trans by blast

lemma stl_edgeD[dest]:
  assumes "(u, v) \<in> stl.E"
  shows "(u, v) \<in> E \<and> connected s u \<and> connected s v \<and> connected u t \<and> connected v t
        \<and> Suc (min_dist s u + min_dist v t) = min_dist s t"
proof (intro conjI)
  from assms show "(u, v) \<in> E" using stl_sub_c.E_ss by blast
  from assms have L_NOT_Z: "st_layering c s t (u, v) \<noteq> 0" using stl.E_def by blast
  then show "connected s u" "connected v t" unfolding st_layering_def by (smt case_prod_conv)+
  with \<open>(u, v) \<in> E\<close> show "connected s v" "connected u t"
    by (auto elim: connected_append_edge connected_prepend_edge)
  from L_NOT_Z show "Suc (min_dist s u + min_dist v t) = st_dist"
    unfolding st_layering_def by (smt case_prod_conv)
qed


lemma stl_edge_iff: "(u, v) \<in> stl.E \<longleftrightarrow> (u, v) \<in> E \<and> connected s u \<and> connected v t \<and> Suc (min_dist s u + min_dist v t) = min_dist s t"
  unfolding st_layering_def Graph.E_def by simp

lemma stl_shortest_st_path_remains_path:
  assumes SP: "isShortestPath s p t"
  shows "stl.isPath s p t"
  unfolding stl.isPath_alt
proof
  from SP show "isLinked s p t" using shortestPath_is_path isLinked_if_isPath by blast
  show "(set p) \<subseteq> stl.E"
  proof clarify
    fix u v
    assume SET: "(u, v) \<in> set p"
    with SP have "(u, v) \<in> E" using isPath_edgeset shortestPath_is_path by blast
    moreover have "connected s u" "connected v t" "Suc (min_dist s u + min_dist v t) = min_dist s t"
      using isShortestPath_level_edge[OF SP SET] by auto
    ultimately show "(u, v) \<in> stl.E" unfolding stl_edge_iff by simp
  qed
qed

(*
lemma stl_s_path_is_shortest_base_path: "stl.isPath s p u \<Longrightarrow> isShortestPath s p u"
  by (simp add: sl_s_path_is_shortest_base_path stl_sub_sl.sg_paths_are_base_paths)

lemma stl_shortest_st_path_iff: "stl.isShortestPath s p t \<longleftrightarrow> isShortestPath s p t"
proof
  assume "stl.isShortestPath s p t"
  then show "isShortestPath s p t"
    using stl.shortestPath_is_path stl_s_path_is_shortest_base_path by blast
next
  assume "isShortestPath s p t"
  then show "stl.isShortestPath s p t"
    using stl_shortest_st_path_remains_path stl_sub_c.shortest_paths_remain_if_contained by blast
qed
*)

lemma stl_obtain_shortest_st_path:
  assumes EDGE: "(u, v) \<in> stl.E"
  obtains p p' where "stl.isShortestPath s (p @ (u, v) # p') t"
proof -
  from EDGE obtain p p' where "isShortestPath s (p @ (u, v) # p') t"
    by (fastforce elim: obtain_shortest_path simp: isPath_append isShortestPath_min_dist_def)
  then have "stl.isShortestPath s (p @ (u, v) # p') t"
    using stl_shortest_st_path_remains_path stl_sub_c.shortest_paths_remain_if_contained by blast
  then show ?thesis using that by blast
qed

sublocale stl: ST_Layer_Graph "st_layering c s t" s t
proof
  fix u
  assume "u \<in> stl.V"
  then obtain p p' where "stl.isShortestPath s p u" "stl.isShortestPath u p' t"
    by (fastforce elim!: stl.vertex_cases stl_obtain_shortest_st_path dest: stl.split_shortest_path_around_edge)
  then show "stl.connected s u \<and> stl.connected u t"
    unfolding stl.connected_def by (auto intro: stl.shortestPath_is_path)
next
  fix u v
  assume EDGE: "(u, v) \<in> stl.E"
  then obtain p p' where SP: "stl.isShortestPath s (p @ (u, v) # p') t"
    by (rule stl_obtain_shortest_st_path)
  then have "stl.isShortestPath s p u" "stl.isShortestPath v p' t"
    by (auto dest: stl.split_shortest_path_around_edge)
  with SP show "Suc (stl.min_dist s u + stl.min_dist v t) = stl.min_dist s t"
    unfolding stl.isShortestPath_min_dist_def by simp
qed


corollary stl_maintains_st_connected: "connected s t \<Longrightarrow> stl.connected s t"
  using obtain_shortest_path stl_shortest_st_path_remains_path stl.connected_def by metis


theorem st_layering_is_shortest_st_paths_union:
  "isPathUnion (st_layering c s t) (shortestSTPaths s t)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> stl.E"
  then obtain p p' where "isShortestPath s (p @ (u, v) # p') t"
    by (fastforce elim: obtain_shortest_path simp: isPath_append isShortestPath_min_dist_def)
  then show "(u, v) \<in> \<Union> (set ` shortestSTPaths s t)" unfolding shortestSTPaths_def by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` shortestSTPaths s t)"
  then obtain p where "isShortestPath s p t" and "(u, v) \<in> set p" using shortestSTPaths_def by auto
  then show "(u, v) \<in> stl.E" using stl_shortest_st_path_remains_path stl.isPath_edgeset by blast
qed

end \<comment> \<open>ST_Graph\<close>


end
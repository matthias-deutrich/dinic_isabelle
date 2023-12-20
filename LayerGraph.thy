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

locale Shortest_Path_Union = CapacityCompatibleGraphs +
  fixes S T
  assumes shortest_path_union: "E' = \<Union>{set p | p. \<exists>s t. s \<in> S \<and> t \<in> T \<and> isShortestPath s p t}"
begin
sublocale Subgraph
  using shortest_path_union isPath_edgeset shortestPath_is_path by unfold_locales blast

lemma edge_on_shortest_path:
  "(u, v) \<in> E' \<Longrightarrow> \<exists>s t p. s \<in> S \<and> t \<in> T \<and> isShortestPath s p t \<and> (u, v) \<in> set p"
  using shortest_path_union by blast

lemma obtain_shortest_ST_edge_path:
  assumes "(u, v) \<in> E'"
  obtains s t p\<^sub>1 p\<^sub>2 where "s \<in> S" "t \<in> T" "isShortestPath s (p\<^sub>1 @ (u, v) # p\<^sub>2) t"
  using assms by (metis edge_on_shortest_path in_set_conv_decomp)

lemma obtain_shortest_ST_paths:
  assumes "u \<in> V'"
  obtains s t p\<^sub>1 p\<^sub>2 where "s \<in> S" "t \<in> T" "isShortestPath s p\<^sub>1 u" "isShortestPath u p\<^sub>2 t" "isShortestPath s (p\<^sub>1 @ p\<^sub>2) t"
  using assms apply (elim g'.vertex_cases obtain_shortest_ST_edge_path)
   apply (metis split_shortest_path_around_edge)
  by (metis split_shortest_path_around_edge append.assoc append.left_neutral append_Cons)
(*  using assms proof (cases rule: g'.vertex_cases)
  case (incoming v)
  then obtain s t p\<^sub>1 p\<^sub>2 where "s \<in> S" "t \<in> T" "isShortestPath s (p\<^sub>1 @ [(v, u)] @ p\<^sub>2) t" using obtain_shortest_ST_edge_path
    by (metis append.left_neutral append_Cons)
  with that[where p\<^sub>1="p\<^sub>1 @ [(v, u)]"] show ?thesis
    by (metis append.assoc append.left_neutral append_Cons split_shortest_path_around_edge)
qed (meson split_shortest_path_around_edge obtain_shortest_ST_edge_path)*)
(* TODO cleanup *)

(*
lemma obtain_shortest_ST_paths:
  assumes "u \<in> V'"
  obtains s t p p' where "s \<in> S" "t \<in> T" "isShortestPath s p u" "isShortestPath u p' t"
  using assms by (metis g'.vertex_cases obtain_shortest_ST_edge_path split_shortest_path_around_edge)
*)

lemma shortest_ST_path_remains:
  assumes "s \<in> S" "t \<in> T" and SP: "isShortestPath s p t"
  shows "g'.isShortestPath s p t"
proof -
  from assms have "g'.isPath s p t"
    by (auto simp: Graph.isPath_alt shortest_path_union dest: shortestPath_is_path)
  with SP show ?thesis by (auto intro: shortest_path_remains_if_contained)
qed

text \<open>Note: for the direction from g' to g, we actually DO need BOTH endpoints in S/T.
      Alternatively, it also works as long as one of these sets has cardinality \<le> 1.\<close>
lemma shortest_ST_path_transfer:
  assumes "s \<in> S" "t \<in> T"
  shows "g'.isShortestPath s p t \<longleftrightarrow> isShortestPath s p t"
proof
  assume "g'.isShortestPath s p t"
  then show "isShortestPath s p t"
    by (metis connected_def Graph.isShortestPath_min_dist_def assms obtain_shortest_path sg_paths_are_base_paths shortest_ST_path_remains)
qed (rule shortest_ST_path_remains[OF assms])

corollary min_ST_dist_transfer: "\<lbrakk>s \<in> S; t \<in> T; connected s t\<rbrakk> \<Longrightarrow> g'.min_dist s t = min_dist s t"
  using shortest_ST_path_transfer by (metis Graph.isShortestPath_min_dist_def obtain_shortest_path)

(* TODO is every path is a shortest path? Though this is more of a property of the resulting layering *)



(* NOT TRUE *)
(*lemma shortest_path_in_base: "g'.isShortestPath u p v \<Longrightarrow> isShortestPath u p v"
proof (rule ccontr)
  assume G'_SP: "g'.isShortestPath u p v" and "\<not> isShortestPath u p v"
  then obtain p' where "isShortestPath u p' v" "length p' < length p"
    by (metis Graph.obtain_shortest_path Graph.shortestPath_is_path antisym_conv1 connected_def isShortestPath_def sg_paths_are_base_paths)
  with G'_SP have "2 \<le> length p"
    by (metis Graph.isPath.simps(1) Graph.isShortestPath_min_dist_def One_nat_def length_0_conv less_2_cases less_one linorder_le_less_linear not_less_zero shortest_path_remains_if_contained)
  with G'_SP obtain w w' p'' where "p = (u, w) # p'' @ [(w', v)]"
    apply (auto dest!: g'.shortestPath_is_path)
    by (metis Graph.isPath_bwd_cases Graph.isPath_fwd_cases One_nat_def le_eq_less_or_eq length_Suc_conv list.size(3) nat_1_add_1 not_less_eq_eq plus_1_eq_Suc rel_simps(28))
  with G'_SP have "(u, w) \<in> E'" "(w', v) \<in> E'"
    using g'.isPath_head g'.isPath_tail g'.isShortestPath_min_dist_def by auto

(*with G'_SP have "u \<noteq> v" "(u, v) \<notin> E'" sledgehammer
    using g'.isShortestPath_min_dist_def apply fastforce
    using G'_SP \<open>isShortestPath u p' v\<close> \<open>length p' < length p\<close>
    by (metis (no_types, lifting) Graph.isPath.simps(1) Graph.isPath_append_edge Orderings.order_eq_iff Suc_leI append_Nil g'.isShortestPath_def length_Cons length_greater_0_conv list.size(3) order_less_le shortestPath_is_path)*)


(*then obtain p' where "isPath u p' v" "length p' < length p" unfolding isShortestPath_def
    using sg_paths_are_base_paths g'.shortestPath_is_path by auto*)
  then show False sorry
qed*)

(* TODO is this sound? might want S/T instead of connected *)
(*lemma min_dist_eq[simp]:
  assumes CON: "g'.connected u v"
  shows "sl.min_dist u v = min_dist u v" oops
*)

(*lemma shortest_ST_path_remains_path:
  "\<lbrakk>s \<in> S; t \<in> T; isShortestPath s p t\<rbrakk> \<Longrightarrow> g'.isPath s p t" unfolding g'.isPath_alt
  using shortestPath_is_path isLinked_if_isPath shortest_path_union by blast

lemma shortest_ST_path_remains_shortest:
  "\<lbrakk>u \<in> S; v \<in> T; isShortestPath u p v\<rbrakk> \<Longrightarrow> g'.isShortestPath u p v"
  using shortest_ST_path_remains_path shortest_path_remains_if_contained by blast*)
end

locale S_Shortest_Path_Union = CapacityCompatibleGraphs + 
  fixes s T
  assumes shortest_s_path_union: "E' = \<Union>{set p | p. \<exists>t. t \<in> T \<and> isShortestPath s p t}"
begin
sublocale Subgraph
  using shortest_s_path_union isPath_edgeset shortestPath_is_path by unfold_locales blast

sublocale Shortest_Path_Union c' c "{s}" T
  by unfold_locales (simp add: shortest_s_path_union)

(* TODO can we improve on the latter two? *)
thm edge_on_shortest_path[simplified]
thm obtain_shortest_ST_edge_path[simplified]
thm shortest_ST_path_remains[simplified]

lemma obtain_shortest_sT_edge_path:
  assumes "(u, v) \<in> E'"
  obtains t p p' where "t \<in> T" "isShortestPath s (p @ (u, v) # p') t"
  using assms by (blast elim: obtain_shortest_ST_edge_path)

 (* TODO remove, since we get this immediately from sublocale *)
(*lemma shortest_sT_path_remains_path:
  "\<lbrakk>t \<in> T; isShortestPath s p t\<rbrakk> \<Longrightarrow> g'.isShortestPath s p t" using shortest_ST_path_remains by simp*)
lemma shortest_sT_path_remains_path:
  "\<lbrakk>t \<in> T; isShortestPath s p t\<rbrakk> \<Longrightarrow> g'.isShortestPath s p t" using shortest_ST_path_remains by simp

(* TODO check if necessary, and if so, cleanup *)
lemma shortest_s_path_remains_path: "\<lbrakk>u \<in> V'; isShortestPath s p u\<rbrakk> \<Longrightarrow> g'.isPath s p u"
proof (elim g'.vertex_cases)
  fix v
  assume SP: "isShortestPath s p u" and "(u, v) \<in> E'"
  then obtain t p\<^sub>1 p\<^sub>2 where "t \<in> T" "isShortestPath s (p\<^sub>1 @ (u, v) # p\<^sub>2) t"
    by (elim obtain_shortest_sT_edge_path)
  with SP have "isShortestPath s (p @ (u, v) # p\<^sub>2) t"
    by (metis (no_types, lifting) isShortestPath_min_dist_def isPath_append length_append split_shortest_path_around_edge)
  with \<open>t \<in> T\<close> have "g'.isShortestPath s (p @ (u, v) # p\<^sub>2) t" using shortest_ST_path_remains by blast
  then show ?thesis using g'.shortestPath_is_path g'.split_shortest_path_around_edge by blast
next
  fix v
  assume SP: "isShortestPath s p u" and "(v, u) \<in> E'"
  then obtain t p\<^sub>1 p\<^sub>2 where "t \<in> T" "isShortestPath s (p\<^sub>1 @ (v, u) # p\<^sub>2) t"
    by (elim obtain_shortest_sT_edge_path)
  with SP have "isShortestPath s (p @ p\<^sub>2) t"
    by (metis (mono_tags, lifting) Graph.isShortestPath_min_dist_def append.assoc append_Cons isPath_append length_append self_append_conv2 split_shortest_path_around_edge)
  with \<open>t \<in> T\<close> have "g'.isShortestPath s (p @  p\<^sub>2) t" using shortest_ST_path_remains by blast
  with SP show ?thesis
    by (meson Graph.isPath_alt Graph.shortestPath_is_path g'.split_shortest_path)
qed

(* TODO fix this *)
lemma s_path_is_base_shortest: "g'.isPath s p u \<Longrightarrow> isShortestPath s p u"
  by (smt (verit, ccfv_SIG) Graph.isPath_back_induct Graph.isShortestPath_level_edge(4) Graph.isShortestPath_min_dist_def Graph.shortestPath_append_edge Suc_eq_plus1 edge'_if_edge edge_on_shortest_path g'.isPath.simps(1) list.size(3) min_dist_z sg_paths_are_base_paths singletonD)

sublocale S_Layer_Graph c' s
proof
  fix u
  assume "u \<in> V'"
  then obtain p\<^sub>1 p\<^sub>2 t where "t \<in> T" "isShortestPath s p\<^sub>1 u" "isShortestPath s (p\<^sub>1 @ p\<^sub>2) t"
    by (blast elim: obtain_shortest_ST_paths)
  then have "g'.isShortestPath s (p\<^sub>1 @ p\<^sub>2) t" using shortest_sT_path_remains_path by blast
  with \<open>isShortestPath s p\<^sub>1 u\<close> show "g'.connected s u" unfolding g'.connected_def
    by (fastforce dest: Graph.shortestPath_is_path simp: g'.isPath_append Graph.isPath_alt)
next
  fix u v
  assume "(u, v) \<in> E'"
  then show "Suc (g'.min_dist s u) = g'.min_dist s v"
    using edge_on_shortest_path g'.isShortestPath_level_edge(4) shortest_sT_path_remains_path by fastforce
qed

lemma shortest_path_transfer: "g'.isPath u p v \<Longrightarrow> isShortestPath u p v"
proof (induction rule: g'.isPath_back_induct)
  case (SelfPath u)
  then show ?case by (simp add: isShortestPath_def)
next
  case (EdgePath p u' v)
  show ?case
  proof (rule ccontr)
    assume "\<not> isShortestPath u (p @ [(u', v)]) v"
    from EdgePath have "isPath u (p @ [(u', v)]) v"
      by (simp add: Graph.isPath_append_edge edge'_if_edge shortestPath_is_path)
    moreover have "connected u v" by (meson EdgePath.hyps(1) EdgePath.hyps(2) Graph.connected_def Subgraph.sg_connected_remains_base_connected Subgraph_axioms g'.isPath_append_edge)
    ultimately obtain p\<^sub>F where "isShortestPath u p\<^sub>F v" "length p\<^sub>F \<le> length p"
      by (metis Graph.isPath_distD Graph.isShortestPath_min_dist_def Graph.min_dist_minD \<open>\<not> isShortestPath u (p @ [(u', v)]) v\<close> le_antisym length_append_singleton not_less_eq_eq obtain_shortest_path)

    from EdgePath obtain t p\<^sub>1 p\<^sub>2 where "t \<in> T" "isShortestPath s (p\<^sub>1 @ (u', v) # p\<^sub>2) t"
      using obtain_shortest_ST_edge_path by (metis singletonD) (* TODO if we keep sT_edge_path, use that and remove singletonD *)
    then have "g'.isShortestPath s (p\<^sub>1 @ (u', v) # p\<^sub>2) t" by (simp add: shortest_ST_path_remains)
    from EdgePath obtain p' where "isShortestPath s (p' @ [(u', v)]) v"
      using obtain_shortest_ST_edge_path by (metis singletonD split_shortest_path_around_edge) (* TODO if we keep sT_edge_path, use that and remove singletonD *)
    (*then have "Suc (g'.min_dist s u) = g'.min_dist s v" by simp*)
    obtain p\<^sub>u where "g'.isPath s p\<^sub>u u"
      by (metis EdgePath.hyps(2) Graph.distinct_nodes_in_V_if_connected(1) Graph.isShortestPath_min_dist_def Graph.split_shortest_path_around_edge \<open>g'.isShortestPath s (p\<^sub>1 @ (u', v) # p\<^sub>2) t\<close> g'.connected_def s_connected)
    with \<open>g'.isPath u p u'\<close> have "g'.isPath s (p\<^sub>u @ p) u'" using g'.isPath_append by blast
    then have "g'.isShortestPath s (p\<^sub>u @ p) u'" by blast
    with EdgePath show False
      by (smt (verit, ccfv_SIG) \<open>\<not> isShortestPath u (p @ [(u', v)]) v\<close> \<open>g'.isPath s (p\<^sub>u @ p) u'\<close> \<open>isPath u (p @ [(u', v)]) v\<close> append_assoc g'.isPath_append_edge isPath_fwd_cases s_path_is_base_shortest split_shortest_path_around_edge)
  qed
qed (* TODO cleanup this horrible mess *)

corollary min_dist_transfer: "g'.connected u v \<Longrightarrow> g'.min_dist u v = min_dist u v"
  using shortest_path_transfer g'.obtain_shortest_path g'.shortestPath_is_path min_dist_eqI
  by meson

(* TODO is this useful? *)
(* lemma sl_shortest_s_path_iff[simp]: "sl.isShortestPath s p u \<longleftrightarrow> isShortestPath s p u" *)

end

locale T_Shortest_Path_Union = CapacityCompatibleGraphs +
  fixes S t
  assumes shortest_t_path_union: "E' = \<Union>{set p | p. \<exists>s. s \<in> S \<and> isShortestPath s p t}"
begin
sublocale Subgraph
  using shortest_t_path_union isPath_edgeset shortestPath_is_path by unfold_locales blast

sublocale Shortest_Path_Union c' c S "{t}"
  by unfold_locales (simp add: shortest_t_path_union)

thm edge_on_shortest_path[simplified]

lemma obtain_shortest_St_edge_path:
  assumes "(u, v) \<in> E'"
  obtains s p p' where "s \<in> S" "isShortestPath s (p @ (u, v) # p') t"
  using assms by (blast elim: obtain_shortest_ST_edge_path)

sublocale T_Layer_Graph c' t sorry (* TODO *)
end

locale ST_Shortest_Path_Union = CapacityCompatibleGraphs +
  fixes s t
  assumes shortest_st_path_union: "E' = \<Union>{set p | p. isShortestPath s p t}"
begin
sublocale Subgraph
  using shortest_st_path_union isPath_edgeset shortestPath_is_path by unfold_locales blast

sublocale S_Shortest_Path_Union c' c s "{t}"
  by unfold_locales (simp add: shortest_st_path_union)

sublocale T_Shortest_Path_Union c' c "{s}" t
  by unfold_locales (simp add: shortest_st_path_union)

thm edge_on_shortest_path[simplified]

lemma obtain_shortest_st_edge_path: (* TODO this idea is once again reused *)
  assumes "(u, v) \<in> E'"
  obtains p p' where "isShortestPath s (p @ (u, v) # p') t"
  using assms by (blast elim: obtain_shortest_ST_edge_path)

sublocale ST_Layer_Graph c' s t sorry (* TODO, using obtain_shortest_st_edge_path, shortest_path_remains and then new Intro for ST_Layer_Edge *)
end

(* TODO move the following transfer properties to the shortest path union locales *)

(*interpretation ST_Shortest_Path_Union undefined undefined undefined undefined sorry*)

subsubsection \<open>Building a source layering from an arbitrary graph\<close>

definition induced_s_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "induced_s_layering c s \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Suc (Graph.min_dist c s u) = Graph.min_dist c s v then
      c (u, v)
    else
      0"

lemma induced_s_layering_subgraph: "isSubgraph (induced_s_layering c s) c" (* TODO remove *)
  unfolding isSubgraph_def induced_s_layering_def by simp


interpretation sl: S_Shortest_Path_Union "induced_s_layering c s" c s "Graph.V c"
proof
  interpret Graph c .
  interpret g': Graph "induced_s_layering c s" .
  show "g'.E = \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t}"
  proof (rule pair_set_eqI)
    fix u v
    assume "(u, v) \<in> g'.E"
    then have "(u, v) \<in> E" "connected s u \<and> Suc (min_dist s u) = min_dist s v"
      unfolding induced_s_layering_def Graph.E_def by (smt case_prod_conv mem_Collect_eq)+
    then obtain p where "isShortestPath s (p @ [(u, v)]) v"
      using obtain_shortest_path shortestPath_append_edge by metis
    moreover from \<open>(u, v) \<in> E\<close> have "v \<in> V" unfolding V_def by blast
    ultimately show "(u, v) \<in> \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t}" by fastforce
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t}"
    then obtain t p where "isShortestPath s p t" "(u, v) \<in> set p" by blast
    then have "(u, v) \<in> E" "connected s u" "Suc (min_dist s u) = min_dist s v"
      using isShortestPath_level_edge by (auto intro: isPath_edgeset shortestPath_is_path)
    then show "(u, v) \<in> g'.E" unfolding induced_s_layering_def Graph.E_def by simp
  qed
qed (simp add: induced_s_layering_def)


locale S_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node

subsection \<open>Layering from source to target node\<close>


definition st_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "st_layering c s t \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t \<and> Suc (Graph.min_dist c s u + Graph.min_dist c v t) = Graph.min_dist c s t then
      c (u, v)
    else
      0"

(* TODO why can this not coexist with sl? *)
(*
interpretation stl: ST_Shortest_Path_Union "st_layering c s t" c s t
proof
  interpret Graph c .
  interpret g': Graph "st_layering c s t" .
  show "g'.E = \<Union> {set p |p. isShortestPath s p t}"
  proof (rule pair_set_eqI)
    fix u v
    assume "(u, v) \<in> g'.E"
    then have MIN_DIST: "(u, v) \<in> E \<and> Suc (min_dist s u + min_dist v t) = min_dist s t" and "connected s u \<and> connected v t"
      unfolding st_layering_def Graph.E_def by (smt case_prod_conv mem_Collect_eq)+
    then obtain p\<^sub>1 p\<^sub>2 where "isShortestPath s p\<^sub>1 u" "isShortestPath v p\<^sub>2 t"
      by (meson obtain_shortest_path)
    with MIN_DIST have "isShortestPath s (p\<^sub>1 @ (u, v) # p\<^sub>2) t" unfolding isShortestPath_min_dist_def
      by (simp add: isPath_append)
    then show "(u, v) \<in> \<Union> {set p |p. isShortestPath s p t}" by fastforce
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. isShortestPath s p t}"
    then obtain p where "isShortestPath s p t" "(u, v) \<in> set p" by blast
    then have "(u, v) \<in> E" "connected s u" "connected v t" "Suc (min_dist s u + min_dist v t) = min_dist s t"
      using isShortestPath_level_edge by (auto intro: isPath_edgeset shortestPath_is_path)
    then show "(u, v) \<in> g'.E" unfolding st_layering_def Graph.E_def by simp
  qed
qed (simp add: st_layering_def)
*)

(*
lemma st_layering_subgraph: "isSubgraph (st_layering c s t) (induced_s_layering c s)"
  unfolding isSubgraph_def induced_s_layering_def st_layering_def
  apply (auto dest!: Graph.min_dist_is_dist intro!: Graph.zero_cap_simp)
  using Graph.dist_suc Graph.min_dist_split(1) by fastforce (* TODO prettify *)
*)
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
    using stl_shortest_st_path_remains_path stl_sub_c.shortest_path_remains_if_contained by blast
qed
*)

lemma stl_obtain_shortest_st_path:
  assumes EDGE: "(u, v) \<in> stl.E"
  obtains p p' where "stl.isShortestPath s (p @ (u, v) # p') t"
proof -
  from EDGE obtain p p' where "isShortestPath s (p @ (u, v) # p') t"
    by (fastforce elim: obtain_shortest_path simp: isPath_append isShortestPath_min_dist_def)
  then have "stl.isShortestPath s (p @ (u, v) # p') t"
    using stl_shortest_st_path_remains_path stl_sub_c.shortest_path_remains_if_contained by blast
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
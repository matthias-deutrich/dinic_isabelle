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
end \<comment> \<open>LayerGraphExplicit\<close>

(*
definition layering :: "_ graph \<Rightarrow> node \<Rightarrow> _ graph"
  where "layering c s \<equiv> \<lambda>(u, v).
    if Graph.min_dist c s u + 1 = Graph.min_dist c s v then
      c (u, v)
    else
      0"
*)

locale InducedSourceLayering = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
  assumes s_node[simp, intro!]: "s \<in> V"
begin

definition s_layering :: "'capacity graph"
  where "s_layering \<equiv> \<lambda>(u, v).
    if connected s u \<and> min_dist s u + 1 = min_dist s v then
      c (u, v)
    else
      0"

sublocale l: Graph s_layering .

sublocale l_sub: Subgraph s_layering c
  unfolding Subgraph_def isSubgraph_def s_layering_def by simp

(* TODO check if this is a good idea, and if "connected s v" should also be a property *)
lemma l_edgeE[elim]:
  assumes "(u, v) \<in> l.E"
  obtains "(u, v) \<in> E"
    and "connected s u" "connected s v" "min_dist s u + 1 = min_dist s v"
proof
  from assms show "(u, v) \<in> E" using l_sub.E_ss by blast
  from assms have layering_not_z: "s_layering (u, v) \<noteq> 0" using l.E_def by blast
  then show "connected s u" unfolding s_layering_def by (smt case_prod_conv)
  then show "connected s v" using  \<open>(u, v) \<in> E\<close> by (rule connected_append_edge)
  from layering_not_z show "min_dist s u + 1 = min_dist s v" unfolding s_layering_def by (smt case_prod_conv)
qed

lemma l_edge_iff: "(u, v) \<in> l.E \<longleftrightarrow> (u, v) \<in> E \<and> connected s u \<and> min_dist s u + 1 = min_dist s v" (* TODO necessary? *)
  using E_def' l.E_def' s_layering_def by auto

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

lemma l_vertices_connected_in_l: "u \<in> l.V \<Longrightarrow> l.connected s u" unfolding l.connected_def
  using l_vertices_connected_in_base obtain_shortest_path shortest_s_path_remains_path by meson

lemma shortest_s_path_remains_shortest: "isShortestPath s p u \<Longrightarrow> l.isShortestPath s p u"
  using shortest_s_path_remains_path l_sub.shortest_paths_remain_if_contained by blast


(* TODO necessary? or reuse from LayerGraphExplicit *)
lemma path_adds_to_source_dist: "l.isPath u p v \<Longrightarrow> min_dist s u + length p = min_dist s v"
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

(*sublocale l: LayerGraphExplicit "s_layering" s "min_dist s" (* TODO necessary? *)
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
  show "\<forall>(u, v) \<in> l.E. min_dist s u + 1 = min_dist s v" by blast
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
  "isPathUnion s_layering (shortestSPaths s V)" unfolding isPathUnion_def
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

locale InducedSourceTargetLayering = InducedSourceLayering c s for c :: "'capacity::linordered_idom graph" and s +
  fixes t :: node
  assumes t_node[simp, intro!]: "t \<in> V"
  assumes s_not_t[simp, intro!]: "s \<noteq> t" (* TODO check if necessary *)
begin
(*
(* This definition is incorrect, since it may include paths that are longer than the shortest s-t path *)
definition s_t_layering :: "'capacity graph"
  where "s_t_layering \<equiv> \<lambda>(u, v).
    if connected s u \<and> min_dist s u + 1 = min_dist s v \<and> connected v t \<and> min_dist u t = min_dist v t + 1 then
      c (u, v)
    else
      0"
*)

definition s_t_layering :: "'capacity graph"
  where "s_t_layering \<equiv> \<lambda>(u, v).
    if connected s u \<and> connected v t \<and> min_dist s u + 1 + min_dist v t = min_dist s t then
      c (u, v)
    else
      0"

sublocale l': Graph s_t_layering .


(* TODO do this for the source dist as well, then simplify subgraph proof *)
lemma l'_edge_reduces_t_dist: "(u, v) \<in> l'.E \<Longrightarrow> min_dist u t = min_dist v t + 1" sorry

sublocale l'_sub: Subgraph s_t_layering s_layering (* TODO adapt this so we immediately get the transitive properties *)
  unfolding Subgraph_def isSubgraph_def
proof clarify
  fix u v
  assume 0: "s_t_layering (u, v) \<noteq> 0"
  then have "s_t_layering (u, v) = c (u, v)" "connected s u" "connected v t" "min_dist s u + 1 + min_dist v t = min_dist s t"
    unfolding s_t_layering_def case_prod_conv by meson+
  then have "s_layering (u, v) = c (u, v)" unfolding s_layering_def
    by (smt (verit, best) min_dist_is_dist zero_cap_simp Suc_eq_plus1 case_prod_conv dist_suc min_dist_split(1))
  with \<open>s_t_layering (u, v) = c (u, v)\<close> show "s_t_layering (u, v) = s_layering (u, v)" by simp
qed (* TODO cleanup *)

lemma l'_edgeE[elim]:
  assumes "(u, v) \<in> l'.E"
  obtains "(u, v) \<in> E"
    and "connected s u" "connected s v"
    and "connected u t" "connected v t"
    and  "min_dist s u + 1 + min_dist v t = min_dist s t"
proof
  from assms show "(u, v) \<in> E" using l_sub.E_ss l'_sub.E_ss by blast
  from assms show "connected s u" "connected s v" using l'_sub.E_ss by blast+
  from assms have layering_not_z: "s_t_layering (u, v) \<noteq> 0" using l'.E_def by blast
  then show "connected v t" unfolding s_t_layering_def by (smt case_prod_conv)
  with \<open>(u, v) \<in> E\<close> show "connected u t" by (rule connected_prepend_edge)
  from layering_not_z show "min_dist s u + 1 + min_dist v t = min_dist s t" unfolding s_t_layering_def case_prod_conv by meson
qed

lemma l'_edge_iff: "(u, v) \<in> l'.E \<longleftrightarrow> (u, v) \<in> E \<and> connected s u \<and> connected v t \<and> min_dist s u + 1 + min_dist v t = min_dist s t" (* TODO necessary? *)
  using E_def' l'.E_def' s_t_layering_def by auto

(* TODO place in a different location *)
lemma path_adds_to_source_dist': "l'.isPath u p v \<Longrightarrow> min_dist s u + length p = min_dist s v"
  using l'_sub.sg_paths_are_base_paths path_adds_to_source_dist by simp

lemma path_adds_to_target_dist': "l'.isPath u p v \<Longrightarrow> min_dist u t = length p + min_dist v t"
  by (induction rule: l'.isPath_custom_induct) (auto simp: l'_edge_reduces_t_dist)

(*
proof (induction rule: l'.isPath_custom_induct)
  case (SelfPath u)
  then show ?case by simp
next
  case (EdgePath u v p w)
  then have "min_dist u t = min_dist v t + 1" sorry
  with EdgePath show ?case by simp
  proof (simp, rule le_antisym)
    show "min_dist u t \<le> Suc (length p + min_dist w t)" sorry
    show "Suc (length p + min_dist w t) \<le> min_dist u t" sorry
  qed
  thm EdgePath.IH
  then have "min_dist s u + 1 + min_dist v t = min_dist s t" by blast
  with EdgePath.IH have "min_dist s u + 1 + length p + min_dist w t = min_dist s t" by simp
  with EdgePath show ?case sorry
qed
*)

lemma l'_vertexE[elim]:
  assumes "u \<in> l'.V"
  obtains "u \<in> V"
    and "connected s u" "connected u t"
    and "min_dist s u + min_dist u t = min_dist s t"
proof
  from assms show "u \<in> V" using l_sub.V_ss l'_sub.V_ss by blast
  from assms show "connected s u" "connected u t"
    using l'.V_def by blast+
  from assms show "min_dist s u + min_dist u t = min_dist s t"
  proof (rule l'.vertex_cases)
    fix v
    assume "(u, v) \<in> l'.E"
    then obtain p where "isPath u ((u, v) # p) t" "min_dist s u + 1 + length p = min_dist s t"
      using obtain_shortest_path isShortestPath_min_dist_def l'_edgeE by (metis isPath.simps(2))
    have "length p + 1 = min_dist u t"
    proof (rule le_antisym)
      show "length p + 1 \<le> min_dist u t"
      proof (rule ccontr, drule not_le_imp_less)
        assume "min_dist u t < length p + 1"
        with \<open>connected u t\<close> obtain p' where "isPath u p' t" "length p' \<le> length p"
          using obtain_shortest_path isShortestPath_min_dist_def
          by (metis Suc_eq_plus1 linorder_not_le not_less_eq)
        with \<open>connected s u\<close> have "min_dist s t \<le> min_dist s u + length p'"
          by (meson dist_trans min_dist_is_dist min_dist_minD isPath_distD)
        with \<open>min_dist s u + 1 + length p = min_dist s t\<close> \<open>length p' \<le> length p\<close> show False by simp
      qed
      from \<open>isPath u ((u, v) # p) t\<close> show "min_dist u t \<le> length p + 1"
        by (metis isPath_distD min_dist_minD Suc_eq_plus1 length_Cons)
        (* using isPath_distD min_dist_minD by fastforce *)
    qed
    with \<open>min_dist s u + 1 + length p = min_dist s t\<close> show ?thesis by simp
  next
    fix v
    assume "(v, u) \<in> l'.E"
    then obtain p where "isPath s (p @ [(v, u)]) u" "length p + 1 + min_dist u t = min_dist s t"
      using obtain_shortest_path isShortestPath_min_dist_def l'_edgeE isPath_append_edge by metis
    have "length p + 1 = min_dist s u"
    proof (rule le_antisym)
      show "length p + 1 \<le> min_dist s u"
      proof (rule ccontr, drule not_le_imp_less)
        assume "min_dist s u < length p + 1"
        with \<open>connected s u\<close> obtain p' where "isPath s p' u" "length p' \<le> length p"
          using obtain_shortest_path isShortestPath_min_dist_def
          by (metis Suc_eq_plus1 linorder_not_le not_less_eq)
        with \<open>connected u t\<close> have "min_dist s t \<le> min_dist u t + length p'"
          by (metis dist_trans min_dist_is_dist min_dist_minD isPath_distD add.commute)
        with \<open>length p + 1 + min_dist u t = min_dist s t\<close> \<open>length p' \<le> length p\<close> show False by simp
      qed
      from \<open>isPath s (p @ [(v, u)]) u\<close> show "min_dist s u \<le> length p + 1"
        using isPath_distD min_dist_minD by fastforce
    qed
    with \<open>length p + 1 + min_dist u t = min_dist s t\<close> show ?thesis by simp
  qed
qed
(*
assume "u \<in> l'.V"
  then obtain v where "(u, v) \<in> l'.E \<or> (v, u) \<in> l'.E" unfolding l'.V_def by blast
  then have "min_dist s u + min_dist u t = min_dist s t"
  proof
    assume "(u, v) \<in> l'.E"
    then show ?thesis
      by (smt (verit, best) ab_semigroup_add_class.add_ac(1) l'.connected_append_edge l'.connected_edgeRtc l'.connected_refl l'.rtc_isPath l'_edgeE l'_sub.E_ss l_edge_iff path_adds_to_source_dist' path_adds_to_target_dist' subsetD)
  next
    assume "(v, u) \<in> l'.E"
    then show ?thesis
      by (smt (verit, best) ab_semigroup_add_class.add_ac(1) l'.connected_append_edge l'.connected_edgeRtc l'.connected_refl l'.rtc_isPath l'_edgeE l'_sub.E_ss l_edge_iff path_adds_to_source_dist' path_adds_to_target_dist' subsetD)
  qed
*)

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
  using shortest_s_path_remains_path shortest_s_t_path_remains_path l_sub.shortest_paths_remain_if_contained l'_sub.shortest_paths_remain_if_contained by blast

theorem s_t_layering_is_shortest_s_t_paths_union:
  "isPathUnion s_t_layering (shortestSTPaths s t)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> l'.E"
  then have "(u, v) \<in> E" "connected s u" "connected v t" "min_dist s u + 1 + min_dist v t = min_dist s t" by auto
  then obtain p p' where "isShortestPath s p u" "isShortestPath v p' t" using obtain_shortest_path by meson
  with \<open>min_dist s u + 1 + min_dist v t = min_dist s t\<close> have "length p + 1 + length p' = min_dist s t"
    using isShortestPath_min_dist_def by simp
  moreover from \<open>isShortestPath s p u\<close> \<open>isShortestPath v p' t\<close> \<open>(u, v) \<in> E\<close> have "isPath s (p @ [(u, v)] @ p') t"
    using shortestPath_is_path isPath_append by simp
  ultimately have "isShortestPath s (p @ [(u, v)] @ p') t" unfolding isShortestPath_min_dist_def by simp
  then show "(u, v) \<in> \<Union> (set ` shortestSTPaths s t)" unfolding shortestSTPaths_def by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` shortestSTPaths s t)"
  then obtain p where "isShortestPath s p t" and "(u, v) \<in> set p" using shortestSTPaths_def by auto
  then show "(u, v) \<in> l'.E" using shortest_s_t_path_remains_path l'.isPath_edgeset by blast
qed
end

end
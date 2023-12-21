theory LayerGraph
  imports Subgraph
begin

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
end \<comment> \<open>Generic_Layer_Graph\<close>

locale S_Layer_Graph = Graph +
  fixes s
  assumes s_connected[intro]: "u \<in> V \<Longrightarrow> connected s u"
      and s_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist s u) = min_dist s v" (* TODO which direction is better for simp? *)
begin
abbreviation "layer \<equiv> min_dist s"
sublocale Generic_Layer_Graph c layer by unfold_locales simp

lemma s_in_V_if_nonempty: "V \<noteq> {} \<Longrightarrow> s \<in> V"
  using connected_inV_iff by blast

lemma only_s_without_incoming[simp]: "\<lbrakk>u \<in> V; incoming u = {}\<rbrakk> \<Longrightarrow> u = s"
  using distinct_nodes_have_in_out_if_connected by blast

corollary no_incomingD: "incoming u = {} \<Longrightarrow> u \<notin> V \<or> u = s" by simp

lemma front_terminal_path_is_s_path:
  "isPath u p v \<Longrightarrow> v \<in> V \<Longrightarrow> incoming u = {} \<Longrightarrow> isPath s p v"
  using connected_def connected_inV_iff no_incomingD by blast
end \<comment> \<open>S_Layer_Graph\<close>

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
end \<comment> \<open>T_Layer_Graph\<close>

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
end \<comment> \<open>ST_Layer_Graph\<close>

\<comment> \<open>Layerings\<close>

subsection \<open>Unions of shortest paths\<close>

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

lemma shortest_ST_path_remains:
  assumes "s \<in> S" "t \<in> T" and SP: "isShortestPath s p t"
  shows "g'.isShortestPath s p t"
proof -
  from assms have "g'.isPath s p t"
    by (auto simp: Graph.isPath_alt shortest_path_union dest: shortestPath_is_path)
  with SP show ?thesis by (auto intro: shortest_path_remains_if_contained)
qed

(*
corollary obtain_shortest_ST_paths': (* TODO is this necessary? *)
  assumes "u \<in> V'"
  obtains s t p\<^sub>1 p\<^sub>2 where "s \<in> S" "t \<in> T" "g'.isShortestPath s p\<^sub>1 u" "g'.isShortestPath u p\<^sub>2 t" "g'.isShortestPath s (p\<^sub>1 @ p\<^sub>2) t"
  using assms obtain_shortest_ST_paths shortest_ST_path_remains
  by (smt (verit, best) Graph.shortestPath_is_path Graph.split_shortest_path_around_edge isPath_bwd_cases isPath_fwd_cases) (* TODO prettify *)
*)

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
  using obtain_shortest_path shortest_ST_path_transfer min_dist_eqI by meson
end \<comment> \<open>Shortest_Path_Union\<close>

locale Layered_Shortest_Path_Union = Shortest_Path_Union + Generic_Layer_Graph c'
begin
(* TODO cleanup *)
lemma tmp: "\<lbrakk>s \<in> S; t \<in> T; isPath s p t; layer t = layer s + length p\<rbrakk> \<Longrightarrow> g'.isPath s p t"
  (*by (metis (no_types, opaque_lifting) Graph.connected_def add_le_cancel_left g'.isShortestPath_def isShortestPath_min_dist_def nle_le obtain_shortest_path path_ascends_layer shortest_ST_path_transfer)*)
  by (metis (no_types, lifting) add_left_imp_eq connected_distI g'.shortestPath_is_path isPath_distD isShortestPath_min_dist_def obtain_shortest_path path_ascends_layer shortest_ST_path_remains)
(* TODO this is questionable, since layer t > layer s + length p will be a contradiction *)
lemma tmp': "\<lbrakk>s \<in> S; t \<in> T; isPath s p t; layer t \<ge> layer s + length p\<rbrakk> \<Longrightarrow> g'.isPath s p t"
  by (smt (verit) Graph.isShortestPath_min_dist_def connected_distI isPath_distD le_antisym min_dist_minD nat_add_left_cancel_le obtain_shortest_path path_ascends_layer shortest_ST_path_remains)

find_theorems "(?a = ?b \<Longrightarrow> ?P ?a ?b) \<Longrightarrow> (?a \<noteq> ?b \<Longrightarrow> ?P ?a ?b) \<Longrightarrow> ?P ?a ?b"
thm case_split
(* TODO finish *)

lemma path_respects_layers:
  assumes CON': "g'.connected u v" and PATH: "isPath u p v"
  shows "layer v \<le> layer u + length p"
proof (rule ccontr, drule not_le_imp_less)
  assume L_JUMP: "layer u + length p < layer v"
  then show False
  proof (cases "u = v")
    case False
    with CON' have "u \<in> V'" "v \<in> V'" using g'.distinct_nodes_in_V_if_connected by auto
    then obtain s t p\<^sub>1 p\<^sub>3 where TAILS: "s \<in> S" "g'.isPath s p\<^sub>1 u" "t \<in> T" "g'.isPath v p\<^sub>3 t"
      by (metis (no_types, lifting) Graph.isPath_alt Graph.shortestPath_is_path g'.split_shortest_path obtain_shortest_ST_paths shortest_ST_path_remains)
    moreover from CON' obtain p\<^sub>2 where "g'.isPath u p\<^sub>2 v" using g'.connected_def by blast
    ultimately have "g'.isPath s (p\<^sub>1 @ p\<^sub>2 @ p\<^sub>3) t" using g'.isPath_append by blast

    (* TODO fix this *)
    from TAILS PATH have "isPath s (p\<^sub>1 @ p @ p\<^sub>3) t" using isPath_append sg_paths_are_base_paths by blast
    with TAILS PATH have "g'.isPath s (p\<^sub>1 @ p @ p\<^sub>3) t" apply (auto intro!: tmp')
      using Generic_Layer_Graph.path_ascends_layer Generic_Layer_Graph_axioms L_JUMP by fastforce
    with \<open>g'.isPath s (p\<^sub>1 @ p\<^sub>2 @ p\<^sub>3) t\<close> show False
      by (smt (verit) L_JUMP \<open>g'.isPath u p\<^sub>2 v\<close> add_left_imp_eq add_right_imp_eq length_append nat_neq_iff path_ascends_layer)
  qed simp
qed (* TODO cleanup *)

lemma shortest_path_transfer: "g'.isPath u p v \<Longrightarrow>  isShortestPath u p v" unfolding isShortestPath_def
  using path_ascends_layer path_respects_layers sg_paths_are_base_paths g'.connected_def by fastforce

corollary min_dist_transfer: "g'.connected u v \<Longrightarrow> g'.min_dist u v = min_dist u v"
  using shortest_path_transfer g'.obtain_shortest_path g'.shortestPath_is_path min_dist_eqI
  by meson


(*
lemma edge_respects_layers:
  assumes CON': "g'.connected u v" and EDGE: "(u, v) \<in> E" (* TODO can we do this directly with path? *)
  shows "layer v \<le> Suc (layer u)"
proof (rule ccontr, drule not_le_imp_less)
  assume L_JUMP: "Suc (layer u) < layer v"
  then show False
  proof (cases "u = v")
    case True
    with L_JUMP show ?thesis by simp
  next
    case False
    with CON' have "u \<in> V'" "v \<in> V'" using g'.distinct_nodes_in_V_if_connected by auto
    from \<open>u \<in> V'\<close> obtain s p\<^sub>1 where P1: "s \<in> S" "g'.isPath s p\<^sub>1 u"
      by (metis Graph.shortestPath_is_path g'.isPath_alt g'.isPath_append isLinked_if_isPath obtain_shortest_ST_paths shortest_ST_path_remains)
    moreover from CON' obtain p\<^sub>2 where "g'.isPath u p\<^sub>2 v" using g'.connected_def by blast
    moreover from \<open>v \<in> V'\<close> obtain t p\<^sub>3 where P3: "t \<in> T" "g'.isPath v p\<^sub>3 t"
      by (metis Graph.shortestPath_is_path g'.isPath_alt g'.isPath_append isLinked_if_isPath obtain_shortest_ST_paths shortest_ST_path_remains)
    ultimately have "g'.isPath s (p\<^sub>1 @ p\<^sub>2 @ p\<^sub>3) t" using g'.isPath_append by blast
    from P1 P3 EDGE have "g'.isPath s (p
    then show ?thesis sorry
  qed
qed
*)

(*
(* TODO need some property about u and v being in V' *)
lemma edge_respects_layers: "(u, v) \<in> E \<Longrightarrow> layer v \<le> Suc (layer u)" sorry

lemma path_respects_layers: "isPath u p v \<Longrightarrow> layer v \<le> layer u + length p"
  by (induction rule: isPath_front_induct) (auto dest: edge_respects_layers)
*)
end

(* TODO cleanup this locale *)
locale S_Shortest_Path_Union = CapacityCompatibleGraphs + 
  fixes s T
  assumes shortest_s_path_union: "E' = \<Union>{set p | p. \<exists>t. t \<in> T \<and> isShortestPath s p t}"
begin
sublocale Subgraph
  using shortest_s_path_union isPath_edgeset shortestPath_is_path by unfold_locales blast

sublocale Shortest_Path_Union c' c "{s}" T
  by unfold_locales (simp add: shortest_s_path_union)

sublocale S_Layer_Graph c' s
proof
  fix u
  assume "u \<in> V'"
  then obtain p\<^sub>1 p\<^sub>2 t where "t \<in> T" "isShortestPath s p\<^sub>1 u" "isShortestPath s (p\<^sub>1 @ p\<^sub>2) t"
    by (blast elim: obtain_shortest_ST_paths)
  then have "g'.isShortestPath s (p\<^sub>1 @ p\<^sub>2) t" using shortest_ST_path_remains by blast
  with \<open>isShortestPath s p\<^sub>1 u\<close> show "g'.connected s u" unfolding g'.connected_def
    by (fastforce dest: Graph.shortestPath_is_path simp: g'.isPath_append Graph.isPath_alt)
next
  fix u v
  assume "(u, v) \<in> E'"
  then show "Suc (g'.min_dist s u) = g'.min_dist s v"
    using edge_on_shortest_path g'.isShortestPath_level_edge(4) shortest_ST_path_remains by fastforce
qed

sublocale Layered_Shortest_Path_Union c' c "{s}" T layer unfolding Layered_Shortest_Path_Union_def
  using Shortest_Path_Union_axioms Generic_Layer_Graph_axioms by blast

(* TODO check if necessary, and if so, cleanup *)
lemma shortest_s_path_remains_path: "\<lbrakk>u \<in> V'; isShortestPath s p u\<rbrakk> \<Longrightarrow> g'.isPath s p u"
proof (elim g'.vertex_cases)
  fix v
  assume SP: "isShortestPath s p u" and "(u, v) \<in> E'"
  then obtain t p\<^sub>1 p\<^sub>2 where "t \<in> T" "isShortestPath s (p\<^sub>1 @ (u, v) # p\<^sub>2) t"
    using obtain_shortest_ST_edge_path by force
    (*by (elim obtain_shortest_ST_edge_path)*)
  with SP have "isShortestPath s (p @ (u, v) # p\<^sub>2) t"
    by (metis (no_types, lifting) isShortestPath_min_dist_def isPath_append length_append split_shortest_path_around_edge)
  with \<open>t \<in> T\<close> have "g'.isShortestPath s (p @ (u, v) # p\<^sub>2) t" using shortest_ST_path_remains by blast
  then show ?thesis using g'.shortestPath_is_path g'.split_shortest_path_around_edge by blast
next
  fix v
  assume SP: "isShortestPath s p u" and "(v, u) \<in> E'"
  then obtain t p\<^sub>1 p\<^sub>2 where "t \<in> T" "isShortestPath s (p\<^sub>1 @ (v, u) # p\<^sub>2) t"
    using obtain_shortest_ST_edge_path by force
    (*by (elim obtain_shortest_sT_edge_path)*)
  with SP have "isShortestPath s (p @ p\<^sub>2) t"
    by (metis (mono_tags, lifting) Graph.isShortestPath_min_dist_def append.assoc append_Cons isPath_append length_append self_append_conv2 split_shortest_path_around_edge)
  with \<open>t \<in> T\<close> have "g'.isShortestPath s (p @  p\<^sub>2) t" using shortest_ST_path_remains by blast
  with SP show ?thesis
    by (meson Graph.isPath_alt Graph.shortestPath_is_path g'.split_shortest_path)
qed
end \<comment> \<open>S_Shortest_Path_Union\<close>

locale T_Shortest_Path_Union = CapacityCompatibleGraphs +
  fixes S t
  assumes shortest_t_path_union: "E' = \<Union>{set p | p. \<exists>s. s \<in> S \<and> isShortestPath s p t}"
begin
text \<open>Note that this is symmetric to S_Shortest_Path_Union, thus the path/dist transfer properties
      hold here as well. However, since we never use this locale without the other, and we would
      need to setup Generic_Layer_Graph using int instead of nat, we do not show them here again.\<close>

sublocale Shortest_Path_Union c' c S "{t}"
  by unfold_locales (simp add: shortest_t_path_union)

sublocale T_Layer_Graph c' t
proof
  fix u
  assume "u \<in> V'"
  then obtain p\<^sub>1 p\<^sub>2 s where "s \<in> S" "isShortestPath u p\<^sub>2 t" "isShortestPath s (p\<^sub>1 @ p\<^sub>2) t"
    by (blast elim: obtain_shortest_ST_paths)
  then have "g'.isShortestPath s (p\<^sub>1 @ p\<^sub>2) t" using shortest_ST_path_remains by blast
  with \<open>isShortestPath u p\<^sub>2 t\<close> show "g'.connected u t" unfolding g'.connected_def
    by (fastforce dest: Graph.shortestPath_is_path simp: g'.isPath_append Graph.isPath_alt)
next
  fix u v
  assume "(u, v) \<in> E'"
  then show "Suc (g'.min_dist v t) = g'.min_dist u t"
    using edge_on_shortest_path g'.isShortestPath_level_edge(5) shortest_ST_path_remains by fastforce
qed
end \<comment> \<open>T_Shortest_Path_Union\<close>

locale ST_Shortest_Path_Union = CapacityCompatibleGraphs +
  fixes s t
  assumes shortest_st_path_union: "E' = \<Union>{set p | p. isShortestPath s p t}"
begin
sublocale S_Shortest_Path_Union c' c s "{t}"
  by unfold_locales (simp add: shortest_st_path_union)

sublocale T_Shortest_Path_Union c' c "{s}" t
  by unfold_locales (simp add: shortest_st_path_union)

text \<open>Note that due connectivity being declared as intro for S/T_Layer_Graph, this proof is
      completely automatic (as opposed to the ones in S/T_Shortest_Path_Union.\<close>
sublocale ST_Layer_Graph c' s t unfolding ST_Layer_Graph_def
  using edge_on_shortest_path g'.isShortestPath_level_edge(6) shortest_ST_path_remains by fastforce
end \<comment> \<open>ST_Shortest_Path_Union\<close>

\<comment> \<open>Unions of shortest paths\<close>

subsection \<open>Building a layering from an arbitrary graph\<close>

subsubsection \<open>Building from source node\<close>

definition induced_s_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "induced_s_layering c s \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Suc (Graph.min_dist c s u) = Graph.min_dist c s v then
      c (u, v)
    else
      0"

(*interpretation sl: S_Shortest_Path_Union "induced_s_layering c s" c s "Graph.V c"*)
theorem induced_s_shortest_path_union: "S_Shortest_Path_Union (induced_s_layering c s) c s (Graph.V c)"
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

subsubsection \<open>Building from source to target node\<close>

definition st_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "st_layering c s t \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t \<and> Suc (Graph.min_dist c s u + Graph.min_dist c v t) = Graph.min_dist c s t then
      c (u, v)
    else
      0"

(* TODO why can this not coexist with sl? *)
(*interpretation stl: ST_Shortest_Path_Union "st_layering c s t" c s t*)
theorem induced_st_shortest_path_union: "ST_Shortest_Path_Union (st_layering c s t) c s t"
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

\<comment> \<open>Building a layering from an arbitrary graph\<close>

end
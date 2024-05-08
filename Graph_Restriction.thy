theory Graph_Restriction
  imports Graph_Comparison
begin

(* TODO is it useful to unify all the scattered locales into using a generic restriction function? *)
find_consts "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b"
find_consts name:restrict
find_consts name:filter
term Set.filter
term filter

definition restrict_edges :: "_ graph \<Rightarrow> (edge \<Rightarrow> bool) \<Rightarrow> _ graph"
  where "restrict_edges c P \<equiv> \<lambda>(u, v). if P (u, v) then c (u, v) else 0"

lemma restrict_edges_Subgraph: "Subgraph (restrict_edges c P) c" unfolding restrict_edges_def
  by unfold_locales (auto simp: Graph.E_def split: if_splits)

type_synonym path_kind = "node \<Rightarrow> edge list \<Rightarrow> node \<Rightarrow> bool"

definition is_in_some_path :: "path_kind \<Rightarrow> node set \<Rightarrow> node set \<Rightarrow> edge \<Rightarrow> bool"
  where "is_in_some_path \<pi> S T \<equiv> \<lambda>(u, v). \<exists> s t p. s \<in> S \<and> t \<in> T \<and> \<pi> s p t \<and> (u, v) \<in> set p"

definition restrict_paths :: "_ graph \<Rightarrow> path_kind => node set \<Rightarrow> node set \<Rightarrow> _ graph"
  where "restrict_paths c \<pi> S T \<equiv> restrict_edges c (is_in_some_path \<pi> S T)"

definition bounded_path :: "nat \<Rightarrow> path_kind \<Rightarrow> path_kind"
  where "bounded_path b \<pi> \<equiv> \<lambda> s p t. \<pi> s p t \<and> length p \<le> b"

(* TODO check whether something like this can be useful*)
(*
typedef (overloaded) 'capacity::linordered_idom irreducible_graph = "{c::('capacity graph). Irreducible_Graph c}"
  by (metis irreducibleI mem_Collect_eq reduce_reduced_cong reduced_cong_iff_reduce_eq)
*)

locale Restricted_Graph = Capacity_Compatible +
  fixes P
  assumes filtered_edges: "E' = Set.filter P E"
begin
sublocale Subgraph
  using filtered_edges by unfold_locales fastforce

lemma restricted_unique: "Restricted_Graph c'' c P \<Longrightarrow> c'' = c'"
  by (simp add: CapComp_comm CapComp_transfer Capacity_Compatible.eq_if_E_eq Restricted_Graph.axioms(1) Restricted_Graph.filtered_edges filtered_edges)
end

thm Graph.split_shortest_path
thm Graph.split_simple_path
thm Graph.isPath_append
thm Graph.split_shortest_path_around_edge

locale Path_Kind =
  fixes isKindPath
  assumes path_kind: "\<And>c u p v. isKindPath c u p v \<Longrightarrow> Graph.isPath c u p v"
begin
lemma connected: "isKindPath c u p v \<Longrightarrow> Graph.connected c u v"
  using Graph.connected_def path_kind by blast
end

locale Splittable_Path_Kind = Path_Kind +
  assumes split_path: "\<And>c u p\<^sub>1 p\<^sub>2 v. isKindPath c u (p\<^sub>1 @ p\<^sub>2) v \<Longrightarrow> \<exists>w. isKindPath c u p\<^sub>1 w \<and> isKindPath c w p\<^sub>2 v"
begin
lemma split_around_edge:
  assumes "isKindPath c s (p @ (u, v) # p') t"
  shows "isKindPath c s p u \<and> isKindPath c u ((u, v) # p') t
        \<and> isKindPath c s (p @ [(u, v)]) v \<and> isKindPath c v p' t"
proof (intro conjI)
  from assms obtain w where "isKindPath c s p w" "isKindPath c w ((u, v) # p') t"
    using split_path by blast
  moreover from this have "w = u" by (meson Graph.isPath.simps(2) path_kind)
  ultimately show "isKindPath c s p u" "isKindPath c u ((u, v) # p') t" by auto
next
  from assms obtain w where "isKindPath c s (p @ [(u, v)]) w" "isKindPath c w p' t"
    using split_path by (metis append.assoc append_Cons append_Nil)
  moreover from this have "w = v" by (metis Graph.isPath_tail path_kind snd_conv)
  ultimately show "isKindPath c s (p @ [(u, v)]) v" "isKindPath c v p' t" by auto
qed
end

(* TODO is this useful? *)
locale Connecting_Path_Kind = Path_Kind +
  assumes connecting: "\<And>c u v. Graph.connected c u v \<Longrightarrow> \<exists>p. isKindPath c u p v"
begin
(* TODO can we derive this if we just assume Path_Kind? *)
(* sublocale Splittable_Path_Kind *)

lemma obtain_path:
  assumes "Graph.connected c u v"
  obtains p where "isKindPath c u p v"
  using assms connecting by blast
end

locale Subgraph_Path_Kind = Path_Kind +
  assumes transfer_path: "\<And>c' c u p v. \<lbrakk>Subgraph c' c; set p \<subseteq> Graph.E c'; isKindPath c u p v\<rbrakk> \<Longrightarrow> isKindPath c' u p v"

locale Regular_Path_Kind = Splittable_Path_Kind + Connecting_Path_Kind + Subgraph_Path_Kind

(* TODO manually prove the interpretations, then replace the corresponding theorems in Graph.thy *)
interpretation isPath: Regular_Path_Kind Graph.isPath
  apply unfold_locales
     apply simp
    apply (simp add: Graph.isPath_append)
   apply (simp add: Graph.connected_def)
  by (simp add: Graph.isPath_alt)

interpretation isSimplePath: Regular_Path_Kind Graph.isSimplePath
  apply unfold_locales
    apply (simp add: Graph.isSimplePath_def)
    apply (simp add: Graph.split_simple_path)
  using Graph.connected_def Graph.isSPath_pathLE apply blast
  by (simp add: Graph.isPath_alt Graph.isSimplePath_def)

interpretation isShortestPath: Regular_Path_Kind Graph.isShortestPath
  apply unfold_locales
     apply (simp add: Graph.shortestPath_is_path)
    apply (simp add: Graph.split_shortest_path)
   apply (meson Graph.obtain_shortest_path)
  by (meson Graph.shortestPath_is_path Subgraph_def Subset_Graph.sub_shortest_path_if_contained isPath.transfer_path)

locale Graph_Prop_Union = Capacity_Compatible c' c
  for P c' c +
  (* for P and c' c :: "'capacity::linordered_idom graph" + *)
  fixes S T
  assumes path_union: "E' = \<Union> {set p | p. \<exists>s t. s \<in> S \<and> t \<in> T \<and> P c s p t}"

locale Source_Graph_Prop_Union = Capacity_Compatible c' c
  for P c' c +
  (* for P and c' c :: "'capacity::linordered_idom graph" + *)
  fixes s T
  assumes source_path_union: "E' = \<Union> {set p | p. \<exists>t. t \<in> T \<and> P c s p t}"
sublocale Source_Graph_Prop_Union \<subseteq> Graph_Prop_Union _ _ _ "{s}"
  by unfold_locales (simp add: source_path_union)

locale Target_Graph_Prop_Union = Capacity_Compatible c' c
  for P c' c +
  (* for P and c' c :: "'capacity::linordered_idom graph" + *)
  fixes S t
  assumes target_path_union: "E' = \<Union> {set p | p. \<exists>s. s \<in> S \<and> P c s p t}"
sublocale Target_Graph_Prop_Union \<subseteq> Graph_Prop_Union _ _ _ _ "{t}"
  by unfold_locales (simp add: target_path_union)

locale Dual_Graph_Prop_Union = Capacity_Compatible c' c
  for P c' c +
  (* for P and c' c :: "'capacity::linordered_idom graph" + *)
  fixes s t
  assumes dual_path_union: "E' = \<Union> {set p | p. P c s p t}"
sublocale Dual_Graph_Prop_Union \<subseteq> Source_Graph_Prop_Union _ _ _ _ "{t}"
  by unfold_locales (simp add: dual_path_union)
sublocale Dual_Graph_Prop_Union \<subseteq> Target_Graph_Prop_Union _ _ _ "{s}"
  by unfold_locales (simp add: dual_path_union)


locale Path_Kind_Union = Path_Kind + Graph_Prop_Union isKindPath
begin
sublocale Restricted_Graph c' c "\<lambda>e. \<exists>p s t. e \<in> set p \<and> s \<in> S \<and> t \<in> T \<and> isKindPath c s p t"
  by unfold_locales (fastforce simp: path_union intro: path_kind isPath_edgeset)

lemma edge_on_path:
  "(u, v) \<in> E' \<Longrightarrow> \<exists>s t p. s \<in> S \<and> t \<in> T \<and> isKindPath c s p t \<and> (u, v) \<in> set p"
  using path_union by blast

lemma obtain_ST_path_via_edge:
  assumes "(u, v) \<in> E'"
  obtains s t p\<^sub>s p\<^sub>t where "s \<in> S" "t \<in> T" "isKindPath c s (p\<^sub>s @ (u, v) # p\<^sub>t) t"
  using assms by (metis edge_on_path in_set_conv_decomp)
end

locale Splittable_Path_Kind_Union = Splittable_Path_Kind + Graph_Prop_Union isKindPath
begin
sublocale Path_Kind_Union by intro_locales

lemma obtain_ST_paths:
  assumes "u \<in> V'"
  obtains s t p\<^sub>s p\<^sub>t where "s \<in> S" "t \<in> T" "isKindPath c s p\<^sub>s u" "isKindPath c u p\<^sub>t t" "isKindPath c s (p\<^sub>s @ p\<^sub>t) t"
  using assms apply (elim g'.vertex_cases obtain_ST_path_via_edge)
   apply (metis split_around_edge)
  by (metis split_around_edge append.assoc append.left_neutral append_Cons)

lemma obtain_connected_ST:
  assumes "u \<in> V'"
  obtains s t where "s \<in> S" "t \<in> T" "connected s u" "connected u t"
  using assms by (fastforce elim: obtain_ST_paths intro: connected)
end

locale Subgraph_Path_Kind_Union = Subgraph_Path_Kind + Graph_Prop_Union isKindPath
begin
sublocale Path_Kind_Union by intro_locales

lemma ST_path_remains:
  assumes PATH: "isKindPath c s p t"
    and "s \<in> S" "t \<in> T"
  shows "isKindPath c' s p t"
proof -
  from assms have "set p \<subseteq> E'" by (auto simp: path_union)
  with PATH show ?thesis using transfer_path 
    using Subgraph_Path_Kind.transfer_path Subgraph_Path_Kind_axioms Subgraph_axioms by blast
qed
end

locale Regular_Path_Kind_Union = Regular_Path_Kind + Graph_Prop_Union isKindPath
begin
sublocale Splittable_Path_Kind_Union by intro_locales
sublocale Subgraph_Path_Kind_Union by intro_locales
end




(* TODO do these make sense? *)
(*
locale Source_Path_Kind_Union = Path_Kind + Capacity_Compatible +
  fixes s T
  assumes source_path_union: "E' = \<Union> {set p | p. \<exists>t. t \<in> T \<and> isKindPath c s p t}"
begin
sublocale Path_Kind_Union _ _ _ "{s}"
  by unfold_locales (simp add: source_path_union)
end

locale Target_Path_Kind_Union = Path_Kind + Capacity_Compatible +
  fixes S t
  assumes target_path_union: "E' = \<Union> {set p | p. \<exists>s. s \<in> S \<and> isKindPath c s p t}"
begin
sublocale Path_Kind_Union _ _ _ _ "{t}"
  by unfold_locales (simp add: target_path_union)
end

locale Dual_Path_Kind_Union = Path_Kind + Capacity_Compatible +
  fixes s t
  assumes dual_path_union: "E' = \<Union> {set p | p. isKindPath c s p t}"
begin
sublocale Source_Path_Kind_Union _ _ _ _ "{t}"
  by unfold_locales (simp add: dual_path_union)

sublocale Target_Path_Kind_Union _ _ _ "{s}"
  by unfold_locales (simp add: dual_path_union)
end
*)

locale Path_Union = Graph_Prop_Union Graph.isPath
sublocale Path_Union \<subseteq> Regular_Path_Kind_Union Graph.isPath by intro_locales

(*
begin
lemma transfer_ST_connected_edge:
  assumes EDGE: "(u, v) \<in> E"
    and DUAL_CON: "\<exists>s\<in>S. connected s u" "\<exists>t\<in>T. connected v t"
  shows "(u, v) \<in> E'"
proof -
  from DUAL_CON obtain s t p\<^sub>s p\<^sub>t where ST: "s \<in> S" "t \<in> T" and "isPath s p\<^sub>s u" "isPath v p\<^sub>t t"
    unfolding connected_def by blast
  with EDGE have "isPath s (p\<^sub>s @ (u, v) # p\<^sub>t) t" by (simp add: isPath_append)
  with ST show ?thesis using path_union by fastforce
qed

lemma transfer_ST_connected_path:
  assumes PATH: "isPath u p v"
    and DUAL_CON: "\<exists>s\<in>S. connected s u" "\<exists>t\<in>T. connected v t"
  shows "g'.isPath u p v"
using PATH DUAL_CON(1) proof (induction rule: isPath_front_induct)
  case (EdgePath u w p)
  with DUAL_CON(2) have "(u, w) \<in> E'"
    using transfer_ST_connected_edge connected connected_trans by meson
  moreover from EdgePath have "g'.isPath w p v"
    using connected_append_edge by blast
  ultimately show ?case by simp
qed simp

corollary ST_path_remains: "\<lbrakk>isPath s p t; s \<in> S; t \<in> T\<rbrakk> \<Longrightarrow> g'.isPath s p t"
  using transfer_ST_connected_path by blast
end
*)

locale Source_Path_Union = Source_Graph_Prop_Union Graph.isPath
sublocale Source_Path_Union \<subseteq> Path_Union _ _ "{s}" by intro_locales

locale Target_Path_Union = Target_Graph_Prop_Union Graph.isPath
sublocale Target_Path_Union \<subseteq> Path_Union _ _ _ "{t}" by intro_locales

locale Dual_Path_Union = Dual_Graph_Prop_Union Graph.isPath
sublocale Dual_Path_Union \<subseteq> Source_Path_Union _ _ _ "{t}" by intro_locales
sublocale Dual_Path_Union \<subseteq> Target_Path_Union _ _ "{s}" by intro_locales

lemma Dual_Path_Union_right_leftI:
  assumes RIGHT: "Source_Path_Union c' c s (Graph.V c)"
    and LEFT: "Target_Path_Union c'' c (Graph.V c') t"
  shows "Dual_Path_Union c'' c s t"
proof -
  from RIGHT interpret right: Source_Path_Union c' c s "Graph.V c" .
  from LEFT interpret left: Target_Path_Union c'' c "Graph.V c'" t .
  interpret Subgraph c'' c by intro_locales

  show ?thesis
  proof (unfold_locales, intro pair_set_eqI)
    fix u v
    assume "(u, v) \<in> left.E'"
    then obtain w p where "w \<in> right.V'" and IN_P: "(u, v) \<in> set p" and P: "right.isPath w p t"
      using left.target_path_union by blast
    then obtain p' where "right.isPath s p' w" using right.obtain_ST_paths by blast
    with P have "right.isPath s (p' @ p) t" using right.isPath_append by blast
    with IN_P show "(u, v) \<in> \<Union> {set p |p. right.isPath s p t}" by fastforce
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. right.isPath s p t}"
    then obtain p where P: "(u, v) \<in> set p" "right.isPath s p t" by blast
    then have "right.g'.isPath s p t" apply (elim right.ST_path_remains) apply simp (* TODO *)
      by (metis (no_types, lifting) Graph.isPath_bwd_cases P(2) empty_iff empty_set mem_Collect_eq right.V_def)
(*
      using right.ST_path_remains
      by (smt (verit, del_insts) Graph.V_def Graph.distinct_nodes_in_V_if_connected(2) empty_iff empty_set insertI1 isPath.connected mem_Collect_eq right.isPath_fwd_cases)
*)
    then have "s \<in> right.V'"
      by (metis (no_types, lifting) Graph.isPath_fwd_cases P(1) emptyE list.set(1) mem_Collect_eq right.g'.V_def) (* TODO *)
    with P show "(u, v) \<in> left.E'" unfolding left.target_path_union by blast
  qed
qed




















subsection \<open>Unions of shortest paths\<close>

locale Shortest_Path_Union = Graph_Prop_Union Graph.isShortestPath
begin
sublocale Regular_Path_Kind_Union Graph.isShortestPath by intro_locales

lemma obtain_connected_subgraph_ST:
  assumes "u \<in> V'"
  obtains s t where "s \<in> S" "t \<in> T" "g'.connected s u" "g'.connected u t"
proof -
  from assms obtain s t p\<^sub>1 p\<^sub>2 where "s \<in> S" "t \<in> T" "isShortestPath s p\<^sub>1 u" "isShortestPath u p\<^sub>2 t" "isShortestPath s (p\<^sub>1 @ p\<^sub>2) t"
    by (rule obtain_ST_paths)
  then have "isPath s p\<^sub>1 u" "isPath u p\<^sub>2 t" "g'.isPath s (p\<^sub>1 @ p\<^sub>2) t"
    by (auto intro: Graph.shortestPath_is_path ST_path_remains)
  with that \<open>s \<in> S\<close> \<open>t \<in> T\<close> show thesis
    by (meson g'.connected_def Graph.isPath_alt g'.isPath_append)
qed

text \<open>Note: for the direction from g' to g, we actually DO need BOTH endpoints in S/T.
      Alternatively, it also works as long as g' is layered, which we show later.\<close>
lemma shortest_ST_path_transfer:
  assumes "s \<in> S" "t \<in> T"
  shows "g'.isShortestPath s p t \<longleftrightarrow> isShortestPath s p t"
proof
  assume "g'.isShortestPath s p t"
  then show "isShortestPath s p t"
    by (metis connected_def Graph.isShortestPath_min_dist_def assms obtain_shortest_path sub_path ST_path_remains)
qed (simp add: assms ST_path_remains)

corollary min_ST_dist_transfer: "\<lbrakk>s \<in> S; t \<in> T; connected s t\<rbrakk> \<Longrightarrow> g'.min_dist s t = min_dist s t"
  using obtain_shortest_path shortest_ST_path_transfer min_dist_eqI by meson
end \<comment> \<open>Shortest_Path_Union\<close>

locale Layered_Shortest_Path_Union = Shortest_Path_Union + Generic_Layer_Graph c'
begin
lemma path_respects_layer:
  assumes CON': "g'.connected u v" and PATH: "isPath u p v"
  shows "layer v \<le> layer u + length p"
proof (cases "u = v")
  case False
  with PATH CON' have "p \<noteq> []" "u \<in> V'" "v \<in> V'" using g'.distinct_nodes_in_V_if_connected by auto
  then obtain s t p\<^sub>s p\<^sub>t where "s \<in> S" "t \<in> T" "g'.isPath s p\<^sub>s u" "g'.isPath v p\<^sub>t t"
    by (fastforce elim: obtain_connected_subgraph_ST simp: g'.connected_def)
  moreover from CON' obtain p' where PATH': "g'.isPath u p' v" using g'.connected_def by blast
  ultimately have "isShortestPath s (p\<^sub>s @ p' @ p\<^sub>t) t"
    using g'.isPath_append shortest_ST_path_transfer by blast
  then have "\<exists>u' v'. isShortestPath u' p' v'" using split_shortest_path by blast
  with \<open>p \<noteq> []\<close> PATH' have "isShortestPath u p' v" unfolding isShortestPath_min_dist_def
    using isPath_endpoints_eq by fastforce
  with PATH have "length p' \<le> length p" unfolding isShortestPath_def by blast
  with PATH' show ?thesis using path_ascends_layer by simp
qed simp

(* TODO not true, fix *)
text \<open>Note: the previous proof almost gave us a Prelayer_Graph. However, there may still be multiple
      weakly connected components in the subgraph, each of which may have a shifted layering. Actually
      proofing Prelayer_Graph in this locale would require reasoning about the ability to choose a
      correct layering function, which is somewhat involved and unnecessary for our purposes.\<close>

lemma shortest_path_transfer: "g'.isPath u p v \<Longrightarrow>  isShortestPath u p v" unfolding isShortestPath_def
  using path_ascends_layer path_respects_layer sub_path g'.connected_def by fastforce

corollary min_dist_transfer: "g'.connected u v \<Longrightarrow> g'.min_dist u v = min_dist u v"
  using shortest_path_transfer g'.obtain_shortest_path g'.shortestPath_is_path min_dist_eqI
  by meson
end \<comment> \<open>Layered_Shortest_Path_Union\<close>

locale Source_Shortest_Path_Union = Source_Graph_Prop_Union Graph.isShortestPath
begin
sublocale Shortest_Path_Union _ _ "{s}" by intro_locales

sublocale Source_Layer_Graph c' s
proof
  fix u
  assume "u \<in> V'"
  then obtain p\<^sub>1 p\<^sub>2 t where "t \<in> T" "isShortestPath s p\<^sub>1 u" "isShortestPath s (p\<^sub>1 @ p\<^sub>2) t"
    by (blast elim: obtain_ST_paths)
  then have "g'.isShortestPath s (p\<^sub>1 @ p\<^sub>2) t" using ST_path_remains by blast
  with \<open>isShortestPath s p\<^sub>1 u\<close> show "g'.connected s u" unfolding g'.connected_def
    by (fastforce dest: Graph.shortestPath_is_path simp: g'.isPath_append Graph.isPath_alt)
next
  fix u v
  assume "(u, v) \<in> E'"
  then show "Suc (g'.min_dist s u) = g'.min_dist s v"
    using edge_on_path g'.isShortestPath_level_edge(4) ST_path_remains by fastforce
qed

sublocale Layered_Shortest_Path_Union _ _ "{s}" T layer by intro_locales


(* TODO prettify, necessary? *)
sublocale Local_Prelayer_Graph c layer V'
  apply unfold_locales
  by (metis Graph.isPath_distD dist_trans min_dist_is_dist min_dist_minD min_dist_transfer s_connected sub_connected)

lemma restrict_T_to_reachable: "Source_Shortest_Path_Union c' c s (reachableNodes s \<inter> T)"
  using source_path_union reachableNodes_def connected_def isShortestPath_min_dist_def
  by unfold_locales auto

(* TODO check if necessary, and if so, cleanup *)
lemma shortest_s_path_remains_path: "\<lbrakk>u \<in> V'; isShortestPath s p u\<rbrakk> \<Longrightarrow> g'.isPath s p u"
proof (elim g'.vertex_cases)
  fix v
  assume SP: "isShortestPath s p u" and "(u, v) \<in> E'"
  then obtain t p\<^sub>1 p\<^sub>2 where "t \<in> T" "isShortestPath s (p\<^sub>1 @ (u, v) # p\<^sub>2) t"
    using obtain_ST_path_via_edge by force
    (*by (elim obtain_shortest_ST_edge_path)*)
  with SP have "isShortestPath s (p @ (u, v) # p\<^sub>2) t"
    by (metis (no_types, lifting) isShortestPath_min_dist_def isPath_append length_append split_shortest_path_around_edge)
  with \<open>t \<in> T\<close> have "g'.isShortestPath s (p @ (u, v) # p\<^sub>2) t" using ST_path_remains by blast
  then show ?thesis using g'.shortestPath_is_path g'.split_shortest_path_around_edge by blast
next
  fix v
  assume SP: "isShortestPath s p u" and "(v, u) \<in> E'"
  then obtain t p\<^sub>1 p\<^sub>2 where "t \<in> T" "isShortestPath s (p\<^sub>1 @ (v, u) # p\<^sub>2) t"
    using obtain_ST_path_via_edge by force
    (*by (elim obtain_shortest_sT_edge_path)*)
  with SP have "isShortestPath s (p @ p\<^sub>2) t"
    by (metis (mono_tags, lifting) Graph.isShortestPath_min_dist_def append.assoc append_Cons isPath_append length_append self_append_conv2 split_shortest_path_around_edge)
  with \<open>t \<in> T\<close> have "g'.isShortestPath s (p @  p\<^sub>2) t" using ST_path_remains by blast
  with SP show ?thesis
    by (meson Graph.isPath_alt Graph.shortestPath_is_path g'.split_shortest_path)
qed
end \<comment> \<open>Source_Shortest_Path_Union\<close>

locale Target_Shortest_Path_Union = Target_Graph_Prop_Union Graph.isShortestPath
begin
text \<open>Note that this is symmetric to Source_Shortest_Path_Union, thus the path/dist transfer properties
      hold here as well. However, since we never use this locale without the other, and we would
      need to setup Generic_Layer_Graph using int instead of nat, we do not show them here again.\<close>
sublocale Shortest_Path_Union _ _ _ "{t}" by intro_locales

sublocale Target_Layer_Graph c' t
proof
  fix u
  assume "u \<in> V'"
  then obtain p\<^sub>1 p\<^sub>2 s where "s \<in> S" "isShortestPath u p\<^sub>2 t" "isShortestPath s (p\<^sub>1 @ p\<^sub>2) t"
    by (blast elim: obtain_ST_paths)
  then have "g'.isShortestPath s (p\<^sub>1 @ p\<^sub>2) t" using ST_path_remains by blast
  with \<open>isShortestPath u p\<^sub>2 t\<close> show "g'.connected u t" unfolding g'.connected_def
    by (fastforce dest: Graph.shortestPath_is_path simp: g'.isPath_append Graph.isPath_alt)
next
  fix u v
  assume "(u, v) \<in> E'"
  then show "Suc (g'.min_dist v t) = g'.min_dist u t"
    using edge_on_path g'.isShortestPath_level_edge(5) ST_path_remains by fastforce
qed
end \<comment> \<open>Target_Shortest_Path_Union\<close>

locale Dual_Shortest_Path_Union = Dual_Graph_Prop_Union Graph.isShortestPath
begin
sublocale Source_Shortest_Path_Union _ _ _"{t}" by intro_locales

sublocale Target_Shortest_Path_Union _ _ "{s}" by intro_locales

text \<open>Note that due connectivity being declared as intro for S/T_Layer_Graph, this proof is
      completely automatic (as opposed to the ones in S/T_Shortest_Path_Union).\<close>
sublocale Dual_Layer_Graph c' s t
  apply unfold_locales
   apply blast
  using edge_on_path g'.isShortestPath_level_edge(6) ST_path_remains by fastforce

lemma st_connected_iff: "g'.connected s t \<longleftrightarrow> connected s t"
  by (meson Graph.obtain_shortest_path isShortestPath.connected ST_path_remains singletonI sub_connected)
  (*using empty_iff_ST_disconnected g'.empty_connected s_in_V_if_nonempty by fastforce*)

(*
lemma empty_iff: "g'.isEmpty \<longleftrightarrow> (connected s t \<longleftrightarrow> s = t)"
  using empty_iff_ST_disconnected by blast
*)
end \<comment> \<open>Dual_Shortest_Path_Union\<close>

(*
lemma ST_SPU_dualI: (* TODO prettify *)
  "\<lbrakk>Source_Shortest_Path_Union c' c s {t}; T_Shortest_Path_Union c' c {s} t\<rbrakk> \<Longrightarrow> Dual_Shortest_Path_Union c' c s t"
  by (smt (verit, best) Collect_cong Dual_Shortest_Path_Union_axioms.intro Dual_Shortest_Path_Union_def T_Shortest_Path_Union.axioms(1) T_Shortest_Path_Union.shortest_t_path_union singleton_iff)
*)

(* TODO adapt style to the one for paths, maybe unify *)
lemma Dual_Shortest_Path_Union_right_leftI:
  assumes RIGHT: "Source_Shortest_Path_Union c' c s (Graph.V c)"
    and LEFT: "Target_Shortest_Path_Union c'' c' (Graph.V c') t"
  shows "Dual_Shortest_Path_Union c'' c s t"
proof
  from RIGHT interpret right: Source_Shortest_Path_Union c' c s "Graph.V c" .
  from LEFT interpret left: Target_Shortest_Path_Union c'' c' "Graph.V c'" t .

  show "\<And>u v. c'' (u, v) = 0 \<or> c (u, v) = 0 \<or> c'' (u, v) = c (u, v)"
    by (metis right.sg_cap_cases left.sg_cap_cases)

  show "left.E' = \<Union> {set p |p. right.isShortestPath s p t}" (* TODO prettify *)
  proof (intro pair_set_eqI)
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. right.isShortestPath s p t}"
    then obtain p where SP: "(u, v) \<in> set p" "right.isShortestPath s p t" by blast
    then have "s \<in> right.V" "t \<in> right.V" using right.distinct_nodes_in_V_if_connected right.isShortestPath_level_edge
      by (metis right.min_dist_z empty_set ex_in_conv right.isShortestPath_min_dist_def length_0_conv)+
    with SP have "right.g'.isShortestPath s p t" using right.ST_path_remains by blast
    with \<open>(u, v) \<in> set p\<close> \<open>s \<in> right.V\<close> show "(u, v) \<in> left.E'" using left.target_path_union
      using Graph.isEmpty_def Graph.isPath_edgeset Graph.isShortestPath_min_dist_def right.s_in_V_if_nonempty by fastforce
  next
    fix u v
    assume "(u, v) \<in> left.E'"
    then obtain p w where "(u, v) \<in> set p" "w \<in> right.V'" "right.g'.isShortestPath w p t"
      using left.target_path_union by blast
    then obtain p' where "right.g'.isShortestPath s p' w" using right.g'.obtain_shortest_path by blast
    with \<open>right.g'.isShortestPath w p t\<close> have "right.isShortestPath s (p' @ p) t"
      using right.g'.shortestPath_is_path right.g'.isPath_append right.shortest_path_transfer by blast
    with \<open>(u, v) \<in> set p\<close> show "(u, v) \<in> \<Union> {set p |p. right.isShortestPath s p t}" by auto
  qed
qed
\<comment> \<open>Unions of shortest paths\<close>



(* TODO refactor starting here *)








(* TODO this is mostly the same, but includes a length bound. Is there a way without so much duplication? *)
subsection \<open>Unions of bounded length shortest paths\<close>

(* TODO cleanup and check which lemma are actually necessary *)
locale Bounded_Shortest_Path_Union = Capacity_Compatible +
  fixes S T b
  assumes bounded_shortest_path_union:
    "E' = \<Union>{set p | p. \<exists>s t. s \<in> S \<and> t \<in> T \<and> isShortestPath s p t \<and> length p \<le> b}"
begin
sublocale Subgraph
  using bounded_shortest_path_union isPath_edgeset shortestPath_is_path by unfold_locales blast

lemma edge_on_bounded_shortest_path:
  "(u, v) \<in> E' \<Longrightarrow> \<exists>s t p. s \<in> S \<and> t \<in> T \<and> isShortestPath s p t \<and> length p \<le> b \<and> (u, v) \<in> set p"
  using bounded_shortest_path_union by blast

lemma obtain_bounded_shortest_ST_edge_path:
  assumes "(u, v) \<in> E'"
  obtains s t p\<^sub>s p\<^sub>t where "s \<in> S" "t \<in> T" "isShortestPath s (p\<^sub>s @ (u, v) # p\<^sub>t) t" "length (p\<^sub>s @ (u, v) # p\<^sub>t) \<le> b"
  using assms by (metis edge_on_bounded_shortest_path in_set_conv_decomp)

lemma obtain_bounded_shortest_ST_paths:
  assumes "u \<in> V'"
  obtains s t p\<^sub>s p\<^sub>t where "s \<in> S" "t \<in> T" "isShortestPath s p\<^sub>s u" "isShortestPath u p\<^sub>t t"
    "isShortestPath s (p\<^sub>s @ p\<^sub>t) t" "length (p\<^sub>s @ p\<^sub>t) \<le> b"
  using assms apply (elim g'.vertex_cases obtain_bounded_shortest_ST_edge_path)
   apply (metis split_shortest_path_around_edge)
  by (smt (verit, ccfv_threshold) Graph.split_shortest_path_around_edge append.left_neutral append_Cons append_assoc)
  (*by (metis split_shortest_path_around_edge append.assoc append.left_neutral append_Cons)*)
  (* TODO improve *)

lemma bounded_shortest_ST_path_remains:
  assumes "s \<in> S" "t \<in> T" and SP: "length p \<le> b" "isShortestPath s p t"
  shows "g'.isShortestPath s p t"
proof -
  from assms have "g'.isPath s p t"
    by (auto simp: Graph.isPath_alt bounded_shortest_path_union dest: shortestPath_is_path)
  with SP show ?thesis by (auto intro: sub_shortest_path_if_contained)
qed

lemma obtain_close_ST:
  assumes "u \<in> V'"
  obtains s t where "s \<in> S" "t \<in> T" "g'.connected s u" "g'.connected u t" "g'.min_dist s u \<le> b" "g'.min_dist u t \<le> b"
proof -
  from assms obtain s t p\<^sub>1 p\<^sub>2 where "s \<in> S" "t \<in> T" and SPs: "isShortestPath s p\<^sub>1 u" "isShortestPath u p\<^sub>2 t"
    and "isShortestPath s (p\<^sub>1 @ p\<^sub>2) t" "length (p\<^sub>1 @ p\<^sub>2) \<le> b"
    by (rule obtain_bounded_shortest_ST_paths)
  then have "g'.isPath s (p\<^sub>1 @ p\<^sub>2) t"
    using g'.shortestPath_is_path bounded_shortest_ST_path_remains by blast
  with SPs have "g'.isShortestPath s p\<^sub>1 u" "g'.isShortestPath u p\<^sub>2 t"
     apply (auto simp: Graph.isPath_alt intro!: sub_shortest_path_if_contained)
    by (auto intro: isLinked_if_isPath shortestPath_is_path)
  with that[OF \<open>s \<in> S\<close> \<open>t \<in> T\<close>] \<open>length (p\<^sub>1 @ p\<^sub>2) \<le> b\<close> show thesis
    unfolding g'.connected_def g'.isShortestPath_min_dist_def by auto
qed

lemma bounded_shortest_ST_path_transfer:
  assumes "s \<in> S" "t \<in> T" "length p \<le> b"
  shows "g'.isShortestPath s p t \<longleftrightarrow> isShortestPath s p t"
proof
  assume "g'.isShortestPath s p t"
  with assms show "isShortestPath s p t"
    by (smt (verit) Graph.connected_def Graph.isPath_distD Graph.isShortestPath_min_dist_def Graph.min_dist_minD bounded_shortest_ST_path_remains dual_order.trans obtain_shortest_path sub_path)
qed (rule bounded_shortest_ST_path_remains[OF assms])

(* TODO fix or remove
corollary min_ST_dist_transfer: "\<lbrakk>s \<in> S; t \<in> T; g'.connected s t\<rbrakk> \<Longrightarrow> g'.min_dist s t = min_dist s t"
  using obtain_shortest_path shortest_ST_path_transfer min_dist_eqI by meson
*)
end

locale Bounded_Layered_Shortest_Path_Union = Bounded_Shortest_Path_Union + Generic_Layer_Graph c'

locale Bounded_Source_Shortest_Path_Union = Capacity_Compatible + 
  fixes s T b
  assumes bounded_shortest_s_path_union:
    "E' = \<Union>{set p | p. \<exists>t. t \<in> T \<and> isShortestPath s p t \<and> length p \<le> b}"
begin
sublocale Subgraph
  using bounded_shortest_s_path_union isPath_edgeset shortestPath_is_path by unfold_locales blast

sublocale Bounded_Shortest_Path_Union c' c "{s}" T b
  by unfold_locales (simp add: bounded_shortest_s_path_union)

sublocale Source_Shortest_Path_Union c' c s "{t. t \<in> T \<and> min_dist s t \<le> b}"
  apply unfold_locales
  by (smt (verit) Collect_cong Graph.isShortestPath_min_dist_def bounded_shortest_s_path_union mem_Collect_eq) (* TODO prettify *)

text \<open>Notably, this immediately yields the fact that g' is s_layered\<close>
thm Source_Layer_Graph_axioms

sublocale Distance_Bounded_Graph c' b
proof (intro g'.Distance_Bounded_Graph_PathI)
  fix u p v
  assume PATH: "g'.isPath u p v"
  show "length p \<le> b"
  proof (cases "p = []")
    case False
    with PATH have "v \<in> V'" using g'.V_def g'.isPath_bwd_cases by fastforce
    with PATH show ?thesis using path_ascends_layer by (auto elim: obtain_close_ST)
  qed simp
qed
end \<comment> \<open>Bounded_Source_Shortest_Path_Union\<close>

text \<open>Lemma for the special case of paths to ALL nodes.\<close>
context
  fixes c' c s b
  assumes BSPU: "Bounded_Source_Shortest_Path_Union c' c s (Graph.V c) b"
begin
interpretation Bounded_Source_Shortest_Path_Union c' c s "Graph.V c" b using BSPU .

lemma BSPU_V'_boundedReachable: "V' \<union> {s} = boundedReachableNodes b s"
proof (intro equalityI; intro subsetI)
  fix u
  assume "u \<in> V' \<union> {s}"
  then obtain p where "isShortestPath s p u" "length p \<le> b"
    using g'.connected_def path_length_bounded shortest_path_transfer by blast
  then show "u \<in> boundedReachableNodes b s"
    unfolding boundedReachableNodes_def isShortestPath_min_dist_def connected_def by auto
next
  fix u
  assume "u \<in> boundedReachableNodes b s"
  then obtain p where SP: "isShortestPath s p u" "length p \<le> b" unfolding boundedReachableNodes_def
    using obtain_shortest_path isShortestPath_min_dist_def by auto
  then show "u \<in> V' \<union> {s}"
  proof (cases "p = []")
    case True
    with SP show ?thesis using shortestPath_is_path by fastforce
  next
    case False
    with SP show ?thesis
      by (metis Graph.connected_def Graph.distinct_nodes_in_V_if_connected(2) Graph.shortestPath_is_path UnCI bounded_shortest_ST_path_remains singleton_iff)
  qed
qed

end

(* TODO move or remove *)
(*
lemma Un_le_nat_extract: "\<Union> {S n |n. n \<le> (b :: nat)} = \<Union> {S n |n. n < b} \<union> S b"
  unfolding Union_SetCompr_eq using nat_less_le by auto
*)


(* TODO prettify and generalize *)
(* TODO create better setup for "exactDistNodes n s \<times> exactDistNodes (Suc n) s" *)

(*
(* TODO fix, needs \<inter> E *)
lemma (in CapacityCompatibleGraphs) bounded_s_union_edges_iff:
  "Bounded_Source_Shortest_Path_Union c' c s V b \<longleftrightarrow> E' = \<Union>{exactDistNodes n s \<times> exactDistNodes (Suc n) s | n. n < b}"
proof -
  have "\<Union>{set p | p. \<exists>t. t \<in> V \<and> isShortestPath s p t \<and> length p \<le> b} = \<Union>{exactDistNodes n s \<times> exactDistNodes (Suc n) s | n. n < b}"
  proof (induction b)
    case 0
    then show ?case by auto
  next
    case (Suc b)
    have "\<Union> {exactDistNodes n s \<times> exactDistNodes (Suc n) s |n. n < Suc b} = \<Union> {exactDistNodes n s \<times> exactDistNodes (Suc n) s |n. n < b} \<union> exactDistNodes b s \<times> exactDistNodes (Suc b) s"
      unfolding Union_SetCompr_eq using less_Suc_eq by auto
    also from Suc have "... = \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t \<and> length p \<le> b} \<union> exactDistNodes b s \<times> exactDistNodes (Suc b) s" by simp
    also have "... = \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t \<and> length p \<le> Suc b}"
    proof (intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t \<and> length p \<le> b} \<union> exactDistNodes b s \<times> exactDistNodes (Suc b) s"
      then show "(u, v) \<in> \<Union> {set p |p. \<exists>t. t \<in> V \<and> isShortestPath s p t \<and> length p \<le> Suc b}"
      proof
        assume "(u, v) \<in> exactDistNodes b s \<times> exactDistNodes (Suc b) s"
        (*
        then have "connected s u" "min_dist s v = Suc (min_dist s u)"
          unfolding exactDistNodes_def by auto
        *)
        thm shortestPath_append_edge

        then have "connected s u" "Suc (min_dist s u) = min_dist s v" "(u, v) \<in> E"
          unfolding exactDistNodes_def apply auto oops
        then obtain p where "isShortestPath s (p @ [(u, v)]) v"
        then show ?thesis sorry
      qed sorry (fastforce)
    next
    finally show ?case by simp (* TODO *)
  qed
  then show ?thesis
    by (simp add: Bounded_Source_Shortest_Path_Union_axioms_def Bounded_Source_Shortest_Path_Union_def CapacityCompatibleGraphs_axioms)
qed
*)

locale Bounded_Target_Shortest_Path_Union = Capacity_Compatible +
  fixes S t b
  assumes bounded_shortest_t_path_union:
    "E' = \<Union>{set p | p. \<exists>s. s \<in> S \<and> isShortestPath s p t \<and> length p \<le> b}"
begin
sublocale Bounded_Shortest_Path_Union c' c S "{t}" b
  by unfold_locales (simp add: bounded_shortest_t_path_union)
end \<comment> \<open>Bounded_Target_Shortest_Path_Union\<close>

locale Bounded_Dual_Shortest_Path_Union = Capacity_Compatible +
  fixes s t b
  assumes bounded_shortest_st_path_union: "E' = \<Union>{set p | p. isShortestPath s p t \<and> length p \<le> b}"
begin
sublocale Bounded_Source_Shortest_Path_Union c' c s "{t}" b
  by unfold_locales (simp add: bounded_shortest_st_path_union)

sublocale Bounded_Target_Shortest_Path_Union c' c "{s}" t b
  by unfold_locales (simp add: bounded_shortest_st_path_union)

thm Source_Layer_Graph_axioms
thm s_connected s_layered
(* TODO prettify and generalize *)
sublocale Dual_Layer_Graph c' s t
  apply unfold_locales
  using obtain_close_ST apply blast
  by (metis Graph.min_dist_is_dist UnCI add_Suc dist_layer g'.V_alt image_eqI obtain_close_ST s_layered singletonD snd_conv)

find_theorems "(?P \<longrightarrow> ?Q) \<Longrightarrow> \<not> ?Q \<longrightarrow> \<not> ?P" (* TODO *)
thm not_mono

lemma st_connected_if_bound_path: "isPath s p t \<and> length p \<le> b \<Longrightarrow> g'.connected s t"
proof -
  assume "isPath s p t \<and> length p \<le> b"
  then obtain p' where "isShortestPath s p' t" "length p' \<le> b"
    by (meson obtain_shortest_path connected_def isShortestPath_def le_trans)
  then have "g'.isShortestPath s p' t" using bounded_shortest_ST_path_transfer by blast
  then show "g'.connected s t" using g'.connected_def g'.shortestPath_is_path by blast
qed

lemma empty_iff_no_short_paths: "g'.isEmpty \<longleftrightarrow> (\<forall>p. isPath s p t \<longrightarrow> p = [] \<or> b < length p)"
  oops (* TODO *)

end \<comment> \<open>Bounded_Dual_Shortest_Path_Union\<close>

(* TODO *)
lemma min_st_dist_bound:
  "Graph.min_dist c s t \<le> b \<Longrightarrow> Bounded_Dual_Shortest_Path_Union c' c s t b \<longleftrightarrow> Dual_Shortest_Path_Union c' c s t"
  unfolding Bounded_Dual_Shortest_Path_Union_def
  unfolding Dual_Shortest_Path_Union_def
  unfolding Bounded_Dual_Shortest_Path_Union_axioms_def
  unfolding Dual_Graph_Prop_Union_def
  unfolding Dual_Graph_Prop_Union_axioms_def
  unfolding Graph.isShortestPath_min_dist_def
  by fastforce

\<comment> \<open>Unions of bounded length shortest paths\<close>











subsection \<open>Building a layering from an arbitrary graph\<close>

subsubsection \<open>Building from source node\<close>

definition induced_s_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "induced_s_layering c s \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Suc (Graph.min_dist c s u) = Graph.min_dist c s v then
      c (u, v)
    else
      0"

(*interpretation sl: Source_Shortest_Path_Union "induced_s_layering c s" c s "Graph.V c"*)
theorem induced_Source_Shortest_path_union: "Source_Shortest_Path_Union (induced_s_layering c s) c s (Graph.V c)"
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

definition induced_st_layering :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "induced_st_layering c s t \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t \<and> Suc (Graph.min_dist c s u + Graph.min_dist c v t) = Graph.min_dist c s t then
      c (u, v)
    else
      0"

(* TODO why can this not coexist with sl? *)
(*interpretation stl: Dual_Shortest_Path_Union "induced_st_layering c s t" c s t*)
theorem induced_st_shortest_path_union: "Dual_Shortest_Path_Union (induced_st_layering c s t) c s t"
proof
  interpret Graph c .
  interpret g': Graph "induced_st_layering c s t" .
  show "g'.E = \<Union> {set p |p. isShortestPath s p t}"
  proof (rule pair_set_eqI)
    fix u v
    assume "(u, v) \<in> g'.E"
    then have MIN_DIST: "(u, v) \<in> E \<and> Suc (min_dist s u + min_dist v t) = min_dist s t" and "connected s u \<and> connected v t"
      unfolding induced_st_layering_def Graph.E_def by (smt case_prod_conv mem_Collect_eq)+
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
    then show "(u, v) \<in> g'.E" unfolding induced_st_layering_def Graph.E_def by simp
  qed
qed (simp add: induced_st_layering_def)

\<comment> \<open>Building a layering from an arbitrary graph\<close>

end
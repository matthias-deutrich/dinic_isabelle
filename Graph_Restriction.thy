theory Graph_Restriction
  imports Graph_Comparison
begin

(* For presentation *)
definition (in Graph) restrict_edges :: "(edge \<Rightarrow> bool) \<Rightarrow> _ graph"
  where "restrict_edges P \<equiv> \<lambda>(u, v). if P (u, v) then c (u, v) else 0"

lemma (in Graph) restrict_edges_Subgraph: "Subgraph (restrict_edges P) c"
  apply unfold_locales
  unfolding restrict_edges_def Graph.E_def by auto

(* TODO check whether something like this can be useful*)
(*
typedef (overloaded) 'capacity::linordered_idom irreducible_graph = "{c::('capacity graph). Irreducible_Graph c}"
  by (metis irreducibleI mem_Collect_eq reduce_reduced_cong reduced_cong_iff_reduce_eq)
*)

locale Restricted_Graph = Capacity_Compatible +
  fixes P :: "edge \<Rightarrow> bool"
  assumes filtered_edges: "E' = Set.filter P E"
begin
sublocale Subgraph
  using filtered_edges by unfold_locales fastforce

lemma restricted_unique: "Restricted_Graph c'' c P \<Longrightarrow> c'' = c'"
  by (simp add: CapComp_comm CapComp_transfer Capacity_Compatible.eq_if_E_eq Restricted_Graph.axioms(1) Restricted_Graph.filtered_edges filtered_edges)
end

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
  shows "(u, v) \<in> Graph.E c
        \<and> isKindPath c s p u \<and> isKindPath c u ((u, v) # p') t
        \<and> isKindPath c s (p @ [(u, v)]) v \<and> isKindPath c v p' t"
proof (intro conjI)
  from assms show "(u, v) \<in> Graph.E c"
    by (meson Graph.isPath_edgeset in_set_conv_decomp path_kind)
next
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
  fixes s
  assumes source_path_union: "E' = \<Union> {set p | p. \<exists>t\<in>V. P c s p t}"
sublocale Source_Graph_Prop_Union \<subseteq> Graph_Prop_Union _ _ _ "{s}" V
  by unfold_locales (auto simp: source_path_union)

locale Target_Graph_Prop_Union = Capacity_Compatible c' c
  for P c' c +
  fixes t
  assumes target_path_union: "E' = \<Union> {set p | p. \<exists>s\<in>V. P c s p t}"
sublocale Target_Graph_Prop_Union \<subseteq> Graph_Prop_Union _ _ _ V "{t}"
  by unfold_locales (auto simp: target_path_union)

locale Dual_Graph_Prop_Union = Capacity_Compatible c' c
  for P c' c +
  fixes s t
  assumes dual_path_union: "E' = \<Union> {set p | p. P c s p t}"
sublocale Dual_Graph_Prop_Union \<subseteq> Graph_Prop_Union _ _ _ "{s}" "{t}"
  by unfold_locales (auto simp: dual_path_union)

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

locale Splittable_Subgraph_Path_Kind_Union = Splittable_Path_Kind_Union + Subgraph_Path_Kind_Union
begin
lemma obtain_connected_subgraph_ST:
  assumes "u \<in> V'"
  obtains s t where "s \<in> S" "t \<in> T" "g'.connected s u" "g'.connected u t"
proof -
  from assms obtain s t p\<^sub>1 p\<^sub>2 where "s \<in> S" "t \<in> T" "isKindPath c s p\<^sub>1 u" "isKindPath c u p\<^sub>2 t" "isKindPath c s (p\<^sub>1 @ p\<^sub>2) t"
    by (rule obtain_ST_paths)
  then have "isPath s p\<^sub>1 u" "isPath u p\<^sub>2 t" "isKindPath c' s (p\<^sub>1 @ p\<^sub>2) t"
    by (auto intro: path_kind ST_path_remains)
  with that \<open>s \<in> S\<close> \<open>t \<in> T\<close> show thesis
    by (metis Graph.isPath_alt Path_Kind.connected Path_Kind.path_kind Path_Kind_axioms isPath.Path_Kind_axioms le_sup_iff set_append)
qed
end

locale Regular_Path_Kind_Union = Regular_Path_Kind + Graph_Prop_Union isKindPath
begin
sublocale Splittable_Subgraph_Path_Kind_Union by intro_locales
end

locale Path_Union = Graph_Prop_Union Graph.isPath
sublocale Path_Union \<subseteq> Regular_Path_Kind_Union Graph.isPath by intro_locales

locale Source_Path_Union = Source_Graph_Prop_Union Graph.isPath
sublocale Source_Path_Union \<subseteq> Path_Union _ _ "{s}" V by intro_locales

locale Target_Path_Union = Target_Graph_Prop_Union Graph.isPath
sublocale Target_Path_Union \<subseteq> Path_Union _ _ V "{t}" by intro_locales

locale Dual_Path_Union = Dual_Graph_Prop_Union Graph.isPath
sublocale Dual_Path_Union \<subseteq> Path_Union _ _ "{s}" "{t}" by intro_locales

lemma Dual_Path_Union_right_leftI:
  assumes RIGHT: "Source_Path_Union c' c s"
    and LEFT: "Target_Path_Union c'' c' t"
  shows "Dual_Path_Union c'' c s t"
proof -
  from RIGHT interpret right: Source_Path_Union c' c s .
  from LEFT interpret left: Target_Path_Union c'' c' t .
  interpret Subgraph c'' c
    using left.Subgraph_axioms right.Subgraph_axioms by force

  show ?thesis
  proof (unfold_locales, intro pair_set_eqI)
    fix u v
    assume "(u, v) \<in> left.E'"
    then obtain w p where "w \<in> right.V'" and IN_P: "(u, v) \<in> set p" and P: "right.g'.isPath w p t"
      using left.target_path_union by blast
    then obtain p' where "right.isPath s p' w" using right.obtain_ST_paths by blast
    with P have "right.isPath s (p' @ p) t" using right.isPath_append using right.sub_path by blast
    with IN_P show "(u, v) \<in> \<Union> {set p |p. right.isPath s p t}" by fastforce
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. right.isPath s p t}"
    then obtain p where P: "(u, v) \<in> set p" "right.isPath s p t" by blast
    then have P': "right.g'.isPath s p t" apply (elim right.ST_path_remains) apply simp (* TODO *)
      by (metis (no_types, lifting) Graph.isPath_bwd_cases P(2) empty_iff empty_set mem_Collect_eq right.V_def)
(*
      using right.ST_path_remains
      by (smt (verit, del_insts) Graph.V_def Graph.distinct_nodes_in_V_if_connected(2) empty_iff empty_set insertI1 isPath.connected mem_Collect_eq right.isPath_fwd_cases)
*)
    then have "s \<in> right.V'"
      by (metis (no_types, lifting) Graph.isPath_fwd_cases P(1) emptyE list.set(1) mem_Collect_eq right.g'.V_def) (* TODO *)
    with P(1) P' show "(u, v) \<in> left.E'" unfolding left.target_path_union by blast
  qed
qed


subsection \<open>Unions of shortest paths\<close>

locale Shortest_Path_Union = Graph_Prop_Union Graph.isShortestPath
begin
sublocale Regular_Path_Kind_Union Graph.isShortestPath by intro_locales

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

(* TODO refactor? *)
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
sublocale Shortest_Path_Union _ _ "{s}" V by intro_locales

sublocale Source_Layer_Graph c' s
proof
  fix u v
  assume "(u, v) \<in> E'"
  then show "Suc (g'.min_dist s u) = g'.min_dist s v"
    using edge_on_path g'.isShortestPath_level_edge(4) ST_path_remains by fastforce
qed (blast elim: obtain_connected_subgraph_ST)

sublocale Layered_Shortest_Path_Union _ _ "{s}" V layer by intro_locales


(* TODO prettify, necessary? *)
sublocale Local_Prelayer_Graph c layer V'
  apply unfold_locales
  by (metis Graph.isPath_distD dist_trans min_dist_is_dist min_dist_minD min_dist_transfer s_connected sub_connected)

(* TODO check if necessary, and if so, cleanup *)
lemma shortest_s_path_remains_path: "\<lbrakk>u \<in> V'; isShortestPath s p u\<rbrakk> \<Longrightarrow> g'.isPath s p u"
proof (elim g'.vertex_cases)
  fix v
  assume SP: "isShortestPath s p u" and "(u, v) \<in> E'"
  then obtain t p\<^sub>1 p\<^sub>2 where "t \<in> V" "isShortestPath s (p\<^sub>1 @ (u, v) # p\<^sub>2) t"
    using obtain_ST_path_via_edge by force
    (*by (elim obtain_shortest_ST_edge_path)*)
  with SP have "isShortestPath s (p @ (u, v) # p\<^sub>2) t"
    by (metis (no_types, lifting) isShortestPath_min_dist_def isPath_append length_append split_shortest_path_around_edge)
  with \<open>t \<in> V\<close> have "g'.isShortestPath s (p @ (u, v) # p\<^sub>2) t" using ST_path_remains by blast
  then show ?thesis using g'.shortestPath_is_path g'.split_shortest_path_around_edge by blast
next
  fix v
  assume SP: "isShortestPath s p u" and "(v, u) \<in> E'"
  then obtain t p\<^sub>1 p\<^sub>2 where "t \<in> V" "isShortestPath s (p\<^sub>1 @ (v, u) # p\<^sub>2) t"
    using obtain_ST_path_via_edge by force
    (*by (elim obtain_shortest_sT_edge_path)*)
  with SP have "isShortestPath s (p @ p\<^sub>2) t"
    by (metis (mono_tags, lifting) Graph.isShortestPath_min_dist_def append.assoc append_Cons isPath_append length_append self_append_conv2 split_shortest_path_around_edge)
  with \<open>t \<in> V\<close> have "g'.isShortestPath s (p @  p\<^sub>2) t" using ST_path_remains by blast
  with SP show ?thesis
    by (meson Graph.isPath_alt Graph.shortestPath_is_path g'.split_shortest_path)
qed
end \<comment> \<open>Source_Shortest_Path_Union\<close>

locale Target_Shortest_Path_Union = Target_Graph_Prop_Union Graph.isShortestPath
begin
text \<open>Note that this is symmetric to Source_Shortest_Path_Union, thus the path/dist transfer properties
      hold here as well. However, since we never use this locale without the other, and we would
      need to setup Generic_Layer_Graph using int instead of nat, we do not show them here again.\<close>
sublocale Shortest_Path_Union _ _ V "{t}" by intro_locales

sublocale Target_Layer_Graph c' t
proof
  fix u v
  assume "(u, v) \<in> E'"
  then show "Suc (g'.min_dist v t) = g'.min_dist u t"
    using edge_on_path g'.isShortestPath_level_edge(5) ST_path_remains by fastforce
qed (blast elim: obtain_connected_subgraph_ST)
end \<comment> \<open>Target_Shortest_Path_Union\<close>

locale Dual_Shortest_Path_Union = Dual_Graph_Prop_Union Graph.isShortestPath
begin
sublocale Shortest_Path_Union _ _ "{s}" "{t}" by intro_locales

sublocale Dual_Layer_Graph c' s t
proof
  fix u v
  assume "(u, v) \<in> E'"
  then show "Suc (g'.min_dist s u + g'.min_dist v t) = g'.min_dist s t"
    using edge_on_path g'.isShortestPath_level_edge(6) ST_path_remains by fastforce
qed (blast elim: obtain_connected_subgraph_ST)

sublocale Layered_Shortest_Path_Union _ _ "{s}" "{t}" layer by intro_locales

sublocale Local_Prelayer_Graph c layer V'
  apply unfold_locales
  by (metis Graph.isPath_distD dist_trans min_dist_is_dist min_dist_minD min_dist_transfer s_connected sub_connected)

(* TODO right place? *)
lemma st_connected_iff: "g'.connected s t \<longleftrightarrow> connected s t"
  by (meson Graph.obtain_shortest_path isShortestPath.connected ST_path_remains singletonI sub_connected)
  (*using empty_iff_ST_disconnected g'.empty_connected s_in_V_if_nonempty by fastforce*)
end \<comment> \<open>Dual_Shortest_Path_Union\<close>

(* TODO adapt style to the one for paths, maybe unify *)
lemma Dual_Shortest_Path_Union_right_leftI:
  assumes RIGHT: "Source_Shortest_Path_Union c' c s"
    and LEFT: "Target_Shortest_Path_Union c'' c' t"
  shows "Dual_Shortest_Path_Union c'' c s t"
proof
  from RIGHT interpret right: Source_Shortest_Path_Union c' c s .
  from LEFT interpret left: Target_Shortest_Path_Union c'' c' t .

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

(* TODO this is mostly the same, but includes a length bound. Is there a way without so much duplication? *)
subsection \<open>Unions of bounded length shortest paths\<close>

definition isBoundedShortestPath :: "nat \<Rightarrow> _ graph \<Rightarrow> node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" where
  "isBoundedShortestPath b c u p v \<equiv> Graph.isShortestPath c u p v \<and> length p \<le> b"

interpretation isBoundedShortestPath: Splittable_Path_Kind "isBoundedShortestPath b" +
    isBoundedShortestPath: Subgraph_Path_Kind "isBoundedShortestPath b" for b
  unfolding isBoundedShortestPath_def
  by unfold_locales (auto simp: isShortestPath.path_kind isShortestPath.split_path intro: isShortestPath.transfer_path)

locale Bounded_Shortest_Path_Union = Graph_Prop_Union "isBoundedShortestPath b" for b
sublocale Bounded_Shortest_Path_Union \<subseteq> Splittable_Subgraph_Path_Kind_Union "isBoundedShortestPath b" by intro_locales

locale Bounded_Source_Shortest_Path_Union = Source_Graph_Prop_Union "isBoundedShortestPath b" for b
begin
sublocale Bounded_Shortest_Path_Union _ _ "{s}" V b by intro_locales

sublocale Source_Layer_Graph c' s
proof
  fix u v
  assume "(u, v) \<in> E'"
  (*
  then show "Suc (g'.min_dist s u) = g'.min_dist s v"
    using edge_on_path g'.isShortestPath_level_edge(4) ST_path_remains isBoundedShortestPath_def by fastforce
  *)
  then obtain p t where "t \<in> V" "isBoundedShortestPath b c s p t" "(u, v) \<in> set p"
    using edge_on_path by blast
  then have "isBoundedShortestPath b c' s p t" using ST_path_remains by simp
  with \<open>(u, v) \<in> set p\<close> show "Suc (g'.min_dist s u) = g'.min_dist s v"
    unfolding isBoundedShortestPath_def using g'.isShortestPath_level_edge(4) by force
qed (blast elim: obtain_connected_subgraph_ST)

sublocale Distance_Bounded_Graph c' b
proof (intro g'.Distance_Bounded_Graph_PathI)
  fix u p v
  assume PATH: "g'.isPath u p v"
  show "length p \<le> b"
  proof (cases "p = []")
    case False
    with PATH have "v \<in> V'" using g'.V_def g'.isPath_bwd_cases by fastforce
    then obtain p' where "isBoundedShortestPath b c' s p' v"
      using obtain_ST_paths ST_path_remains vertex'_if_vertex by (metis singleton_iff)
    then have "layer v \<le> b" unfolding isBoundedShortestPath_def g'.isShortestPath_min_dist_def by simp
    with PATH show ?thesis using path_ascends_layer by simp
  qed simp
qed

lemma V'_boundedReachable: "V' \<union> {s} = boundedReachableNodes b s"
proof (intro equalityI; intro subsetI)
  fix u
  assume "u \<in> V' \<union> {s}"

  (* TODO clean up this part *)
  then have "connected s u" "g'.connected s u"
    using obtain_connected_ST obtain_connected_subgraph_ST by auto
  then have "g'.min_dist s u \<le> b"
    by (metis Graph.min_dist_is_dist bounded)
  from \<open>connected s u\<close> obtain p where "isShortestPath s p u"
    using obtain_shortest_path by blast
  with \<open>g'.min_dist s u \<le> b\<close> have "length p \<le> b"
    by (metis (no_types, lifting) \<open>g'.connected s u\<close> g'.isShortestPath_alt g'.obtain_shortest_path g'.shortestPath_is_path isShortestPath_def le_Suc_ex sub_path trans_le_add1)

  with \<open>isShortestPath s p u\<close> show "u \<in> boundedReachableNodes b s"
    unfolding boundedReachableNodes_def isShortestPath_min_dist_def connected_def by auto
next
  fix u
  assume "u \<in> boundedReachableNodes b s"
  then obtain p where SP: "isBoundedShortestPath b c s p u"
    by (fastforce elim: obtain_shortest_path simp: isShortestPath_min_dist_def isBoundedShortestPath_def boundedReachableNodes_def)
  then show "u \<in> V' \<union> {s}"
  proof (cases "p = []")
    case True
    with SP show ?thesis using isBoundedShortestPath.path_kind by fastforce
  next
    case False
    with SP show ?thesis
      by (metis Graph.distinct_nodes_in_V_if_connected(2) ST_path_remains UnCI insert_iff isBoundedShortestPath.connected)
  qed
qed
end

locale Bounded_Target_Shortest_Path_Union = Target_Graph_Prop_Union "isBoundedShortestPath b" for b
sublocale Bounded_Target_Shortest_Path_Union \<subseteq> Bounded_Shortest_Path_Union _ _ V "{t}" b by intro_locales

locale Bounded_Dual_Shortest_Path_Union = Dual_Graph_Prop_Union "isBoundedShortestPath b" for b
begin
sublocale Bounded_Shortest_Path_Union _ _ "{s}" "{t}" b by intro_locales

sublocale Dual_Layer_Graph c' s t
proof
  fix u v
  assume "(u, v) \<in> E'"
  then obtain p where "isBoundedShortestPath b c s p t" "(u, v) \<in> set p"
    using edge_on_path by blast
  then have "isBoundedShortestPath b c' s p t" using ST_path_remains by simp
  with \<open>(u, v) \<in> set p\<close> show "Suc (g'.min_dist s u + g'.min_dist v t) = g'.min_dist s t"
    unfolding isBoundedShortestPath_def using g'.isShortestPath_level_edge(6) by fastforce
qed (blast elim: obtain_connected_subgraph_ST)

sublocale Distance_Bounded_Graph c' b
proof (intro g'.Distance_Bounded_Graph_PathI)
  fix u p v
  assume PATH: "g'.isPath u p v"
  show "length p \<le> b"
  proof (cases "p = []")
    case False
    with PATH have "v \<in> V'" using g'.V_def g'.isPath_bwd_cases by fastforce
    then obtain p\<^sub>s p\<^sub>t where "isPath s p\<^sub>s v" "isBoundedShortestPath b c s (p\<^sub>s @ p\<^sub>t) t"
      using obtain_ST_paths vertex'_if_vertex isBoundedShortestPath.path_kind by (metis singletonD)
    then have "isBoundedShortestPath b c' s p\<^sub>s v"
      using ST_path_remains isBoundedShortestPath.split_path isBoundedShortestPath.path_kind
      by (metis Graph.isPath_alt isBoundedShortestPath_def path_is_shortest singletonI)
    then have "layer v \<le> b" unfolding isBoundedShortestPath_def g'.isShortestPath_min_dist_def by simp
    with PATH show ?thesis using path_ascends_layer by simp
  qed simp
qed
end

lemma min_st_dist_bound:
  "Graph.min_dist c s t \<le> b \<Longrightarrow> Bounded_Dual_Shortest_Path_Union c' c s t b \<longleftrightarrow> Dual_Shortest_Path_Union c' c s t"
  unfolding Bounded_Dual_Shortest_Path_Union_def
  unfolding Dual_Shortest_Path_Union_def
  unfolding Dual_Graph_Prop_Union_def
  unfolding Dual_Graph_Prop_Union_axioms_def
  unfolding isBoundedShortestPath_def
  unfolding Graph.isShortestPath_min_dist_def
  by fastforce

end
theory Original_Dinitz_Algo
  imports
    Graph_Restriction
    Network_Utils
    Refine_Monadic.Refine_Monadic
begin
definition (in Graph) cleaning :: "node \<Rightarrow> node \<Rightarrow> _ graph"
  where "cleaning s t \<equiv> \<lambda>(u, v).
    if connected s u \<and> connected v t then
      c (u, v)
    else
      0"

lemma Dual_Path_Union_cleaningI: "Dual_Path_Union (Graph.cleaning c s t) c s t"
proof
  interpret Graph_Comparison "Graph.cleaning c s t" c .
  show "E' = \<Union> {set p |p. isPath s p t}"
  proof (intro pair_set_eqI)
    fix u v
    assume "(u, v) \<in> E'"
    then have "connected s u" "connected v t" "(u, v) \<in> E"
      unfolding cleaning_def Graph.E_def by simp_all presburger+
    then obtain p\<^sub>s p\<^sub>t where "isPath s (p\<^sub>s @ (u, v) # p\<^sub>t) t"
      using connected_def isPath_append by auto
    then show "(u, v) \<in> \<Union> {set p |p. isPath s p t}"
      by fastforce
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. isPath s p t}"
    then obtain p\<^sub>s p\<^sub>t where "isPath s (p\<^sub>s @ (u, v) # p\<^sub>t) t" using split_list by fastforce
    then have "connected s u" "connected v t" "(u, v) \<in> E"
      using connected_def isPath_append by auto
    then show "(u, v) \<in> E'" unfolding cleaning_def Graph.E_def by simp
  qed
qed (simp add: Graph.cleaning_def split_paired_all)

lemma Dual_Path_Union_iff_cleaning: "Dual_Path_Union c' c s t \<longleftrightarrow> c' = Graph.cleaning c s t"
proof
  assume "Dual_Path_Union c' c s t"
  then interpret union': Dual_Path_Union c' c s t .
  interpret Dual_Path_Union "Graph.cleaning c s t" c s t using Dual_Path_Union_cleaningI .
  show "c' = Graph.cleaning c s t"
    using restricted_unique union'.Restricted_Graph_axioms by blast
qed (simp add: Dual_Path_Union_cleaningI)

subsubsection \<open>Building from source to target node\<close>

definition (in Graph) induced_dual_layering :: "node \<Rightarrow> node \<Rightarrow> _ graph"
  where "induced_dual_layering s t \<equiv> \<lambda>(u, v).
    if connected s u \<and> connected v t \<and> Suc (min_dist s u + min_dist v t) = min_dist s t then
      c (u, v)
    else
      0"

lemma Dual_Shortest_Path_Union_layeringI:
  "Dual_Shortest_Path_Union (Graph.induced_dual_layering c s t) c s t"
proof
  interpret Graph c .
  interpret g': Graph "Graph.induced_dual_layering c s t" .
  show "g'.E = \<Union> {set p |p. isShortestPath s p t}"
  proof (rule pair_set_eqI)
    fix u v
    assume "(u, v) \<in> g'.E"
    then have MIN_DIST: "(u, v) \<in> E \<and> Suc (min_dist s u + min_dist v t) = min_dist s t" and "connected s u \<and> connected v t"
      unfolding induced_dual_layering_def Graph.E_def by (smt case_prod_conv mem_Collect_eq)+
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
    then show "(u, v) \<in> g'.E" unfolding induced_dual_layering_def Graph.E_def by simp
  qed
qed (simp add: Graph.induced_dual_layering_def split_paired_all)

lemma Dual_Shortest_Path_Union_iff_induced:
  "Dual_Shortest_Path_Union c' c s t \<longleftrightarrow> c' = Graph.induced_dual_layering c s t"
proof
  assume "Dual_Shortest_Path_Union c' c s t"
  then interpret union': Dual_Shortest_Path_Union c' c s t .
  interpret Dual_Shortest_Path_Union "Graph.induced_dual_layering c s t" c s t
    using Dual_Shortest_Path_Union_layeringI .
  show "c' = Graph.induced_dual_layering c s t"
    using restricted_unique union'.Restricted_Graph_axioms by blast
qed (simp add: Dual_Shortest_Path_Union_layeringI)

\<comment> \<open>Building a layering from an arbitrary graph\<close>

subsection \<open>Properties when removing a flow from the ST_Layering\<close>
locale Dinitz_Subtract =
  g': Irreducible_Graph c' +
  Nonnegative_Graph c +
  f: Graph f + Dual_Shortest_Path_Union c' c s t + f_c': Contained_Graph f c'
  for c' c :: "'capacity::linordered_idom graph" and s t and f :: "'capacity graph"
begin
interpretation f_c': Pos_Contained_Graph f c'
  by (intro f_c'.Pos_Contained_Graph_if_Nonnegative) intro_locales

interpretation f_c: Pos_Contained_Graph f c
  apply (intro Contained_Graph.Pos_Contained_Graph_if_Nonnegative)
   apply (rule contained_trans[where c'=c'])
  by intro_locales
(*
interpretation f_c: Pos_Contained_Graph 
interpretation f'_stl: Pos_Contained_Graph f' stl
  by (meson Pos_Contained_Graph_leI f'_stl.cap_abs_bounded stl.cap_non_negative order_trans)

interpretation f'_cf: Pos_Contained_Graph f' cf
  by unfold_locales (metis c'_sg_c_old f'_stl.cap_le f'_stl.cap_nonzero resE_nonNegative)*)

abbreviation "new_c \<equiv> subtract_skew_graph f"
abbreviation "new_c' \<equiv> Graph.cleaning (g'.subtract_graph f) s t"
interpretation new: Graph_Comparison new_c' new_c .

(*
abbreviation "aug_cf \<equiv> cf_of (augment f')"
interpretation aug_cf: Graph aug_cf .

lemma aug_cf_alt: "aug_cf = cf.subtract_skew_graph f'"
  by (rule augment_alt') intro_locales

abbreviation "stl' \<equiv> Graph.cleaning (stl.subtract_graph f') s t"
interpretation stl_minus_f': Graph "stl.subtract_graph f'" .
interpretation stl': Graph stl' .
*)

definition new_edge_count :: "path \<Rightarrow> nat"
  where "new_edge_count p \<equiv> length (filter (\<lambda>e. e \<notin> E) p)"

lemma new_edge_prelayered:
  "\<lbrakk>u \<in> V'; v \<in> V'; new.isPath u p v\<rbrakk> \<Longrightarrow> layer v + 2 * new_edge_count p \<le> layer u + length p"
proof (induction "new_edge_count p" arbitrary: u p v rule: less_induct)
  case less
  then show ?case
  proof (cases "new_edge_count p" rule: nat.exhaust_disc)
    case zero
    with less.prems have "isPath u p v"
      unfolding new_edge_count_def Graph.isPath_alt
      by (metis empty_filter_conv length_0_conv subrelI)
    with zero less.prems show ?thesis using path_prelayered by simp
  next
    case Suc
    then obtain w\<^sub>1 w\<^sub>2 p\<^sub>1 p\<^sub>2 where P: "p = p\<^sub>1 @ (w\<^sub>1, w\<^sub>2) # p\<^sub>2" and W_NOT_E: "(w\<^sub>1, w\<^sub>2) \<notin> E"
      unfolding new_edge_count_def
      by (metis filter_False in_set_conv_decomp length_0_conv subrelI subsetD)
    then have P1_COUNT: "new_edge_count p\<^sub>1 < new_edge_count p"
      and P2_COUNT: "new_edge_count p\<^sub>2 < new_edge_count p"
      unfolding new_edge_count_def by auto

    from less.prems P have P1_PATH: "new.isPath u p\<^sub>1 w\<^sub>1" and P2_PATH: "new.isPath w\<^sub>2 p\<^sub>2 v"
      using new.isPath_append by auto

    from P less.prems have "(w\<^sub>1, w\<^sub>2) \<in> new.E" using new.isPath_append by simp
    with W_NOT_E have "(w\<^sub>2, w\<^sub>1) \<in> f.E" using f_c.subtract_skew_edges_sub by blast
    then have "(w\<^sub>2, w\<^sub>1) \<in> E'" using f_c'.E_ss by blast
    then have "w\<^sub>1 \<in> V'" "w\<^sub>2 \<in> V'" and W_L: "layer w\<^sub>1 = Suc (layer w\<^sub>2)" unfolding g'.V_def by auto

    show ?thesis using W_NOT_E
        less.hyps[OF P1_COUNT \<open>u \<in> V'\<close> \<open>w\<^sub>1 \<in> V'\<close> P1_PATH]
        less.hyps[OF P2_COUNT \<open>w\<^sub>2 \<in> V'\<close> \<open>v \<in> V'\<close> P2_PATH]
      by (simp add: W_L P new_edge_count_def)
  qed
qed

(*
find_theorems layer
corollary "\<lbrakk>u \<in> V'; v \<in> V'; aug_cf.isPath u p v\<rbrakk> \<Longrightarrow> g'.min_dist s v + 2 * new_edge_count p \<le> g'.min_dist s u + length p"
  using aug_cf_new_edge_prelayered try0
*)

(*
lemma st_min_dist_non_decreasing: "aug_cf.connected s t \<Longrightarrow> cf.min_dist s t \<le> aug_cf.min_dist s t"
proof (cases "Graph.isEmpty f'")
  case True
  then show ?thesis unfolding aug_cf_alt cf.subtract_skew_graph_def Graph.isEmpty_def by simp
next
  assume "aug_cf.connected s t"
  then obtain p where SP': "aug_cf.isShortestPath s p t" by (rule aug_cf.obtain_shortest_path)

  case False
  then have IN_V': "s \<in> V'" "t \<in> V'"
    using f'_stl.E_ss s_in_V_if_nonempty t_in_V_if_nonempty
    unfolding Graph.isEmpty_def by auto
  then have "cf.min_dist s t = layer t" using min_dist_transfer s_connected by simp
  also from SP' IN_V' have "layer t \<le> length p"
    using aug_cf.shortestPath_is_path aug_cf_new_edge_prelayered by fastforce
  finally show ?thesis using SP' aug_cf.isShortestPath_min_dist_def by simp
qed
*)

lemma st_min_dist_non_decreasing: "min_dist_less_eq s t c new_c"
proof (cases f.isEmpty)
  case True
  then show ?thesis unfolding subtract_skew_graph_def Graph.isEmpty_def by simp
next
  case False
  then have IN_V': "s \<in> V'" "t \<in> V'"
    using f_c'.E_ss s_in_V_if_nonempty t_in_V_if_nonempty
    unfolding Graph.isEmpty_def by auto
  then have C_LAYER: "min_dist s t = layer t" using min_dist_transfer s_connected by simp

  show ?thesis unfolding min_dist_less_eq_def
  proof (intro impI conjI)
    from IN_V' show "connected s t" using s_connected st_connected_iff by blast

    assume NEW_CON: "new.connected s t"
    then obtain p where SP': "new.isShortestPath s p t" by (rule new.obtain_shortest_path)
    with IN_V' have "layer t \<le> length p"
      using new.shortestPath_is_path new_edge_prelayered by fastforce
    with C_LAYER show "min_dist s t \<le> new.min_dist s t"
      using SP' new.isShortestPath_min_dist_def by fastforce
  qed
qed

lemma new_path_transfer:
  "\<lbrakk>new.isPath u p v; g'.isPath u p v\<rbrakk> \<Longrightarrow> Graph.isPath (g'.subtract_graph f) u p v"
proof (unfold Graph.isPath_alt, clarify)
  fix w\<^sub>1 w\<^sub>2
  assume "(w\<^sub>1, w\<^sub>2) \<in> set p" "set p \<subseteq> new.E" "set p \<subseteq> E'"
  then have assms: "(w\<^sub>1, w\<^sub>2) \<in> new.E" "(w\<^sub>1, w\<^sub>2) \<in> E'" by auto
  then have "(w\<^sub>2, w\<^sub>1) \<notin> E'" using no_parallel_edge by blast
  then have "f (w\<^sub>2, w\<^sub>1) = 0"
    using f.zero_cap_simp f_c'.E_ss by blast
  with assms show "(w\<^sub>1, w\<^sub>2) \<in> Graph.E (g'.subtract_graph f)"
    unfolding Graph.E_def g'.subtract_graph_def subtract_skew_graph_def
    by simp (metis cap_compatible cap_nonzero)
qed

lemma cleaning_maintains_bounded_union:
  "Bounded_Dual_Shortest_Path_Union new_c' new_c s t (min_dist s t)"
proof (cases f.isEmpty)
  case True
  then have "(g'.subtract_graph f) = c'"
    unfolding Graph.isEmpty_def g'.subtract_graph_def by auto
  then have "new_c' = c'"
    unfolding Graph.cleaning_def using g'.V_def g'.zero_cap_simp by fastforce
  moreover from True have "new_c = c"
    unfolding Graph.isEmpty_def subtract_skew_graph_def by simp
  moreover note Dual_Shortest_Path_Union_axioms
  ultimately show ?thesis  by (simp add: min_st_dist_bound)
next
  case False
  then have IN_V': "s \<in> V'" "t \<in> V'"
    using f_c'.E_ss s_in_V_if_nonempty t_in_V_if_nonempty
    unfolding Graph.isEmpty_def by auto

  interpret cleaning: Dual_Path_Union new_c' "g'.subtract_graph f"
    using Dual_Path_Union_cleaningI .
  interpret subtract_subgraph: Subgraph "g'.subtract_graph f" new_c
    by (rule irreducible_contained_skew_subtract) intro_locales
  interpret stl'_sub_aug_cf: Subgraph new_c' new_c
    by (rule subgraph.order_trans[where y="g'.subtract_graph f"]) intro_locales

  show ?thesis
  proof (unfold_locales, intro pair_set_eqI)
    fix u v
    assume "(u, v) \<in> new.E'"
    then obtain p where "Graph.isPath (g'.subtract_graph f) s p t" "(u, v) \<in> set p"
      using cleaning.dual_path_union by blast
    then have "new.isPath s p t" using subtract_subgraph.sub_path by blast
    moreover have "length p = min_dist s t"
    proof -
      interpret sub_cont: Contained_Graph "g'.subtract_graph f" c'
        using f_c'.subtract_contained .
      from \<open>Graph.isPath (g'.subtract_graph f) s p t\<close> have "g'.isPath s p t"
        unfolding Graph.isPath_alt using sub_cont.E_ss by blast
      then show ?thesis using isShortestPath_min_dist_def shortest_path_transfer by blast
    qed
    moreover from \<open>new.isPath s p t\<close> have "min_dist s t \<le> new.min_dist s t"
      using st_min_dist_non_decreasing new.connected_def unfolding min_dist_less_eq_def by blast
    moreover note \<open>(u, v) \<in> set p\<close>
    ultimately show "(u, v) \<in> \<Union> {set p |p. isBoundedShortestPath (min_dist s t) new_c s p t}"
      unfolding isBoundedShortestPath_def new.isShortestPath_min_dist_def
      using new.isPath_distD new.min_dist_minD by fastforce
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. isBoundedShortestPath (min_dist s t) new_c s p t}"
    then obtain p where SP': "new.isShortestPath s p t" "length p \<le> min_dist s t"
      and UV_IN_P: "(u, v) \<in> set p" unfolding isBoundedShortestPath_def by blast
    with IN_V' have "layer t + 2 * new_edge_count p \<le> layer s + min_dist s t"
      using new_edge_prelayered new.shortestPath_is_path by fastforce
    with IN_V' have "new_edge_count p = 0" using min_dist_transfer st_connected by simp
    with SP' have "isShortestPath s p t"
      unfolding new_edge_count_def Graph.isShortestPath_min_dist_def
      by (metis new.connected_def Graph.isPath_alt empty_filter_conv length_0_conv nle_le st_min_dist_non_decreasing min_dist_less_eq_def subset_code(1)) (* TODO fix *)
    then have "g'.isPath s p t" using IN_V' by (simp add: ST_path_remains path_kind)
    with SP' have "Graph.isPath (g'.subtract_graph f) s p t"
      using new_path_transfer new.shortestPath_is_path by blast
    then have "new.g'.isPath s p t"
      using cleaning.dual_path_union unfolding Graph.isPath_alt by blast
    with UV_IN_P show "(u, v) \<in> new.E'"
      using Graph.isPath_edgeset by blast
  qed
qed

(*
lemma augment_NFlow: "NFlow c s t (augment f')"
proof (intro NFlowI)
  show "Network c s t" using Network_axioms .
  have "Flow cf s t f'"
    using transfer_flow[OF f'.Flow_axioms cf.Nonnegative_Graph_axioms cf.Finite_Graph_axioms] .
  then show "Flow c s t (augment f')" using augment_flow_presv by blast
qed
*)

lemma E_pss_if_saturated_edge:
  "\<exists>e. c' e = f e \<and> f e > 0 \<Longrightarrow> new.E' \<subset> E'"
proof
  assume "\<exists>e. c' e = f e \<and> f e > 0"
  then obtain e where "c' e = f e" "f e > 0" by blast
  then have "e \<in> E'" "e \<notin> new.E'"
    unfolding Graph.E_def g'.subtract_graph_def Graph.cleaning_def by auto
  then show "new.E' \<noteq> E'" by blast

  show "new.E' \<subseteq> E'"
  proof -
    interpret sub_cont: Contained_Graph "g'.subtract_graph f" c'
      using f_c'.subtract_contained .
    interpret cleaning: Dual_Path_Union new_c' "g'.subtract_graph f"
      by (simp add: Dual_Path_Union_cleaningI)
    show ?thesis using cleaning.E_ss sub_cont.E_ss by blast
  qed
qed
end

\<comment> \<open>Properties when removing a flow from the ST_Layering\<close>

subsection \<open>Dinitz inner loop\<close>

interpretation Refine_Monadic_Syntax .

context NFlow
begin
definition dinitzPhase :: "_ flow nres" where
  "dinitzPhase \<equiv> do {
    let stl = cf.induced_dual_layering s t;
    (f', _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, stl'). Graph.connected stl' s t)
      (\<lambda>(f', stl'). do {
        p \<leftarrow> spec p. Graph.isPath stl' s p t;
        let stl' = Graph.cleaning (Graph.subtract_path stl' p) s t;
        let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
        return (f', stl')})
      (f, stl);
    return f'}"

definition dinitzPhaseInvar :: "_ flow \<times> _ graph \<Rightarrow> bool" where
  "dinitzPhaseInvar \<equiv> \<lambda>(f', stl).
    NFlow c s t f'
    \<and> Bounded_Dual_Shortest_Path_Union stl (cf_of f') s t (cf.min_dist s t)
    \<and> min_dist_less_eq s t cf (cf_of f')"

lemma dinitzPhase_step:
  fixes f' stl
  assumes INVAR: "dinitzPhaseInvar (f', stl)"
      and PATH: "Graph.isPath stl s p t"
  defines "aug_f' \<equiv> NFlow.augment c f' (NPreflow.augmentingFlow c f' p)"
      and "stl' \<equiv> Graph.cleaning (Graph.subtract_path stl p) s t"
    shows "dinitzPhaseInvar (aug_f', stl') \<and> Graph.E stl' \<subset> Graph.E stl \<and> finite (Graph.E stl)"
proof (unfold dinitzPhaseInvar_def, intro case_prodI conjI)
  from INVAR interpret f': NFlow c s t f' unfolding dinitzPhaseInvar_def by blast

  have BOUND_EQ: "cf.min_dist s t = f'.cf.min_dist s t"
  proof (intro antisym)
    from INVAR interpret Bounded_Dual_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
      unfolding dinitzPhaseInvar_def by blast

    from PATH INVAR show "cf.min_dist s t \<le> f'.cf.min_dist s t"
      unfolding dinitzPhaseInvar_def Graph.connected_def min_dist_less_eq_def
      using sub_path by blast

    from PATH have "f'.cf.min_dist s t \<le> g'.min_dist s t"
      using isPath.connected sub_min_dist_geq by blast
    also have "... = length p" using PATH path_ascends_layer by force
    also have "... \<le> cf.min_dist s t" using PATH path_length_bounded by simp
    finally show "f'.cf.min_dist s t \<le> cf.min_dist s t" .
  qed
  with INVAR interpret Dual_Shortest_Path_Union stl f'.cf s t
    unfolding dinitzPhaseInvar_def using min_st_dist_bound by fastforce

  from PATH show "NFlow c s t aug_f'"
    by (fastforce simp: aug_f'_def f'.isAugmentingPath_def
                  intro: NFlowI f'.augment_flow_presv f'.augFlow_resFlow shortest_path_transfer f'.cf.shortestPath_is_simple)

  interpret g': Nonnegative_Graph stl
    by (intro sg_Nonnegative_Graph) intro_locales
  interpret g': Irreducible_Graph stl
    using no_parallel_edge by unfold_locales

  from PATH have INDUCED_EQ: "f'.cf.path_induced_graph p = g'.path_induced_graph p"
    using f'.cf.Nonnegative_Graph_axioms g'.isPath_alt path_induced_graph_eq by simp

  interpret dinitz_subtract: Pos_Contained_Graph "f'.augmentingFlow p" stl
    by (simp add: INDUCED_EQ f'.augmentingFlow_alt g'.path_induced_graph_pos_contained)
  interpret dinitz_subtract: Dinitz_Subtract stl f'.cf s t "f'.augmentingFlow p" by intro_locales

  have stl'_alt: "stl' = dinitz_subtract.new_c'"
    unfolding stl'_def g'.subtract_path_alt f'.augmentingFlow_alt using INDUCED_EQ by simp

  have cf_aug_f'_alt: "cf_of aug_f' = dinitz_subtract.new_c"
  proof -
    have "Contained_Graph (f'.augmentingFlow p) f'.cf"
      by (rule contained_trans) intro_locales
    then show ?thesis unfolding aug_f'_def using f'.augment_alt' by simp
  qed

  show "Bounded_Dual_Shortest_Path_Union stl' (cf_of aug_f') s t (cf.min_dist s t)"
    unfolding stl'_alt cf_aug_f'_alt
    using dinitz_subtract.cleaning_maintains_bounded_union BOUND_EQ by simp

  from INVAR show "min_dist_less_eq s t cf (cf_of aug_f')"
    unfolding cf_aug_f'_alt dinitzPhaseInvar_def
    using dinitz_subtract.st_min_dist_non_decreasing min_dist_preorder.order_trans by blast

  show "Graph.E stl' \<subset> E'"
  proof (unfold stl'_alt, intro dinitz_subtract.E_pss_if_saturated_edge exI conjI)
    from PATH have P_NOT_EMPTY: "p \<noteq> []" using t_not_s by auto
    with INDUCED_EQ have PATH_CAP: "f'.augmentingFlow p (arg_min_list stl p) = g'.pathCap p"
      unfolding f'.augmentingFlow_alt  g'.path_induced_graph_def
      using arg_min_list_in by auto
    with P_NOT_EMPTY show "stl (arg_min_list stl p) = f'.augmentingFlow p (arg_min_list stl p)"
      using f_arg_min_list_f g'.pathCap_alt by auto

    from PATH P_NOT_EMPTY PATH_CAP show "0 < f'.augmentingFlow p (arg_min_list stl p)"
      unfolding g'.isPath_alt using g'.nonempty_path_cap_positive by simp
  qed

  show "finite E'" using E_ss finite_subset by auto
qed








(*
(* TODO introduce notion of blocking flow or reuse from Push Relabel, then connect this concept *)
definition res_dist_increasing_flow
  where "res_dist_increasing_flow f' \<equiv>
    NFlow c s t f' \<and> (Graph.connected (cf_of f') s t \<longrightarrow> cf.min_dist s t < Graph.min_dist (cf_of f') s t)"

(*definition blocking_flow*)

lemma dinitzPhase_final:
  fixes f' stl
    assumes DISCON: "\<not> Graph.connected stl s t"
      and INVAR: "dinitzPhaseInvar (f', stl)"
    shows "res_dist_increasing_flow f'"
  unfolding res_dist_increasing_flow_def
proof
  from INVAR show "NFlow c s t f'" unfolding dinitzPhaseInvar_def by blast
  then interpret f': NFlow c s t f' .

  from INVAR interpret Bounded_Dual_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
    unfolding dinitzPhaseInvar_def by blast
  from DISCON show "f'.cf.connected s t \<longrightarrow> cf.min_dist s t < f'.cf.min_dist s t"
    by (metis Bounded_Dual_Shortest_Path_Union_axioms Dual_Shortest_Path_Union.st_connected_iff le_eq_less_or_eq linorder_neqE_nat min_st_dist_bound)
qed

lemma dinitzPhase_correct:
  "dinitzPhase \<le> (spec f'. res_dist_increasing_flow f')"
  unfolding dinitzPhase_def
  apply (refine_vcg WHILET_rule[where I=dinitzPhaseInvar and R="inv_image finite_psubset (Graph.E \<circ> snd)"])
       apply (simp_all add: dinitzPhase_step dinitzPhase_final)
  apply (simp add: dinitzPhaseInvar_def NFlow_axioms) (* TODO *)
  by (simp_all add: dinitzPhaseInvar_def res_dist_increasing_flow_def NFlow_axioms Dual_Shortest_Path_Union_layeringI min_st_dist_bound)*)
context
  assumes RES_CON: "cf.connected s t"
begin
lemma dinitzPhase_final:
  fixes f' stl
    assumes DISCON: "\<not> Graph.connected stl s t"
      and INVAR: "dinitzPhaseInvar (f', stl)"
    shows "NFlow c s t f' \<and> min_dist_less s t cf (cf_of f')"
proof
  from INVAR show "NFlow c s t f'" unfolding dinitzPhaseInvar_def by blast
  then interpret f': NFlow c s t f' .

  have "f'.cf.connected s t \<Longrightarrow> cf.min_dist s t < f'.cf.min_dist s t"
  proof -
    assume "f'.cf.connected s t"
    with DISCON have "\<not> Dual_Shortest_Path_Union stl f'.cf s t"
      using Dual_Shortest_Path_Union.st_connected_iff by blast
    with INVAR show "cf.min_dist s t < f'.cf.min_dist s t"
      unfolding dinitzPhaseInvar_def using min_st_dist_bound linorder_not_le by fastforce
  qed
  with RES_CON show "min_dist_less s t cf f'.cf" unfolding min_dist_less_def by blast
qed

lemma dinitzPhase_correct:
  "dinitzPhase \<le> (spec f'. NFlow c s t f' \<and> min_dist_less s t cf (cf_of f'))"
  unfolding dinitzPhase_def
  apply (refine_vcg WHILET_rule[where I=dinitzPhaseInvar and R="inv_image finite_psubset (Graph.E \<circ> snd)"])
       apply (simp_all add: dinitzPhase_step dinitzPhase_final)
  by (simp add: dinitzPhaseInvar_def NFlow_axioms Dual_Shortest_Path_Union_layeringI min_st_dist_bound)
end

end

\<comment> \<open>Dinitz inner loop\<close>

subsection \<open>Dinitz algorithm\<close>
context Network
begin
definition dinitz :: "_ flow nres" where
  "dinitz \<equiv> do {
    f \<leftarrow> WHILE\<^sub>T
      (\<lambda>f. Graph.connected (residualGraph c f) s t)
      (\<lambda>f. NFlow.dinitzPhase c s t f)
      (\<lambda>_. 0);
    return f}"

definition dist_greater_rel :: "(_ graph) rel"
  where "dist_greater_rel \<equiv> {(c', c''). min_dist_less s t c'' c' \<and> Graph.V c' \<subseteq> V}"

lemma dist_greater_wf: "wf dist_greater_rel"
proof (rule wf_subset)
  let ?r = "less_than_bool <*lex*> (greater_bounded (card V))"
    and ?f = "\<lambda>c'. (Graph.connected c' s t, Graph.min_dist c' s t)"

  show "wf (inv_image ?r ?f)" by blast

  have "\<And>c'. \<lbrakk>Graph.connected c' s t; Graph.V c' \<subseteq> V\<rbrakk> \<Longrightarrow> Graph.min_dist c' s t < card V"
    by (metis Finite_Graph.intro Finite_Graph.min_dist_less_V Graph.distinct_nodes_in_V_if_connected(1) card_mono dual_order.strict_trans1 finite_V rev_finite_subset t_not_s)
  then show "dist_greater_rel \<subseteq> inv_image ?r ?f"
    unfolding dist_greater_rel_def min_dist_less_def greater_bounded_def by fastforce
qed

definition res_dist_rel :: "(_ flow) rel"
  where "res_dist_rel \<equiv> {(f', f). min_dist_less s t (cf_of f) (cf_of f')}"

lemma res_dist_rel_alt: "res_dist_rel = inv_image dist_greater_rel cf_of"
  unfolding res_dist_rel_def dist_greater_rel_def using cf_of_V_ss by auto

lemma res_dist_wf: "wf res_dist_rel"
  using res_dist_rel_alt dist_greater_wf by auto

theorem dinitz_correct: "dinitz \<le> (spec f. isMaxFlow f)"
  unfolding dinitz_def
  apply (refine_vcg WHILET_rule[where I="NFlow c s t" and R=res_dist_rel])
     apply (rule res_dist_wf)
    apply (simp add: NFlowI zero_is_flow)
   apply (simp add: NFlow.dinitzPhase_correct res_dist_rel_def)
  by (simp add: Graph.connected_def Graph.isSimplePath_def NFlow.axioms(1) NFlow.ford_fulkerson(1) NPreflow.isAugmentingPath_def)
end

end
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
      unfolding cleaning_def Graph.E_def apply simp_all by presburger+
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
qed (simp add: Graph.cleaning_def)

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
qed (simp add: Graph.induced_dual_layering_def)

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
locale ST_Layered_Flow = NFlow c s t f + Dual_Shortest_Path_Union stl cf s t + f': Flow stl s t f'
  for c s t f stl f'
begin
interpretation g': Irreducible_Graph stl
  unfolding Irreducible_Graph_def Irreducible_Graph_axioms_def
  using no_parallel_edge cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

abbreviation "stl' \<equiv> Graph.cleaning (g'.subtract_graph f') s t"
interpretation stl': Graph stl' .

interpretation aug_cf: Graph_Comparison stl' "cf_of (augment f')" .

interpretation f'_cont_cf: Pos_Contained_Graph f' cf
  by unfold_locales (metis NPreflow.resE_nonNegative NPreflow_axioms c'_sg_c_old f'.flow_pos_cont.cap_le order_trans)

interpretation cleaning: Dual_Path_Union stl' "g'.subtract_graph f'"
  using Dual_Path_Union_cleaningI .

find_theorems name:augment_alt
find_theorems "residualGraph ?c (NFlow.augment ?c ?f ?f') = Graph.subtract_skew_graph (residualGraph ?c ?f) ?f'"
find_theorems "Contained_Graph ?f' cf \<Longrightarrow> cf_of (augment ?f') = cf.subtract_skew_graph ?f'"

lemma aug_cf_alt: "cf_of (augment f') = cf.subtract_skew_graph f'"
  using augment_alt' f'_cont_cf.Contained_Graph_axioms .

definition new_edge_count :: "path \<Rightarrow> nat"
  where "new_edge_count p \<equiv> length (filter (\<lambda>e. e \<notin> cf.E) p)"

thm path_prelayered
thm g'.E_def
thm cf.E_def
thm aug_cf.E_def
thm stl'.E_def
find_theorems "layer ?v \<le> layer ?u + length ?p"

lemma aug_cf_new_edge_prelayered:
  "\<lbrakk>u \<in> V'; v \<in> V'; aug_cf.isPath u p v\<rbrakk> \<Longrightarrow> layer v + 2 * new_edge_count p \<le> layer u + length p"
proof (induction "new_edge_count p" arbitrary: u p v rule: less_induct)
  case less
  then show ?case
  proof (cases "new_edge_count p" rule: nat.exhaust_disc)
    case zero
    with less.prems have "cf.isPath u p v"
      unfolding new_edge_count_def Graph.isPath_alt
      by (metis empty_filter_conv length_0_conv subrelI)
    with zero less.prems show ?thesis using path_prelayered by simp
  next
    case Suc
    then obtain w\<^sub>1 w\<^sub>2 p\<^sub>1 p\<^sub>2 where P: "p = p\<^sub>1 @ (w\<^sub>1, w\<^sub>2) # p\<^sub>2" and W_NOT_CF: "(w\<^sub>1, w\<^sub>2) \<notin> cf.E"
      unfolding new_edge_count_def
      by (metis filter_False in_set_conv_decomp length_0_conv subrelI subsetD)
    then have P1_COUNT: "new_edge_count p\<^sub>1 < new_edge_count p"
      and P2_COUNT: "new_edge_count p\<^sub>2 < new_edge_count p"
      unfolding new_edge_count_def by auto

    from less.prems P have P1_PATH: "aug_cf.isPath u p\<^sub>1 w\<^sub>1" and P2_PATH: "aug_cf.isPath w\<^sub>2 p\<^sub>2 v"
      using aug_cf.isPath_append by auto

    from P less.prems have "(w\<^sub>1, w\<^sub>2) \<in> aug_cf.E" using aug_cf.isPath_append by simp
    with W_NOT_CF have "(w\<^sub>2, w\<^sub>1) \<in> Graph.E f'"
      unfolding aug_cf_alt using f'_cont_cf.subtract_skew_edges_sub by blast
    then have "(w\<^sub>2, w\<^sub>1) \<in> E'" using f'.flow_pos_cont.E_ss by blast
    then have "w\<^sub>1 \<in> V'" "w\<^sub>2 \<in> V'" and W_L: "layer w\<^sub>1 = Suc (layer w\<^sub>2)" unfolding g'.V_def by auto

    show ?thesis using W_NOT_CF
        less.hyps[OF P1_COUNT \<open>u \<in> V'\<close> \<open>w\<^sub>1 \<in> V'\<close> P1_PATH]
        less.hyps[OF P2_COUNT \<open>w\<^sub>2 \<in> V'\<close> \<open>v \<in> V'\<close> P2_PATH]
      by (simp add: W_L P new_edge_count_def)
  qed
qed

lemma st_min_dist_non_decreasing: "aug_cf.connected s t \<Longrightarrow> cf.min_dist s t \<le> aug_cf.min_dist s t"
proof (cases "Graph.isEmpty f'")
  case True
  then show ?thesis unfolding aug_cf_alt cf.subtract_skew_graph_def Graph.isEmpty_def by simp
next
  assume "aug_cf.connected s t"
  then obtain p where SP': "aug_cf.isShortestPath s p t" by (rule aug_cf.obtain_shortest_path)

  case False
  then have IN_V': "s \<in> V'" "t \<in> V'"
    using f'.flow_pos_cont.E_ss s_in_V_if_nonempty t_in_V_if_nonempty
    unfolding Graph.isEmpty_def by auto
  then have "cf.min_dist s t = layer t" using min_dist_transfer s_connected by simp
  also from SP' IN_V' have "layer t \<le> length p"
    using aug_cf.shortestPath_is_path aug_cf_new_edge_prelayered by fastforce
  finally show ?thesis using SP' aug_cf.isShortestPath_min_dist_def by simp
qed

lemma aug_cf_path_transfer:
  "\<lbrakk>aug_cf.isPath u p v; g'.isPath u p v\<rbrakk> \<Longrightarrow> Graph.isPath (g'.subtract_graph f') u p v"
proof (unfold Graph.isPath_alt, clarify)
  fix w\<^sub>1 w\<^sub>2
  assume "(w\<^sub>1, w\<^sub>2) \<in> set p" "set p \<subseteq> aug_cf.E" "set p \<subseteq> E'"
  then have assms: "(w\<^sub>1, w\<^sub>2) \<in> aug_cf.E" "(w\<^sub>1, w\<^sub>2) \<in> E'" by auto
  then have "(w\<^sub>2, w\<^sub>1) \<notin> E'" using no_parallel_edge by blast
  then have "f' (w\<^sub>2, w\<^sub>1) = 0"
    using Graph.zero_cap_simp f'.flow_pos_cont.E_ss by blast
  with assms show "(w\<^sub>1, w\<^sub>2) \<in> Graph.E (g'.subtract_graph f')"
    unfolding Graph.E_def aug_cf_alt g'.subtract_graph_def cf.subtract_skew_graph_def
    by simp (metis cap_compatible cap_nonzero)
qed

lemma cleaning_maintains_bounded_union:
  "Bounded_Dual_Shortest_Path_Union stl' (cf_of (augment f')) s t (cf.min_dist s t)"
proof (cases "Graph.isEmpty f'")
  case True
  then have "(g'.subtract_graph f') = stl"
    unfolding Graph.isEmpty_def g'.subtract_graph_def by simp
  then have "stl' = stl"
    unfolding Graph.cleaning_def using g'.V_def g'.zero_cap_simp by fastforce
  moreover from True have "cf_of (augment f') = cf"
    unfolding Graph.isEmpty_def aug_cf_alt cf.subtract_skew_graph_def by simp
  moreover note Dual_Shortest_Path_Union_axioms
  ultimately show ?thesis  by (simp add: min_st_dist_bound)
next
  case False
  then have ST_IN_V': "s \<in> V'" "t \<in> V'"
    using f'.flow_pos_cont.E_ss s_in_V_if_nonempty t_in_V_if_nonempty
    unfolding Graph.isEmpty_def by auto

  (* TODO make SUB an interpretation *)


  have "Subgraph stl' (g'.subtract_graph f')" by intro_locales
  also have SUB: "Subgraph ... (cf_of (augment f'))" unfolding aug_cf_alt
    using irreducible_contained_skew_subtract f'.flow_pos_cont.Contained_Graph_axioms g'.Irreducible_Graph_axioms .
  finally interpret Capacity_Compatible stl' "cf_of (augment f')"
    unfolding Subgraph_def by blast
  show ?thesis
  proof (unfold_locales, intro pair_set_eqI)
    (*show "aug_cf.E' = \<Union> {set p |p. aug_cf.isShortestPath s p t \<and> length p \<le> cf.min_dist s t}"*)
    fix u v
    assume "(u, v) \<in> stl'.E"
    then obtain p where "Graph.isPath (g'.subtract_graph f') s p t" "(u, v) \<in> set p"
      using cleaning.dual_path_union by blast
    with SUB have "aug_cf.isPath s p t"
      using Subgraph_def Subset_Graph.sub_path by blast
    moreover have "length p = cf.min_dist s t"
    proof -
      interpret f'': Contained_Graph "g'.subtract_graph f'" stl
        using f'.flow_pos_cont.subtract_contained .
      from \<open>Graph.isPath (g'.subtract_graph f') s p t\<close> have "g'.isPath s p t"
        unfolding Graph.isPath_alt using f''.E_ss by blast
      then show ?thesis using cf.isShortestPath_min_dist_def (* using shortest_path_transfer by presburger *)
        by (metis Graph.connected_def g'.isShortestPath_min_dist_def insert_iff min_ST_dist_transfer path_is_shortest st_connected_iff)
    qed
    moreover from \<open>aug_cf.isPath s p t\<close> have "cf.min_dist s t \<le> aug_cf.min_dist s t"
      using st_min_dist_non_decreasing aug_cf.connected_def by blast
    moreover note \<open>(u, v) \<in> set p\<close>
    ultimately show "(u, v) \<in> \<Union> {set p |p. isBoundedShortestPath (cf.min_dist s t) (cf_of (augment f')) s p t}"
      unfolding isBoundedShortestPath_def aug_cf.isShortestPath_min_dist_def
      using aug_cf.isPath_distD aug_cf.min_dist_minD by fastforce
  next
    fix u v
    assume "(u, v) \<in> \<Union> {set p |p. isBoundedShortestPath (cf.min_dist s t) (cf_of (augment f')) s p t}"
    then obtain p where SP': "aug_cf.isShortestPath s p t" "length p \<le> cf.min_dist s t"
      and UV_IN_P: "(u, v) \<in> set p" unfolding isBoundedShortestPath_def by blast
    with ST_IN_V' have "layer t + 2 * new_edge_count p \<le> layer s + cf.min_dist s t"
      using aug_cf_new_edge_prelayered aug_cf.shortestPath_is_path by fastforce
    with ST_IN_V' have "new_edge_count p = 0" using min_dist_transfer st_connected by simp
    with SP' have "cf.isShortestPath s p t"
      unfolding new_edge_count_def Graph.isShortestPath_min_dist_def
      by (metis aug_cf.connected_def Graph.isPath_alt empty_filter_conv length_0_conv nle_le st_min_dist_non_decreasing subset_code(1)) (* TODO fix *)
    then have "g'.isPath s p t" using ST_IN_V' by (simp add: ST_path_remains path_kind)
    with SP' have "Graph.isPath (g'.subtract_graph f') s p t"
      using aug_cf_path_transfer aug_cf.shortestPath_is_path by blast
    then have "Graph.isPath stl' s p t"
      using cleaning.dual_path_union unfolding Graph.isPath_alt by blast
    with UV_IN_P show "(u, v) \<in> Graph.E stl'"
      using Graph.isPath_edgeset by blast
  qed
qed

lemma augment_NFlow: "NFlow c s t (augment f')"
proof (intro NFlowI)
  show "Network c s t" using Network_axioms .
  have "Flow cf s t f'"
    using transfer_flow[OF f'.Flow_axioms cf.Nonnegative_Graph_axioms cf.Finite_Graph_axioms] .
  then show "Flow c s t (augment f')" using augment_flow_presv by blast
qed

lemma E_pss_if_saturated_edge:
  "\<exists>u v. stl (u, v) = f' (u, v) \<and> f' (u, v) > 0 \<Longrightarrow> aug_cf.E' \<subset> E'"
proof
  assume "\<exists>u v. stl (u, v) = f' (u, v) \<and> f' (u, v) > 0"
  then obtain u v where "stl (u, v) = f' (u, v)" "f' (u, v) > 0" by blast
  then have "(u, v) \<in> E'" "(u, v) \<notin> aug_cf.E'"
    unfolding Graph.E_def g'.subtract_graph_def Graph.cleaning_def by auto
  then show "aug_cf.E' \<noteq> E'" by blast

  show "aug_cf.E' \<subseteq> E'"
  proof -
    interpret f'': Contained_Graph "g'.subtract_graph f'" stl
      using f'.flow_pos_cont.subtract_contained .
    show ?thesis using cleaning.E_ss f''.E_ss by blast
  qed
qed
end

\<comment> \<open>Properties when removing a flow from the ST_Layering\<close>

subsection \<open>Dinitz inner loop\<close>
context NFlow
begin
(*
definition dinitz_phase :: "_ flow nres" where
  "dinitz_phase \<equiv> do {
    if cf.connected s t
      then do {
        let stl = induced_st_layering cf s t;
        (f', _) \<leftarrow> WHILE\<^sub>T
          (\<lambda>(_, stl). Graph.connected stl s t)
          (\<lambda>(f', stl). do {
            p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
            let stl = cleaning s t (Graph.subtract_path stl p);
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl)})
          (f, stl);
        RETURN f'}
      else RETURN f}"
*)
definition dinitz_phase :: "_ flow nres" where
  "dinitz_phase \<equiv> do {
    let stl = Graph.induced_dual_layering cf s t;
    (f', _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, stl). Graph.connected stl s t)
      (\<lambda>(f', stl). do {
        p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
        let stl = Graph.cleaning (Graph.subtract_path stl p) s t;
        let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
        RETURN (f', stl)})
      (f, stl);
    RETURN f'}"
thm Graph.subtract_path_alt

definition dinitzPhaseInvar :: "(_ flow \<times> _ graph) \<Rightarrow> bool" where
  "dinitzPhaseInvar \<equiv> \<lambda>(f', stl).
    NFlow c s t f'
    \<and> Bounded_Dual_Shortest_Path_Union stl (cf_of f') s t (cf.min_dist s t)
    \<and> (Graph.connected (cf_of f') s t \<longrightarrow> (cf.min_dist s t) \<le> (Graph.min_dist (cf_of f') s t))"

(* TODO use this in phase step *)
lemma dual_spu_if_invar_and_path:
  assumes INVAR: "dinitzPhaseInvar (f', stl)"
    and PATH: "Graph.isPath stl s p t"
  shows "Dual_Shortest_Path_Union stl (cf_of f') s t"
proof -
  from INVAR interpret f': NFlow c s t f' unfolding dinitzPhaseInvar_def by blast
  find_theorems "length ?p \<le> _" Graph.isPath
  have BOUND_EQ: "cf.min_dist s t = f'.cf.min_dist s t"
  proof -
    from INVAR interpret Bounded_Dual_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
      unfolding dinitzPhaseInvar_def by simp
    show ?thesis
    proof (intro antisym)
      from PATH INVAR show "cf.min_dist s t \<le> f'.cf.min_dist s t"
        unfolding dinitzPhaseInvar_def Graph.connected_def
        using sub_path by blast

      from PATH have "f'.cf.min_dist s t \<le> g'.min_dist s t"
        using isPath.connected sub_min_dist_geq by blast
      also have "... = length p" using PATH path_ascends_layer by force
      also have "... \<le> cf.min_dist s t" using PATH path_length_bounded by simp
      finally show "f'.cf.min_dist s t \<le> cf.min_dist s t" .
    qed
  qed
  with INVAR show "Dual_Shortest_Path_Union stl (f'.cf) s t"
    unfolding dinitzPhaseInvar_def using min_st_dist_bound by fastforce
qed

lemma dinitz_phase_step:
  fixes f' stl
  assumes PATH: "Graph.isPath stl s p t"
      and INVAR: "dinitzPhaseInvar (f', stl)"
  defines "aug_f' \<equiv> NFlow.augment c f' (NPreflow.augmentingFlow c f' p)"
      and "stl' \<equiv> Graph.cleaning (Graph.subtract_path stl p) s t"
    shows "dinitzPhaseInvar (aug_f', stl') \<and> Graph.E stl' \<subset> Graph.E stl \<and> finite (Graph.E stl)"
proof (intro conjI)
  from INVAR interpret f': NFlow c s t f' unfolding dinitzPhaseInvar_def by blast

  have BOUND_EQ: "cf.min_dist s t = f'.cf.min_dist s t"
  proof -
    from INVAR interpret Bounded_Dual_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
      unfolding dinitzPhaseInvar_def by simp
    show ?thesis
    proof (intro antisym)
      from PATH INVAR show "cf.min_dist s t \<le> f'.cf.min_dist s t"
        unfolding dinitzPhaseInvar_def Graph.connected_def
        using sub_path by blast

      from PATH have "f'.cf.min_dist s t \<le> g'.min_dist s t"
        using isPath.connected sub_min_dist_geq by blast
      also have "... = length p" using PATH path_ascends_layer by force
      also have "... \<le> cf.min_dist s t" using PATH path_length_bounded by simp
      finally show "f'.cf.min_dist s t \<le> cf.min_dist s t" .
    qed
  qed
  with INVAR interpret Dual_Shortest_Path_Union stl f'.cf s t
    unfolding dinitzPhaseInvar_def using min_st_dist_bound by fastforce

  interpret g': Nonnegative_Graph stl
    using f'.cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

  have INDUCED_EQ: "f'.cf.path_induced_graph p = g'.path_induced_graph p"
    using PATH f'.cf.Nonnegative_Graph_axioms g'.isPath_alt path_induced_graph_eq by simp

  (* TODO the following is just a consequence of f'.augFlow_resFlow and Subgraphing, extract *)
  thm f'.augFlow_resFlow

  interpret st_layered_flow.f': Flow stl s t "f'.augmentingFlow p"
  proof (intro Pos_Contained_Graph.conservation_FlowI)
    from INDUCED_EQ show "Pos_Contained_Graph (f'.augmentingFlow p) stl"
      unfolding f'.augmentingFlow_alt using g'.path_induced_graph_pos_contained by simp

    show "\<forall>v\<in>V' - {s, t}. sum (f'.augmentingFlow p) (g'.incoming v) = sum (f'.augmentingFlow p) (g'.outgoing v)"
    proof
      fix v
      assume "v \<in> V' - {s, t}"
      then have "v \<in> V - {s, t}" using V_ss by auto
      let ?aug_sum = "sum (f'.augmentingFlow p)"

      have "?aug_sum (g'.incoming v) = ?aug_sum (g'.incoming v) + ?aug_sum (f'.cf.incoming v - E')"
        using PATH unfolding f'.augmentingFlow_alt f'.cf.path_induced_graph_def g'.isPath_alt
        by (fastforce intro: sum.neutral)
      also have "... = ?aug_sum (g'.incoming v) + ?aug_sum (f'.cf.incoming v - (g'.incoming v))"
        unfolding Graph.incoming_def by (auto intro: arg_cong[where f="?aug_sum"])
      also have "... = ?aug_sum (f'.cf.incoming v \<inter> g'.incoming v) + ?aug_sum (f'.cf.incoming v - (g'.incoming v))"
        using incoming_ss by (auto intro!: arg_cong[where f="?aug_sum"])
      also have "... = ?aug_sum (f'.cf.incoming v)"
        using sum.Int_Diff by (metis f'.cf.incoming_edges cfE_of_finite rev_finite_subset)
      also from \<open>v \<in> V - {s, t}\<close> have "... = ?aug_sum (f'.cf.outgoing v)"
        using Flow.conservation_const f'.augFlow_resFlow PATH
        using f'.cf.shortestPath_is_simple f'.isAugmentingPath_def f'.resV_netV shortest_path_transfer by blast
        (* TODO prettify *)
      also have "... = ?aug_sum (f'.cf.outgoing v \<inter> g'.outgoing v) + ?aug_sum (f'.cf.outgoing v - (g'.outgoing v))"
        using sum.Int_Diff by (metis f'.cf.outgoing_edges cfE_of_finite rev_finite_subset)
      also have "... = ?aug_sum (g'.outgoing v) + ?aug_sum (f'.cf.outgoing v - (g'.outgoing v))"
        using outgoing_ss by (auto intro!: arg_cong[where f="?aug_sum"])
      also have "... = ?aug_sum (g'.outgoing v) + ?aug_sum (f'.cf.outgoing v - E')"
        unfolding Graph.outgoing_def by (auto intro: arg_cong[where f="?aug_sum"])
      also have "... = ?aug_sum (g'.outgoing v)"
        using PATH unfolding f'.augmentingFlow_alt f'.cf.path_induced_graph_def g'.isPath_alt
        by (fastforce intro: sum.neutral)

      finally show "sum (f'.augmentingFlow p) (g'.incoming v) = sum (f'.augmentingFlow p) (g'.outgoing v)" .
    qed
  qed
  interpret st_layered_flow: ST_Layered_Flow c s t f' stl "f'.augmentingFlow p" by intro_locales

  have "NFlow c s t aug_f'" unfolding aug_f'_def using st_layered_flow.augment_NFlow .
  moreover have "Bounded_Dual_Shortest_Path_Union stl' (cf_of aug_f') s t (cf.min_dist s t)"
    using st_layered_flow.cleaning_maintains_bounded_union INDUCED_EQ BOUND_EQ
    unfolding g'.subtract_path_alt f'.augmentingFlow_alt aug_f'_def stl'_def by simp
  moreover have "(Graph.connected (cf_of aug_f') s t \<longrightarrow> cf.min_dist s t \<le> Graph.min_dist (cf_of aug_f') s t)"
    using st_layered_flow.st_min_dist_non_decreasing BOUND_EQ unfolding aug_f'_def by simp
  ultimately show "dinitzPhaseInvar (aug_f', stl')"
    unfolding dinitzPhaseInvar_def by simp

  (* TODO cleanup this horrible mess *)
  have "stl (arg_min_list stl p) = f'.augmentingFlow p (arg_min_list stl p)" unfolding f'.augmentingFlow_def f'.resCap_alt
    by (smt (verit, ccfv_threshold) Graph.isPath.simps(1) PATH arg_min_list_in case_prod_conv f'.cf.Nonnegative_Graph_axioms f'.cf.pathCap_def f'.resCap_alt f'.resCap_def f_arg_min_list_f g'.isPath_alt g'.pathCap_alt pathCap_eq surj_pair t_not_s)
  moreover have "0 < f'.augmentingFlow p (arg_min_list stl p)" unfolding f'.augmentingFlow_def f'.resCap_alt
    by (metis Graph.isPath.simps(1) Nonnegative_Graph.nonempty_path_cap_positive PATH calculation f'.augmentingFlow_def f'.resCap_alt f_arg_min_list_f g'.Nonnegative_Graph_axioms g'.isPath_alt g'.pathCap_alt t_not_s)
  ultimately show "Graph.E stl' \<subset> E'"
    unfolding stl'_def g'.subtract_path_alt INDUCED_EQ[symmetric] f'.augmentingFlow_alt[symmetric]
    using st_layered_flow.E_pss_if_saturated_edge by (metis surj_pair)

  show "finite E'" using E_ss finite_subset by auto
qed

(* TODO introduce notion of blocking flow or reuse from Push Relabel, then connect this concept *)
definition res_dist_increasing_flow
  where "res_dist_increasing_flow f' \<equiv>
    NFlow c s t f' \<and> (Graph.connected (cf_of f') s t \<longrightarrow> cf.min_dist s t < Graph.min_dist (cf_of f') s t)"

lemma dinitz_phase_final:
  fixes f' stl
    assumes DISCON: "\<not> Graph.connected stl s t"
      and INVAR: "dinitzPhaseInvar (f', stl)"
    shows "res_dist_increasing_flow f'"
  unfolding res_dist_increasing_flow_def
proof
  from INVAR interpret f': NFlow c s t f' unfolding dinitzPhaseInvar_def by blast
  show "NFlow c s t f'" using f'.NFlow_axioms .

  from INVAR interpret Bounded_Dual_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
    unfolding dinitzPhaseInvar_def by blast
  from DISCON show "f'.cf.connected s t \<longrightarrow> cf.min_dist s t < f'.cf.min_dist s t"
    by (metis Bounded_Dual_Shortest_Path_Union_axioms Dual_Shortest_Path_Union.st_connected_iff le_eq_less_or_eq linorder_neqE_nat min_st_dist_bound)
qed

lemma dinitz_phase_correct:
  "dinitz_phase \<le> SPEC (\<lambda>f'. res_dist_increasing_flow f')"
  unfolding dinitz_phase_def
  apply (refine_vcg WHILET_rule[where I=dinitzPhaseInvar and R="inv_image finite_psubset (Graph.E \<circ> snd)"])
       apply (simp_all add: dinitz_phase_step dinitz_phase_final)
  apply (simp add: dinitzPhaseInvar_def NFlow_axioms) (* TODO *)
  by (simp_all add: dinitzPhaseInvar_def res_dist_increasing_flow_def NFlow_axioms Dual_Shortest_Path_Union_layeringI min_st_dist_bound)
end

\<comment> \<open>Dinitz inner loop\<close>

subsection \<open>Dinitz algorithm\<close>
context Network
begin
definition dinitz :: "_ flow nres" where
  "dinitz \<equiv> do {
    f \<leftarrow> WHILE\<^sub>T
      (\<lambda>f. Graph.connected (residualGraph c f) s t)
      (\<lambda>f. NFlow.dinitz_phase c s t f)
      (\<lambda>_. 0);
    RETURN f}"

(* TODO check if something like this already exists *)
definition res_dist_rel :: "(_ flow) rel"
  where "res_dist_rel \<equiv> {(f', f). Graph.connected (cf_of f) s t
    \<and> (\<not> Graph.connected (cf_of f') s t \<or> Graph.min_dist (cf_of f) s t < Graph.min_dist (cf_of f') s t)}"

lemma res_dist_wf: "wf res_dist_rel"
proof (rule wf_subset)
  let ?r = "less_than_bool <*lex*> (greater_bounded (card V))"
    and ?f = "\<lambda>f. (Graph.connected (cf_of f) s t, Graph.min_dist (cf_of f) s t)"

  show "wf (inv_image ?r ?f)" by blast

  have "\<And>f. Graph.connected (cf_of f) s t \<Longrightarrow> Graph.min_dist (cf_of f) s t < card (Graph.V (cf_of f))"
    by (simp add: Finite_Graph.min_dist_less_V Graph.Finite_Graph_EI Graph.distinct_nodes_in_V_if_connected(1))
  moreover have "\<And>f. Graph.V (cf_of f) \<subseteq> V"
    unfolding residualGraph_def Graph.V_def Graph.E_def by auto
  ultimately have "\<And>f. Graph.connected (cf_of f) s t \<Longrightarrow> Graph.min_dist (cf_of f) s t < card V"
    by (meson card_mono dual_order.strict_trans1 finite_V)
  then show "res_dist_rel \<subseteq> inv_image ?r ?f"
    by (fastforce simp: res_dist_rel_def greater_bounded_def)
qed

theorem dinitz_correct: "dinitz \<le> SPEC (\<lambda>f. isMaxFlow f)"
  unfolding dinitz_def
  apply (refine_vcg WHILET_rule[where I="NFlow c s t" and R=res_dist_rel])
     apply (rule res_dist_wf)
    apply (simp add: NFlowI Network_axioms zero_is_flow)
   apply (fastforce intro: NFlow.dinitz_phase_correct[THEN SPEC_cons_rule] simp: NFlow.res_dist_increasing_flow_def res_dist_rel_def)
  by (simp add: Graph.connected_def Graph.isSimplePath_def NFlow.axioms(1) NFlow.ford_fulkerson(1) NPreflow.isAugmentingPath_def)
end


end
theory Dinic_Algo
  imports Refinement NetworkUtils
begin

subsection \<open>Properties when removing a flow from the ST_Layering\<close>
locale ST_Layered_Flow = NFlow c s t f + ST_Shortest_Path_Union stl cf s t + f': Flow stl s t f'
  for c s t f stl f'
begin
interpretation g': Irreducible_Graph stl
  unfolding Irreducible_Graph_def Irreducible_Graph_axioms_def
  using no_parallel_edge cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

interpretation aug_cf: GraphComparison "cleaning (g'.subtract_graph f') s t" "cf_of (augment f')" .

interpretation f'_cont_cf: Pos_Contained_Graph f' cf
  by unfold_locales (metis NPreflow.resE_nonNegative NPreflow_axioms c'_sg_c_old f'.flow_pos_cont.cap_le order_trans)

lemma aug_cf_alt: "cf_of (augment f') = cf.subtract_skew_graph f'"
  using augment_alt f'_cont_cf.Contained_Graph_axioms .

definition new_edge_count :: "path \<Rightarrow> nat"
  where "new_edge_count p \<equiv> length (filter (\<lambda>e. e \<notin> cf.E) p)"

lemma aug_cf_new_edge_layered:
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
    then have "(w\<^sub>2, w\<^sub>1) \<in> E'" using f'.flow_pos_cont.edges_ss by blast
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
    using f'.flow_pos_cont.edges_ss s_in_V_if_nonempty t_in_V_if_nonempty
    unfolding Graph.isEmpty_def by auto
  then have "cf.min_dist s t = layer t" using min_dist_transfer s_connected by simp
  also from SP' IN_V' have "layer t \<le> length p"
    using aug_cf.shortestPath_is_path aug_cf_new_edge_layered by fastforce
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
    using Graph.zero_cap_simp f'.flow_pos_cont.edges_ss by blast
  with assms show "(w\<^sub>1, w\<^sub>2) \<in> Graph.E (g'.subtract_graph f')"
    unfolding Graph.E_def aug_cf_alt g'.subtract_graph_def cf.subtract_skew_graph_def
    by simp (metis cap_compatible cap_nonzero)
qed

lemma cleaning_maintains_bounded_union:
  "Bounded_ST_Shortest_Path_Union (cleaning (g'.subtract_graph f') s t) (cf_of (augment f')) s t (cf.min_dist s t)"
proof (cases "Graph.isEmpty f'")
  case True
  then have "(g'.subtract_graph f') = stl"
    unfolding Graph.isEmpty_def g'.subtract_graph_def by simp
  then have "(cleaning (g'.subtract_graph f') s t) = stl"
    unfolding cleaning_def using g'.V_def g'.zero_cap_simp by fastforce
  moreover from True have "cf_of (augment f') = cf"
    unfolding Graph.isEmpty_def aug_cf_alt cf.subtract_skew_graph_def by simp
  moreover note ST_Shortest_Path_Union_axioms
  ultimately show ?thesis  by (simp add: min_st_dist_bound)
next
  case False
  then have ST_IN_V': "s \<in> V'" "t \<in> V'"
    using f'.flow_pos_cont.edges_ss s_in_V_if_nonempty t_in_V_if_nonempty
    unfolding Graph.isEmpty_def by auto
  
  show ?thesis unfolding Bounded_ST_Shortest_Path_Union_def Bounded_ST_Shortest_Path_Union_axioms_def
  proof
    have "Subgraph (cleaning (g'.subtract_graph f') s t) (g'.subtract_graph f')"
      using cleaning_rp_Subgraph right_pass_Subgraph subgraph.order.trans by blast
    also have SUB: "Subgraph ... (cf_of (augment f'))" unfolding aug_cf_alt
      using irreducible_contained_skew_subtract f'.flow_pos_cont.Contained_Graph_axioms g'.Irreducible_Graph_axioms .
    finally show "CapacityCompatibleGraphs (cleaning (g'.subtract_graph f') s t) (cf_of (augment f'))"
      unfolding Subgraph_def by blast
  
    show "aug_cf.E' = \<Union> {set p |p. aug_cf.isShortestPath s p t \<and> length p \<le> cf.min_dist s t}"
    proof (intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> aug_cf.E'"
      then obtain p where "Graph.isPath (g'.subtract_graph f') s p t" "(u, v) \<in> set p"
        using ST_Graph.cleaning_edge_set by blast
      with SUB have "aug_cf.isPath s p t"
        using Subgraph.sg_paths_are_base_paths by blast
      moreover have "length p = cf.min_dist s t"
      proof -
        from \<open>Graph.isPath (g'.subtract_graph f') s p t\<close> have "g'.isPath s p t"
          unfolding Graph.isPath_alt
          using Contained_Graph.edges_ss f'.flow_pos_cont.subtract_contained by blast
        then show ?thesis using cf.isShortestPath_min_dist_def shortest_path_transfer by presburger
      qed
      moreover from \<open>aug_cf.isPath s p t\<close> have "cf.min_dist s t \<le> aug_cf.min_dist s t"
        using st_min_dist_non_decreasing aug_cf.connected_def by blast
      moreover note \<open>(u, v) \<in> set p\<close>
      ultimately show "(u, v) \<in> \<Union> {set p |p. aug_cf.isShortestPath s p t \<and> length p \<le> cf.min_dist s t}"
        unfolding aug_cf.isShortestPath_min_dist_def
        using aug_cf.isPath_distD aug_cf.min_dist_minD by fastforce
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. aug_cf.isShortestPath s p t \<and> length p \<le> cf.min_dist s t}"
      then obtain p where SP': "aug_cf.isShortestPath s p t" "length p \<le> cf.min_dist s t"
        and UV_IN_P: "(u, v) \<in> set p" by blast
      with ST_IN_V' have "layer t + 2 * new_edge_count p \<le> layer s + cf.min_dist s t"
        using aug_cf_new_edge_layered aug_cf.shortestPath_is_path by fastforce
      with ST_IN_V' have "new_edge_count p = 0" using min_dist_transfer st_connected by simp
      with SP' have "cf.isShortestPath s p t"
        unfolding new_edge_count_def Graph.isShortestPath_min_dist_def
        by (metis aug_cf.connected_def Graph.isPath_alt empty_filter_conv length_0_conv nle_le st_min_dist_non_decreasing subset_code(1)) (* TODO fix *)
      then have "g'.isPath s p t" using ST_IN_V' shortest_s_path_remains_path by blast
      with SP' have "Graph.isPath (g'.subtract_graph f') s p t"
        using aug_cf_path_transfer aug_cf.shortestPath_is_path by blast
      then have "Graph.isPath (cleaning (g'.subtract_graph f') s t) s p t"
        using ST_Graph.cleaning_edge_set unfolding Graph.isPath_alt by blast
      with UV_IN_P show "(u, v) \<in> Graph.E (cleaning (g'.subtract_graph f') s t)"
        using Graph.isPath_edgeset by blast
    qed
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
    unfolding Graph.E_def g'.subtract_graph_def cleaning_def by auto
  then show "aug_cf.E' \<noteq> E'" by blast

  show "aug_cf.E' \<subseteq> E'"
    by (meson Contained_Graph.edges_ss Subgraph.E'_ss cleaning_rp_Subgraph f'.flow_pos_cont.subtract_contained right_pass_Subgraph subset_trans)
qed
end

\<comment> \<open>Properties when removing a flow from the ST_Layering\<close>

subsection \<open>Dinic inner loop\<close>
context NFlow
begin
definition dinic_inner_partial :: "_ flow nres" where
  "dinic_inner_partial \<equiv> do {
    if cf.connected s t
      then do {
        let stl = induced_st_layering cf s t;
        (f', _) \<leftarrow> WHILE
          (\<lambda>(_, stl). Graph.connected stl s t)
          (\<lambda>(f', stl). do {
            p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
            let stl = cleaning (Nonnegative_Graph.subtract_path stl p) s t;
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl)})
          (f, stl);
        RETURN f'}
      else RETURN f}"

definition dinic_inner_partial_invar :: "(_ flow \<times> _ graph) \<Rightarrow> bool" where
  "dinic_inner_partial_invar \<equiv> \<lambda>(f', stl). NFlow c s t f'
    \<and> Bounded_ST_Shortest_Path_Union stl (cf_of f') s t (cf.min_dist s t)
    \<and> (Graph.connected (cf_of f') s t \<longrightarrow> (cf.min_dist s t) \<le> (Graph.min_dist (cf_of f') s t))"

lemma dinic_inner_partial_step:
  fixes f' stl
  assumes PATH: "Graph.isPath stl s p t"
      and INVAR: "dinic_inner_partial_invar (f', stl)"
    shows "dinic_inner_partial_invar (NFlow.augment c f' (NPreflow.augmentingFlow c f' p), cleaning (Nonnegative_Graph.subtract_path stl p) s t)"
      (is "dinic_inner_partial_invar (?aug_f', ?stl')")
proof -
  from INVAR interpret f': NFlow c s t f' unfolding dinic_inner_partial_invar_def by blast

  have BOUND_EQ: "cf.min_dist s t = f'.cf.min_dist s t"
  proof -
    from INVAR interpret Bounded_ST_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
      unfolding dinic_inner_partial_invar_def by simp
    show ?thesis
    proof (intro antisym)
      from PATH INVAR show "cf.min_dist s t \<le> f'.cf.min_dist s t"
        unfolding dinic_inner_partial_invar_def Graph.connected_def
        using sg_paths_are_base_paths by blast
      from PATH show "f'.cf.min_dist s t \<le> cf.min_dist s t"
      using f'.cf.isShortestPath_min_dist_def path_length_bounded shortest_path_transfer by simp
    qed
  qed
  with INVAR interpret ST_Shortest_Path_Union stl f'.cf s t
    unfolding dinic_inner_partial_invar_def using min_st_dist_bound by fastforce

  interpret g': Nonnegative_Graph stl
    using f'.cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

  have INDUCED_EQ: "f'.cf.path_induced_graph p = g'.path_induced_graph p"
    using PATH f'.cf.Nonnegative_Graph_axioms g'.isPath_alt path_induced_graph_eq by simp

  (* TODO extract this, using augFlow_resFlow *)
  have "Flow stl s t (f'.augmentingFlow p)"
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
  then interpret st_layered_flow: ST_Layered_Flow c s t f' stl "f'.augmentingFlow p"
    using f'.NFlow_axioms ST_Shortest_Path_Union_axioms by (intro ST_Layered_Flow.intro)

  have "NFlow c s t ?aug_f'" using st_layered_flow.augment_NFlow .
  moreover have "Bounded_ST_Shortest_Path_Union ?stl' (cf_of ?aug_f') s t (cf.min_dist s t)"
    using st_layered_flow.cleaning_maintains_bounded_union INDUCED_EQ BOUND_EQ
    unfolding g'.subtract_path_alt f'.augmentingFlow_alt by simp
  moreover have "(Graph.connected (cf_of ?aug_f') s t \<longrightarrow> cf.min_dist s t \<le> Graph.min_dist (cf_of ?aug_f') s t)"
    using st_layered_flow.st_min_dist_non_decreasing BOUND_EQ by simp
  ultimately show "dinic_inner_partial_invar (?aug_f', ?stl')"
    unfolding dinic_inner_partial_invar_def by simp

  thm st_layered_flow.E_pss_if_saturated_edge
  (* TODO termination *)
qed

lemma dinic_inner_partial_final:
  fixes f' stl
    assumes DISCON: "\<not> Graph.connected stl s t"
      and INVAR: "dinic_inner_partial_invar (f', stl)"
    shows "NFlow c s t f' \<and> (Graph.connected (cf_of f') s t \<longrightarrow> cf.min_dist s t < Graph.min_dist (cf_of f') s t)"
proof
  from INVAR interpret f': NFlow c s t f' unfolding dinic_inner_partial_invar_def by blast
  show "NFlow c s t f'" using f'.NFlow_axioms .

  from INVAR interpret Bounded_ST_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
    unfolding dinic_inner_partial_invar_def by blast
  from DISCON show "f'.cf.connected s t \<longrightarrow> cf.min_dist s t < f'.cf.min_dist s t"
    by (metis Bounded_ST_Shortest_Path_Union_axioms ST_Shortest_Path_Union.st_connected_iff le_eq_less_or_eq linorder_neqE_nat min_st_dist_bound)
qed

lemma dinic_inner_partial_correct:
  "dinic_inner_partial \<le> SPEC (\<lambda>f'. NFlow c s t f'\<and> (Graph.connected (cf_of f') s t \<longrightarrow> cf.min_dist s t < Graph.min_dist (cf_of f') s t))"
  unfolding dinic_inner_partial_def
  apply (refine_vcg WHILE_rule[where I=dinic_inner_partial_invar])
       apply (simp_all add: dinic_inner_partial_step dinic_inner_partial_final)
  by (simp_all add: dinic_inner_partial_invar_def NFlow_axioms induced_st_shortest_path_union min_st_dist_bound)

text \<open>Total correctness\<close>
definition dinitz_phase :: "_ flow nres" where
  "dinitz_phase \<equiv> do {
    if cf.connected s t
      then do {
        let stl = induced_st_layering cf s t;
        (f', _) \<leftarrow> WHILE\<^sub>T
          (\<lambda>(_, stl). Graph.connected stl s t)
          (\<lambda>(f', stl). do {
            p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
            let stl = cleaning (Nonnegative_Graph.subtract_path stl p) s t;
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl)})
          (f, stl);
        RETURN f'}
      else RETURN f}"

definition dinitz_phase_invar :: "(_ flow \<times> _ graph) \<Rightarrow> bool" where
  "dinitz_phase_invar \<equiv> \<lambda>(f', stl).
    NFlow c s t f'
    \<and> Bounded_ST_Shortest_Path_Union stl (cf_of f') s t (cf.min_dist s t)
    \<and> (Graph.connected (cf_of f') s t \<longrightarrow> (cf.min_dist s t) \<le> (Graph.min_dist (cf_of f') s t))"

lemma dinitz_phase_step:
  fixes f' stl
  assumes PATH: "Graph.isPath stl s p t"
      and INVAR: "dinitz_phase_invar (f', stl)"
  defines "aug_f' \<equiv> NFlow.augment c f' (NPreflow.augmentingFlow c f' p)"
      and "stl' \<equiv> cleaning (Nonnegative_Graph.subtract_path stl p) s t"
    shows "dinitz_phase_invar (aug_f', stl') \<and> Graph.E stl' \<subset> Graph.E stl \<and> finite (Graph.E stl)"
proof (intro conjI)
  from INVAR interpret f': NFlow c s t f' unfolding dinitz_phase_invar_def by blast

  have BOUND_EQ: "cf.min_dist s t = f'.cf.min_dist s t"
  proof -
    from INVAR interpret Bounded_ST_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
      unfolding dinitz_phase_invar_def by simp
    show ?thesis
    proof (intro antisym)
      from PATH INVAR show "cf.min_dist s t \<le> f'.cf.min_dist s t"
        unfolding dinitz_phase_invar_def Graph.connected_def
        using sg_paths_are_base_paths by blast
      from PATH show "f'.cf.min_dist s t \<le> cf.min_dist s t"
      using f'.cf.isShortestPath_min_dist_def path_length_bounded shortest_path_transfer by simp
    qed
  qed
  with INVAR interpret ST_Shortest_Path_Union stl f'.cf s t
    unfolding dinitz_phase_invar_def using min_st_dist_bound by fastforce

  interpret g': Nonnegative_Graph stl
    using f'.cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

  have INDUCED_EQ: "f'.cf.path_induced_graph p = g'.path_induced_graph p"
    using PATH f'.cf.Nonnegative_Graph_axioms g'.isPath_alt path_induced_graph_eq by simp

  (* TODO extract this, using augFlow_resFlow *)
  have "Flow stl s t (f'.augmentingFlow p)"
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
  then interpret st_layered_flow: ST_Layered_Flow c s t f' stl "f'.augmentingFlow p"
    using f'.NFlow_axioms ST_Shortest_Path_Union_axioms by (intro ST_Layered_Flow.intro)

  have "NFlow c s t aug_f'" unfolding aug_f'_def using st_layered_flow.augment_NFlow .
  moreover have "Bounded_ST_Shortest_Path_Union stl' (cf_of aug_f') s t (cf.min_dist s t)"
    using st_layered_flow.cleaning_maintains_bounded_union INDUCED_EQ BOUND_EQ
    unfolding g'.subtract_path_alt f'.augmentingFlow_alt aug_f'_def stl'_def by simp
  moreover have "(Graph.connected (cf_of aug_f') s t \<longrightarrow> cf.min_dist s t \<le> Graph.min_dist (cf_of aug_f') s t)"
    using st_layered_flow.st_min_dist_non_decreasing BOUND_EQ unfolding aug_f'_def by simp
  ultimately show "dinitz_phase_invar (aug_f', stl')"
    unfolding dinitz_phase_invar_def by simp

  thm st_layered_flow.E_pss_if_saturated_edge
  (* TODO termination *)
  show "Graph.E stl' \<subset> E'" sorry
  show "finite E'" sorry
qed

lemma dinitz_phase_final:
  fixes f' stl
    assumes DISCON: "\<not> Graph.connected stl s t"
      and INVAR: "dinitz_phase_invar (f', stl)"
    shows "NFlow c s t f' \<and> (Graph.connected (cf_of f') s t \<longrightarrow> cf.min_dist s t < Graph.min_dist (cf_of f') s t)"
proof
  from INVAR interpret f': NFlow c s t f' unfolding dinitz_phase_invar_def by blast
  show "NFlow c s t f'" using f'.NFlow_axioms .

  from INVAR interpret Bounded_ST_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
    unfolding dinitz_phase_invar_def by blast
  from DISCON show "f'.cf.connected s t \<longrightarrow> cf.min_dist s t < f'.cf.min_dist s t"
    by (metis Bounded_ST_Shortest_Path_Union_axioms ST_Shortest_Path_Union.st_connected_iff le_eq_less_or_eq linorder_neqE_nat min_st_dist_bound)
qed

lemma dinitz_phase_correct:
  "dinitz_phase \<le> SPEC (\<lambda>f'. NFlow c s t f'\<and> (Graph.connected (cf_of f') s t \<longrightarrow> cf.min_dist s t < Graph.min_dist (cf_of f') s t))"
  unfolding dinitz_phase_def
  apply (refine_vcg WHILET_rule[where I=dinitz_phase_invar and R="inv_image finite_psubset (Graph.E \<circ> snd)"])
       apply (simp_all add: dinitz_phase_step dinitz_phase_final)
  by (simp_all add: dinitz_phase_invar_def NFlow_axioms induced_st_shortest_path_union min_st_dist_bound)
end



(*
context Network
begin

(* TODO rework using inner *)
definition dinic :: "_ flow nres" where
  "dinic \<equiv> do {
    (f, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, n). n < card V)
      (\<lambda>(f, _). do {
        let stl = induced_st_layering (residualGraph c f) s t;
        if Graph.connected stl s t
          then do {
            let n = Graph.min_dist stl s t;
            (f, _) \<leftarrow> WHILE\<^sub>T
              (\<lambda>(_, stl). Graph.connected stl s t)
              (\<lambda>(f, stl). do {
                p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
                let stl = Nonnegative_Graph.subtract_path stl p;
                let f = NFlow.augment c f (NPreflow.augmentingFlow c f p);
                RETURN (f, stl)})
              (f, stl);
            RETURN (f, n)}
          else RETURN (f, (card V))})
      ((\<lambda>_. 0), 0);
    RETURN f}"

theorem dinic_correct: "dinic \<le> SPEC (\<lambda>f. isMaxFlow f)" oops
end
*)
end
theory Original_Dinitz_Algo
  imports Layering_Algo NetworkUtils (*EdmondsKarp_Maxflow.EdmondsKarp_Impl*) (*Refine_Monadic.Refine_Monadic*)
begin
(* TODO do we need f? *)
subsection \<open>Properties when removing a flow from the ST_Layering\<close>
locale ST_Layered_Flow = NFlow c s t f + ST_Shortest_Path_Union stl cf s t + f': Flow stl s t f'
  for c s t f stl f'
begin
interpretation g': Irreducible_Graph stl
  unfolding Irreducible_Graph_def Irreducible_Graph_axioms_def
  using no_parallel_edge cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

interpretation aug_cf: GraphComparison "cleaning s t (g'.subtract_graph f')" "cf_of (augment f')" .

interpretation f'_cont_cf: Pos_Contained_Graph f' cf
  by unfold_locales (metis NPreflow.resE_nonNegative NPreflow_axioms c'_sg_c_old f'.flow_pos_cont.cap_le order_trans)

find_theorems name:augment_alt
find_theorems "residualGraph ?c (NFlow.augment ?c ?f ?f') = Graph.subtract_skew_graph (residualGraph ?c ?f) ?f'"
find_theorems "Contained_Graph ?f' cf \<Longrightarrow> cf_of (augment ?f') = cf.subtract_skew_graph ?f'"

lemma aug_cf_alt: "cf_of (augment f') = cf.subtract_skew_graph f'"
  using augment_alt' f'_cont_cf.Contained_Graph_axioms .

definition new_edge_count :: "path \<Rightarrow> nat"
  where "new_edge_count p \<equiv> length (filter (\<lambda>e. e \<notin> cf.E) p)"

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
    using Graph.zero_cap_simp f'.flow_pos_cont.edges_ss by blast
  with assms show "(w\<^sub>1, w\<^sub>2) \<in> Graph.E (g'.subtract_graph f')"
    unfolding Graph.E_def aug_cf_alt g'.subtract_graph_def cf.subtract_skew_graph_def
    by simp (metis cap_compatible cap_nonzero)
qed

lemma cleaning_maintains_bounded_union:
  "Bounded_ST_Shortest_Path_Union (cleaning s t (g'.subtract_graph f')) (cf_of (augment f')) s t (cf.min_dist s t)"
proof (cases "Graph.isEmpty f'")
  case True
  then have "(g'.subtract_graph f') = stl"
    unfolding Graph.isEmpty_def g'.subtract_graph_def by simp
  then have "(cleaning s t (g'.subtract_graph f')) = stl"
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
    have "Subgraph (cleaning s t (g'.subtract_graph f')) (g'.subtract_graph f')"
      using cleaning_rp_Subgraph right_pass_Subgraph subgraph.order.trans by blast
    also have SUB: "Subgraph ... (cf_of (augment f'))" unfolding aug_cf_alt
      using irreducible_contained_skew_subtract f'.flow_pos_cont.Contained_Graph_axioms g'.Irreducible_Graph_axioms .
    finally show "CapacityCompatibleGraphs (cleaning s t (g'.subtract_graph f')) (cf_of (augment f'))"
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
        using aug_cf_new_edge_prelayered aug_cf.shortestPath_is_path by fastforce
      with ST_IN_V' have "new_edge_count p = 0" using min_dist_transfer st_connected by simp
      with SP' have "cf.isShortestPath s p t"
        unfolding new_edge_count_def Graph.isShortestPath_min_dist_def
        by (metis aug_cf.connected_def Graph.isPath_alt empty_filter_conv length_0_conv nle_le st_min_dist_non_decreasing subset_code(1)) (* TODO fix *)
      then have "g'.isPath s p t" using ST_IN_V' shortest_s_path_remains_path by blast
      with SP' have "Graph.isPath (g'.subtract_graph f') s p t"
        using aug_cf_path_transfer aug_cf.shortestPath_is_path by blast
      then have "Graph.isPath (cleaning s t (g'.subtract_graph f')) s p t"
        using ST_Graph.cleaning_edge_set unfolding Graph.isPath_alt by blast
      with UV_IN_P show "(u, v) \<in> Graph.E (cleaning s t (g'.subtract_graph f'))"
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

subsection \<open>Dinitz inner loop\<close>
context NFlow
begin
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
thm Graph.subtract_path_alt

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
      and "stl' \<equiv> cleaning s t (Graph.subtract_path stl p)"
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
  moreover have "Bounded_ST_Shortest_Path_Union stl' (cf_of aug_f') s t (cf.min_dist s t)"
    using st_layered_flow.cleaning_maintains_bounded_union INDUCED_EQ BOUND_EQ
    unfolding g'.subtract_path_alt f'.augmentingFlow_alt aug_f'_def stl'_def by simp
  moreover have "(Graph.connected (cf_of aug_f') s t \<longrightarrow> cf.min_dist s t \<le> Graph.min_dist (cf_of aug_f') s t)"
    using st_layered_flow.st_min_dist_non_decreasing BOUND_EQ unfolding aug_f'_def by simp
  ultimately show "dinitz_phase_invar (aug_f', stl')"
    unfolding dinitz_phase_invar_def by simp

  (* TODO cleanup this horrible mess *)
  have "stl (arg_min_list stl p) = f'.augmentingFlow p (arg_min_list stl p)" unfolding f'.augmentingFlow_def f'.resCap_alt
    by (smt (verit, ccfv_threshold) Graph.isPath.simps(1) PATH arg_min_list_in case_prod_conv f'.cf.Nonnegative_Graph_axioms f'.cf.pathCap_def f'.resCap_alt f'.resCap_def f_arg_min_list_f g'.isPath_alt g'.pathCap_alt pathCap_eq surj_pair t_not_s)
  moreover have "0 < f'.augmentingFlow p (arg_min_list stl p)" unfolding f'.augmentingFlow_def f'.resCap_alt
    by (metis Graph.isPath.simps(1) Nonnegative_Graph.nonempty_path_cap_positive PATH calculation f'.augmentingFlow_def f'.resCap_alt f_arg_min_list_f g'.Nonnegative_Graph_axioms g'.isPath_alt g'.pathCap_alt t_not_s)
  ultimately show "Graph.E stl' \<subset> E'"
    unfolding stl'_def g'.subtract_path_alt INDUCED_EQ[symmetric] f'.augmentingFlow_alt[symmetric]
    using st_layered_flow.E_pss_if_saturated_edge by (metis surj_pair)

  show "finite E'" using edges_ss finite_subset by auto
qed

(* TODO introduce notion of blocking flow or reuse from Push Relabel, then connect this concept *)
definition res_dist_increasing_flow
  where "res_dist_increasing_flow f' \<equiv>
    NFlow c s t f' \<and> (Graph.connected (cf_of f') s t \<longrightarrow> cf.min_dist s t < Graph.min_dist (cf_of f') s t)"

lemma dinitz_phase_final:
  fixes f' stl
    assumes DISCON: "\<not> Graph.connected stl s t"
      and INVAR: "dinitz_phase_invar (f', stl)"
    shows "res_dist_increasing_flow f'"
  unfolding res_dist_increasing_flow_def
proof
  from INVAR interpret f': NFlow c s t f' unfolding dinitz_phase_invar_def by blast
  show "NFlow c s t f'" using f'.NFlow_axioms .

  from INVAR interpret Bounded_ST_Shortest_Path_Union stl f'.cf s t "cf.min_dist s t"
    unfolding dinitz_phase_invar_def by blast
  from DISCON show "f'.cf.connected s t \<longrightarrow> cf.min_dist s t < f'.cf.min_dist s t"
    by (metis Bounded_ST_Shortest_Path_Union_axioms ST_Shortest_Path_Union.st_connected_iff le_eq_less_or_eq linorder_neqE_nat min_st_dist_bound)
qed

lemma dinitz_phase_correct:
  "dinitz_phase \<le> SPEC (\<lambda>f'. res_dist_increasing_flow f')"
  unfolding dinitz_phase_def
  apply (refine_vcg WHILET_rule[where I=dinitz_phase_invar and R="inv_image finite_psubset (Graph.E \<circ> snd)"])
       apply (simp_all add: dinitz_phase_step dinitz_phase_final)
  by (simp_all add: dinitz_phase_invar_def res_dist_increasing_flow_def NFlow_axioms induced_st_shortest_path_union min_st_dist_bound)
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
  apply (refine_vcg WHILET_rule[where I="\<lambda>f'. NFlow c s t f'" and R=res_dist_rel])
     apply (rule res_dist_wf)
    apply (simp add: NFlowI Network_axioms zero_is_flow)
   apply (fastforce intro: NFlow.dinitz_phase_correct[THEN SPEC_cons_rule] simp: NFlow.res_dist_increasing_flow_def res_dist_rel_def)
  by (simp add: Graph.connected_def Graph.isSimplePath_def NFlow.axioms(1) NFlow.ford_fulkerson(1) NPreflow.isAugmentingPath_def)
end

subsection \<open>Dinitz phase refinement\<close>
context Graph
begin
(* TODO bounded version *)
definition build_st_layering :: "node \<Rightarrow> node \<Rightarrow> _ graph nres" where
  "build_st_layering s t \<equiv> do {
    sl \<leftarrow> ebfs s;
    stl \<leftarrow> Graph.back_ebfs sl t;
    RETURN stl
  }"
end

(* TODO is Finite_Graph really what we want? *)
context Finite_Graph
begin
lemma build_st_layering_correct:
  "build_st_layering s t \<le> (spec c'. ST_Shortest_Path_Union c' c s t)"
  unfolding build_st_layering_def
proof (refine_vcg, simp)
  have "reachableNodes s \<subseteq> V \<union> {s}"
    using Graph.distinct_nodes_in_V_if_connected(2) reachableNodes_def by auto
  then have "finite (reachableNodes s)" using finite_V by (simp add: finite_subset)
  then have "ebfs s \<le> (spec sl. S_Shortest_Path_Union sl c s V)" by (rule ebfs_correct)
  also have "... \<le> (spec sl. Graph.back_ebfs sl t \<le> (spec c'. ST_Shortest_Path_Union c' c s t))"
  proof (rule SPEC_rule)
    fix c'
    assume "S_Shortest_Path_Union c' c s V"
    then interpret S_Shortest_Path_Union c' c s V .

    have "{u. g'.connected u t} \<subseteq> V' \<union> {t}"
      using g'.distinct_nodes_in_V_if_connected by auto
    then have "finite {u. g'.connected u t}" using finite_V V_ss by (simp add: finite_subset)
    then have "g'.back_ebfs t \<le> (spec c''. T_Shortest_Path_Union c'' c' V' t)"
      by (rule g'.back_ebfs_correct)
    also from \<open>S_Shortest_Path_Union c' c s V\<close> have "... \<le> (spec c''. ST_Shortest_Path_Union c'' c s t)"
      using SPEC_rule ST_SPU_dualI by metis
    finally show "g'.back_ebfs t \<le> (spec c''. ST_Shortest_Path_Union c'' c s t)" .
  qed
  finally show "ebfs s \<le> (spec sl. Graph.back_ebfs sl t \<le> (spec c'. ST_Shortest_Path_Union c' c s t))" .
qed

end



context NFlow
begin

(* TODO *)
(*declare fun_relI[refine del]*)
lemma RELATESI_workaround[refine_dref_pattern]:
  "RELATES R \<Longrightarrow> S \<le> (spec x. (x, y) \<in> R) \<Longrightarrow> S \<le> (spec x. (x, y) \<in> R)" .

thm build_st_layering_correct
  ST_Layer_Graph.greedy_st_path_finding_correct
  subtract_path_algo_correct
  Graph.inner_path_vertices_algo_correct
  Finite_Bounded_Graph.cleaning_algo_correct

(* TODO cleanup assertions *)

definition dinitz_phase_assert :: "_ flow nres" where
  "dinitz_phase_assert \<equiv> do {
    stl \<leftarrow> (spec c'. ST_Shortest_Path_Union c' c s t);
    assert (ST_Shortest_Path_Union stl c s t);
    (f', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, _, brk). \<not> brk)
      (\<lambda>(f', stl, _). do {
        assert (ST_Shortest_Path_Union stl c s t);
        p' \<leftarrow> select p. Graph.isPath stl s p t;
        case p' of
          None \<Rightarrow> RETURN (f', stl, True)
        | Some p \<Rightarrow> do {
            assert (Graph.isPath stl s p t);
            Q_ls \<leftarrow> return (tl (butlast (Graph.pathVertices s p)));
            assert (set Q_ls = set (Graph.pathVertices s p) - {s, t});
            stl' \<leftarrow> return (Graph.subtract_path stl p);
            assert (Subgraph stl' stl \<and> Graph.E stl \<subseteq> Graph.E stl' \<union> set p);
            stl' \<leftarrow> return (cleaning s t stl');
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl, False)
          }})
      (f, stl, False);
    RETURN f'}"

definition dinitz_phase_concrete :: "_ flow nres" where
  "dinitz_phase_concrete \<equiv> do {
    stl \<leftarrow> build_st_layering s t;
    assert (ST_Shortest_Path_Union stl c s t);
    (f', _, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, _, brk). \<not> brk)
      (\<lambda>(f', stl, _). do {
        assert (ST_Shortest_Path_Union stl c s t);
        p' \<leftarrow> Graph.greedy_st_path_finding stl s t;
        case p' of
          None \<Rightarrow> RETURN (f', stl, True)
        | Some p \<Rightarrow> do {
            assert (Graph.isPath stl s p t);
            Q_ls \<leftarrow> inner_path_vertices_algo p;
            assert (set Q_ls = set (Graph.pathVertices s p) - {s, t});
            stl' \<leftarrow> Graph.subtract_path_algo stl p;
            assert (Subgraph stl' stl \<and> Graph.E stl \<subseteq> Graph.E stl' \<union> set p);
            stl' \<leftarrow> cleaning_algo (set Q_ls) stl';
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl, False)
          }})
      (f, stl, False);
    RETURN f'}"





find_theorems Graph.pathVertices set
find_theorems Graph.pathVertices_fwd set
find_theorems Graph.pathVertices
thm Graph.pathVertices_append

(*
lemma (in Graph) aux: "u \<notin> set (pathVertices s p) \<Longrightarrow> (u, v) \<notin> set p"
  by (induction p arbitrary: s) auto(*TODO*)
lemma (in Graph) aux2: "u \<notin> set (pathVertices s p) \<Longrightarrow> (v, u) \<notin> set p"
  apply (induction p arbitrary: s)
   apply simp
  apply simp sledgehammer
  apply (induction p arbitrary: s rule: rev_induct)
   apply simp
  apply (simp add: Graph.pathVertices_append) apply auto
  by (induction p arbitrary: s) auto(*TODO*)*)

lemma "dinitz_phase_concrete \<le> \<Down> Id dinitz_phase_assert"
  unfolding dinitz_phase_concrete_def dinitz_phase_assert_def
  apply refine_rcg
            apply refine_dref_type
           apply clarsimp_all
  using build_st_layering_correct apply simp
proof -
  fix stl
  assume "ST_Shortest_Path_Union stl c s t"
  then interpret ST_Shortest_Path_Union stl c s t .
  show "Graph.greedy_st_path_finding stl s t \<le> (select p. Graph.isPath stl s p t)"
    using greedy_st_path_finding_correct .

  fix p
  assume "g'.isPath s p t"
  then have SP: "g'.isShortestPath s p t" by blast
  
  show "inner_path_vertices_algo p \<le> RES {tl (butlast (g'.pathVertices s p))}"
    using inner_path_vertices_algo_correct by (simp add: RES_sng_eq_RETURN)

  from SP show "g'.subtract_path_algo p \<le> RES {g'.subtract_path p}"
    using g'.isSPath_distinct g'.shortestPath_is_simple g'.subtract_path_algo_correct
    by (fastforce simp: RES_sng_eq_RETURN)

  thm Finite_Bounded_Graph.cleaning_algo_correct
  fix stl'
  assume "Subgraph stl' stl" "Graph.E stl \<subseteq> Graph.E stl' \<union> set p"
  show "cleaning_algo (set (g'.pathVertices s p) - {s, t}) stl' \<le> RES {cleaning s t stl'}"
  proof (unfold RES_sng_eq_RETURN, intro Finite_Bounded_Graph.cleaning_algo_correct)
    show "s \<notin> set (g'.pathVertices s p) - {s, t}"
      "t \<notin> set (g'.pathVertices s p) - {s, t}"
      "finite (set (g'.pathVertices s p) - {s, t})"
      by auto
    from \<open>Subgraph stl' stl\<close> show "Finite_Bounded_Graph stl' (layer t)" unfolding Finite_Bounded_Graph_def
      by (meson Distance_Bounded_Graph_axioms Finite_Graph.intro Subgraph.V_ss Subgraph.sg_Distance_Bounded V_ss finite_V rev_finite_subset)
    from \<open>Subgraph stl' stl\<close> show "Graph.incoming stl' s = {}"
      by (metis Subgraph.incoming_ss Subgraph_axioms incoming_s_empty subset_empty)
    from \<open>Subgraph stl' stl\<close> show "Graph.outgoing stl' t = {}"
      by (metis Subgraph.outgoing_ss Subgraph_axioms outgoing_t_empty subset_empty)
    from \<open>Graph.E stl \<subseteq> Graph.E stl' \<union> set p\<close> show "\<forall>u\<in>Graph.V stl' - (set (g'.pathVertices s p) - {s, t}) - {s, t}. Graph.incoming stl' u \<noteq> {} \<and> Graph.outgoing stl' u \<noteq> {}"
    proof auto (* TODO *)
      fix v
      assume "v \<in> Graph.V stl'"
      then have "v \<in> V'" using Subgraph.V_ss[OF \<open>Subgraph stl' stl\<close>] by blast
      moreover assume "v \<noteq> s" "v \<noteq> t"
      ultimately obtain u w where IN_OUT: "(u, v) \<in> E'" "(v, w) \<in> E'"
        by (metis Graph.isPath_fwd_cases g'.connected_def g'.isPath_bwd_cases st_connected)
      
      assume "v \<notin> set (g'.pathVertices s p)"
      with \<open>g'.isPath s p t\<close> have "v \<notin> set (g'.pathVertices_fwd s p)"
        by (simp add: g'.pathVertices_fwd)
      from IN_OUT have "(u, v) \<notin> set p" "(v, w) \<notin> set p" using g'.adjacent_edges_not_on_path[OF \<open>g'.isPath s p t\<close> \<open>v \<notin> set (g'.pathVertices_fwd s p)\<close>]
        unfolding g'.adjacent_def g'.incoming_def g'.outgoing_def by auto
      with \<open>Graph.E stl \<subseteq> Graph.E stl' \<union> set p\<close> IN_OUT have "(u, v) \<in> Graph.E stl'" "(v, w) \<in> Graph.E stl'" by auto
      then show "Graph.incoming stl' v = {} \<Longrightarrow> False" "Graph.outgoing stl' v = {} \<Longrightarrow> False"
        unfolding Graph.incoming_def Graph.outgoing_def by auto
    qed
  qed
qed
end
end
theory Dinic_Algo
  imports Refinement "Flow_Networks.Ford_Fulkerson"
begin

(* TODO change definition of NFlow *)
text \<open>This is a workaround to introduce NFlow more easily, since it usually requires showing Preflow twice.\<close>
lemma NFlowI: "\<lbrakk>Network c s t; Flow c s t f\<rbrakk> \<Longrightarrow> NFlow c s t f"
  unfolding NFlow_def NPreflow_def Flow_def by simp

sublocale Network \<subseteq> Irreducible_Graph
  using cap_non_negative no_parallel_edge by unfold_locales auto

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


(* TODO move *)
context NFlow
begin
context
  fixes f' :: "'capacity flow"
  assumes f'_flow: "Flow cf s t f'"
begin
(*
interpretation cf: Nonnegative_Graph cf using Nonnegative_Graph_def resE_nonNegative by blast (* TODO make sublocale *)
interpretation n': NFlow c s t "augment f'"
  by (simp add: NFlowI Network_axioms augment_flow_presv f'_flow)

thm n'.capacity_const

lemma subtract_augment_Subgraph: "Subgraph (cf.subtract_graph f') n'.cf"
proof (intro Subgraph_edgeI)
  fix u v
  assume "cf.subtract_graph f' (u, v) \<noteq> 0"
  then show "n'.cf (u, v) = cf.subtract_graph f' (u, v)" sorry
qed
*)

interpretation cf: Nonnegative_Graph cf using Nonnegative_Graph_def resE_nonNegative by blast (* TODO make sublocale *)
interpretation f': Flow cf s t f' using f'_flow .
interpretation n': NFlow c s t "augment f'"
  by (simp add: NFlowI Network_axioms augment_flow_presv f'_flow)

thm n'.capacity_const
thm f'.capacity_const
thm n'.capacity_const[unfolded augment_def, simplified]
thm f'.capacity_const[unfolded cf_def, simplified]

thm residualGraph_def
thm no_parallel_edge_cases (* TODO use *)

lemma subtract_augment_Subgraph: "Subgraph (cf.subtract_graph f') (residualGraph c (augment f'))"
proof (intro Subgraph_edgeI)
  fix u v
  assume assm: "cf.subtract_graph f' (u, v) \<noteq> 0"
  thm this[unfolded cf_def Graph.subtract_graph_def]
  thm this[unfolded cf_def Graph.subtract_graph_def, simplified]
  consider (EDGE) "(u, v) \<in> E" "(v, u) \<notin> E"
    | (REV_EDGE) "(u, v) \<notin> E" "(v, u) \<in> E"
    | (NO_EDGE) "(u, v) \<notin> E" "(v, u) \<notin> E"
    using no_parallel_edge by blast
  then show "n'.cf (u, v) = cf.subtract_graph f' (u, v)"
  proof cases (*(cases rule: no_parallel_edge_cases)*)
    case NO_EDGE
    then show ?thesis
      unfolding n'.cf_def Graph.subtract_graph_def cf_def augment_def residualGraph_def
      apply simp
      by (smt (verit, ccfv_threshold) cf_def dual_order.strict_trans1 f'.capacity_const order_less_irrefl order_neq_le_trans split_conv)
  next
    case EDGE
    moreover from EDGE have A0: "0 \<le> f (u, v) + f' (u, v) - f' (v, u)" and A1: "f (u, v) + f' (u, v) - f' (v, u) \<le> c (u, v)"
      using n'.capacity_const unfolding augment_def by (smt (verit) case_prod_conv)+
    moreover from EDGE have B0: "0 \<le> f' (u, v)" and B1: "f' (u, v) \<le> c (u, v) - f (u, v)"
      using f'.capacity_const unfolding cf_def by (smt (verit) case_prod_conv)+
    moreover from EDGE have C0: "0 \<le> f' (v, u)" and C1: "f' (v, u) \<le> f (u, v)"
      using f'.capacity_const unfolding cf_def by (smt (verit) case_prod_conv)+
    moreover from EDGE assm have "c (u, v) - f (u, v) - f' (u, v) \<noteq> 0" unfolding cf_def Graph.subtract_graph_def by simp
    ultimately show ?thesis
      unfolding n'.cf_def Graph.subtract_graph_def cf_def augment_def residualGraph_def
      apply simp
      sorry
  next
    case REV_EDGE
    then show ?thesis
      unfolding n'.cf_def Graph.subtract_graph_def cf_def augment_def residualGraph_def
      apply simp sorry
  qed
qed
(*
  apply (intro Subgraph_isSubgraphI)
  unfolding cf.subtract_graph_def residualGraph_def augment_def Graph.subtract_graph_def isSubgraph_def E_def
  apply auto defer defer defer
  using no_parallel_edge zero_cap_simp apply blast
*)
end

context
  fixes p
  assumes "isAugmentingPath p"
begin
interpretation cf: Nonnegative_Graph cf using Nonnegative_Graph_def resE_nonNegative by blast (* TODO make sublocale *)
interpretation n': NFlow c s t "augment (augmentingFlow p)"
  using NFlowI Network_axioms \<open>isAugmentingPath p\<close> augFlow_resFlow augment_flow_presv by blast

lemma subtract_augment_path_Subgraph: "Subgraph (cf.subtract_path p) n'.cf"
proof -
  have "cf.path_induced_graph p = augmentingFlow p"
    unfolding cf.path_induced_graph_def augmentingFlow_def cf.pathCap_def resCap_def by auto
  then show ?thesis unfolding cf.subtract_path_alt using subtract_augment_Subgraph
    by (simp add: \<open>isAugmentingPath p\<close> augFlow_resFlow)
qed
(*
proof (intro Subgraph_edgeI)
  fix u v
  assume "g'.subtract_path p (u, v) \<noteq> 0"
  then show "n'.cf (u, v) = g'.subtract_path p (u, v)" sorry
qed
*)
end
end
thm NFlow.subtract_augment_path_Subgraph

context NFlow
begin

definition dinic_inner_partial :: "(_ flow \<times> nat) nres" where
  "dinic_inner_partial \<equiv> do {
    if Graph.connected cf s t
      then do {
        let n = Graph.min_dist cf s t;
        let stl = induced_st_layering (residualGraph c f) s t;
        (f', _) \<leftarrow> WHILE
          (\<lambda>(_, stl). Graph.connected stl s t)
          (\<lambda>(f', stl). do {
            p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
            let stl = cleaningAbstract (Nonnegative_Graph.subtract_path stl p) s t;
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl)})
          (f, stl);
        RETURN (f', n)}
      else RETURN (f, (card V))}"

definition dinic_inner_partial_invar :: "nat \<Rightarrow> (_ flow \<times> _ graph) \<Rightarrow> bool" where
  "dinic_inner_partial_invar b \<equiv> \<lambda>(f', stl). NFlow c s t f'
                                 \<and> Bounded_ST_Shortest_Path_Union stl (NPreflow.cf c f') s t b
                                 \<and> b \<le> (Graph.min_dist (NPreflow.cf c f') s t)"

lemma dinic_inner_partial_step:
  assumes PATH: "Graph.isPath stl s p t"
      and BOUNDED_UNION: "Bounded_ST_Shortest_Path_Union stl cf s t b"
      and B_LE: "b \<le> cf.min_dist s t"
    shows "NFlow c s t (augment (augmentingFlow p))
    \<and> Bounded_ST_Shortest_Path_Union (cleaningAbstract (Nonnegative_Graph.subtract_path stl p) s t) (cf_of (augment (augmentingFlow p))) s t b
    \<and> b \<le> Graph.min_dist (cf_of (augment (augmentingFlow p))) s t"
proof (intro conjI)
  have B_EQ: "b = cf.min_dist s t"
  proof (intro antisym)
    interpret Bounded_ST_Shortest_Path_Union stl cf s t b using BOUNDED_UNION .
    from PATH show "cf.min_dist s t \<le> b"
      using cf.isShortestPath_min_dist_def path_length_bounded shortest_path_transfer by force
  qed (rule B_LE)
  with BOUNDED_UNION interpret ST_Shortest_Path_Union stl cf s t using min_st_dist_bound by blast

  show "NFlow c s t (augment (augmentingFlow p))"
    apply (intro NFlowI, simp add: Network_axioms)
    by (simp add: PATH augFlow_resFlow augment_flow_presv cf.shortestPath_is_simple isAugmentingPath_def shortest_path_transfer)
  then interpret n': NFlow c s t "augment (augmentingFlow p)" .

  interpret Nonnegative_Graph cf
    using Nonnegative_Graph_def resE_nonNegative by blast
  interpret g': Nonnegative_Graph stl
    using Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

  show "Bounded_ST_Shortest_Path_Union (cleaningAbstract (g'.subtract_path p) s t) n'.cf s t b"
    unfolding Bounded_ST_Shortest_Path_Union_def Bounded_ST_Shortest_Path_Union_axioms_def
  proof
    have "Subgraph (cleaningAbstract (g'.subtract_path p) s t) (g'.subtract_path p)"
      using cleaning_right_subgraph right_pass_subgraph subgraph.order.trans by blast (* TODO extract *)
    moreover have "Subgraph (g'.subtract_path p) (subtract_path p)"
      using subtract_path_maintains_Subgraph Nonnegative_Graph_axioms PATH by blast
    moreover from PATH have "Subgraph (subtract_path p) n'.cf"
      using subtract_augment_path_Subgraph cf.shortestPath_is_simple isAugmentingPath_def shortest_path_transfer by blast
    ultimately have "Subgraph (cleaningAbstract (g'.subtract_path p) s t) n'.cf"
      by (auto dest!: Subgraph.c'_sg_c)
    then show "CapacityCompatibleGraphs (cleaningAbstract (g'.subtract_path p) s t) n'.cf"
      unfolding Subgraph_def by blast
  next
    show "Graph.E (cleaningAbstract (g'.subtract_path p) s t) = \<Union> {set p |p. n'.cf.isShortestPath s p t \<and> length p \<le> b}"
    proof (intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> Graph.E (cleaningAbstract (g'.subtract_path p) s t)"
      then show "(u, v) \<in> \<Union> {set p |p. n'.cf.isShortestPath s p t \<and> length p \<le> b}" sorry
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. n'.cf.isShortestPath s p t \<and> length p \<le> b}"
      then show "(u, v) \<in> Graph.E (cleaningAbstract (g'.subtract_path p) s t)" sorry
    qed
  qed
  show "b \<le> n'.cf.min_dist s t" sorry
qed


lemma dinic_inner_partial_correct:
  "dinic_inner_partial \<le> SPEC (\<lambda>(f', n). NFlow c s t f' \<and> \<not> (\<exists>p. NPreflow.isAugmentingPath c s t f' p \<and> length p \<le> n))"
  unfolding dinic_inner_partial_def
proof (refine_vcg WHILE_rule[where I="dinic_inner_partial_invar (cf.min_dist s t)"], clarsimp_all)
  interpret ST_Shortest_Path_Union "induced_st_layering cf s t" cf s t
    using induced_st_shortest_path_union .

  show "dinic_inner_partial_invar (cf.min_dist s t) (f, induced_st_layering cf s t)"
    unfolding dinic_inner_partial_invar_def
    by (auto simp: min_st_dist_bound intro: NFlow_axioms ST_Shortest_Path_Union_axioms)

  show "NFlow c s t f" using NFlow_axioms .

  show "\<And>p. \<lbrakk>\<not> cf.connected s t; isAugmentingPath p\<rbrakk> \<Longrightarrow> False"
    unfolding isAugmentingPath_def cf.connected_def cf.isSimplePath_def by blast

  show "\<And>f' stl. dinic_inner_partial_invar (cf.min_dist s t) (f', stl) \<Longrightarrow> NFlow c s t f'"
    unfolding dinic_inner_partial_invar_def by blast

  show "\<And>ba x1 p.
       \<lbrakk>cf.connected s t; dinic_inner_partial_invar (cf.min_dist s t) (x1, ba); \<not> Graph.connected ba s t;
        NPreflow.isAugmentingPath c s t x1 p; length p \<le> cf.min_dist s t\<rbrakk>
       \<Longrightarrow> False" using LayerGraph.Bounded_ST_Shortest_Path_Union.st_connected_if_bound_path
    using Graph.isSimplePath_def NFlow_def NPreflow.isAugmentingPath_def dinic_inner_partial_invar_def by fastforce

  show "\<And>aa ba x.
       \<lbrakk>cf.connected s t; dinic_inner_partial_invar (cf.min_dist s t) (aa, ba); Graph.connected ba s t; Graph.isPath ba s x t\<rbrakk>
       \<Longrightarrow> dinic_inner_partial_invar (cf.min_dist s t)
            (NFlow.augment c aa (NPreflow.augmentingFlow c aa x), cleaningAbstract (Nonnegative_Graph.subtract_path ba x) s t)"
    unfolding dinic_inner_partial_invar_def using NFlow.dinic_inner_partial_step by blast
qed
end
end
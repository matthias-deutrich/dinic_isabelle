theory Dinic_Algo
  imports Refinement NetworkUtils
begin


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

context NFlow
begin
context
  fixes stl p
  assumes SPU: "ST_Shortest_Path_Union stl cf s t"
      and PATH: "Graph.isPath stl s p t"
begin
interpretation ST_Shortest_Path_Union stl cf s t using SPU .

interpretation g': Irreducible_Graph stl
  unfolding Irreducible_Graph_def Irreducible_Graph_axioms_def
  using no_parallel_edge cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

lemma subtract_augment_Subgraph: "Subgraph (g'.subtract_path p) (cf_of (augment (augmentingFlow p)))"
proof -
  have INDUCED: "augmentingFlow p = g'.path_induced_graph p" unfolding augmentingFlow_alt
    using PATH g'.isPath_alt cf.Nonnegative_Graph_axioms by (auto simp: path_induced_graph_eq)

  have CONT_STL: "Contained_Graph (g'.path_induced_graph p) stl" using g'.path_induced_graph_pos_contained
    by (simp add: Contained_Graph.intro Le_Graph.cap_le Nonnegative_Graph.cap_non_negative Pos_Contained_Graph_def) (* TODO *)
  also have "Contained_Graph stl cf" by (simp add: Contained_Graph_axioms)
  finally have CONT_CF: "Contained_Graph (g'.path_induced_graph p) cf" .

  show ?thesis unfolding g'.subtract_path_alt INDUCED augment_alt[OF CONT_CF]
    using CONT_STL g'.Irreducible_Graph_axioms by (intro irreducible_contained_skew_subtract)
qed
end

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
            let stl = cleaning (Nonnegative_Graph.subtract_path stl p) s t;
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
    \<and> Bounded_ST_Shortest_Path_Union (cleaning (Nonnegative_Graph.subtract_path stl p) s t) (cf_of (augment (augmentingFlow p))) s t b
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

  interpret g': Nonnegative_Graph stl
    using cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

  have "cf.min_dist s t \<le> n'.cf.min_dist s t" sorry
  with B_EQ show "b \<le> n'.cf.min_dist s t" by simp

  (*interpret tmp: CapacityCompatibleGraphs "(cleaning (g'.subtract_path p) s t)" n'.cf sorry*)

  show "Bounded_ST_Shortest_Path_Union (cleaning (g'.subtract_path p) s t) n'.cf s t b"
    (*apply unfold_locales*)
    (*apply intro_locales prefer 2 subgoal apply unfold_locales*)
    unfolding Bounded_ST_Shortest_Path_Union_def Bounded_ST_Shortest_Path_Union_axioms_def
  proof
    have "Subgraph (cleaning (g'.subtract_path p) s t) (g'.subtract_path p)"
      by (metis ST_Graph.cl_is_c_if_st_connected Subgraph_edgeI cleaning_nz_iff)
      (*using cleaning_right_subgraph right_pass_subgraph subgraph.order.trans by blast*) (* TODO extract *)
    also have "Subgraph ... n'.cf" using subtract_augment_Subgraph
      using PATH ST_Shortest_Path_Union_axioms by blast
    finally have "Subgraph (cleaning (g'.subtract_path p) s t) n'.cf" .
    then show "CapacityCompatibleGraphs (cleaning (g'.subtract_path p) s t) n'.cf"
      unfolding Subgraph_def by blast
  next
    show "Graph.E (cleaning (g'.subtract_path p) s t) = \<Union> {set p |p. n'.cf.isShortestPath s p t \<and> length p \<le> b}"
    proof (intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> Graph.E (cleaning (g'.subtract_path p) s t)"
      then show "(u, v) \<in> \<Union> {set p |p. n'.cf.isShortestPath s p t \<and> length p \<le> b}" sorry
    next
      fix u v
      assume "(u, v) \<in> \<Union> {set p |p. n'.cf.isShortestPath s p t \<and> length p \<le> b}"
      then obtain p' where "(u, v) \<in> set p'" "n'.cf.isShortestPath s p' t" "length p' \<le> b" by blast
      with \<open>b \<le> n'.cf.min_dist s t\<close> have "length p' = b"
        unfolding n'.cf.isShortestPath_min_dist_def by simp
      then show "(u, v) \<in> Graph.E (cleaning (g'.subtract_path p) s t)" sorry
    qed
  qed
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
            (NFlow.augment c aa (NPreflow.augmentingFlow c aa x), cleaning (Nonnegative_Graph.subtract_path ba x) s t)"
    unfolding dinic_inner_partial_invar_def using NFlow.dinic_inner_partial_step by blast
qed
end
end
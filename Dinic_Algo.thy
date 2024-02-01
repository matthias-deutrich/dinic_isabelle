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
(* TODO deprecated, remove *)
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

context
  fixes stl f'
  assumes CONTAINED: "Contained_Graph f' stl"
      and STU: "ST_Shortest_Path_Union stl cf s t"
begin
interpretation ST_Shortest_Path_Union stl cf s t using STU .

interpretation g': Irreducible_Graph stl
  unfolding Irreducible_Graph_def Irreducible_Graph_axioms_def
  using no_parallel_edge cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

(*
interpretation con: Contained_Graph f' stl using CONTAINED .
*)

lemma f'_cont: "Contained_Graph f' cf"
  using CONTAINED Contained_Graph_axioms contained_trans by blast

thm g'.E_def
thm st_connected_iff

interpretation cf': Graph "cf.subtract_skew_graph f'" .

find_consts name:filter
thm filter.simps
(* TODO is there something better than length (filter P) ? didn't find anything *)
find_theorems length filter

thm path_prelayered
lemma aux: "Graph.isPath (cf_of (augment f')) u p v \<Longrightarrow> cf.min_dist u v + 2 * (length (filter (\<lambda>e. e \<notin> cf.E) p))\<le> length p"
  unfolding augment_alt[OF f'_cont]
proof (induction "length (filter (\<lambda>e. e \<notin> cf.E) p)")
  case 0
  then show ?case
  proof (cases "p = []")
    case True
    with 0 show ?thesis by simp
  next
    case False
    with 0 have "u \<in> cf.V" "v \<in> cf.V"
      using cf'.isPath_fwd_cases cf.V_def apply fastforce
      using False 0 cf'.isPath_bwd_cases cf.V_def by fastforce (* TODO improve *)
    moreover from 0 have "cf.isPath u p v"
      by (metis cf'.isPath_alt cf.isPath_alt empty_filter_conv length_0_conv subset_code(1))
    ultimately show ?thesis using path_prelayered sorry
  qed



  then have "cf.isPath u p v"
    sby (metis cf'.isPath_alt cf.isPath_alt empty_filter_conv length_0_conv subset_code(1))
  moreover from 0 have 
  then have "cf.min_dist u v \<le> length p"
    using 
  then show ?case
    apply (simp add: 0)
next
  case (Suc x)
  then show ?case sorry
qed

(*
thm path_prelayered
(* TODO check if using s is actually necessary *)
lemma aux: "\<lbrakk>Graph.isPath (cf_of (augment f')) s p u; \<not> cf.isPath s p u\<rbrakk> \<Longrightarrow> cf.min_dist s u < length p"
  unfolding augment_alt[OF f'_cont]
proof (induction rule: cf'.isPath_back_induct)
  case (SelfPath u)
  then show ?case by simp
next
  case (EdgePath p u v)
  thm path_prelayered
  then have "cf.isPath s p u" sorry (* TODO make this work *)
  then show ?case sorry
qed
  assume "cf'.isPath s p t" "\<not> cf.isPath s p t"
  then obtain u v where "(u, v) \<in> set p" "(u, v) \<notin> cf.E"
    unfolding Graph.isPath_alt by auto
  with \<open>cf'.isPath s p t\<close> obtain p\<^sub>s p\<^sub>t where "cf'.isPath s (p\<^sub>s @ (u, v) # p\<^sub>t) t"
    by (metis split_list)
*)
(* TODO rename *)
(*
lemma aux:
  "\<lbrakk>Graph.isPath (cf_of (augment f')) s p t; \<not> cf.isPath s p t\<rbrakk> \<Longrightarrow> cf.min_dist s t < length p"
  unfolding augment_alt[OF f'_cont]
proof -
  interpret cf': Graph "cf.subtract_skew_graph f'" .
  assume "cf'.isPath s p t" "\<not> cf.isPath s p t"
  then obtain u v where "(u, v) \<in> set p" "(u, v) \<notin> cf.E"
    unfolding Graph.isPath_alt by auto
  with \<open>cf'.isPath s p t\<close> obtain p\<^sub>s p\<^sub>t where "cf'.isPath s (p\<^sub>s @ (u, v) # p\<^sub>t) t"
    by (metis split_list)
*)

(* TODO do we need the flow properties? *)
lemma dinic_inner_flow_step:
  "cf.min_dist s t \<le> Graph.min_dist (cf_of (augment f')) s t \<and>
  Bounded_ST_Shortest_Path_Union (cleaning (g'.subtract_graph f') s t) (cf_of (augment f')) s t (cf.min_dist s t)"
  unfolding augment_alt[OF f'_cont]
proof
  show "cf.min_dist s t \<le> cf'.min_dist s t" sorry

  show "Bounded_ST_Shortest_Path_Union (cleaning (g'.subtract_graph f') s t) (cf.subtract_skew_graph f') s t (cf.min_dist s t)"
    unfolding Bounded_ST_Shortest_Path_Union_def Bounded_ST_Shortest_Path_Union_axioms_def
  proof
    have "Subgraph (cleaning (g'.subtract_graph f') s t) (g'.subtract_graph f')"
      using cleaning_rp_Subgraph right_pass_Subgraph subgraph.order.trans by blast
    also have "Subgraph ... (cf.subtract_skew_graph f')"
      using irreducible_contained_skew_subtract[OF CONTAINED g'.Irreducible_Graph_axioms] .
    (*finally have "Subgraph (cleaning (g'.subtract_graph f') s t) (cf.subtract_skew_graph f')" .*)
    finally show "CapacityCompatibleGraphs (cleaning (g'.subtract_graph f') s t) (cf.subtract_skew_graph f')"
      unfolding Subgraph_def by blast

    thm ST_Graph.cleaning_edge_set

    show "Graph.E (cleaning (g'.subtract_graph f') s t) = \<Union> {set p |p. cf'.isShortestPath s p t \<and> length p \<le> cf.min_dist s t}"
    proof (intro pair_set_eqI)
      fix u v
      assume "(u, v) \<in> Graph.E (cleaning (g'.subtract_graph f') s t)"
      then obtain p where "Graph.isPath (g'.subtract_graph f') s p t" "(u, v) \<in> set p"
        using ST_Graph.cleaning_edge_set by blast
      with \<open>Subgraph (g'.subtract_graph f') (cf.subtract_skew_graph f')\<close> have "cf'.isPath s p t"
        using Subgraph.sg_paths_are_base_paths by blast
      moreover have "length p = cf.min_dist s t" sorry
      moreover note \<open>cf.min_dist s t \<le> cf'.min_dist s t\<close>
      moreover note \<open>(u, v) \<in> set p\<close>
      ultimately show "(u, v) \<in> \<Union> {set p |p. cf'.isShortestPath s p t \<and> length p \<le> cf.min_dist s t}"
        unfolding cf'.isShortestPath_min_dist_def
        using cf'.isPath_distD cf'.min_dist_minD by fastforce
  qed
end


lemma dinic_inner_partial_step:
  assumes PATH: "Graph.isPath stl s p t"
      and BOUNDED_UNION: "Bounded_ST_Shortest_Path_Union stl cf s t b"
      and B_LE: "b \<le> cf.min_dist s t"
    shows "NFlow c s t (augment (augmentingFlow p))
    \<and> b \<le> Graph.min_dist (cf_of (augment (augmentingFlow p))) s t
    \<and> Bounded_ST_Shortest_Path_Union (cleaning (Nonnegative_Graph.subtract_path stl p) s t) (cf_of (augment (augmentingFlow p))) s t b"
proof -
  have B_EQ: "b = cf.min_dist s t"
  proof (intro antisym)
    interpret Bounded_ST_Shortest_Path_Union stl cf s t b using BOUNDED_UNION .
    from PATH show "cf.min_dist s t \<le> b"
      using cf.isShortestPath_min_dist_def path_length_bounded shortest_path_transfer by force
  qed (rule B_LE)
  with BOUNDED_UNION interpret ST_Shortest_Path_Union stl cf s t using min_st_dist_bound by blast

  interpret g': Nonnegative_Graph stl
    using cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

  have INDUCED: "augmentingFlow p = g'.path_induced_graph p" unfolding augmentingFlow_alt
    using PATH g'.isPath_alt cf.Nonnegative_Graph_axioms by (auto simp: path_induced_graph_eq)

  interpret p_con: Pos_Contained_Graph "g'.path_induced_graph p" stl
    using g'.path_induced_graph_pos_contained .

  have "NFlow c s t (augment (augmentingFlow p))"
    apply (intro NFlowI, simp add: Network_axioms)
    by (simp add: PATH augFlow_resFlow augment_flow_presv cf.shortestPath_is_simple isAugmentingPath_def shortest_path_transfer)
  then show ?thesis unfolding B_EQ g'.subtract_path_alt INDUCED
    using dinic_inner_flow_step[OF p_con.Contained_Graph_axioms ST_Shortest_Path_Union_axioms] by rule
qed
(*
  thm p_con.Contained_Graph_axioms

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
*)

lemma dinic_inner_partial_step':
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
    unfolding dinic_inner_partial_invar_def using NFlow.dinic_inner_partial_step' by blast
qed
end
end
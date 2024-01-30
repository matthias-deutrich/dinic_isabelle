theory Dinic_Algo
  imports Refinement "Flow_Networks.Ford_Fulkerson"
begin

(* TODO change definition of NFlow *)
text \<open>This is a workaround to introduce NFlow more easily, since it usually requires showing Preflow twice.\<close>
lemma NFlowI: "\<lbrakk>Network c s t; Flow c s t f\<rbrakk> \<Longrightarrow> NFlow c s t f"
  unfolding NFlow_def NPreflow_def Flow_def by simp

sublocale Network \<subseteq> Irreducible_Graph
  using cap_non_negative no_parallel_edge by unfold_locales auto

context NPreflow
begin
sublocale cf: Nonnegative_Graph cf using Nonnegative_Graph_def resE_nonNegative by blast
end

subsection \<open>Alternative definitions\<close>
(* TODO check which of these are used *)
context Flow
begin
thm zero_flow_simp
lemma residualGraph_alt: "residualGraph c f = (\<lambda>(u, v). if (u, v) \<in> E then c (u, v) - f(u, v) else f (v, u))"
  unfolding residualGraph_def by auto

lemma contained: "Contained_Graph f c" using capacity_const by unfold_locales blast
end

context NPreflow
begin
lemma resCap_pathCap: "resCap p = cf.pathCap p"
  unfolding resCap_def cf.pathCap_def ..

lemma augmentingFlow_alt: "augmentingFlow p = cf.path_induced_graph p"
  unfolding augmentingFlow_def cf.path_induced_graph_def resCap_pathCap ..
end

(*find_theorems "?f = ?f' \<Longrightarrow>(\<lambda>x. ?f x) = (\<lambda>x. ?f' x)"*)
context NFlow
begin
lemma augment_alt: "Contained_Graph f' cf \<Longrightarrow> cf_of (augment f') = cf.subtract_skew_graph f'"
proof (rule ext, unfold split_paired_all)
  fix u v
  assume "Contained_Graph f' cf"
  then interpret Contained_Graph f' cf .
  show "cf_of (augment f') (u, v) = cf.subtract_skew_graph f' (u, v)"
  proof (cases "(u, v) \<notin> E \<and> (v, u) \<notin> E")
    case True
    then have "f' (u, v) = 0" "f' (v, u) = 0"
      using cap_abs_le NPreflow.cf_def NPreflow_axioms nle_le by fastforce+
    then show ?thesis unfolding Graph.subtract_skew_graph_def augment_def residualGraph_def by auto
  next
    case False
    then show ?thesis unfolding Graph.subtract_skew_graph_def augment_def residualGraph_def by auto
  qed
qed
end
\<comment> \<open>Alternative definitions\<close>

subsection \<open>Auxiliary statements concerning the edges of augments\<close>
context Pos_Contained_Graph
begin
lemma subtract_skew_edges_sub: "Graph.E (subtract_skew_graph c') \<subseteq> E \<union> E'\<inverse>"
  unfolding subtract_skew_graph_def Graph.E_def
  by auto (metis cap_le g'.cap_non_negative nle_le)

lemma subtract_skew_edges_sup: "E \<subseteq> Graph.E (subtract_skew_graph c') \<union> E'"
  unfolding subtract_skew_graph_def Graph.E_def
  by auto (metis cap_le g'.cap_non_negative add_nonneg_eq_0_iff)
end





context NFlow
begin
(* TODO necessary? *)
context
  fixes f' :: "'capacity flow"
  assumes f'_flow: "Flow cf s t f'"
begin
interpretation f': Flow cf s t f' using f'_flow .
(* TODO necessary? *)
interpretation Pos_Contained_Graph f' cf
  using f'_flow unfolding Flow_def Preflow_def by unfold_locales auto

interpretation f'': Flow c s t "augment f'" using f'_flow augment_flow_presv by blast

interpretation n': NFlow c s t "augment f'" by intro_locales

lemma augment_edges_sub: "n'.cf.E \<subseteq> cf.E \<union> E'\<inverse>"
  unfolding augment_alt[OF f'.contained] using subtract_skew_edges_sub .
proof (clarify,rule ccontr)
  fix u v
  assume "(u, v) \<notin> E" "(v, u) \<notin> E'"
  then have [simp]: "c (u, v) = 0" "f (u, v) = 0" "f' (v, u) = 0" by simp_all
    (*then have "f' (u, v) \<le> f (v, u)"
      by (smt (verit, best) \<open>(u, v) \<notin> E\<close> cap_le residualGraph_alt split_conv)*)
  assume "(u, v) \<in> n'.cf.E"
  then have "0 < augment f' (v, u)"
    unfolding f''.residualGraph_alt Graph.E_def by (simp add: f''.capacity_const less_le)
  then have "f' (u, v) < f (v, u)" unfolding augment_def by (auto split:if_splits)
  then show False sorry
qed
    with \<open>f' (u, v) \<le> f (v, u)\<close> have "f' (v, u) > 0" sorry
    then have "f' (v, u) > 0" sorry
    moreover have "f' (u, v) \<le> f (v, u)"
      by (smt (verit, del_insts) \<open>(u, v) \<notin> E\<close> cap_le residualGraph_alt split_conv)
    moreover have "f' (v, u) \<le> f' (u, v) - f (v, u)" sorry
    ultimately show "(v, u) \<in> E'" unfolding g'.E_def by auto
    then have "False" unfolding f''.residualGraph_alt
      unfolding augment_def Graph.E_def apply (auto split: if_splits)
      using \<open>(u, v) \<in> n'.cf.E\<close> f''.residualGraph_alt f''.zero_flow_simp n'.cf.E_def sorry by fastforce
    then show "(v, u) \<in> E'" sorry
  qed
  then show ?thesis by clarify
qed
lemma augment_edges_sub: "n'.cf.E \<subseteq> E \<union> E'\<inverse>" (*apply clarify*)
proof -
  have "\<And>u v. \<lbrakk>(u, v) \<in> n'.cf.E; (u, v) \<notin> E\<rbrakk> \<Longrightarrow> (v, u) \<in> E'"
  proof -
    fix u v
    assume "(u, v) \<notin> E"
    then have [simp]: "c (u, v) = 0" "f (u, v) = 0" by simp_all
    then have "f' (u, v) \<le> f (v, u)"
      by (smt (verit, best) \<open>(u, v) \<notin> E\<close> cap_le residualGraph_alt split_conv)
    assume "(u, v) \<in> n'.cf.E"
    then have "0 < augment f' (v, u)"
      unfolding f''.residualGraph_alt Graph.E_def by (simp add: f''.capacity_const less_le)
    then have "f' (u, v) < f (v, u) + f' (v, u)" unfolding augment_def by (auto split:if_splits)
    with \<open>f' (u, v) \<le> f (v, u)\<close> have "f' (v, u) > 0" sorry
    then have "f' (v, u) > 0" sorry
    moreover have "f' (u, v) \<le> f (v, u)"
      by (smt (verit, del_insts) \<open>(u, v) \<notin> E\<close> cap_le residualGraph_alt split_conv)
    moreover have "f' (v, u) \<le> f' (u, v) - f (v, u)" sorry
    ultimately show "(v, u) \<in> E'" unfolding g'.E_def by auto
    then have "False" unfolding f''.residualGraph_alt
      unfolding augment_def Graph.E_def apply (auto split: if_splits)
      using \<open>(u, v) \<in> n'.cf.E\<close> f''.residualGraph_alt f''.zero_flow_simp n'.cf.E_def sorry by fastforce
    then show "(v, u) \<in> E'" sorry
  qed
  then show ?thesis by clarify
qed



(*(intro subrelI)*) (*unfolding residualGraph_def augment_def Graph.E_def apply auto*)
lemma augment_edges_sup: "E \<subseteq> Graph.E (subtract_graph c') \<union> E'" oops
end
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

context NFlow
begin
(* TODO we don't need SPU, but only Subgraph and Irreducible, also only need contained*)
context
  fixes stl f'
  assumes SPU: "ST_Shortest_Path_Union stl cf s t"
      and POS_CONTAINED: "Pos_Contained_Graph f' stl"
begin
interpretation ST_Shortest_Path_Union stl cf s t using SPU .

interpretation g': Irreducible_Graph stl
  unfolding Irreducible_Graph_def Irreducible_Graph_axioms_def
  using no_parallel_edge cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

interpretation p_con: Pos_Contained_Graph f' stl using POS_CONTAINED .

interpretation f': Irreducible_Graph f'
  using p_con.contained_irreducible g'.Irreducible_Graph_axioms by blast
thm less_le_trans
thm less_imp_neq
thm le_neq_trans
lemma subtract_augment_Subgraph: "Subgraph (g'.subtract_graph f') (cf_of (augment f'))" (* TODO fix this horrible proof *)
proof (intro Subgraph_edgeI)
  fix u v
  assume "g'.subtract_graph f' (u, v) \<noteq> 0"
(*
  then have "stl (u, v) \<noteq> 0" unfolding g'.subtract_graph_def
    using p_con.cap_le p_con.g'.cap_non_negative
    apply (auto intro!: less_imp_neq)
    apply (auto dest!: le_neq_trans intro: less_le_trans intro!: less_imp_neq)
    apply (intro less_imp_neq)
    
    
    apply simp using p_con.cap_le p_con.g'.cap_non_negative nle_le
    by (metis nle_le)*)
  then have "f' (u, v) < stl (u, v)"
    unfolding g'.subtract_graph_def using p_con.cap_le by (auto intro: le_neq_trans)
  then have "stl (u, v) \<noteq> 0" by (metis leD p_con.g'.cap_non_negative)
  then have "stl (v, u) = 0" by (rule g'.no_parallel_capacity)
  then have "f' (v, u) = 0"
    by (metis nle_le p_con.cap_le p_con.g'.cap_non_negative)
  then show "cf_of (augment f') (u, v) = g'.subtract_graph f' (u, v)" unfolding g'.subtract_graph_def residualGraph_def augment_def apply auto
    using Irreducible_Graph.no_parallel_edge Irreducible_Graph_axioms apply blast
    using \<open>stl (u, v) \<noteq> 0\<close> cap_compatible cap_nonzero residualGraph_alt apply fastforce
     apply (metis \<open>stl (u, v) \<noteq> 0\<close> add_diff_cancel_right' cap_compatible cap_nonzero diff_ge_0_iff_ge f_non_negative flow_of_cf_def fo_rg_inv le_add_diff_inverse)
    using \<open>stl (u, v) \<noteq> 0\<close> cap_nonzero cf_def by fastforce
qed
end

context
  fixes stl p
  assumes SPU: "ST_Shortest_Path_Union stl cf s t"
      and PATH: "Graph.isPath stl s p t"
begin
interpretation ST_Shortest_Path_Union stl cf s t using SPU .
thm pathCap_eq

interpretation g': Irreducible_Graph stl
  unfolding Irreducible_Graph_def Irreducible_Graph_axioms_def
  using no_parallel_edge cf.Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

(* TODO fix *)
thm subtract_augment_Subgraph[OF SPU g'.path_induced_graph_pos_contained]

lemma aux': "augmentingFlow p = g'.path_induced_graph p"
  unfolding augmentingFlow_alt
  using PATH g'.isPath_alt cf.Nonnegative_Graph_axioms by (auto simp: path_induced_graph_eq)


lemma aux: "Subgraph (g'.subtract_path p) (cf_of (augment (augmentingFlow p)))"
  unfolding g'.subtract_path_alt aux'
  using subtract_augment_Subgraph[OF SPU g'.path_induced_graph_pos_contained] .
(* TODO fix and use this instead *)
(*
proof -
  have INDUCED: "augmentingFlow p = g'.path_induced_graph p" unfolding augmentingFlow_alt
    using PATH g'.isPath_alt cf.Nonnegative_Graph_axioms by (auto simp: path_induced_graph_eq)

  have "Contained_Graph (g'.path_induced_graph p) stl" using g'.path_induced_graph_pos_contained
    by (simp add: Contained_Graph.intro Le_Graph.cap_le Nonnegative_Graph.cap_non_negative Pos_Contained_Graph_def) (* TODO *)
  also have "Contained_Graph stl cf" by (simp add: Contained_Graph_axioms)
  finally have CONT: "Contained_Graph (g'.path_induced_graph p) cf" .

  show ?thesis unfolding g'.subtract_path_alt INDUCED augment_alt[OF CONT] sorry
qed
*)
end
thm aux

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
    also have "Subgraph ... n'.cf" using aux
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
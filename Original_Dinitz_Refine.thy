theory Original_Dinitz_Refine
  imports
    Original_Dinitz_Algo
    Original_Dinitz_Components
begin
text \<open>This theory takes the abstract definition of the Original Dinitz algorithm and refines
      it towards a concrete version. The goal here is not yet to arrive at an executable version,
      but to refine it as much as possible without choosing a particular datatype representation
      or execution framework. The functions will thus still include simple, but not necessarily
      executable, primitives such as set operations.\<close>

text \<open>For several refinement proofs in this theory, we need an additional pattern for refine_dref_type\<close>
lemma RELATESI_in_spec:
  "RELATES R \<Longrightarrow> S \<le> (spec x. (x, y) \<in> R) \<Longrightarrow> S \<le> (spec x. (x, y) \<in> R)" .

subsection \<open>Restructuring\<close>
(* TODO the proofs in this locale are quite messy, fix *)
context RGraph
begin
definition dinitzPhaseRestructured :: "(_ graph \<times> bool) nres" where
  "dinitzPhaseRestructured \<equiv> do {
    stl \<leftarrow> spec c'. Dual_Shortest_Path_Union c' cf s t;
    (cf', _, _, changed) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, _, brk, _). \<not> brk)
      (\<lambda>(cf', stl', _, changed). do {
        p_opt \<leftarrow> select p. Graph.isPath stl' s p t;
        case p_opt of
          None \<Rightarrow> return (cf', stl', True, changed)
        | Some p \<Rightarrow> do {
            stl'' \<leftarrow> return (Graph.subtract_path stl' p);
            cf' \<leftarrow> return (Graph.subtract_skew_path cf' p);
            stl'' \<leftarrow> spec c'. Dual_Path_Union c' stl'' s t;
            return (cf', stl'', False, True)}})
      (cf, stl, False, False);
    return (cf', changed)}"

definition dinitzPhaseRestructuredInvar :: "(_ graph \<times> _ graph \<times> bool \<times> bool) \<Rightarrow> bool" where
  "dinitzPhaseRestructuredInvar \<equiv> \<lambda>(cf', stl, brk, changed).
    RGraph c s t cf'
    \<and> Bounded_Dual_Shortest_Path_Union stl cf' s t (cf.min_dist s t)
    \<and> (Graph.connected cf' s t \<longrightarrow> cf.min_dist s t \<le> Graph.min_dist cf' s t)
    \<and> (brk \<longrightarrow> \<not> Graph.connected stl s t)
    \<and> (Flow.val c s f \<le> Flow.val c s (flow_of_cf cf'))
    \<and> (changed \<longleftrightarrow> cf' \<noteq> cf)
    \<and> (changed \<longrightarrow> cf.connected s t)"

lemma dinitzPhaseRestructuredInvar_alt:
  assumes "dinitzPhaseRestructuredInvar (cf', stl, brk, changed)"
  shows "f.dinitzPhaseInvar (flow_of_cf cf', stl)"
  using assms
  unfolding dinitzPhaseRestructuredInvar_def f.dinitzPhaseInvar_def
  by clarsimp (metis RGraph.is_NFlow RGraph.this_loc_rpg RPreGraph.rg_fo_inv)

lemma dual_spu_if_invar_and_path:
  assumes INVAR: "dinitzPhaseRestructuredInvar (cf', stl, brk, changed)"
    and PATH: "Graph.isPath stl s p t"
  shows "Dual_Shortest_Path_Union stl cf' s t"
proof -
  from INVAR interpret rg': RGraph c s t cf' unfolding dinitzPhaseRestructuredInvar_def by blast
  (*from INVAR interpret f': NFlow c s t "flow_of_cf cf'" unfolding f.dinitzPhaseInvar_def by blast*)
  have BOUND_EQ: "cf.min_dist s t = rg'.cf.min_dist s t"
  proof -
    from INVAR interpret Bounded_Dual_Shortest_Path_Union stl cf' s t "cf.min_dist s t"
      unfolding dinitzPhaseRestructuredInvar_def by simp
    show ?thesis
    proof (intro antisym)
      from PATH INVAR show "cf.min_dist s t \<le> rg'.cf.min_dist s t"
        unfolding dinitzPhaseRestructuredInvar_def Graph.connected_def
        using sub_path by auto

      from PATH have "rg'.cf.min_dist s t \<le> g'.min_dist s t"
        using isPath.connected sub_min_dist_geq by blast
      also have "... = length p" using PATH path_ascends_layer by force
      also have "... \<le> cf.min_dist s t" using PATH path_length_bounded by simp
      finally show "rg'.cf.min_dist s t \<le> cf.min_dist s t" .
    qed
  qed
  with INVAR show "Dual_Shortest_Path_Union stl cf' s t"
    unfolding dinitzPhaseRestructuredInvar_def using min_st_dist_bound by fastforce
qed

lemma dinitzPhaseRestructured_step:
  fixes cf' stl stl' changed
  assumes PATH: "Graph.isPath stl s p t"
      and CLEANED: "Dual_Path_Union stl' (Graph.subtract_path stl p) s t"
      and INVAR: "dinitzPhaseRestructuredInvar (cf', stl, False, changed)"
  defines "aug_cf' \<equiv> Graph.subtract_skew_path cf' p"
    shows "dinitzPhaseRestructuredInvar (aug_cf', stl', False, True) \<and> Graph.E stl' \<subset> Graph.E stl \<and> finite (Graph.E stl)"
  unfolding dinitzPhaseRestructuredInvar_def
proof (simp, intro conjI)
  interpret stl: Graph stl .
  interpret stl': Graph stl' .

  from INVAR have INVAR_UNFOLD: "RGraph c s t cf'"
    "Bounded_Dual_Shortest_Path_Union stl cf' s t (cf.min_dist s t)"
    "Graph.connected cf' s t \<longrightarrow> cf.min_dist s t \<le> Graph.min_dist cf' s t"
    "f.val \<le> Flow.val c s (flow_of_cf cf')"
    "changed = (cf' \<noteq> cf)"
    "changed \<longrightarrow> cf.connected s t"
    unfolding dinitzPhaseRestructuredInvar_def by auto

  then interpret rg': RGraph c s t cf' +
    old_bounded: Bounded_Dual_Shortest_Path_Union stl cf' s t "cf.min_dist s t" by simp_all

  from CLEANED have stl'_alt: "stl' = Graph.cleaning (Graph.subtract_path stl p) s t"
    using Dual_Path_Union_iff_cleaning by blast

  from PATH have "Graph.isPath cf' s p t" by (simp add: old_bounded.sub_path)
  then interpret p_pos_cont: Pos_Contained_Graph "Graph.path_induced_graph cf' p" cf'
    using rg'.f.cf.path_induced_graph_pos_contained by auto
  have aug_cf'_alt: "aug_cf' = cf_of (rg'.f.augment (rg'.f.augmentingFlow p))"
    unfolding aug_cf'_def rg'.cf.subtract_skew_path_alt rg'.f.augmentingFlow_alt
    using rg'.f.augment_alt' p_pos_cont.Contained_Graph_axioms by simp

  from INVAR PATH have FLOW_INVAR:
    "f.dinitzPhaseInvar (rg'.f.augment (rg'.f.augmentingFlow p), stl')"
    and "stl'.E \<subset> stl.E" "finite (stl.E)"
    using dinitzPhaseRestructuredInvar_alt f.dinitzPhase_step stl'_alt rg'.f_def
    by metis+
  then show "stl'.E \<subset> stl.E" "finite (stl.E)" by simp_all
  from FLOW_INVAR show "RGraph c s t aug_cf'"
    "Bounded_Dual_Shortest_Path_Union stl' aug_cf' s t (cf.min_dist s t)"
    "Graph.connected aug_cf' s t \<longrightarrow> cf.min_dist s t \<le> Graph.min_dist aug_cf' s t"
    unfolding f.dinitzPhaseInvar_def aug_cf'_alt
    using NFlow.is_RGraph by auto
  then interpret aug_rg: RGraph c s t aug_cf' by blast
  from \<open>f.val \<le> Flow.val c s (flow_of_cf cf')\<close> have "f.val \<le> rg'.f.val" unfolding rg'.f_def .

  have "f.val < Flow.val c s (flow_of_cf aug_cf')"
  proof -
    have BOUND_EQ: "cf.min_dist s t = rg'.cf.min_dist s t"
    proof -
      (*from INVAR interpret Bounded_Dual_Shortest_Path_Union stl cf' s t "cf.min_dist s t"
        unfolding dinitzPhaseInvar_def by simp*)
      show ?thesis
      proof (intro antisym)
        from PATH INVAR show "cf.min_dist s t \<le> rg'.cf.min_dist s t"
          unfolding dinitzPhaseRestructuredInvar_def Graph.connected_def
          using old_bounded.sub_path by blast
  
        from PATH have "rg'.cf.min_dist s t \<le> stl.min_dist s t"
          using isPath.connected old_bounded.sub_min_dist_geq by blast
        also have "... = length p" using PATH old_bounded.path_ascends_layer by force
        also have "... \<le> cf.min_dist s t" using PATH old_bounded.path_length_bounded by simp
        finally show "rg'.cf.min_dist s t \<le> cf.min_dist s t" .
      qed
        qed
        then interpret stu: Dual_Shortest_Path_Union stl cf' s t
          using min_st_dist_bound old_bounded.Bounded_Dual_Shortest_Path_Union_axioms by fastforce
    have 0: "Flow rg'.f.cf s t (rg'.f.augmentingFlow p)"
      apply (intro rg'.f.augFlow_resFlow)
      unfolding rg'.f.isAugmentingPath_def
      using PATH rg'.f.cf.isShortestPath_alt stu.shortest_path_transfer rg'.rg_fo_inv by simp

    have 1: "rg'.f.isAugmentingPath p"
      by (metis Graph.isSimplePath_def PATH \<open>rg'.cf.isPath s p t\<close> old_bounded.paths_are_simple rg'.f.isAugmentingPath_def rg'.rg_is_cf)
    
    have "rg'.f.cf.isPath s p t" by (simp add: \<open>rg'.cf.isPath s p t\<close>)
    then have "0 < Flow.val rg'.f.cf s (rg'.f.augmentingFlow p)"
      using rg'.f.augFlow_val[OF 1] rg'.f.resCap_gzero_aux by simp
    with rg'.f.augment_flow_value[OF 0] have "rg'.f.val < Flow.val c s (rg'.f.augment (rg'.f.augmentingFlow p))"
      by simp
    with \<open>f.val \<le> Flow.val c s (flow_of_cf cf')\<close> show ?thesis
      unfolding rg'.f_def using aug_cf'_alt
      by (metis "0" Flow.axioms(1) NFlow.augment_flow_presv NPreflow.is_RPreGraph NPreflow_def RPreGraph.f_unique \<open>0 < Flow.val rg'.f.cf s (rg'.f.augmentingFlow p)\<close> \<open>Flow.val c s (rg'.f.augment (rg'.f.augmentingFlow p)) = rg'.f.val + Flow.val rg'.f.cf s (rg'.f.augmentingFlow p)\<close> add.commute add_strict_increasing aug_rg.is_NPreflow aug_rg.rg_fo_inv rg'.f_def rg'.is_NFlow)
  qed
  then show "f.val \<le> Flow.val c s (flow_of_cf aug_cf')" "aug_cf' \<noteq> cf" unfolding f_def by auto
  show "cf.connected s t"
    using INVAR_UNFOLD(5) INVAR_UNFOLD(6) \<open>rg'.cf.isPath s p t\<close> isPath.connected by blast
qed

definition dist_increasing_cf
  where "dist_increasing_cf cf' \<equiv>
    RGraph c s t cf' \<and> (Graph.connected cf' s t \<longrightarrow> cf.min_dist s t < Graph.min_dist cf' s t)"

lemma dinitzPhaseRestructured_final:
  fixes cf' stl
    assumes INVAR: "dinitzPhaseRestructuredInvar (cf', stl, True, changed)"
    shows "dist_increasing_cf cf'"
  unfolding dist_increasing_cf_def
proof
  from INVAR show "RGraph c s t cf'" unfolding dinitzPhaseRestructuredInvar_def by blast
  then interpret rg': RGraph c s t cf' .

  from INVAR interpret Bounded_Dual_Shortest_Path_Union stl cf' s t "cf.min_dist s t"
    unfolding dinitzPhaseRestructuredInvar_def by blast
  from INVAR have "\<not> Graph.connected stl s t" unfolding dinitzPhaseRestructuredInvar_def by blast
  then show "rg'.cf.connected s t \<longrightarrow> cf.min_dist s t < rg'.cf.min_dist s t"
    by (metis Bounded_Dual_Shortest_Path_Union_axioms Dual_Shortest_Path_Union.st_connected_iff le_eq_less_or_eq linorder_neqE_nat min_st_dist_bound)
qed

definition "dinitzPhaseRestructured_wf_rel \<equiv> inv_image
  (less_than_bool <*lex*> finite_psubset)
  (\<lambda>(_, stl, brk, _). (\<not>brk, Graph.E stl))"

lemma dinitzPhaseRestructured_correct:
  "dinitzPhaseRestructured \<le> SPEC (\<lambda>(cf', changed). dist_increasing_cf cf' \<and> changed = (cf' \<noteq> cf) \<and> (changed \<longrightarrow> cf.connected s t))"
  unfolding dinitzPhaseRestructured_def
  apply (refine_vcg WHILET_rule[where I=dinitzPhaseRestructuredInvar and R=dinitzPhaseRestructured_wf_rel])
              apply (all \<open>(simp add: dinitzPhaseRestructuredInvar_def; fail)?\<close>)
        apply (simp add: dinitzPhaseRestructured_wf_rel_def wf_lex_prod)
       apply (simp add: dinitzPhaseRestructuredInvar_def RGraph_axioms f_def min_st_dist_bound)
      apply (simp add: dinitzPhaseRestructured_step)
     apply (simp add: dinitzPhaseRestructured_step dinitzPhaseRestructured_wf_rel_def)
    apply (simp add: dinitzPhaseRestructuredInvar_def Graph.connected_def)
   apply (simp add: dinitzPhaseRestructured_wf_rel_def)
  by (simp add: dinitzPhaseRestructured_final)
end

context Network
begin

(* TODO we need only one of these to be an rgraph, check which is better *)
(*RGraph c s t cf \<and> *)
definition "cf_dist_rel \<equiv> {(cf', cf).
  RGraph c s t cf \<and>
  Graph.connected cf s t \<and> (\<not> Graph.connected cf' s t \<or> Graph.min_dist cf s t < Graph.min_dist cf' s t)}"

lemma cf_dist_rel_wf: "wf cf_dist_rel"
proof (rule wf_subset)
  let ?r = "less_than_bool <*lex*> (greater_bounded (card V))"
    and ?cf = "\<lambda>cf. (Graph.connected cf s t, Graph.min_dist cf s t)"

  show "wf (inv_image ?r ?cf)" by blast

  have "\<And>cf. RGraph c s t cf \<and> Graph.connected cf s t \<Longrightarrow> Graph.min_dist cf s t < card (Graph.V cf)"
    by (metis Finite_Graph.min_dist_less_V Finite_Graph_def Graph.distinct_nodes_in_V_if_connected(1) RGraph.this_loc_rpg RPreGraph.resV_netV finite_V t_not_s)
  moreover have "\<And>cf. RGraph c s t cf \<Longrightarrow> Graph.V cf \<subseteq> V"
    using RGraph.this_loc_rpg RPreGraph.resV_netV by blast
  ultimately have "\<And>cf. RGraph c s t cf \<and> Graph.connected cf s t \<Longrightarrow> Graph.min_dist cf s t < card V"
    by (meson card_mono dual_order.strict_trans1 finite_V)
  then show "cf_dist_rel \<subseteq> inv_image ?r ?cf"
    by (fastforce simp: cf_dist_rel_def greater_bounded_def)
qed

definition dinitzRestructured :: "_ flow nres" where
  "dinitzRestructured \<equiv> do {
    (cf, _) \<leftarrow> WHILE\<^sub>T snd (RGraph.dinitzPhaseRestructured s t \<circ> fst) (c, True);
    f \<leftarrow> return (flow_of_cf cf);
    return f}"

theorem dinitzRestructured_correct: "dinitzRestructured \<le> (spec f. isMaxFlow f)"
  unfolding dinitzRestructured_def
  apply (refine_vcg WHILET_rule[where I="\<lambda>(cf, m). RGraph c s t cf \<and> (m \<or> isMaxFlow (flow_of_cf cf))"
          and R="inv_image (less_than_bool <*lex*> cf_dist_rel) prod.swap"])
      apply (fastforce simp: cf_dist_rel_wf)
     apply (clarsimp_all simp: c_is_RGraph)
proof -
  fix cf
  assume RG: "RGraph c s t cf"
  then interpret RGraph c s t cf .
  have "dinitzPhaseRestructured \<le> SPEC (\<lambda>(cf', changed). dist_increasing_cf cf' \<and> changed = (cf' \<noteq> cf) \<and> (changed \<longrightarrow> cf.connected s t))"
    using dinitzPhaseRestructured_correct .
  also have "... \<le> (spec s'. (case s' of (cf', m) \<Rightarrow> RGraph c s t cf' \<and> (m \<or> isMaxFlow (flow_of_cf cf'))) \<and> (prod.swap s', True, cf) \<in> less_than_bool <*lex*> cf_dist_rel)"
  proof (clarsimp, intro conjI)
    fix cf'
    assume "dist_increasing_cf cf'" and CON_IF_NEQ: "(cf' \<noteq> cf) \<longrightarrow> cf.connected s t"
    then show "RGraph c s t cf'"
      unfolding dist_increasing_cf_def by simp
    then interpret rg': RGraph c s t cf' .
    from \<open>dist_increasing_cf cf'\<close> have DIST: "rg'.cf.connected s t \<longrightarrow> cf.min_dist s t < rg'.cf.min_dist s t"
      unfolding dist_increasing_cf_def by simp
    with CON_IF_NEQ RG show "cf' = cf \<or> cf' \<noteq> cf \<and> (cf', cf) \<in> cf_dist_rel" unfolding cf_dist_rel_def by blast
    from CON_IF_NEQ show "cf' = cf \<longrightarrow>  isMaxFlow (flow_of_cf cf)"
      by (metis DIST Graph.isPath_rtc Graph.isSimplePath_def cf.connected_edgeRtc f.isAugmentingPath_def f.noAugPath_iff_maxFlow f_def le_eq_less_or_eq linorder_not_le rg_fo_inv)
  qed
  finally show "dinitzPhaseRestructured
  \<le> (spec s'.
         (case s' of (cf', m) \<Rightarrow> RGraph c s t cf' \<and> (m \<or> isMaxFlow (flow_of_cf cf'))) \<and>
         (prod.swap s', True, cf) \<in> less_than_bool <*lex*> cf_dist_rel)" .
qed
end
\<comment> \<open>Restructuring\<close>
subsection \<open>Dinitz phase refinement\<close>

subsubsection \<open>Abstract version with assertions\<close>
context RGraph
begin
definition dinitzPhaseAssert :: "(_ graph \<times> bool) nres" where
  "dinitzPhaseAssert \<equiv> do {
    stl \<leftarrow> spec c'. Dual_Shortest_Path_Union c' cf s t;
    (cf', _, _, changed) \<leftarrow> WHILE\<^sub>T\<^bsup>dinitzPhaseRestructuredInvar\<^esup>
      (\<lambda>(_, _, brk, _). \<not> brk)
      (\<lambda>(cf', stl', _, changed). do {
        p_opt \<leftarrow> select p. Graph.isPath stl' s p t;
        case p_opt of
          None \<Rightarrow> return (cf', stl', True, changed)
        | Some p \<Rightarrow> do {
            assert (Graph.isPath stl' s p t);
            assert (Dual_Shortest_Path_Union stl' cf' s t);
            stl'' \<leftarrow> return (Graph.subtract_path stl' p);
            cf' \<leftarrow> return (Graph.subtract_skew_path cf' p);
            assert (Contained_Graph stl'' stl');
            assert (Graph.E stl' \<subseteq> Graph.E stl'' \<union> set p);
            stl'' \<leftarrow> spec c'. Dual_Path_Union c' stl'' s t;
            return (cf', stl'', False, True)}})
      (cf, stl, False, False);
    return (cf', changed)}"

lemma dinitzPhaseAssert_correct:
  "dinitzPhaseAssert \<le> SPEC (\<lambda>(cf', changed). dist_increasing_cf cf' \<and> changed = (cf' \<noteq> cf) \<and> (changed \<longrightarrow> cf.connected s t))"
  unfolding dinitzPhaseAssert_def
  apply (refine_vcg WHILEIT_rule[where R=dinitzPhaseRestructured_wf_rel])
                      apply (all \<open>(simp add: dinitzPhaseRestructuredInvar_def; fail)?\<close>)
              apply (simp add: dinitzPhaseRestructured_wf_rel_def wf_lex_prod)
          apply (simp add: dinitzPhaseRestructuredInvar_def RGraph_axioms f_def min_st_dist_bound)
         apply (fastforce  intro: dual_spu_if_invar_and_path)
        defer
        apply (simp add: Graph.subtract_path_alt) using Graph.subtract_graph_untouched_edges apply (metis (no_types, lifting) Graph.isPath_alt Graph.path_induced_graph_edges Int_Un_eq(4) Int_absorb1 Int_commute Un_Diff_cancel2 cf.isPath.simps(1) set_eq_subset t_not_s)
       apply (simp add: dinitzPhaseRestructured_step)
      apply (simp add: dinitzPhaseRestructured_step dinitzPhaseRestructured_wf_rel_def)
     apply (simp add: dinitzPhaseRestructuredInvar_def Graph.connected_def)
    apply (simp add: dinitzPhaseRestructured_wf_rel_def)
  apply (simp add: dinitzPhaseRestructured_final)
proof clarsimp_all
  fix cf' stl p changed
  assume INVAR: "dinitzPhaseRestructuredInvar (cf', stl, False, changed)"
     and PATH: "Graph.isPath stl s p t"
     and "Dual_Shortest_Path_Union stl cf' s t"
  (*interpret cf': Graph cf' .*)
  then interpret spu: Dual_Shortest_Path_Union stl cf' s t + rg': RGraph c s t cf'
    by (auto simp: dinitzPhaseRestructuredInvar_def)
  interpret rg'.cf: Nonnegative_Graph cf'
    using rg'.f.cf.Nonnegative_Graph_axioms by auto
  interpret spu.g': Nonnegative_Graph stl
    using rg'.cf.Nonnegative_Graph_axioms spu.sg_Nonnegative_Graph by blast
  (* TODO replace this with a simple 'have', need some way to use sublocale relations *)
  interpret subt_pos_cont: Pos_Contained_Graph "spu.g'.subtract_path p" stl
    unfolding spu.g'.subtract_path_alt
    using spu.g'.path_induced_graph_pos_contained Pos_Contained_Graph.subtract_le_contained by blast
  show "Contained_Graph (spu.g'.subtract_path p ) stl" by intro_locales
qed
end
\<comment> \<open>Abstract version with assertions\<close>

subsubsection \<open>Refining the assertion version\<close>
context RGraph
begin
definition dinitzPhaseRefine :: "(_ graph \<times> bool) nres" where
  "dinitzPhaseRefine \<equiv> do {
    stl \<leftarrow> cf.buildDualLayering s t;
    (cf', _, _, changed) \<leftarrow> WHILE\<^sub>T\<^bsup>dinitzPhaseRestructuredInvar\<^esup>
      (\<lambda>(_, _, brk, _). \<not> brk)
      (\<lambda>(cf', stl', _, changed). do {
        p_opt \<leftarrow> Graph.greedyPathFinding stl' s t;
        case p_opt of
          None \<Rightarrow> return (cf', stl', True, changed)
        | Some p \<Rightarrow> do {
            stl'' \<leftarrow> Graph.subtractPathRefine stl' p;
            cf' \<leftarrow> Graph.subtractSkewPathRefine cf' p;
            stl'' \<leftarrow> cleaningRefine p stl'';
            return (cf', stl'', False, True)}})
      (cf, stl, False, False);
    return (cf', changed)}"

lemma dinitzPhaseRefine_refine:
  notes [refine_dref_pattern] = RELATESI_in_spec
  shows "dinitzPhaseRefine \<le> \<Down> Id dinitzPhaseAssert"
  unfolding dinitzPhaseRefine_def dinitzPhaseAssert_def
proof (refine_rcg, refine_dref_type, clarsimp_all)
  show "cf.buildDualLayering s t \<le> (spec c'. Dual_Shortest_Path_Union c' cf s t)"
    using cf.buildDualLayering_correct .

  fix cf' stl' changed
  assume "dinitzPhaseRestructuredInvar (cf', stl', False, changed)"
  then interpret bdspu: Bounded_Dual_Shortest_Path_Union stl' cf' s t "cf.min_dist s t"
    unfolding dinitzPhaseRestructuredInvar_def by blast
  show "bdspu.g'.greedyPathFinding s t \<le> (select p. bdspu.g'.isPath s p t)"
    using bdspu.greedyPathFinding_correct .
next
  fix cf' stl' p changed
  assume "Dual_Shortest_Path_Union stl' cf' s t"
    and INVAR: "dinitzPhaseRestructuredInvar (cf', stl', False, changed)"
  then interpret dspu: Dual_Shortest_Path_Union stl' cf' s t by blast
  from INVAR interpret rg': RGraph c s t cf' unfolding dinitzPhaseRestructuredInvar_def by blast

  assume PATH: "dspu.g'.isPath s p t"
  then have "dspu.g'.subtractPathRefine p = return (dspu.g'.subtract_path p)"
    using dspu.g'.isSPath_distinct dspu.paths_are_simple dspu.g'.subtractPathRefine_correct by blast
  then show "dspu.g'.subtractPathRefine p \<le> RES {dspu.g'.subtract_path p}" by simp

  from PATH have "dspu.subtractSkewPathRefine p = return (dspu.subtract_skew_path p)"
    using dspu.g'.isSPath_distinct dspu.paths_are_simple dspu.subtractSkewPathRefine_correct by blast
  then show "dspu.subtractSkewPathRefine p \<le> RES {dspu.subtract_skew_path p}" by simp

  fix stl''
  assume "Contained_Graph stl'' stl'" "dspu.E' \<subseteq> Graph.E stl'' \<union> set p"
  with PATH show "cleaningRefine p stl'' \<le> (spec c''. Dual_Path_Union c'' stl'' s t)"
    using dspu.Finite_Graph_EI dspu.sub_Finite_Graph dspu.cleaningRefine_correct by blast
qed

lemma dinitzPhaseRefine_correct:
  "dinitzPhaseRefine \<le> SPEC (\<lambda>(cf', changed). dist_increasing_cf cf' \<and> changed = (cf' \<noteq> cf) \<and> (changed \<longrightarrow> cf.connected s t))"
  using dinitzPhaseRefine_refine dinitzPhaseAssert_correct by simp
end
\<comment> \<open>Refining the assertion version\<close>

subsection \<open>Dinitz outer loop refinement\<close>
context Network
begin
definition dinitzRefine :: "_ flow nres" where
  "dinitzRefine \<equiv> do {
    (cf, _) \<leftarrow> WHILE\<^sub>T snd (RGraph.dinitzPhaseRefine c s t \<circ> fst) (c, True);
    f \<leftarrow> return (flow_of_cf cf);
    return f}"

theorem dinitzRefine_correct: "dinitzRefine \<le> (spec f. isMaxFlow f)"
  unfolding dinitzRefine_def
  apply (refine_vcg WHILET_rule[where I="\<lambda>(cf, m). RGraph c s t cf \<and> (m \<or> isMaxFlow (flow_of_cf cf))"
          and R="inv_image (less_than_bool <*lex*> cf_dist_rel) prod.swap"])
      apply (fastforce simp: cf_dist_rel_wf)
     apply (clarsimp_all simp: c_is_RGraph)
proof -
  fix cf
  assume RG: "RGraph c s t cf"
  then interpret RGraph c s t cf .
  have "dinitzPhaseRefine \<le> SPEC (\<lambda>(cf', changed). dist_increasing_cf cf' \<and> changed = (cf' \<noteq> cf) \<and> (changed \<longrightarrow> cf.connected s t))"
    using dinitzPhaseRefine_correct .
  also have "... \<le> (spec s'. (case s' of (cf', m) \<Rightarrow> RGraph c s t cf' \<and> (m \<or> isMaxFlow (flow_of_cf cf'))) \<and> (prod.swap s', True, cf) \<in> less_than_bool <*lex*> cf_dist_rel)"
  proof (clarsimp, intro conjI)
    fix cf'
    assume "dist_increasing_cf cf'" and CON_IF_NEQ: "(cf' \<noteq> cf) \<longrightarrow> cf.connected s t"
    then show "RGraph c s t cf'"
      unfolding dist_increasing_cf_def by simp
    then interpret rg': RGraph c s t cf' .
    from \<open>dist_increasing_cf cf'\<close> have DIST: "rg'.cf.connected s t \<longrightarrow> cf.min_dist s t < rg'.cf.min_dist s t"
      unfolding dist_increasing_cf_def by simp
    with CON_IF_NEQ RG show "cf' = cf \<or> cf' \<noteq> cf \<and> (cf', cf) \<in> cf_dist_rel" unfolding cf_dist_rel_def by blast
    from CON_IF_NEQ show "cf' = cf \<longrightarrow>  isMaxFlow (flow_of_cf cf)"
      by (metis DIST Graph.isPath_rtc Graph.isSimplePath_def cf.connected_edgeRtc f.isAugmentingPath_def f.noAugPath_iff_maxFlow f_def le_eq_less_or_eq linorder_not_le rg_fo_inv)
  qed
  finally show "dinitzPhaseRefine
  \<le> (spec s'.
         (case s' of (cf', m) \<Rightarrow> RGraph c s t cf' \<and> (m \<or> isMaxFlow (flow_of_cf cf'))) \<and>
         (prod.swap s', True, cf) \<in> less_than_bool <*lex*> cf_dist_rel)" .
qed
end
\<comment> \<open>Dinitz outer loop refinement\<close>
end
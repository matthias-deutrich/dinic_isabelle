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
    \<and> min_dist_less_eq s t cf cf'
    \<and> (brk \<longrightarrow> \<not> Graph.connected stl s t)
    \<and> (Flow.val c s f \<le> Flow.val c s (flow_of_cf cf'))
    \<and> (changed \<longleftrightarrow> cf' \<noteq> cf)
    \<and> (changed \<longrightarrow> cf.connected s t)"

text \<open>This new invariant is an extended version of the old one. However, transitioning from an
      RGraph to a NFlow via flow_of_cf loses some information (namely that cf is nonnegative and
      has the same sum capacity for each node pair), so we need some additional information on the
      unfolded side.\<close>
lemma dinitzPhaseRestructuredInvar_alt: "dinitzPhaseRestructuredInvar (cf', stl, brk, changed) \<longleftrightarrow>
    RGraph c s t cf'
    \<and> f.dinitzPhaseInvar (flow_of_cf cf', stl)
    \<and> (brk \<longrightarrow> \<not> Graph.connected stl s t)
    \<and> f.val \<le> Flow.val c s (flow_of_cf cf')
    \<and> changed = (cf' \<noteq> cf)
    \<and> (changed \<longrightarrow> cf.connected s t)"
  unfolding dinitzPhaseRestructuredInvar_def f.dinitzPhaseInvar_def
  by (auto intro: RGraph.is_NFlow dest: RGraph.this_loc_rpg simp: RPreGraph.rg_fo_inv)

lemma dinitzPhaseRestructured_step:
  fixes cf' stl stl' changed
  assumes PATH: "Graph.isPath stl s p t"
      and CLEANED: "Dual_Path_Union stl' (Graph.subtract_path stl p) s t"
      and INVAR: "dinitzPhaseRestructuredInvar (cf', stl, False, changed)"
  defines "aug_cf' \<equiv> Graph.subtract_skew_path cf' p"
    shows "dinitzPhaseRestructuredInvar (aug_cf', stl', False, True) \<and> Graph.E stl' \<subset> Graph.E stl \<and> finite (Graph.E stl)"
proof -
  interpret cf': Graph cf' + stl: Graph stl + stl': Graph stl' . (* For prettier names *)
  from INVAR interpret Bounded_Dual_Shortest_Path_Union stl cf' s t "cf.min_dist s t" +
    rg': RGraph c s t cf' unfolding dinitzPhaseRestructuredInvar_def by auto

  have "RGraph c s t aug_cf'" "Bounded_Dual_Shortest_Path_Union stl' aug_cf' s t (cf.min_dist s t)"
    "min_dist_less_eq s t cf aug_cf'" "f.val \<le> Flow.val c s (flow_of_cf aug_cf')"
    "aug_cf' \<noteq> cf" "cf.connected s t" "stl'.E \<subset> stl.E" "finite stl.E"
  proof -
    let ?aug_f = "rg'.f.augment (rg'.f.augmentingFlow p)"

    have aug_cf'_alt: "aug_cf' = cf_of (?aug_f)"
    proof -
      from PATH have "cf'.isPath s p t" by (simp add: sub_path)
      then interpret p_pos_cont: Pos_Contained_Graph "cf'.path_induced_graph p" cf'
        using rg'.f.cf.path_induced_graph_pos_contained by auto
      show ?thesis
        unfolding aug_cf'_def cf'.subtract_skew_path_alt rg'.f.augmentingFlow_alt
        using rg'.f.augment_alt' p_pos_cont.Contained_Graph_axioms by simp
    qed

    from INVAR PATH CLEANED have STEP': "f.dinitzPhaseInvar (?aug_f, stl')
      \<and> stl'.E \<subset> stl.E \<and> finite stl.E"
      unfolding dinitzPhaseRestructuredInvar_alt rg'.f_def
      using f.dinitzPhase_step Dual_Path_Union_iff_cleaning by metis
    then interpret aug_f: NFlow c s t ?aug_f unfolding f.dinitzPhaseInvar_def by blast

    from STEP' show "RGraph c s t aug_cf'"
      "Bounded_Dual_Shortest_Path_Union stl' aug_cf' s t (cf.min_dist s t)"
      "min_dist_less_eq s t cf aug_cf'" "stl'.E \<subset> E'" "finite E'"
      unfolding f.dinitzPhaseInvar_def aug_cf'_alt
      using aug_f.is_RGraph by auto

    have "f.val < aug_f.val"
    proof -
      from PATH have AUG_PATH: "rg'.f.isAugmentingPath p"
        using Graph.isSimplePath_def rg'.f.isAugmentingPath_def paths_are_simple sub_path rg'.rg_is_cf
        by metis

      from INVAR have "f.val \<le> rg'.f.val"
        unfolding dinitzPhaseRestructuredInvar_def rg'.f_def by blast
      also from PATH have "... < rg'.f.val + rg'.f.resCap p"
        using rg'.f.resCap_gzero_aux sub_path by simp
      also from AUG_PATH have "... = aug_f.val"
        using rg'.f.augFlow_val rg'.f.augment_flow_value rg'.f.augFlow_resFlow by simp
      finally show ?thesis .
    qed
    then show "f.val \<le> Flow.val c s (flow_of_cf aug_cf')" "aug_cf' \<noteq> cf"
      using aug_cf'_alt aug_f.fo_rg_inv f_def by auto
  
    from INVAR PATH show "cf.connected s t"
      unfolding dinitzPhaseRestructuredInvar_def
      using isPath.connected sub_path by blast
  qed
  then show ?thesis unfolding dinitzPhaseRestructuredInvar_def by blast
qed

lemma dinitzPhaseRestructured_final:
  fixes cf' stl changed
  assumes INVAR: "dinitzPhaseRestructuredInvar (cf', stl, True, changed)"
  shows "RGraph c s t cf' \<and> (if changed then min_dist_less s t cf cf' else isMaxFlow (flow_of_cf cf'))"
proof -
  from INVAR have RG: "RGraph c s t cf'" and "Bounded_Dual_Shortest_Path_Union stl cf' s t (cf.min_dist s t)"
    "min_dist_less_eq s t cf cf'" "\<not> Graph.connected stl s t"
    "changed \<longleftrightarrow> cf' \<noteq> cf" "changed \<longrightarrow> cf.connected s t"
    unfolding dinitzPhaseRestructuredInvar_def by auto
  then have "changed \<Longrightarrow> min_dist_less s t cf cf'" "\<not> changed \<Longrightarrow> isMaxFlow (flow_of_cf cf')"
    unfolding min_dist_less_eq_def min_dist_less_def
    using Dual_Shortest_Path_Union.st_connected_iff min_st_dist_bound RGraph.res_max_if_discon
    by fastforce+
  with RG show ?thesis by simp
qed

lemma dinitzPhaseRestructured_correct:
  "dinitzPhaseRestructured \<le> SPEC (\<lambda>(cf', changed). RGraph c s t cf' \<and> (if changed then min_dist_less s t cf cf' else isMaxFlow (flow_of_cf cf')))"
  unfolding dinitzPhaseRestructured_def
  apply (refine_vcg WHILET_rule[where I=dinitzPhaseRestructuredInvar
        and R="inv_image (less_than_bool <*lex*> finite_psubset) (\<lambda>(_, stl, brk, _). (\<not>brk, Graph.E stl))"])
             apply (all \<open>(auto simp: dinitzPhaseRestructured_step dinitzPhaseRestructured_final; fail)?\<close>)
  by (simp_all add: dinitzPhaseRestructuredInvar_def RGraph_axioms f_def min_st_dist_bound Graph.connected_def)
end

context Network
begin
definition cf_dist_rel :: "(_ graph) rel"
  where "cf_dist_rel \<equiv> {(cf', cf). min_dist_less s t cf cf' \<and> RGraph c s t cf'}"

lemma cf_dist_wf: "wf cf_dist_rel"
  by (fastforce simp: cf_dist_rel_def dist_greater_rel_def RPreGraph.resV_netV
      dest: RGraph.this_loc_rpg intro: wf_subset[OF dist_greater_wf])

definition dinitzRestructured :: "_ flow nres" where
  "dinitzRestructured \<equiv> do {
    (cf, _) \<leftarrow> WHILE\<^sub>T snd (RGraph.dinitzPhaseRestructured s t \<circ> fst) (c, True);
    f \<leftarrow> return (flow_of_cf cf);
    return f}"

theorem dinitzRestructured_correct: "dinitzRestructured \<le> (spec f. isMaxFlow f)"
  unfolding dinitzRestructured_def
  apply (refine_vcg WHILET_rule[where I="\<lambda>(cf, m). RGraph c s t cf \<and> (m \<or> isMaxFlow (flow_of_cf cf))"
          and R="inv_image (less_than_bool <*lex*> cf_dist_rel) prod.swap"])
      apply (fastforce simp: cf_dist_wf)
     apply (simp_all add: c_is_RGraph)
  using SPEC_cons_rule by (fastforce simp: cf_dist_rel_def dest: RGraph.dinitzPhaseRestructured_correct)
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

lemma dinitzPhaseAssert_Dual_Shortest_Path_Union:
  assumes INVAR: "dinitzPhaseRestructuredInvar (cf', stl, False, changed)"
    and PATH: "Graph.isPath stl s p t"
  shows "Dual_Shortest_Path_Union stl cf' s t"
proof -
  interpret cf': Graph cf' + stl: Graph stl .
  from INVAR interpret Bounded_Dual_Shortest_Path_Union stl cf' s t "cf.min_dist s t"
    unfolding dinitzPhaseRestructuredInvar_def by blast
  have "cf.min_dist s t = cf'.min_dist s t"
  proof (intro antisym)
    from PATH INVAR show "cf.min_dist s t \<le> cf'.min_dist s t"
      unfolding dinitzPhaseRestructuredInvar_def Graph.connected_def min_dist_less_eq_def
      using sub_path by blast

    from PATH have "cf'.min_dist s t \<le> stl.min_dist s t"
      using isPath.connected sub_min_dist_geq by blast
    also have "... = length p" using PATH path_ascends_layer by force
    also have "... \<le> cf.min_dist s t" using PATH path_length_bounded by simp
    finally show "cf'.min_dist s t \<le> cf.min_dist s t" .
  qed
  with INVAR show ?thesis
    unfolding dinitzPhaseRestructuredInvar_def using min_st_dist_bound by fastforce
qed

lemma dinitzPhaseAssert_Contained_Graph:
  assumes INVAR: "dinitzPhaseRestructuredInvar (cf', stl, False, changed)"
    and PATH: "Graph.isPath stl s p t"
  shows "Contained_Graph (Graph.subtract_path stl p) stl"
proof -
  from INVAR interpret rg': RGraph c s t cf' + Bounded_Dual_Shortest_Path_Union stl cf' s t "cf.min_dist s t"
    unfolding dinitzPhaseRestructuredInvar_def by auto
  interpret tmp: Pos_Contained_Graph "g'.subtract_path p" stl
    unfolding g'.subtract_path_alt
    using Pos_Contained_Graph.subtract_le_contained Nonnegative_Graph.path_induced_graph_pos_contained
      sg_Nonnegative_Graph rg'.f.cf.Nonnegative_Graph_axioms by auto
  show ?thesis by intro_locales
qed

lemmas dinitzPhase_asserts = dinitzPhaseAssert_Dual_Shortest_Path_Union
  dinitzPhaseAssert_Contained_Graph
  Graph.subtract_path_untouched_edges

lemma dinitzPhaseAssert_correct:
  "dinitzPhaseAssert \<le> SPEC (\<lambda>(cf', changed). RGraph c s t cf' \<and> (if changed then min_dist_less s t cf cf' else isMaxFlow (flow_of_cf cf')))"
  unfolding dinitzPhaseAssert_def
  apply (refine_vcg WHILEIT_rule[where R="inv_image (less_than_bool <*lex*> finite_psubset) (\<lambda>(_, stl, brk, _). (\<not>brk, Graph.E stl))"])
                     apply (all \<open>(auto simp: dinitzPhaseRestructured_step dinitzPhaseRestructured_final dinitzPhase_asserts; fail)?\<close>)
  by (simp_all add: dinitzPhaseRestructuredInvar_def RGraph_axioms f_def min_st_dist_bound Graph.connected_def)
end
(*
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
end*)
\<comment> \<open>Abstract version with assertions\<close>

subsubsection \<open>Refining the assertion version\<close>
context RGraph
begin
definition dinitzPhaseRefine :: "(_ graph \<times> bool) nres" where
  "dinitzPhaseRefine \<equiv> do {
    stl \<leftarrow> cf.buildDualLayering s t;
    (cf', _, _, changed) \<leftarrow> WHILE\<^sub>T
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
  "dinitzPhaseRefine \<le> SPEC (\<lambda>(cf', changed). RGraph c s t cf' \<and> (if changed then min_dist_less s t cf cf' else isMaxFlow (flow_of_cf cf')))"
  using dinitzPhaseRefine_refine dinitzPhaseAssert_correct by simp
end
\<comment> \<open>Refining the assertion version\<close>

subsection \<open>Dinitz outer loop refinement\<close>
context Network
begin
definition dinitzRefine :: "_ flow nres" where
  "dinitzRefine \<equiv> do {
    (cf, _) \<leftarrow> WHILE\<^sub>T snd (RGraph.dinitzPhaseRefine s t \<circ> fst) (c, True);
    f \<leftarrow> return (flow_of_cf cf);
    return f}"

theorem dinitzRefine_correct: "dinitzRefine \<le> (spec f. isMaxFlow f)"
  unfolding dinitzRefine_def
  apply (refine_vcg WHILET_rule[where I="\<lambda>(cf, m). RGraph c s t cf \<and> (m \<or> isMaxFlow (flow_of_cf cf))"
          and R="inv_image (less_than_bool <*lex*> cf_dist_rel) prod.swap"])
      apply (fastforce simp: cf_dist_wf)
     apply (simp_all add: c_is_RGraph)
  using SPEC_cons_rule by (fastforce simp: cf_dist_rel_def dest: RGraph.dinitzPhaseRefine_correct)
end
\<comment> \<open>Dinitz outer loop refinement\<close>
end
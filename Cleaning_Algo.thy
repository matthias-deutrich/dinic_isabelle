theory Cleaning_Algo
  imports LayerMaintenance Graph_Transpose Refine_Imperative_HOL.Sepref_Foreach
begin




subsection \<open>LeftPass\<close>
(* TODO swap tuple *)
definition left_pass_refine :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "left_pass_refine Q c \<equiv> do {
    (c, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(_, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      u \<leftarrow> RES Q;
      let Q = Q - {u};
      if Graph.outgoing c u = {} then do {
        let L = Graph.incoming c u;
        let Q = Q \<union> (fst ` L);
        let c = removeEdges c L;
        RETURN (c, Q)}
      else RETURN (c, Q)
    }) (c, Q);
    RETURN c
  }"

context Finite_Bounded_Graph
begin
interpretation Dual_Graph_Algorithms "left_pass_refine Q" "right_pass_refine Q"
proof
  fix c :: "('capacity::linordered_idom) graph"
  note[refine_dref_RELATES] = RELATESI[of transpose_graph_rel]
  show "left_pass_refine Q c \<le> \<Down> transpose_graph_rel (right_pass_refine Q (transpose_graph c))"
    unfolding right_pass_refine_def left_pass_refine_def
    apply refine_rcg
    apply refine_dref_type
    by (auto simp: transpose_graph_rel_def removeEdges_def)

  show "right_pass_refine Q c \<le> \<Down> transpose_graph_rel (left_pass_refine Q (transpose_graph c))"
    unfolding right_pass_refine_def left_pass_refine_def
    apply refine_rcg
    apply refine_dref_type
    by (auto simp: transpose_graph_rel_def removeEdges_def)
qed

(* TODO cleanup proof *)
theorem left_pass_refine_correct:
  assumes T_NO_OUT: "outgoing t = {}"
    and Q_START: "t \<notin> Q" "\<forall>u \<in> V - Q - {t}. outgoing u \<noteq> {}" "finite Q"
  shows "left_pass_refine Q c \<le> RETURN (left_pass t c)"
  apply (intro transfer_return[where ret'="right_pass t"])
   apply (fastforce simp: right_pass_def left_pass_def)
  apply (intro Finite_Bounded_Graph.right_pass_refine_correct)
  using assms Finite_Bounded_Graph_axioms by (auto simp: converse_empty_simp)
  (*by (metis converse_converse converse_empty)*)
end



lemmas nfoldli_to_fold =
  foldli_eq_nfoldli[where c="\<lambda>_. True", symmetric, unfolded foldli_foldl foldl_conv_fold]

context Graph
begin

(* TODO impl *)
text \<open>See EdmondsKarp_Impl.augment_edge\<close>
definition subtract_edge :: "edge \<Rightarrow> 'capacity \<Rightarrow> _ graph" where
  "subtract_edge e cap \<equiv> c(e := c e - cap)"

text \<open>This is essentially the same as EdmondsKarp_Impl.resCap_cf_impl, except it works on any graph,
      not just the residual graph.\<close>
definition path_cap_algo :: "path \<Rightarrow> 'capacity nres" where
  "path_cap_algo p \<equiv> case p of
    [] \<Rightarrow> RETURN 0
  | (e # p) \<Rightarrow> nfoldli p (\<lambda>_. True) (\<lambda>e cap. RETURN (min (c e) cap)) (c e)"
thm Graph.subtract_path_def
definition subtract_path_algo :: "path \<Rightarrow> _ graph nres" where
  "subtract_path_algo p \<equiv> do {
    cap \<leftarrow> path_cap_algo p;
    c' \<leftarrow> nfoldli p (\<lambda>_. True) (\<lambda>e c'. RETURN (Graph.subtract_edge c' e cap)) c;
    RETURN c'
  }"


lemma path_cap_algo_correct: "path_cap_algo p = RETURN (if p = [] then 0 else pathCap p)"
  unfolding path_cap_algo_def pathCap_alt
  apply (simp split: list.split add: nfoldli_to_fold)
  by (metis (no_types, lifting) Min.set_eq_fold fold_map fun_comp_eq_conv list.set_map list.simps(15))

lemma subtract_path_algo_correct_aux:
  "distinct p \<Longrightarrow> fold (\<lambda>e c'. Graph.subtract_edge c' e cap) p c = (\<lambda>(u, v). if (u, v) \<in> set p then c (u, v) - cap else c (u, v))"
  unfolding Graph.subtract_edge_def by (induction p arbitrary: c) auto

lemma subtract_path_algo_correct:
  assumes "distinct p"
  shows "subtract_path_algo p \<le> RETURN (subtract_path p)"
  unfolding subtract_path_algo_def subtract_path_def
  apply (simp split: list.splits add: nfoldli_to_fold path_cap_algo_correct)
  using assms subtract_path_algo_correct_aux by simp

end

find_theorems Graph.pathVertices
find_theorems Graph.pathVertices_fwd

(* TODO invert *)
definition inner_path_vertices_algo :: "path \<Rightarrow> node list nres" where
  "inner_path_vertices_algo p \<equiv> case p of
    [] \<Rightarrow> RETURN []
  | (_ # p) \<Rightarrow> nfoldli p (\<lambda>_. True) (\<lambda>e us. RETURN (us @ [fst e])) []"

term butlast
term tl
find_theorems butlast tl
thm nfoldli_to_fold
context Graph
begin

find_theorems pathVertices "(@)"
find_theorems pathVertices_fwd "(@)"
thm pathVertices.induct
find_theorems name:induct "(@)"

thm rev_induct
thm pathVertices_alt
thm pathVertices.elims
thm pathVertices.simps

lemma inner_path_vertices_algo_correct:
  "inner_path_vertices_algo p = RETURN (tl (butlast (pathVertices u p)))"
proof (cases p)
  case Nil
  then show ?thesis unfolding inner_path_vertices_algo_def by auto
next
  case (Cons _ p')
  then show ?thesis
  proof (induction p' arbitrary: p rule: rev_induct)
    case Nil
    then show ?case unfolding inner_path_vertices_algo_def by auto
  next
    case (snoc x xs)
    then show ?case
      unfolding inner_path_vertices_algo_def
      apply (auto simp: nfoldli_to_fold elim: pathVertices.elims)
      by (smt (z3) Graph.pathVertices.simps(1) list.simps(8) list.simps(9) list_e_eq_lel(2) map_append pathVertices_alt snoc_eq_iff_butlast)
  qed
qed
end





definition cleaning_algo :: "node set \<Rightarrow> _ graph \<Rightarrow> (_ graph) nres" where
  "cleaning_algo Q c \<equiv> do {
    c \<leftarrow> right_pass_refine Q c;
    c \<leftarrow> left_pass_refine Q c;
    RETURN c}"

context Finite_Bounded_Graph
begin
thm right_pass_refine_correct
thm left_pass_refine_correct
find_theorems "Distance_Bounded_Graph c"

lemma cleaning_algo_correct:
  assumes S_NO_IN: "incoming s = {}"
    and T_NO_OUT: "outgoing t = {}"
    and Q_START: "s \<notin> Q" "t \<notin> Q" "\<forall>u \<in> V - Q - {s, t}. incoming u \<noteq> {} \<and> outgoing u \<noteq> {}" "finite Q"
  shows "cleaning_algo Q c \<le> RETURN (cleaning s t c)"
  unfolding cleaning_algo_def
proof (refine_vcg, simp)
  from T_NO_OUT \<open>\<forall>u \<in> V - Q - {s, t}. incoming u \<noteq> {} \<and> outgoing u \<noteq> {}\<close> have "\<forall>u \<in> V - Q - {s}. incoming u \<noteq> {}"
    by (cases "incoming t = {}") (auto simp: incoming_def outgoing_def V_def)
  with assms have "right_pass_refine Q c \<le> RETURN (right_pass s c)"
    by (blast intro: right_pass_refine_correct)
  also have "... \<le> SPEC (\<lambda>ca. left_pass_refine Q ca \<le> RES {cleaning s t c})"
  proof simp
    interpret Subgraph "right_pass s c" c using right_pass_Subgraph .
    have "left_pass_refine Q (right_pass s c) \<le> RETURN (left_pass t (right_pass s c))" (* TODO prettify *)
      apply (intro Finite_Bounded_Graph.left_pass_refine_correct)
          prefer 3 using assms apply simp
         prefer 4 using assms apply simp
        prefer 2 subgoal
        using \<open>outgoing t = {}\<close>
        unfolding Graph.outgoing_def Graph.E_def right_pass_def by simp
      unfolding Finite_Bounded_Graph_def apply auto[1]
      using edges_ss g'.Finite_Graph_EI rev_finite_subset apply blast
      using Distance_Bounded_Graph_axioms apply (rule sg_Distance_Bounded)
    proof
      fix u
      assume "u \<in> V' - Q - {t}"
      then have "outgoing u \<noteq> {}" (* TODO prettify *)
      proof (cases "outgoing s = {}")
        case True
        with S_NO_IN have "s \<notin> V" unfolding incoming_def outgoing_def V_def by blast
        then have "s \<notin> V'" using V_ss by blast
        with \<open>u \<in> V' - Q - {t}\<close> have "u \<noteq> s" by blast
        with assms \<open>u \<in> V' - Q - {t}\<close> show ?thesis using V_ss by blast
      next
        case False
        with \<open>u \<in> V' - Q - {t}\<close> show ?thesis using assms V_ss by auto
      qed
      then obtain v where "(u, v) \<in> E" by fast

      from \<open>u \<in> V' - Q - {t}\<close> have "u \<in> V'" by blast
      then have "connected s u" unfolding g'.V_def
        using S_Graph.rp_edges_s_connected connected_append_edge edge'_if_edge by blast
      with \<open>(u, v) \<in> E\<close> have "(u, v) \<in> E'"
        using S_Graph.s_connected_edges_remain by blast
      then show "g'.outgoing u \<noteq> {}" unfolding g'.outgoing_def by blast
    qed
    also have "... \<le> RES {cleaning s t c}"
      by (simp add: ST_Graph.left_right_pass_is_cleaning)
    finally show "left_pass_refine Q (right_pass s c) \<le> RES {cleaning s t c}" .
  qed
  finally show "right_pass_refine Q c \<le> SPEC (\<lambda>ca. left_pass_refine Q ca \<le> RES {cleaning s t c})" .
qed
end
end
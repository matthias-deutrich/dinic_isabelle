theory Cleaning_Algo
  imports LayerMaintenance Graph_Transpose Refine_Imperative_HOL.Sepref_Foreach
begin








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





end
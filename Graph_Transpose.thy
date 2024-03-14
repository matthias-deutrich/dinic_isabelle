theory Graph_Transpose
imports GraphUtils Refine_Monadic.Refine_Monadic
begin

definition transpose_graph :: "_ graph \<Rightarrow> _ graph" (*("(_\<inverse>)" [1000] 999)*) where
  "transpose_graph c \<equiv> c \<circ> prod.swap"

(*
abbreviation (input) transpose_syntax (infix "\<up>" 55)
  where "\<And>f f'. f\<up>f' \<equiv> NFlow.augment c f f'"
*)

lemma transpose_transpose[simp]: "transpose_graph (transpose_graph c) = c"
  unfolding transpose_graph_def by fastforce

lemma transpose_concrete: "(transpose_graph c) (u, v) = c (v, u)"
  unfolding transpose_graph_def by simp

lemma transpose_E: "Graph.E (transpose_graph c) = (Graph.E c)\<inverse>"
  unfolding Graph.E_def transpose_graph_def by auto

lemma transpose_V: "Graph.V (transpose_graph c) = Graph.V c"
  unfolding Graph.V_def by (auto simp: transpose_E)

lemma transpose_incoming: "Graph.incoming (transpose_graph c) = converse \<circ> Graph.outgoing c"
  unfolding Graph.incoming_def Graph.outgoing_def by (auto simp: transpose_E)

lemma transpose_outgoing: "Graph.outgoing (transpose_graph c) = converse \<circ> Graph.incoming c"
  unfolding Graph.incoming_def Graph.outgoing_def by (auto simp: transpose_E)

lemma transpose_adjacent: "Graph.adjacent (transpose_graph c) = converse \<circ> Graph.adjacent c"
  unfolding Graph.adjacent_def by (auto simp: transpose_incoming transpose_outgoing)

lemma transpose_incoming': "Graph.incoming' (transpose_graph c) = converse \<circ> Graph.outgoing' c"
  unfolding Graph.incoming'_def Graph.outgoing'_def by (auto simp: transpose_E)

lemma transpose_outgoing': "Graph.outgoing' (transpose_graph c) = converse \<circ> Graph.incoming' c"
  unfolding Graph.incoming'_def Graph.outgoing'_def by (auto simp: transpose_E)

lemma transpose_adjacent': "Graph.adjacent' (transpose_graph c) = converse \<circ> Graph.adjacent' c"
  unfolding Graph.adjacent'_def by (auto simp: transpose_incoming' transpose_outgoing')

(* TODO is_adj_map *)

lemma transpose_adjacent_nodes: "Graph.adjacent_nodes (transpose_graph c) = Graph.adjacent_nodes c"
  unfolding Graph.adjacent_nodes_def by (auto simp: transpose_E)

lemma transpose_Finite_Graph: "Finite_Graph (transpose_graph c) \<longleftrightarrow> Finite_Graph c"
  unfolding Finite_Graph_def by (auto simp: transpose_V)

definition transpose_path :: "edge list \<Rightarrow> edge list" where
  "transpose_path \<equiv> map prod.swap \<circ> rev"

lemma transpose_transpose_path[simp]: "transpose_path (transpose_path p) = p"
  unfolding transpose_path_def by (simp add: rev_map)

lemma transpose_path_length[simp]: "length (transpose_path p) = length p"
  unfolding transpose_path_def by auto

lemma transpose_isPath:
  "Graph.isPath (transpose_graph c) u p v \<longleftrightarrow> Graph.isPath c v (transpose_path p) u"
  by (induction p arbitrary: u) (auto simp: Graph.isPath.simps(1) Graph.isPath_head Graph.isPath_tail transpose_E transpose_path_def)

thm Graph.pathVertices_alt
(*lemma transpose_pathVertices: "Graph.pathVertices"*)
(* TODO pathVertices *)

lemma transpose_connected: "Graph.connected (transpose_graph c) u v \<longleftrightarrow> Graph.connected c v u"
  unfolding Graph.connected_def by (metis transpose_transpose transpose_isPath)

(* TODO reachableNodes *)

lemma transpose_isShortestPath:
  "Graph.isShortestPath (transpose_graph c) u p v \<longleftrightarrow> Graph.isShortestPath c v (transpose_path p) u"
  unfolding Graph.isShortestPath_def by (metis transpose_transpose transpose_isPath transpose_path_length)

lemma transpose_isSimplePath: (* TODO needs pathVertices, then add to simps *)
  "Graph.isSimplePath (transpose_graph c) u p v \<longleftrightarrow> Graph.isSimplePath c v (transpose_path p) u"
  unfolding Graph.isSimplePath_def oops

lemma transpose_dist: "Graph.dist (transpose_graph c) u d v \<longleftrightarrow> Graph.dist c v d u"
  unfolding Graph.dist_def by (metis transpose_transpose transpose_isPath transpose_path_length)

lemma transpose_min_dist:
  "\<lbrakk>Graph.connected c u v; Graph.connected c v u\<rbrakk> \<Longrightarrow> Graph.min_dist (transpose_graph c) u v = Graph.min_dist c v u"
  by (meson Graph.min_dist_is_dist Graph.min_dist_minD transpose_connected transpose_dist order_antisym_conv)

(* TODO add stuff from GraphUtils *)
lemma transpose_Distance_Bounded_Graph:
  "Distance_Bounded_Graph (transpose_graph c) b \<longleftrightarrow> Distance_Bounded_Graph c b"
  unfolding Distance_Bounded_Graph_def by (auto simp: transpose_dist)

corollary transpose_Finite_Bounded_Graph:
  "Finite_Bounded_Graph (transpose_graph c) b \<longleftrightarrow> Finite_Bounded_Graph c b"
  unfolding Finite_Bounded_Graph_def by (simp add: transpose_Finite_Graph transpose_Distance_Bounded_Graph)

text \<open>The following lemmas relate properties of the transposeed graph to the corresponding ones in the
      non-transposeed graph.\<close>
lemmas transpose_graph_simps[simp] =
  transpose_concrete
  transpose_E
  transpose_V
  transpose_incoming
  transpose_outgoing
  transpose_adjacent
  transpose_incoming'
  transpose_outgoing'
  transpose_adjacent'
  transpose_adjacent_nodes
  transpose_Finite_Graph
  transpose_isPath
  transpose_connected
  transpose_isShortestPath
  (* transpose_isSimplePath *)
  transpose_dist
  transpose_min_dist

  transpose_Distance_Bounded_Graph
  transpose_Finite_Bounded_Graph

subsection \<open>Refinement setup\<close>

thm conc_fun_chain
term conc_fun
term single_valued
find_theorems single_valued
thm br_sv
term br
thm br_def
thm galois_connection_def
find_theorems "_ = (\<lambda>_. True)"
thm Option.Option.option.pred_True
find_consts "_ \<Rightarrow> bool" name:True
thm Quot_True_def
term Quot_True
find_theorems single_valued "(\<Down>)"
thm conc_abs_swap

(* TODO how to express this more elegantly *)
definition transpose_graph_rel :: "(_ graph) rel" where
  "transpose_graph_rel \<equiv> {(c, transpose_graph c) | c. True}"

lemma transpose_graph_rel_alt: "transpose_graph_rel = br transpose_graph (\<lambda>_. True)"
  unfolding transpose_graph_rel_def br_def by blast

lemma transpose_graph_rel_sv: "single_valued transpose_graph_rel"
  unfolding transpose_graph_rel_alt by (rule br_sv)

lemma transpose_graph_rel_comp[simp]: "transpose_graph_rel O transpose_graph_rel = Id"
  unfolding transpose_graph_rel_def by fastforce

(* TODO improve or remove *)
thm Id_refine conc_abs_swap conc_fun_chain dual_order.eq_iff dual_order.refl dual_order.trans transpose_graph_rel_comp transpose_graph_rel_sv refine_IdD
lemma "\<Up> transpose_graph_rel = \<Down> transpose_graph_rel"
  apply (intro antisym)
   apply (metis Id_refine conc_abs_swap conc_fun_chain transpose_graph_rel_comp transpose_graph_rel_sv le_funI)
  by (metis (no_types, lifting) Id_refine conc_Id conc_abs_swap conc_fun_chain conc_trans id_apply transpose_graph_rel_comp transpose_graph_rel_sv le_funI)
  (*by (metis Id_refine conc_abs_swap conc_fun_chain dual_order.eq_iff dual_order.refl dual_order.trans transpose_graph_rel_comp transpose_graph_rel_sv refine_IdD)*)

locale Dual_Graph_Algorithms =
  fixes alg alg' :: "_ graph \<Rightarrow> _ graph nres"
  assumes dual_alg: "\<And>c. alg c = \<Down> transpose_graph_rel (alg' (transpose_graph c))"
begin
lemma dual_alg': "\<And>c. alg' c = \<Down> transpose_graph_rel (alg (transpose_graph c))"
  using dual_alg by (simp add: conc_fun_chain)

(* TODO rewrite conclusion? *)
term SPEC
term RES
term RETURN

lemma transfer_spec:
  fixes spec spec' :: "_ graph \<Rightarrow> _ graph" and c
  assumes dual_spec: "spec = transpose_graph \<circ> spec' \<circ> transpose_graph"
    and spec'_correct: "alg' (transpose_graph c) \<le> RETURN (spec' (transpose_graph c))"
  shows "alg c \<le> RETURN (spec c)"
proof -
  from assms dual_alg have "alg c \<le> \<Down> transpose_graph_rel (RETURN (transpose_graph (spec c)))"
    using ref_two_step by fastforce
  also have "... \<le> RETURN (spec c)" unfolding transpose_graph_rel_alt
    by (smt (verit, best) conc_fun_RETURN in_br_conv transpose_transpose lhs_step_SPEC pw_leI) (* TODO *)
  finally show ?thesis .
qed
end

(* TODO can it be sufficient to only show one direction? *)
lemma Dual_Graph_AlgorithmsI[intro]:
  assumes LE1: "\<And>c. alg c \<le> \<Down> transpose_graph_rel (alg' (transpose_graph c))"
    and LE2: "\<And>c. alg' c \<le> \<Down> transpose_graph_rel (alg (transpose_graph c))"
  shows "Dual_Graph_Algorithms alg alg'"
proof (unfold_locales, intro antisym)
  from LE1 show "\<And>c. alg c \<le> \<Down> transpose_graph_rel (alg' (transpose_graph c))" .
  from LE2 show "\<And>c. \<Down> transpose_graph_rel (alg' (transpose_graph c)) \<le> alg c"
    by (metis (no_types, lifting) conc_Id conc_fun_chain conc_trans dual_order.refl id_apply transpose_graph_rel_comp transpose_transpose)
qed

(* TODO sanity check *)
lemma
  assumes "\<And>c. alg c \<le> \<Down> transpose_graph_rel (alg' (transpose_graph c))"
  shows "\<And>c. alg' c \<le> \<Down> transpose_graph_rel (alg (transpose_graph c))"
  using assms oops
end
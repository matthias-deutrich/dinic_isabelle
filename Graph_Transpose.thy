theory Graph_Transpose
imports Graph_Utils Refine_Monadic.Refine_Monadic
begin

definition transpose_graph :: "_ graph \<Rightarrow> _ graph" ("(_\<^sup>T)" [1000] 999) where
  "c\<^sup>T \<equiv> c \<circ> prod.swap"

lemma transpose_transpose[simp]: "(c\<^sup>T)\<^sup>T = c"
  unfolding transpose_graph_def by fastforce

lemma transpose_concrete: "(c\<^sup>T) (u, v) = c (v, u)"
  unfolding transpose_graph_def by simp

lemma transpose_E: "Graph.E (c\<^sup>T) = (Graph.E c)\<inverse>"
  unfolding Graph.E_def transpose_graph_def by auto

lemma transpose_V: "Graph.V (c\<^sup>T) = Graph.V c"
  unfolding Graph.V_def by (auto simp: transpose_E)

lemma transpose_incoming: "Graph.incoming (c\<^sup>T) = converse \<circ> Graph.outgoing c"
  unfolding Graph.incoming_def Graph.outgoing_def by (auto simp: transpose_E)

lemma transpose_outgoing: "Graph.outgoing (c\<^sup>T) = converse \<circ> Graph.incoming c"
  unfolding Graph.incoming_def Graph.outgoing_def by (auto simp: transpose_E)

lemma transpose_adjacent: "Graph.adjacent (c\<^sup>T) = converse \<circ> Graph.adjacent c"
  unfolding Graph.adjacent_def by (auto simp: transpose_incoming transpose_outgoing)

lemma transpose_incoming': "Graph.incoming' (c\<^sup>T) = converse \<circ> Graph.outgoing' c"
  unfolding Graph.incoming'_def Graph.outgoing'_def by (auto simp: transpose_E)

lemma transpose_outgoing': "Graph.outgoing' (c\<^sup>T) = converse \<circ> Graph.incoming' c"
  unfolding Graph.incoming'_def Graph.outgoing'_def by (auto simp: transpose_E)

lemma transpose_adjacent': "Graph.adjacent' (c\<^sup>T) = converse \<circ> Graph.adjacent' c"
  unfolding Graph.adjacent'_def by (auto simp: transpose_incoming' transpose_outgoing')

(* TODO is_adj_map *)

lemma transpose_adjacent_nodes: "Graph.adjacent_nodes (c\<^sup>T) = Graph.adjacent_nodes c"
  unfolding Graph.adjacent_nodes_def by (auto simp: transpose_E)

lemma transpose_Finite_Graph: "Finite_Graph (c\<^sup>T) \<longleftrightarrow> Finite_Graph c"
  unfolding Finite_Graph_def by (auto simp: transpose_V)

definition transpose_path :: "edge list \<Rightarrow> edge list" where
  "transpose_path \<equiv> map prod.swap \<circ> rev"

lemma transpose_transpose_path[simp]: "transpose_path (transpose_path p) = p"
  unfolding transpose_path_def by (simp add: rev_map)

lemma transpose_path_length[simp]: "length (transpose_path p) = length p"
  unfolding transpose_path_def by auto

lemma transpose_path_set[simp]: "set (transpose_path p) = (set p) \<inverse>"
  unfolding transpose_path_def by auto

lemma transpose_isPath:
  "Graph.isPath (c\<^sup>T) u p v \<longleftrightarrow> Graph.isPath c v (transpose_path p) u"
  by (induction p arbitrary: u) (auto simp: Graph.isPath.simps(1) Graph.isPath_head Graph.isPath_tail transpose_E transpose_path_def)

thm Graph.pathVertices_alt
(*lemma transpose_pathVertices: "Graph.pathVertices"*)
(* TODO pathVertices *)

lemma transpose_connected: "Graph.connected (c\<^sup>T) u v \<longleftrightarrow> Graph.connected c v u"
  unfolding Graph.connected_def by (metis transpose_transpose transpose_isPath)

(* TODO reachableNodes *)

lemma transpose_isShortestPath:
  "Graph.isShortestPath (c\<^sup>T) u p v \<longleftrightarrow> Graph.isShortestPath c v (transpose_path p) u"
  unfolding Graph.isShortestPath_def by (metis transpose_transpose transpose_isPath transpose_path_length)

lemma transpose_isSimplePath: (* TODO needs pathVertices, then add to simps *)
  "Graph.isSimplePath (c\<^sup>T) u p v \<longleftrightarrow> Graph.isSimplePath c v (transpose_path p) u"
  unfolding Graph.isSimplePath_def oops

lemma transpose_dist: "Graph.dist (c\<^sup>T) u d v \<longleftrightarrow> Graph.dist c v d u"
  unfolding Graph.dist_def by (metis transpose_transpose transpose_isPath transpose_path_length)

lemma transpose_min_dist:
  "\<lbrakk>Graph.connected c u v; Graph.connected c v u\<rbrakk> \<Longrightarrow> Graph.min_dist (c\<^sup>T) u v = Graph.min_dist c v u"
  by (meson Graph.min_dist_is_dist Graph.min_dist_minD transpose_connected transpose_dist order_antisym_conv)

(* TODO add stuff from GraphUtils *)
lemma transpose_Distance_Bounded_Graph:
  "Distance_Bounded_Graph (c\<^sup>T) b \<longleftrightarrow> Distance_Bounded_Graph c b"
  unfolding Distance_Bounded_Graph_def by (auto simp: transpose_dist)

corollary transpose_Finite_Bounded_Graph:
  "Finite_Bounded_Graph (c\<^sup>T) b \<longleftrightarrow> Finite_Bounded_Graph c b"
  unfolding Finite_Bounded_Graph_def by (simp add: transpose_Finite_Graph transpose_Distance_Bounded_Graph)

text \<open>The following lemmas relate properties of the transposed graph to the corresponding ones in the
      non-transposed graph.\<close>
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
find_theorems galois_connection "(\<Down>)"

(* TODO how to express this more elegantly *)
definition transpose_graph_rel :: "(_ graph) rel" where
  "transpose_graph_rel \<equiv> {(c, c\<^sup>T) | c. True}"

lemma transpose_graph_rel_alt: "transpose_graph_rel = br transpose_graph (\<lambda>_. True)"
  unfolding transpose_graph_rel_def br_def by blast

lemma transpose_graph_rel_sv: "single_valued transpose_graph_rel"
  unfolding transpose_graph_rel_alt by (rule br_sv)

lemma transpose_graph_rel_comp[simp]: "transpose_graph_rel O transpose_graph_rel = Id"
  unfolding transpose_graph_rel_def by fastforce

lemma transpose_graph_relI[intro]: "c' = c\<^sup>T \<Longrightarrow> (c, c') \<in> transpose_graph_rel"
  unfolding transpose_graph_rel_def by blast

lemma transpose_graph_relD[dest]: "(c, c') \<in> transpose_graph_rel \<Longrightarrow> c' = c\<^sup>T"
  unfolding transpose_graph_rel_def by blast

(* TODO improve or remove *)
thm Id_refine conc_abs_swap conc_fun_chain dual_order.eq_iff dual_order.refl dual_order.trans transpose_graph_rel_comp transpose_graph_rel_sv refine_IdD
lemma "\<Up> transpose_graph_rel = \<Down> transpose_graph_rel"
  apply (intro antisym)
   apply (metis Id_refine conc_abs_swap conc_fun_chain transpose_graph_rel_comp transpose_graph_rel_sv le_funI)
  by (metis (no_types, lifting) Id_refine conc_Id conc_abs_swap conc_fun_chain conc_trans id_apply transpose_graph_rel_comp transpose_graph_rel_sv le_funI)
  (*by (metis Id_refine conc_abs_swap conc_fun_chain dual_order.eq_iff dual_order.refl dual_order.trans transpose_graph_rel_comp transpose_graph_rel_sv refine_IdD)*)

locale Dual_Graph_Algorithms =
  fixes alg alg' :: "_ graph \<Rightarrow> _ graph nres"
  assumes dual_alg: "\<And>c. alg c = \<Down> transpose_graph_rel (alg' (c\<^sup>T))"
begin
lemma dual_alg': "\<And>c. alg' c = \<Down> transpose_graph_rel (alg (c\<^sup>T))"
  using dual_alg by (simp add: conc_fun_chain)

lemma conc_simp: "\<Down> transpose_graph_rel (alg c) = alg' (c\<^sup>T)"
  using dual_alg' by simp

lemma conc_simp': "\<Down> transpose_graph_rel (alg' c) = alg (c\<^sup>T)"
  using dual_alg by simp
end

(* TODO can it be sufficient to only show one direction? *)
lemma Dual_Graph_AlgorithmsI[intro]:
  assumes LE1: "\<And>c. alg c \<le> \<Down> transpose_graph_rel (alg' (c\<^sup>T))"
    and LE2: "\<And>c. alg' c \<le> \<Down> transpose_graph_rel (alg (c\<^sup>T))"
  shows "Dual_Graph_Algorithms alg alg'"
proof (unfold_locales, intro antisym)
  from LE1 show "\<And>c. alg c \<le> \<Down> transpose_graph_rel (alg' (c\<^sup>T))" .
  from LE2 show "\<And>c. \<Down> transpose_graph_rel (alg' (c\<^sup>T)) \<le> alg c"
    by (metis (no_types, lifting) conc_Id conc_fun_chain conc_trans dual_order.refl id_apply transpose_graph_rel_comp transpose_transpose)
qed

context Dual_Graph_Algorithms
begin

text \<open>Note: while the duality should hold for any graph, the correctness of the refinement can often
      only be shown for a concrete graph, as we may need some properties of the graph.\<close>
lemma transfer_abstract:
  assumes DUAL_ABST: "Dual_Graph_Algorithms abst abst'"
    and REF'_CORRECT: "alg' (c\<^sup>T) \<le> abst' (c\<^sup>T)"
  shows "alg c \<le> abst c"
  using assms ref_two_step dual_alg unfolding Dual_Graph_Algorithms_def by fastforce

lemma transfer_return:
  assumes DUAL_RET: "ret = transpose_graph \<circ> ret' \<circ> transpose_graph"
    and REF'_CORRECT: "alg' (c\<^sup>T) \<le> RETURN (ret' (c\<^sup>T))"
  shows "alg c \<le> RETURN (ret c)"
  apply (intro transfer_abstract[where abst'="RETURN \<circ> ret'"])
  using assms by (auto simp: in_br_conv transpose_graph_rel_alt)



thm comp_def
thm fcomp_def
term "(\<circ>)"
term "(\<circ>\<circ>)"
term "(\<circ>\<circ>\<circ>)"
(* TODO can we phrase this a nicer way? *)
lemma transfer_spec:
  assumes DUAL_SPEC: "\<And>c c'. spec c c' \<longleftrightarrow> spec' (c\<^sup>T) (c'\<^sup>T)"
    and REF'_CORRECT: "alg' (c\<^sup>T) \<le> SPEC (spec' (c\<^sup>T))"
  shows "alg c \<le> SPEC (spec c)"
  apply (intro transfer_abstract[where abst'="SPEC \<circ> spec'"])
  using assms by (auto simp: build_rel_SPEC transpose_graph_rel_alt)

(* TODO simplify proof *)
lemma transfer_res:
  assumes DUAL_RES: "res = (image transpose_graph) \<circ> res' \<circ> transpose_graph"
    and REF'_CORRECT: "alg' (c\<^sup>T) \<le> RES (res' (c\<^sup>T))"
  shows "alg c \<le> RES (res c)"
  apply (intro transfer_abstract[where abst'="RES \<circ> res'"])
proof
  fix c
  from DUAL_RES show "RES (res c) \<le> \<Down> transpose_graph_rel ((RES \<circ> res') (c\<^sup>T))"
    apply simp
    by (smt (verit, ccfv_threshold) Graph_Transpose.transpose_transpose RES_refine imageE in_br_conv transpose_graph_rel_alt)
  from DUAL_RES show "(RES \<circ> res') c \<le> \<Down> transpose_graph_rel (RES (res (c\<^sup>T)))"
    by (simp add: RES_refine in_br_conv transpose_graph_rel_alt)
next
  from REF'_CORRECT show "alg' (c\<^sup>T) \<le> (RES \<circ> res') (c\<^sup>T)" by simp
qed
end

(*
lemma
  assumes "\<And>c. alg c \<le> \<Down> transpose_graph_rel (alg' (c\<^sup>T))"
  shows "\<And>c. alg' c \<le> \<Down> transpose_graph_rel (alg (c\<^sup>T))"
  using assms oops
*)
end
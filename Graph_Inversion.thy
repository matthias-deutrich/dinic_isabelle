theory Graph_Inversion
imports GraphUtils Refine_Monadic.Refine_Monadic
begin

definition invert_graph :: "_ graph \<Rightarrow> _ graph" (*("(_\<inverse>)" [1000] 999)*) where
  "invert_graph c \<equiv> c \<circ> prod.swap"

(*
abbreviation (input) invert_syntax (infix "\<up>" 55)
  where "\<And>f f'. f\<up>f' \<equiv> NFlow.augment c f f'"
*)

lemma invert_invert[simp]: "invert_graph (invert_graph c) = c"
  unfolding invert_graph_def by fastforce

lemma invert_concrete: "(invert_graph c) (u, v) = c (v, u)"
  unfolding invert_graph_def by simp

lemma invert_E: "Graph.E (invert_graph c) = (Graph.E c)\<inverse>"
  unfolding Graph.E_def invert_graph_def by auto

lemma invert_V: "Graph.V (invert_graph c) = Graph.V c"
  unfolding Graph.V_def by (auto simp: invert_E)

lemma invert_incoming: "Graph.incoming (invert_graph c) = converse \<circ> Graph.outgoing c"
  unfolding Graph.incoming_def Graph.outgoing_def by (auto simp: invert_E)

lemma invert_outgoing: "Graph.outgoing (invert_graph c) = converse \<circ> Graph.incoming c"
  unfolding Graph.incoming_def Graph.outgoing_def by (auto simp: invert_E)

lemma invert_adjacent: "Graph.adjacent (invert_graph c) = converse \<circ> Graph.adjacent c"
  unfolding Graph.adjacent_def by (auto simp: invert_incoming invert_outgoing)

lemma invert_incoming': "Graph.incoming' (invert_graph c) = converse \<circ> Graph.outgoing' c"
  unfolding Graph.incoming'_def Graph.outgoing'_def by (auto simp: invert_E)

lemma invert_outgoing': "Graph.outgoing' (invert_graph c) = converse \<circ> Graph.incoming' c"
  unfolding Graph.incoming'_def Graph.outgoing'_def by (auto simp: invert_E)

lemma invert_adjacent': "Graph.adjacent' (invert_graph c) = converse \<circ> Graph.adjacent' c"
  unfolding Graph.adjacent'_def by (auto simp: invert_incoming' invert_outgoing')

(* TODO is_adj_map *)

lemma invert_adjacent_nodes: "Graph.adjacent_nodes (invert_graph c) = Graph.adjacent_nodes c"
  unfolding Graph.adjacent_nodes_def by (auto simp: invert_E)

lemma invert_Finite_Graph: "Finite_Graph (invert_graph c) \<longleftrightarrow> Finite_Graph c"
  unfolding Finite_Graph_def by (auto simp: invert_V)

definition invert_path :: "edge list \<Rightarrow> edge list" where
  "invert_path \<equiv> map prod.swap \<circ> rev"

lemma invert_invert_path[simp]: "invert_path (invert_path p) = p"
  unfolding invert_path_def by (simp add: rev_map)

lemma invert_path_length[simp]: "length (invert_path p) = length p"
  unfolding invert_path_def by auto

lemma invert_isPath:
  "Graph.isPath (invert_graph c) u p v \<longleftrightarrow> Graph.isPath c v (invert_path p) u"
  by (induction p arbitrary: u) (auto simp: Graph.isPath.simps(1) Graph.isPath_head Graph.isPath_tail invert_E invert_path_def)

thm Graph.pathVertices_alt
(*lemma invert_pathVertices: "Graph.pathVertices"*)
(* TODO pathVertices *)

lemma invert_connected: "Graph.connected (invert_graph c) u v \<longleftrightarrow> Graph.connected c v u"
  unfolding Graph.connected_def by (metis invert_invert invert_isPath)

(* TODO reachableNodes *)

lemma invert_isShortestPath:
  "Graph.isShortestPath (invert_graph c) u p v \<longleftrightarrow> Graph.isShortestPath c v (invert_path p) u"
  unfolding Graph.isShortestPath_def by (metis invert_invert invert_isPath invert_path_length)

lemma invert_isSimplePath: (* TODO needs pathVertices, then add to simps *)
  "Graph.isSimplePath (invert_graph c) u p v \<longleftrightarrow> Graph.isSimplePath c v (invert_path p) u"
  unfolding Graph.isSimplePath_def oops

lemma invert_dist: "Graph.dist (invert_graph c) u d v \<longleftrightarrow> Graph.dist c v d u"
  unfolding Graph.dist_def by (metis invert_invert invert_isPath invert_path_length)

lemma invert_min_dist:
  "\<lbrakk>Graph.connected c u v; Graph.connected c v u\<rbrakk> \<Longrightarrow> Graph.min_dist (invert_graph c) u v = Graph.min_dist c v u"
  by (meson Graph.min_dist_is_dist Graph.min_dist_minD invert_connected invert_dist order_antisym_conv)

(* TODO add stuff from GraphUtils *)

text \<open>The following lemmas relate properties of the inverted graph to the corresponding ones in the
      non-inverted graph.\<close>
lemmas invert_graph_simps[simp] =
  invert_concrete
  invert_E
  invert_V
  invert_incoming
  invert_outgoing
  invert_adjacent
  invert_incoming'
  invert_outgoing'
  invert_adjacent'
  invert_adjacent_nodes
  invert_Finite_Graph
  invert_isPath
  invert_connected
  invert_isShortestPath
  (* invert_isSimplePath *)
  invert_dist
  invert_min_dist

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
definition invert_graph_rel :: "(_ graph) rel" where
  "invert_graph_rel \<equiv> {(c, invert_graph c) | c. True}"

lemma invert_graph_rel_alt: "invert_graph_rel = br invert_graph (\<lambda>_. True)"
  unfolding invert_graph_rel_def br_def by blast

lemma invert_graph_rel_sv: "single_valued invert_graph_rel"
  unfolding invert_graph_rel_alt by (rule br_sv)

lemma invert_graph_rel_comp[simp]: "invert_graph_rel O invert_graph_rel = Id"
  unfolding invert_graph_rel_def by fastforce

(* TODO improve or remove *)
thm Id_refine conc_abs_swap conc_fun_chain dual_order.eq_iff dual_order.refl dual_order.trans invert_graph_rel_comp invert_graph_rel_sv refine_IdD
lemma "\<Up> invert_graph_rel = \<Down> invert_graph_rel"
  apply (intro antisym)
   apply (metis Id_refine conc_abs_swap conc_fun_chain invert_graph_rel_comp invert_graph_rel_sv le_funI)
  by (metis (no_types, lifting) Id_refine conc_Id conc_abs_swap conc_fun_chain conc_trans id_apply invert_graph_rel_comp invert_graph_rel_sv le_funI)
  (*by (metis Id_refine conc_abs_swap conc_fun_chain dual_order.eq_iff dual_order.refl dual_order.trans invert_graph_rel_comp invert_graph_rel_sv refine_IdD)*)

locale Dual_Graph_Algorithms =
  fixes alg alg' :: "_ graph \<Rightarrow> _ graph nres"
  assumes dual_alg: "\<And>c. alg c = \<Down> invert_graph_rel (alg' (invert_graph c))"
begin
lemma dual_alg': "\<And>c. alg' c = \<Down> invert_graph_rel (alg (invert_graph c))"
  using dual_alg by (simp add: conc_fun_chain)
end

(* TODO can it be sufficient to only show one direction? *)
lemma Dual_Graph_AlgorithmsI[intro]:
  assumes LE1: "\<And>c. alg c \<le> \<Down> invert_graph_rel (alg' (invert_graph c))"
    and LE2: "\<And>c. alg' c \<le> \<Down> invert_graph_rel (alg (invert_graph c))"
  shows "Dual_Graph_Algorithms alg alg'"
proof (unfold_locales, intro antisym)
  from LE1 show "\<And>c. alg c \<le> \<Down> invert_graph_rel (alg' (invert_graph c))" .
  from LE2 show "\<And>c. \<Down> invert_graph_rel (alg' (invert_graph c)) \<le> alg c"
    by (metis (no_types, lifting) conc_Id conc_fun_chain conc_trans dual_order.refl id_apply invert_graph_rel_comp invert_invert)
qed

(* TODO sanity check *)
lemma
  assumes "\<And>c. alg c \<le> \<Down> invert_graph_rel (alg' (invert_graph c))"
  shows "\<And>c. alg' c \<le> \<Down> invert_graph_rel (alg (invert_graph c))"
  using assms oops
end
theory Graph_Inversion
imports GraphUtils
begin

definition invert_graph :: "_ graph \<Rightarrow> _ graph" (*("(_\<inverse>)" [1000] 999)*) where
  "invert_graph c \<equiv> c \<circ> prod.swap"

(*
abbreviation (input) invert_syntax (infix "\<up>" 55)
  where "\<And>f f'. f\<up>f' \<equiv> NFlow.augment c f f'"
*)

lemma invert_invert[simp]: "invert_graph (invert_graph c) = c"
  unfolding invert_graph_def by fastforce

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

end
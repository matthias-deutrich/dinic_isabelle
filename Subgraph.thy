theory Subgraph
imports GraphUtils
begin

(* TODO check whether this definition is actually still useful, or whether it should be dropped in favor of the locale *)
definition isSubgraph :: "_ graph \<Rightarrow> _ graph \<Rightarrow> bool"
  where "isSubgraph c' c \<equiv> \<forall>e. c' e = c e \<or> c' e = 0"

definition isProperSubgraph :: "_ graph \<Rightarrow> _ graph \<Rightarrow> bool"
  where "isProperSubgraph c' c \<equiv> isSubgraph c' c \<and> (\<exists>e. c' e \<noteq> c e)"

find_theorems "?P ?A ?B \<Longrightarrow> ?P ?B ?C \<Longrightarrow> ?P ?A ?C"

interpretation subgraph: order isSubgraph isProperSubgraph
  unfolding isSubgraph_def isProperSubgraph_def
  apply unfold_locales
  apply metis
  apply force+
  done
thm subgraph.order_trans
thm subgraph.order_refl
find_theorems "isProperSubgraph ?c' ?c \<Longrightarrow> isSubgraph ?c' ?c"

text \<open>This theory sets up a framework to compare graphs. Its two primary notions are liftings of
      different orders to the level of graphs:
      \<^item> Subgraph compares graphs using the subset relation of the edge set
      \<^item> Contained_Graph compares graphs using the linear order of the capacity type\<close>

text \<open>Fixes two graphs and sets up names. Note that, contrary to the usual naming scheme, the FIRST
      graph is denoted by g' and the second as g. This is because this is mostly used in contexts
      where the first graph is in some sense smaller than the second (either a subgraph or a contained
      graph),  and literature usually denotes the smaller graph as g'.\<close>
locale GraphComparison = g': Graph c' + Graph c
  for c' c :: "'capacity::linordered_idom graph"
begin
(*
notation g'.E ("E''")
notation g'.V ("V''")
*)
abbreviation "E' \<equiv> g'.E"
abbreviation "V' \<equiv> g'.V"

(*definition tmp where "tmp \<equiv> c' + c"*)
end

subsection \<open>Graphs with the same underlying capacity function\<close>

text \<open>We often want to compare graphs on the basis of their edge sets, ignoring the fact that they
      are derived from some capacity function. This section sets up the necessary locales.\<close>

(* TODO is there a way to automatically rename all constants in g' by appending a prime symbol? *)
(* TODO is there a better way to express the idea that both graphs are restrictions of the same function? *)
text \<open>This locale denotes two graphs that are restrictions of the same underlying capacity function
      to (potentially) different edge sets. This allows us to compare the graphs in a natural way
      by reasoning about their edge sets and automatically deriving the corresponding properties
      for the underlying capacity function.\<close>
locale CapacityCompatibleGraphs = GraphComparison c' c
  for c' c :: "'capacity::linordered_idom graph" +
  assumes cap_compatible: "c (u, v) = 0 \<or> c' (u, v) = 0 \<or> c (u, v) = c' (u, v)" (* TODO which is better style: this way or using \<forall> quantifier? *)
begin
lemma eq_if_E_eq[intro]: "E = E' \<Longrightarrow> c = c'"
  unfolding Graph.E_def using cap_compatible by fastforce
end

text \<open>Subgraphs are a lifting of the subset relation for edges of graphs with the same underlying
      capacity function. Note that, in accordance with most literature, g' will be the subgraph of g.\<close>
locale Subgraph = CapacityCompatibleGraphs c' c for c' c :: "'capacity::linordered_idom graph" +
  assumes E'_ss: "E' \<subseteq> E"
begin
lemma edge'_if_edge: "(u, v) \<in> E' \<Longrightarrow> (u, v) \<in> E" using E'_ss by blast (* TODO useful as intro? *)
lemma cap_nonzero: "c' (u, v) \<noteq> 0 \<Longrightarrow> c (u, v) \<noteq> 0" using E'_ss Graph.E_def' by blast

lemma c'_sg_c: "isSubgraph c' c"
  using cap_compatible E'_ss unfolding isSubgraph_def Graph.E_def by fastforce

lemma V_ss: "V' \<subseteq> V" unfolding Graph.V_def using E'_ss by blast

lemma sg_paths_are_base_paths: "g'.isPath u p v \<Longrightarrow> isPath u p v"
  by (induction rule: g'.isPath_front_induct) (auto intro: edge'_if_edge)

corollary sg_connected_remains_base_connected: "g'.connected u v \<Longrightarrow> connected u v"
  unfolding Graph.connected_def using sg_paths_are_base_paths by blast

lemma shortest_path_remains_if_contained: "\<lbrakk>g'.isPath u p v; isShortestPath u p v\<rbrakk> \<Longrightarrow> g'.isShortestPath u p v"
  using sg_paths_are_base_paths by (meson Graph.isShortestPath_def)

(* TODO is this the right location for this? *)
text \<open>Transfer lemmas\<close>
lemma sg_Distance_Bounded: "Distance_Bounded_Graph c b \<Longrightarrow> Distance_Bounded_Graph c' b"
  using sg_paths_are_base_paths by (metis Distance_Bounded_Graph_def Graph.dist_def)

lemma sg_Nonnegative_Graph: "Nonnegative_Graph c \<Longrightarrow> Nonnegative_Graph c'"
  unfolding Nonnegative_Graph_def by (metis Orderings.order_eq_iff cap_compatible cap_nonzero)

lemma CapacityCompatible_transfer:
  "CapacityCompatibleGraphs c c'' \<Longrightarrow> CapacityCompatibleGraphs c' c''"
  unfolding CapacityCompatibleGraphs_def using cap_compatible cap_nonzero by metis
end

lemma Subgraph_isSubgraphI[intro]: "isSubgraph c' c \<Longrightarrow> Subgraph c' c"
  unfolding isSubgraph_def by unfold_locales (force simp: Graph.E_def)+

(*
lemma Subgraph_CapComp_trans: "\<lbrakk>Subgraph c'' c'; CapacityCompatibleGraphs c' c\<rbrakk> \<Longrightarrow> CapacityCompatibleGraphs c'' c"
*)

locale Proper_Subgraph = CapacityCompatibleGraphs c' c
  for c' c :: "'capacity::linordered_idom graph"+
  assumes E'_pss: "E' \<subset> E"
begin
lemma c'_psg_c: "isProperSubgraph c' c"
  using cap_compatible E'_pss unfolding isProperSubgraph_def isSubgraph_def Graph.E_def by force

sublocale Subgraph using E'_pss by unfold_locales blast
end

lemma (in Subgraph) Proper_SubgraphI[intro]: "\<exists>e \<in> E. e \<notin> E' \<Longrightarrow> Proper_Subgraph c' c"
  using E'_ss by unfold_locales blast

lemma Proper_Subgraph_isProperSubgraphI[intro]: "isProperSubgraph c' c \<Longrightarrow> Proper_Subgraph c' c"
proof -
  assume PSG: "isProperSubgraph c' c"
  then interpret Subgraph c' c by auto
  from PSG obtain e where "c' e \<noteq> c e" unfolding isProperSubgraph_def by blast
  then show "Proper_Subgraph c' c" using E'_ss eq_if_E_eq by blast
qed

\<comment> \<open>Graphs with the same underlying capacity function\<close>

subsection "Contained Graphs"

definition le_graph :: "'capacity::linordered_idom graph \<Rightarrow> _ graph \<Rightarrow> bool"
  where "le_graph c' c \<equiv> \<forall>e. c' e \<le> c e"

definition less_graph :: "'capacity::linordered_idom graph \<Rightarrow> _ graph \<Rightarrow> bool"
  where "less_graph c' c \<equiv> (\<forall>e. c' e \<le> c e) \<and> (\<exists>e. c' e < c e)"

interpretation graph_cap_ord: order le_graph less_graph
  unfolding le_graph_def less_graph_def
  apply unfold_locales
  using less_le_not_le apply blast
    apply blast
  using order_trans apply blast
  using nle_le by blast

text \<open>Sometimes merely comparing two graphs based on their edge sets is insufficient, since we need
      to show properties that directly relate to their capacities.\<close>

(* TODO is there a more natural way to define this, as it is merely subtraction of functions? *)
definition (in Graph) subtract_graph :: "_ graph \<Rightarrow> _ graph"
  where "subtract_graph c' \<equiv> \<lambda> (u, v). c (u, v) - c' (u, v)"

locale Contained_Graph = GraphComparison c' c for c' c :: "'capacity:: linordered_idom graph" +
  assumes cap_abs_le:
    "(0 \<le> c' (u, v) \<and> c' (u, v) \<le> c (u, v)) \<or> (c (u, v) \<le> c' (u, v) \<and> c' (u, v) \<le> 0)"
begin
lemma contained_irreducible: "Irreducible_Graph c \<Longrightarrow> Irreducible_Graph c'"
  unfolding Irreducible_Graph_def
  by (metis (mono_tags, lifting) Irreducible_Graph_axioms_def Nonnegative_Graph_def cap_abs_le dual_order.antisym g'.E_def' mem_Collect_eq order_trans zero_cap_simp)

lemma subtract_contained: "Contained_Graph (subtract_graph c') c"
  unfolding subtract_graph_def using cap_abs_le by unfold_locales auto
end

sublocale Subgraph \<subseteq> Contained_Graph
  using cap_compatible cap_nonzero by unfold_locales (metis nle_le)

locale Le_Graph = GraphComparison c' c for c' c :: "'capacity:: linordered_idom graph" +
  assumes cap_le: "c' (u, v) \<le> c (u, v)"

locale Pos_Contained_Graph = Le_Graph c' c + g': Nonnegative_Graph c'
  for c' c :: "'capacity:: linordered_idom graph"
begin
sublocale Nonnegative_Graph c using cap_le g'.cap_non_negative by unfold_locales (metis order_trans)

sublocale Contained_Graph c' c using cap_le g'.cap_non_negative by unfold_locales blast

lemma subtract_le_contained: "Pos_Contained_Graph (subtract_graph c') c"
  unfolding subtract_graph_def using cap_le g'.cap_non_negative by unfold_locales auto
end

context Nonnegative_Graph
begin
definition pathCap :: "path \<Rightarrow> 'capacity"
  where "pathCap p \<equiv> Min {c e | e. e \<in> set p}"

(* TODO why is pathCap_def completely useless? problem also accurs in AugmentingPath.resCap*)
lemma pathCap_alt: "pathCap p = Min (c ` (set p))" unfolding pathCap_def
  by (metis Setcompr_eq_image)

definition path_induced_graph :: "path \<Rightarrow> _ graph"
  where "path_induced_graph p \<equiv> \<lambda> (u, v).
    if (u, v) \<in> set p then
      pathCap p
    else
      0"

lemma path_induced_graph_pos_contained_aux:
  "p \<noteq> [] \<Longrightarrow> 0 \<le> pathCap p" unfolding pathCap_alt using cap_non_negative by auto

lemma path_induced_graph_pos_contained:
  shows "Pos_Contained_Graph (path_induced_graph p) c"
  unfolding path_induced_graph_def apply unfold_locales
  using cap_non_negative apply (simp add: pathCap_alt)
  by (fastforce intro: path_induced_graph_pos_contained_aux)

definition subtract_path :: "path \<Rightarrow> _ graph"
  where "subtract_path p \<equiv> \<lambda>(u, v).
    if (u, v) \<in> (set p) then
      c (u, v) - pathCap p
    else
      c (u, v)"

lemma subtract_path_alt: "subtract_path p = subtract_graph (path_induced_graph p)"
  unfolding subtract_graph_def subtract_path_def path_induced_graph_def by auto

lemma nonempty_path_cap_positive: "\<lbrakk>p \<noteq> []; set p \<subseteq> E\<rbrakk> \<Longrightarrow> 0 < pathCap p" (* TODO necessary? *)
  unfolding pathCap_alt E_def by (auto intro!: le_neq_trans[OF cap_non_negative])
end


context Subgraph
begin
context
  assumes "Nonnegative_Graph c"
begin
interpretation Nonnegative_Graph c using \<open>Nonnegative_Graph c\<close> .
interpretation g': Nonnegative_Graph c' using Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

lemma pathCap_eq: "set p \<subseteq> E' \<Longrightarrow> g'.pathCap p = pathCap p"
proof -
  assume "set p \<subseteq> E'"
  then have "(c' ` set p) = (c ` set p)"
    by (smt (verit) c'_sg_c g'.E_def' image_cong isSubgraph_def mem_Collect_eq subsetD) (* TODO prettify *)
  then show ?thesis unfolding g'.pathCap_alt pathCap_alt by simp
qed

lemma subtract_path_maintains_Subgraph:
  "g'.isPath u p v \<Longrightarrow> Subgraph (g'.subtract_path p) (subtract_path p)"
proof (intro Subgraph_isSubgraphI, unfold isSubgraph_def, clarify)
  assume "g'.isPath u p v"
  then have P_CAP_EQ: "g'.pathCap p = pathCap p" using pathCap_eq g'.isPath_alt by blast

  fix u v
  assume "g'.subtract_path p (u, v) \<noteq> 0"
  then have C': "0 < c' (u, v)" unfolding g'.subtract_path_def g'.pathCap_alt
    apply (auto split: if_splits intro!: le_neq_trans[OF g'.cap_non_negative])
    by (metis List.finite_set Min_le Orderings.order_eq_iff empty_iff finite_imageI g'.pathCap_alt g'.path_induced_graph_pos_contained_aux image_eqI list.set(1))
  then have C_EQ_C': "c (u, v) = c' (u, v)"
    by (metis cap_compatible cap_nonzero less_numeral_extra(3))
  then show "g'.subtract_path p (u, v) = subtract_path p (u, v)"
    unfolding subtract_path_def g'.subtract_path_def using P_CAP_EQ by auto
qed
end
end

end
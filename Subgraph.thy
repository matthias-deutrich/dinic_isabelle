theory Subgraph
imports GraphUtils
begin

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

text \<open>Fixes two graphs and sets up names. Note that, contrary to the usual naming scheme, the FIRST
      graph is denoted by g' and the second as g. This is because this is mostly used in contexts
      where the first graph is a subgraph of the second and literature usually denotes the subgraph
      as g'.\<close>
locale GraphComparison = g': Graph c' + Graph c
  for c' :: "'capacity::linordered_idom graph" and c :: "'capacity graph"
begin
notation g'.E ("E''")
notation g'.V ("V''")
end

(* TODO is there a way to automatically rename all constants in g' by appending a prime symbol? *)
(* TODO is there a better way to express the idea that both graphs are restrictions of the same function? *)
text \<open>This locale denotes two graphs that are restrictions of the same underlying capacity function
      to (potentially) different edge sets. This allows us to compare the graphs in a natural way
      by reasoning about their edge sets and automatically deriving the corresponding properties
      for the underlying capacity function.\<close>
locale CapacityCompatibleGraphs = GraphComparison +
  assumes cap_compatible: "c (u, v) = 0 \<or> c' (u, v) = 0 \<or> c (u, v) = c' (u, v)"
begin
lemma eq_if_E_eq[intro]: "E = E' \<Longrightarrow> c = c'"
  unfolding Graph.E_def using cap_compatible by fastforce
end

text \<open>Subgraphs are a lifting of the subset relation for edges of graphs with the same underlying
      capacity function. Note that, in accordance with most literature, g' will be the subgraph of g.\<close>
locale Subgraph = CapacityCompatibleGraphs +
  assumes E_ss: "E' \<subseteq> E"
begin
lemma edge'_if_edge: "(u, v) \<in> E' \<Longrightarrow> (u, v) \<in> E" using E_ss by blast (* TODO useful as intro? *)

lemma c'_sg_c: "isSubgraph c' c"
  using cap_compatible E_ss unfolding isSubgraph_def Graph.E_def by fastforce

lemma V_ss: "V' \<subseteq> V" unfolding Graph.V_def using E_ss by blast

lemma sg_paths_are_base_paths: "g'.isPath u p v \<Longrightarrow> isPath u p v"
  by (induction rule: g'.isPath_front_induct) (auto intro: edge'_if_edge)

corollary sg_connected_remains_base_connected: "g'.connected u v \<Longrightarrow> connected u v"
  unfolding Graph.connected_def using sg_paths_are_base_paths by blast

lemma shortest_paths_remain_if_contained: "\<lbrakk>g'.isPath u p v; isShortestPath u p v\<rbrakk> \<Longrightarrow> g'.isShortestPath u p v"
  using sg_paths_are_base_paths by (meson Graph.isShortestPath_def)

(* TODO is this the right location for this? *)
lemma sg_Distance_Bounded: "Distance_Bounded_Graph c b \<Longrightarrow> Distance_Bounded_Graph c' b"
  using sg_paths_are_base_paths by (metis Distance_Bounded_Graph_def Graph.dist_def)
end

lemma Subgraph_isSubgraphI[intro]: "isSubgraph c' c \<Longrightarrow> Subgraph c' c"
  unfolding isSubgraph_def by unfold_locales(force simp: Graph.E_def)+

locale Proper_Subgraph = CapacityCompatibleGraphs +
  assumes E_pss: "E' \<subset> E"
begin
lemma c'_psg_c: "isProperSubgraph c' c"
  using cap_compatible E_pss unfolding isProperSubgraph_def isSubgraph_def Graph.E_def by force

sublocale Subgraph
  using c'_psg_c unfolding isProperSubgraph_def by blast
end

lemma (in Subgraph) Proper_SubgraphI[intro]: "\<exists>e \<in> E. e \<notin> E' \<Longrightarrow> Proper_Subgraph c' c"
  using E_ss by unfold_locales blast

lemma Proper_Subgraph_isProperSubgraphI[intro]: "isProperSubgraph c' c \<Longrightarrow> Proper_Subgraph c' c"
proof -
  assume PSG: "isProperSubgraph c' c"
  then interpret Subgraph c' c by auto
  from PSG obtain e where "c' e \<noteq> c e" unfolding isProperSubgraph_def by blast
  then show "Proper_Subgraph c' c" using E_ss eq_if_E_eq by blast
qed

(* TODO are the following locale necessary? *)
locale CapacityLeSubgraph = GraphComparison +
  assumes cap_abs_le: "\<forall>e. (0 \<le> c' e \<and> c' e \<le> c e) \<or> (c e \<le> c' e \<and> c' e \<le> 0)"

sublocale Subgraph \<subseteq> CapacityLeSubgraph
  using c'_sg_c
  unfolding CapacityLeSubgraph_def isSubgraph_def
  by (metis linorder_le_cases)

locale PosCapacityLeSubgraph = CapacityLeSubgraph +
  assumes caps_non_negative: "\<forall>e. 0 \<le> c e \<and> 0 \<le> c' e"
begin
lemma cap_le: "\<forall>e. c' e \<le> c e" using cap_abs_le caps_non_negative by (meson order.trans)
end

end
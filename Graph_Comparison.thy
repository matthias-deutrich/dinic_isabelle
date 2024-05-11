theory Graph_Comparison
  imports Graph_Utils
begin

(* TODO where is <for c' c :: "'capacity::linordered_idom graph"> necessary? *)

text \<open>This theory sets up a framework to compare graphs. Its two primary notions are liftings of
      different orders to the level of graphs:
      \<^item> Subgraph compares graphs using the subset relation of the edge set
      \<^item> Contained_Graph compares graphs using the linear order of the capacity type\<close>

text \<open>Fixes two graphs and sets up names. Note that, contrary to the usual naming scheme, the FIRST
      graph is denoted by g' and the second as g. This is because this is mostly used in contexts
      where the first graph is in some sense smaller than the second (either a subgraph or a contained
      graph),  and literature usually denotes the smaller graph as g'.\<close>
locale Graph_Comparison = g': Graph c' + Graph c for c' c :: "'capacity::linordered_idom graph"
begin
abbreviation "E' \<equiv> g'.E"
abbreviation "V' \<equiv> g'.V"
end

text \<open>Subset_Graphs are simply a lifting of the subset relation to edges of graphs.\<close>
locale Subset_Graph = Graph_Comparison +
  assumes E_ss: "E' \<subseteq> E"
begin
lemma edge'_if_edge: "(u, v) \<in> E' \<Longrightarrow> (u, v) \<in> E" using E_ss by blast (* TODO useful as intro? *)

lemma cap_nonzero: "c' (u, v) \<noteq> 0 \<Longrightarrow> c (u, v) \<noteq> 0" using E_ss Graph.E_def by blast

lemma V_ss: "V' \<subseteq> V" unfolding Graph.V_def using E_ss by blast

lemma vertex'_if_vertex: "u \<in> V' \<Longrightarrow> u \<in> V" using V_ss by blast

lemma sub_path: "g'.isPath u p v \<Longrightarrow> isPath u p v"
  by (induction rule: g'.isPath_front_induct) (auto intro: edge'_if_edge)

corollary sub_connected: "g'.connected u v \<Longrightarrow> connected u v"
  unfolding Graph.connected_def using sub_path by blast

(* TODO use more often *)
lemma sub_min_dist_geq: "g'.connected u v \<Longrightarrow> g'.min_dist u v \<ge> min_dist u v"
  by (metis Graph.isPath_distD Graph.isShortestPath_min_dist_def Graph.min_dist_minD g'.obtain_shortest_path sub_path)

lemma sub_shortest_path_if_contained: "\<lbrakk>g'.isPath u p v; isShortestPath u p v\<rbrakk> \<Longrightarrow> g'.isShortestPath u p v"
  using sub_path by (meson Graph.isShortestPath_def)

lemma incoming_ss: "g'.incoming u \<subseteq> incoming u"
  unfolding Graph.incoming_def using edge'_if_edge by blast

lemma outgoing_ss: "g'.outgoing u \<subseteq> outgoing u"
  unfolding Graph.outgoing_def using edge'_if_edge by blast

lemma sub_Distance_Bounded: "Distance_Bounded_Graph c b \<Longrightarrow> Distance_Bounded_Graph c' b"
  using sub_path by (metis Distance_Bounded_Graph_def Graph.dist_def)
end

subsection \<open>Graphs with the same underlying capacity function\<close>

text \<open>We often want to compare graphs on the basis of their edge sets, ignoring the fact that they
      are derived from some capacity function. This section sets up the necessary locales.\<close>

(* TODO is there a better way to express the idea that both graphs are restrictions of the same function? *)
text \<open>This locale denotes two graphs that are restrictions of the same underlying capacity function
      to (potentially) different edge sets. This allows us to compare the graphs in a natural way
      by reasoning about their edge sets and automatically deriving the corresponding properties
      for the underlying capacity function.\<close>
locale Capacity_Compatible = Graph_Comparison c' c for c' c :: "'capacity::linordered_idom graph" +
  assumes cap_compatible: "\<And>u v. c' (u, v) = 0 \<or> c (u, v) = 0 \<or> c' (u, v) = c (u, v)"
begin
lemma eq_if_E_eq[intro]: "E' = E \<Longrightarrow> c' = c"
  unfolding Graph.E_def using cap_compatible by fastforce
end

lemma CapComp_refl[simp, intro!]: "Capacity_Compatible c c"
  unfolding Capacity_Compatible_def by simp

lemma CapComp_comm: "Capacity_Compatible c' c \<Longrightarrow> Capacity_Compatible c c'"
  unfolding Capacity_Compatible_def by metis

(*
lemma CapComp_eq[intro]: "\<lbrakk>CapacityCompatibleGraphs c' c; Graph.E c' = Graph.E c\<rbrakk> \<Longrightarrow> c' = c"
  using CapacityCompatibleGraphs.eq_if_E_eq .
*)

text \<open>In contrast to the Subset_Graph locale, a Subgraph also require edges of the subgraph to have
      the same capacity as the ones in the supergraph. This is in accordance to the standard usage
      in literature.\<close>
locale Subgraph = Capacity_Compatible c' c + Subset_Graph c' c for c' c :: "'capacity::linordered_idom graph"
begin


(*
lemma c'_sg_c: "isSubgraph c' c"
  using cap_compatible E'_ss unfolding isSubgraph_def Graph.E_def by fastforce
*)

(* TODO rename or remove *)
lemma c'_sg_c_old: "\<forall>e. c' e = c e \<or> c' e = 0" using cap_compatible cap_nonzero by auto

(* TODO check whether this is useful *)
lemma sg_cap_cases': "\<lbrakk>c' (u, v) = c (u, v) \<Longrightarrow> P (u, v); c' (u, v) = 0 \<Longrightarrow> P (u, v)\<rbrakk> \<Longrightarrow> P (u, v)"
  using c'_sg_c_old by blast
lemma sg_cap_cases: "\<And>u v. \<lbrakk>c' (u, v) = c (u, v) \<Longrightarrow> P; c' (u, v) = 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using c'_sg_c_old by blast





(* TODO is this the right location for this? *)
text \<open>Transfer lemmas\<close>
lemma sg_Nonnegative_Graph: "Nonnegative_Graph c \<Longrightarrow> Nonnegative_Graph c'"
  unfolding Nonnegative_Graph_def by (metis Orderings.order_eq_iff cap_compatible cap_nonzero)

lemma CapComp_transfer:
  "Capacity_Compatible c c'' \<Longrightarrow> Capacity_Compatible c' c''"
  unfolding Capacity_Compatible_def using cap_compatible cap_nonzero by metis
end

lemma Subgraph_edgeI[intro]: "(\<And>u v. c' (u, v) \<noteq> 0 \<Longrightarrow> c (u, v) = c' (u, v)) \<Longrightarrow> Subgraph c' c"
  by unfold_locales (auto simp: Graph.E_def)

(*
lemma Subgraph_isSubgraphI[intro]: "isSubgraph c' c \<Longrightarrow> Subgraph c' c"
  unfolding isSubgraph_def by unfold_locales (force simp: Graph.E_def)+
*)

(*
lemma Subgraph_CapComp_trans: "\<lbrakk>Subgraph c'' c'; CapacityCompatibleGraphs c' c\<rbrakk> \<Longrightarrow> CapacityCompatibleGraphs c'' c"
*)

locale Proper_Subgraph = Capacity_Compatible c' c for c' c :: "'capacity::linordered_idom graph" +
  assumes E_pss: "E' \<subset> E"
begin
sublocale Subgraph using E_pss by unfold_locales blast
end

lemma (in Subgraph) Proper_SubgraphI[intro]: "\<exists>e \<in> E. e \<notin> E' \<Longrightarrow> Proper_Subgraph c' c"
  using E_ss by unfold_locales blast


(* TODO currently this has to be repeated for every flavour of prelayering *)
(* TODO necessary? *)
lemma (in Subgraph) prelayer_transfer:
  "Local_Prelayer_Graph c layer S \<Longrightarrow> Local_Prelayer_Graph c' layer S"
  unfolding Local_Prelayer_Graph_def using sub_path by blast

interpretation subgraph: order Subgraph Proper_Subgraph
  apply unfold_locales
  unfolding Subgraph_def Subset_Graph_def Proper_Subgraph_def Proper_Subgraph_axioms_def Capacity_Compatible_def Graph.E_def
  by fastforce+

\<comment> \<open>Graphs with the same underlying capacity function\<close>

subsection \<open>Contained Graphs\<close>

(* TODO transfer to locales *)
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
context Graph
begin
(* TODO is there a more natural way to define this, as it is merely subtraction of functions? *)
definition subtract_graph :: "_ graph \<Rightarrow> _ graph"
  where "subtract_graph c' \<equiv> \<lambda> (u, v). c (u, v) - c' (u, v)"

lemma subtract_graph_untouched_cap: "e \<notin> Graph.E c' \<Longrightarrow> subtract_graph c' e = c e"
  unfolding Graph.E_def subtract_graph_def by simp

lemma subtract_graph_untouched_edges: "Graph.E (subtract_graph c') - Graph.E c' = E - Graph.E c'"
  unfolding Graph.E_def subtract_graph_def by auto

definition subtract_skew_graph :: "_ graph \<Rightarrow> _ graph"
  where "subtract_skew_graph c' \<equiv> \<lambda> (u, v). c (u, v) - c' (u, v) + c' (v, u)"
end

locale Contained_Graph = Graph_Comparison c' c for c' c :: "'capacity:: linordered_idom graph" +
  assumes cap_abs_le:
    "(0 \<le> c' (u, v) \<and> c' (u, v) \<le> c (u, v)) \<or> (c (u, v) \<le> c' (u, v) \<and> c' (u, v) \<le> 0)"
begin
sublocale Subset_Graph
  apply unfold_locales
  unfolding Graph.E_def
  by clarify (metis nle_le cap_abs_le)

lemma contained_irreducible: "Irreducible_Graph c \<Longrightarrow> Irreducible_Graph c'"
  unfolding Irreducible_Graph_def
  by (metis (mono_tags, lifting) Irreducible_Graph_axioms_def Nonnegative_Graph_def cap_abs_le dual_order.antisym g'.E_def' mem_Collect_eq order_trans zero_cap_simp)

lemma subtract_contained: "Contained_Graph (subtract_graph c') c"
  unfolding subtract_graph_def using cap_abs_le by unfold_locales auto
end
lemma contained_trans[trans]: "\<lbrakk>Contained_Graph c'' c'; Contained_Graph c' c\<rbrakk> \<Longrightarrow> Contained_Graph c'' c"
  unfolding Contained_Graph_def by (meson order_trans)

sublocale Subgraph \<subseteq> Contained_Graph
  using cap_compatible cap_nonzero by unfold_locales (metis nle_le)

locale Le_Graph = Graph_Comparison c' c for c' c :: "'capacity:: linordered_idom graph" +
  assumes cap_le: "c' (u, v) \<le> c (u, v)"

locale Pos_Contained_Graph = Le_Graph c' c + g': Nonnegative_Graph c'
  for c' c :: "'capacity:: linordered_idom graph"
begin
sublocale Nonnegative_Graph c using cap_le g'.cap_non_negative by unfold_locales (metis order_trans)

sublocale Contained_Graph c' c using cap_le g'.cap_non_negative by unfold_locales blast
thm Contained_Graph_axioms (* TODO how to make these available outside *)

lemma subtract_le_contained: "Pos_Contained_Graph (subtract_graph c') c"
  unfolding subtract_graph_def using cap_le g'.cap_non_negative by unfold_locales auto
end

context Graph
begin
text \<open>While these definitions mostly make sense for Nonnegative_Graphs, they are part of the Graph
      locale to simplify the proofs\<close>

definition pathCap :: "path \<Rightarrow> 'capacity"
  where "pathCap p \<equiv> Min {c e | e. e \<in> set p}"

lemma pathCap_alt: "pathCap p = Min (c ` (set p))" unfolding pathCap_def
  by (metis Setcompr_eq_image)

definition path_induced_graph :: "path \<Rightarrow> _ graph"
  where "path_induced_graph p \<equiv> \<lambda> (u, v).
    if (u, v) \<in> set p then
      pathCap p
    else
      0"

(* TODO why is this so hard to prove? *)
lemma pathCap_nz:
  assumes "p \<noteq> []" "set p \<subseteq> E"
  shows "pathCap p \<noteq> 0"
proof (rule ccontr)
  assume "\<not> pathCap p \<noteq> 0"
  then have "pathCap p = 0" by simp
  with \<open>p \<noteq> []\<close> obtain e where "e \<in> set p" "c e = 0" unfolding pathCap_alt
    by (metis (mono_tags, lifting) List.finite_set Min_in finite_imageI image_iff image_is_empty set_empty)
  with \<open>set p \<subseteq> E\<close> show False unfolding E_def by auto
qed

lemma path_induced_graph_edges:
  "\<lbrakk>p \<noteq> []; set p \<subseteq> E\<rbrakk> \<Longrightarrow> Graph.E (path_induced_graph p) = E \<inter> set p"
  using pathCap_nz unfolding Graph.E_def path_induced_graph_def by auto

definition subtract_path :: "path \<Rightarrow> _ graph"
  where "subtract_path p \<equiv> \<lambda>(u, v).
    if (u, v) \<in> (set p) then
      c (u, v) - pathCap p
    else
      c (u, v)"

lemma subtract_path_alt: "subtract_path p = subtract_graph (path_induced_graph p)"
  unfolding subtract_graph_def subtract_path_def path_induced_graph_def by auto
end

context Nonnegative_Graph
begin
lemma path_induced_graph_pos_contained_aux:
  "p \<noteq> [] \<Longrightarrow> 0 \<le> pathCap p" unfolding pathCap_alt using cap_non_negative by auto

lemma path_induced_graph_pos_contained: "Pos_Contained_Graph (path_induced_graph p) c"
  unfolding path_induced_graph_def apply unfold_locales
  using cap_non_negative apply (simp add: pathCap_alt)
  by (fastforce intro: path_induced_graph_pos_contained_aux)

lemma nonempty_path_cap_positive: "\<lbrakk>p \<noteq> []; set p \<subseteq> E\<rbrakk> \<Longrightarrow> 0 < pathCap p" (* TODO necessary? *)
  unfolding pathCap_alt E_def
  by (auto intro!: le_neq_trans[OF cap_non_negative])
end

(* TODO prettify *)
lemma (in Subgraph) irreducible_contained_skew_subtract:
  "\<lbrakk>Contained_Graph f c'; Irreducible_Graph c'\<rbrakk> \<Longrightarrow> Subgraph (g'.subtract_graph f) (subtract_skew_graph f)"
  apply (intro Subgraph_edgeI)
  unfolding g'.subtract_graph_def subtract_skew_graph_def
  (*by (smt (verit, best) Contained_Graph.edges_ss Graph.E_def' Irreducible_Graph.no_parallel_capacity c'_sg_c_old case_prod_conv diff_0_right diff_diff_eq2 in_mono mem_Collect_eq) *)
  apply auto
  by (metis (no_types, opaque_lifting) Contained_Graph.cap_abs_le Irreducible_Graph.no_parallel_edge add_cancel_left_right cap_compatible cap_nonzero g'.zero_cap_simp nle_le)








(* TODO from here *)
context Subgraph
begin
context
  fixes f
  assumes "Contained_Graph f c'"
begin

end







context
  assumes "Nonnegative_Graph c"
begin
interpretation Nonnegative_Graph c using \<open>Nonnegative_Graph c\<close> .
interpretation g': Nonnegative_Graph c' using Nonnegative_Graph_axioms sg_Nonnegative_Graph by blast

lemma pathCap_eq: "set p \<subseteq> E' \<Longrightarrow> g'.pathCap p = pathCap p"
  (* unfolding g'.pathCap_alt pathCap_alt by (metis (no_types, lifting) List.finite_set Min_gr_iff c'_sg_c_old dual_order.irrefl finite_imageI g'.nonempty_path_cap_positive g'.pathCap_alt image_cong image_eqI image_is_empty set_empty) *)
proof -
  assume "set p \<subseteq> E'"
  then have "(c' ` set p) = (c ` set p)"
    by (smt (verit) c'_sg_c_old g'.E_def' image_cong mem_Collect_eq subsetD) (* TODO prettify *)
  then show ?thesis unfolding g'.pathCap_alt pathCap_alt by simp
qed

lemma path_induced_graph_eq: "set p \<subseteq> E' \<Longrightarrow> g'.path_induced_graph p = path_induced_graph p"
  unfolding g'.path_induced_graph_def path_induced_graph_def using pathCap_eq by auto

lemma subtract_path_maintains_Subgraph: (* TODO remove or simplify with previous lemma *)
  "g'.isPath u p v \<Longrightarrow> Subgraph (g'.subtract_path p) (subtract_path p)"
proof (intro Subgraph_edgeI)
  assume "g'.isPath u p v"
  then have P_CAP_EQ: "g'.pathCap p = pathCap p" using pathCap_eq g'.isPath_alt by blast

  fix u v
  assume "g'.subtract_path p (u, v) \<noteq> 0"
  then have C': "0 < c' (u, v)" unfolding g'.subtract_path_def g'.pathCap_alt
    apply (auto split: if_splits intro!: le_neq_trans[OF g'.cap_non_negative])
    by (metis List.finite_set Min_le Orderings.order_eq_iff empty_iff finite_imageI g'.pathCap_alt g'.path_induced_graph_pos_contained_aux image_eqI list.set(1))
  then have C_EQ_C': "c (u, v) = c' (u, v)"
    by (metis cap_compatible cap_nonzero less_numeral_extra(3))
  then show "subtract_path p (u, v) = g'.subtract_path p (u, v)"
    unfolding subtract_path_def g'.subtract_path_def using P_CAP_EQ by auto
qed
end
end
end
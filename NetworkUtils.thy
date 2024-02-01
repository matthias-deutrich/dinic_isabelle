theory NetworkUtils
  imports LayerMaintenance Flow_Networks.Ford_Fulkerson
begin
text \<open>This file contains several additions to the AFP concerning networks and flows.\<close>

text \<open>This is a workaround to introduce NFlow more easily, since it usually requires showing Preflow twice.\<close>
lemma NFlowI: "\<lbrakk>Network c s t; Flow c s t f\<rbrakk> \<Longrightarrow> NFlow c s t f"
  unfolding NFlow_def NPreflow_def Flow_def by simp

sublocale Network \<subseteq> Irreducible_Graph
  using cap_non_negative no_parallel_edge by unfold_locales auto

context NPreflow
begin
sublocale cf: Nonnegative_Graph cf using Nonnegative_Graph_def resE_nonNegative by blast
end

subsection \<open>Alternative definitions\<close>
(* TODO check which of these are used *)
context Flow
begin
thm zero_flow_simp
lemma residualGraph_alt: "residualGraph c f = (\<lambda>(u, v). if (u, v) \<in> E then c (u, v) - f(u, v) else f (v, u))"
  unfolding residualGraph_def by auto

lemma contained: "Contained_Graph f c" using capacity_const by unfold_locales blast
end

context NPreflow
begin
lemma resCap_pathCap: "resCap p = cf.pathCap p"
  unfolding resCap_def cf.pathCap_def ..

lemma augmentingFlow_alt: "augmentingFlow p = cf.path_induced_graph p"
  unfolding augmentingFlow_def cf.path_induced_graph_def resCap_pathCap ..
end

context NFlow
begin
lemma augment_alt: "Contained_Graph f' cf \<Longrightarrow> cf_of (augment f') = cf.subtract_skew_graph f'"
proof (rule ext, unfold split_paired_all)
  fix u v
  assume "Contained_Graph f' cf"
  then interpret Contained_Graph f' cf .
  show "cf_of (augment f') (u, v) = cf.subtract_skew_graph f' (u, v)"
  proof (cases "(u, v) \<notin> E \<and> (v, u) \<notin> E")
    case True
    then have "f' (u, v) = 0" "f' (v, u) = 0"
      using cap_abs_le NPreflow.cf_def NPreflow_axioms nle_le by fastforce+
    then show ?thesis unfolding Graph.subtract_skew_graph_def augment_def residualGraph_def by auto
  next
    case False
    then show ?thesis unfolding Graph.subtract_skew_graph_def augment_def residualGraph_def by auto
  qed
qed
end
\<comment> \<open>Alternative definitions\<close>

subsection \<open>Auxiliary statements concerning the edges of augments\<close>

context Pos_Contained_Graph
begin
lemma subtract_skew_edges_sub: "Graph.E (subtract_skew_graph c') \<subseteq> E \<union> E'\<inverse>"
  unfolding subtract_skew_graph_def Graph.E_def
  by auto (metis cap_le g'.cap_non_negative nle_le)

lemma subtract_skew_edges_sup: "E \<subseteq> Graph.E (subtract_skew_graph c') \<union> E'"
  unfolding subtract_skew_graph_def Graph.E_def
  by auto (metis cap_le g'.cap_non_negative add_nonneg_eq_0_iff)
end

context NFlow
begin
context
  fixes f' :: "'capacity flow"
  assumes f'_flow: "Flow cf s t f'"
begin
interpretation Pos_Contained_Graph f' cf
  using f'_flow unfolding Flow_def Preflow_def by unfold_locales auto

lemma f'_augment_alt: "cf_of (augment f') = cf.subtract_skew_graph f'"
  using augment_alt[OF Contained_Graph_axioms] .

lemma augment_edges_sub: "Graph.E (cf_of (augment f')) \<subseteq> cf.E \<union> E'\<inverse>"
  unfolding f'_augment_alt using subtract_skew_edges_sub .

lemma augment_edges_sup: "cf.E \<subseteq> Graph.E (cf_of (augment f')) \<union> E'"
  unfolding f'_augment_alt using subtract_skew_edges_sup .
end

(* TODO should be able to redo much of the following using this unfolding *)
thm f'_augment_alt
end

\<comment> \<open>Auxiliary statements concerning the edges of augments\<close>
end
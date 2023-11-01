theory Dinic
imports LayerGraph "Flow_Networks.Ford_Fulkerson"
begin
find_theorems Graph.isShortestPath










(*lemma test: "(\<And>x. x \<in> S \<Longrightarrow> P x) \<Longrightarrow> \<forall>x \<in> S. P x" sorry*)
thm Set.ballI
thm Set.strip
find_theorems "case ?x of (u, v) \<Rightarrow> ?P u v"
thm prod_cases
thm prod.case
thm Product_Type.split

(*
interpretation tmp: LayerGraphExplicit "layering" s "min_dist s"
proof
  show "\<forall>u\<in>V. connected s u"
  proof
    fix u
    assume "u \<in> V"
    then show "connected s u" sorry
  qed
next
  show "min_dist s s = 0" by (rule min_dist_z)
next
  show "\<forall>(u, v)\<in>E. min_dist s u + 1 = min_dist s v"
  proof
    fix x
    assume "x \<in> E"
    obtain u v where "x = (u, v)" by fastforce
    with \<open>x \<in> E\<close> have "(u, v) \<in> E" by blast
    then have "min_dist s u + 1 = min_dist s v" using layering_def E_def sorry
    with \<open>x \<in> E\<close> \<open>x = (u, v)\<close> show "case x of (u, v) \<Rightarrow> min_dist s u + 1 = min_dist s v" by blast (* TODO prettify *)
  qed
qed
*)
end


(*
GOALS:
- Logically connect the layer graph to the original graph
- Show that any (augmenting) path in the layer graph is also one in the original
- Show that there can be no augmenting paths in the original graph that are shorter than the s-t
  distance in the layer graph (need the network context for this)
*)







(* OLD *)

locale LayerGraph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
begin
definition layered_graph' :: "edge \<Rightarrow> 'capacity"
  where "layered_graph' t \<equiv> 
    if min_dist s (fst t) + 1 = min_dist s (snd t) then
      c ((fst t), (snd t))
    else
      0"


definition layered_graph :: "_ graph"
  where "layered_graph \<equiv> \<lambda>(u, v).
    if min_dist s u + 1 = min_dist s v then
      c (u, v)
    else
      0"

thm layered_graph_def
thm layered_graph'_def

(* TODO check whether this should be a locale or only in context Graph *)
definition vertex_layer :: "nat \<Rightarrow> node set"
  where "vertex_layer n \<equiv> {u. connected s u \<and> min_dist s u = n}"

definition edge_layer :: "nat \<Rightarrow> edge set"
  where "edge_layer n \<equiv> {(u, v). u \<in> vertex_layer n \<and> v \<in> vertex_layer (Suc n)}"

lemma vertex_layer_zero_is_origin: "vertex_layer 0 = {s}"
  unfolding vertex_layer_def by fastforce

end

context Graph
begin
(* TODO check whether it is better to do this in a context or as standalone*)
definition vertex_layer :: "node \<Rightarrow> nat \<Rightarrow> node set"
  where "vertex_layer s n \<equiv> {u. connected s u \<and> min_dist s u = n}"

(* NOTE: this definition deviates by 1 from the original *)
definition edge_layer :: "node \<Rightarrow> nat \<Rightarrow> edge set"
  where "edge_layer s n \<equiv> {(u, v). u \<in> vertex_layer s n \<and> v \<in> vertex_layer s (Suc n)}"

find_theorems Graph.min_dist Graph.connected
find_theorems "?A \<subseteq> ?B \<Longrightarrow> ?B \<subseteq> ?A \<Longrightarrow> ?A = ?B"
(*definition tmp :: "_ graph \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> node"
  where "tmp c s n \<equiv> THE v. v \<in> layer c s n"*)

lemma vertex_layer_zero_is_origin: "vertex_layer s 0 = {s}"
  unfolding vertex_layer_def by fastforce

lemma vertex_layer_one_are_neighbours: "vertex_layer s 1 = E``{s}" unfolding vertex_layer_def
proof
  show "{u. connected s u \<and> min_dist s u = 1} \<subseteq> E `` {s}"
  proof
    fix u
    assume "u \<in> {u. connected s u \<and> min_dist s u = 1}"
    then have "connected s u" "min_dist s u = 1" by blast+
    then obtain p where "isPath s p u" "length p = 1" unfolding connected_def using dist_def min_dist_is_dist
      by (metis \<open>connected s u\<close> dist_def min_dist_is_dist)
    then show "u \<in> E `` {s}" sorry
  qed
next
  show "E `` {s} \<subseteq> {u. connected s u \<and> min_dist s u = 1}" sorry
qed

end

(*Graph.min_dist_def*)

definition layerGraph :: "_ graph \<Rightarrow> node \<Rightarrow> _ graph"
  where "layerGraph c s \<equiv> \<lambda>(u, v).
    if Graph.min_dist c s u + 1 = Graph.min_dist c s v then
      c (u, v)
    else
      0"

thm layerGraph_def
end
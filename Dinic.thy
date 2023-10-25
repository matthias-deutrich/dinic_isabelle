theory Dinic
imports "Flow_Networks.Network"
begin

context Graph
begin
(* TODO would isPath be nicer as an inductive predicate? *)
inductive isPathInductive :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" where
  SelfPath: "isPathInductive u [] u"
| EdgePath: "(u, v) \<in> E \<Longrightarrow> isPathInductive v p w \<Longrightarrow> isPathInductive u ((u, v) # p) w"

lemma isPathInductive_correct: "isPathInductive u p v = isPath u p v"
proof
  assume "isPathInductive u p v"
  then show "isPath u p v" by induction simp_all
next
  assume "isPath u p v"
  then show "isPathInductive u p v" by (induction u p v rule: isPath.induct) (simp_all add: SelfPath EdgePath)
qed

text \<open>This rule allows us to use isPath as if it were an inductive predicate,
which is sometimes more convenient\<close>
lemma isPath_custom_induct[consumes 1, case_names SelfPath EdgePath]: "isPath u' p' v' \<Longrightarrow> (\<And>u. P u [] u) \<Longrightarrow>
(\<And>u v p w. (u, v) \<in> E \<Longrightarrow> isPath v p w \<Longrightarrow> P v p w \<Longrightarrow> P u ((u, v) # p) w) \<Longrightarrow> P u' p' v'"
  apply (simp only: isPathInductive_correct[symmetric])
  using isPathInductive.induct by blast

thm [[show_tags=true]] isPath_custom_induct
end

locale LayerGraphExplicit = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
  fixes  layer :: "node \<Rightarrow> nat"
  assumes fully_connected: "\<forall>u \<in> V. connected s u"
  assumes s_in_layer_zero: "layer s = 0"
  assumes layered: "\<forall>(u, v) \<in> E. layer u + 1 = layer v"
begin
lemma path_ascends_layers[dest]: "isPath u p v \<Longrightarrow> layer v = layer u + length p"
proof (induction rule: isPath_custom_induct)
  case (SelfPath u)
  then show ?case by simp
next
  case (EdgePath u v p w)
  then show ?case using layered by fastforce
qed

lemma paths_unique_len: "\<lbrakk>isPath u p1 v; isPath u p2 v\<rbrakk> \<Longrightarrow> length p1 = length p2"
  by fastforce

definition unique_dist :: "node \<Rightarrow> node \<Rightarrow> nat"
  where "unique_dist u v = (THE d. dist u d v)"

lemma unique_dist_is_min_dist: "connected u v \<Longrightarrow> unique_dist u v = min_dist u v"
  unfolding unique_dist_def
proof (rule the_equality)
  assume "connected u v"
  then show "dist u (min_dist u v) v" unfolding connected_def min_dist_def dist_def
    by (smt (verit, best) LeastI) (* TODO prettify *)
next
  fix d
  show "dist u d v \<Longrightarrow> d = min_dist u v" unfolding min_dist_def dist_def using paths_unique_len
    by (smt (verit, best) LeastI) (* TODO prettify *)
qed
(* TODO check if these lemmata for uniqueness suffice *)

lemma s_node_for_nonempty: "V \<noteq> {} \<Longrightarrow> s \<in> V"
proof -
  assume "V \<noteq> {}"
  then obtain u where "u \<in> V" by blast
  with fully_connected obtain p where "isPath s p u" unfolding connected_def by blast
  then show "s \<in> V"
    using \<open>u \<in> V\<close> connected_inV_iff fully_connected by blast (* TODO prettify *)
qed

thm the_equality[symmetric]

lemma l_is_s_dist: "u \<in> V \<Longrightarrow> layer u = unique_dist s u"
proof -
  assume "u \<in> V"
  with fully_connected obtain p where "isPath s p u" unfolding connected_def by blast
  with path_ascends_layers s_in_layer_zero have "layer u = length p" by simp
  thm the_equality[symmetric]
  with \<open>isPath s p u\<close>  show "layer u = unique_dist s u" unfolding unique_dist_def dist_def
    by (smt (verit, del_insts) add_0 path_ascends_layers s_in_layer_zero the_equality) (* TODO prettify *)
qed

lemma only_s_in_layer_zero: "u \<in> V \<Longrightarrow> layer u = 0 \<Longrightarrow> u = s" (* TODO easier with prev lemma? *)
proof -
  assume "u \<in> V" "layer u = 0"
  then obtain p where "isPath s p u" using fully_connected connected_def by blast
  with \<open>layer u = 0\<close> s_in_layer_zero have "length p = 0" by fastforce
  with \<open>isPath s p u\<close> show "u = s" by simp
qed
end

(*
definition layering :: "_ graph \<Rightarrow> node \<Rightarrow> _ graph"
  where "layering c s \<equiv> \<lambda>(u, v).
    if Graph.min_dist c s u + 1 = Graph.min_dist c s v then
      c (u, v)
    else
      0"
*)

locale InducedLayeredGraph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
  assumes s_node[simp, intro!]: "s \<in> V"
begin

definition layering :: "'capacity graph"
  where "layering \<equiv> \<lambda>(u, v).
    if min_dist s u + 1 = min_dist s v then
      c (u, v)
    else
      0"

interpretation l: Graph layering .

interpretation tmp: LayerGraphExplicit "layering" s "min_dist s"
proof
  show "\<forall>u\<in>l.V. l.connected s u"
  proof
    fix u
    assume "u \<in> l.V"
    then show "l.connected s u" unfolding l.connected_def sorry
  qed
next
  show "min_dist s s = 0" by (rule min_dist_z)
next
  show "\<forall>(u, v)\<in>l.E. min_dist s u + 1 = min_dist s v"
  proof
    fix x
    assume "x \<in> l.E"
    obtain u v where "x = (u, v)" by fastforce
    with \<open>x \<in> l.E\<close> have "(u, v) \<in> l.E" by blast
    then have "layering (u, v) \<noteq> 0" unfolding l.E_def by blast
    then have "min_dist s u + 1 = min_dist s v" unfolding layering_def
      by (smt (verit, best) case_prod_conv)
    with \<open>x \<in> l.E\<close> \<open>x = (u, v)\<close> show "case x of (u, v) \<Rightarrow> min_dist s u + 1 = min_dist s v" by blast (* TODO prettify *)
  qed
qed


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
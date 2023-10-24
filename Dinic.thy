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

lemma isPath_custom_induct: "isPath u' p' v' \<Longrightarrow> (\<And>u. P u [] u) \<Longrightarrow>
(\<And>u v p w. (u, v) \<in> E \<Longrightarrow> isPath v p w \<Longrightarrow> P v p w \<Longrightarrow> P u ((u, v) # p) w) \<Longrightarrow> P u' p' v'"
  apply (simp only: isPathInductive_correct[symmetric])
  using isPathInductive.induct by blast

thm isPath.induct
thm isPathInductive.induct
thm isPath_custom_induct
end

locale LayerGraphExplicit = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
  fixes  l :: "node \<Rightarrow> nat"
  (* assumes s_node[simp, intro!]: "s \<in> V" TODO check if really needed, or whether the following implies this for nonempty *)
  assumes fully_connected: "\<forall>v \<in> V. connected s v"
  assumes s_in_layer_zero: "l s = 0"
  assumes layered: "\<forall>(u, v) \<in> E. l u + 1 = l v"
begin
lemma path_ascends_layers': "isPathInductive u p v \<Longrightarrow> l v = l u + length p"
proof (induction rule: isPathInductive.induct)
  case (SelfPath u)
  then show ?case by simp
next
  case (EdgePath u v p w)
  then show ?case using layered by fastforce
qed

lemma path_ascends_layers[dest]: "isPath u p v \<Longrightarrow> l v = l u + length p"
  using isPathInductive_correct path_ascends_layers' by blast

lemma paths_unique_len: "\<lbrakk>isPath u p1 v; isPath u p2 v\<rbrakk> \<Longrightarrow> length p1 = length p2"
  by fastforce

definition unique_dist :: "node \<Rightarrow> node \<Rightarrow> nat"
  where "unique_dist u v = (THE d. dist u d v)"
thm the_equality

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

(* TODO show that l is simply the distance from s; need to first define unique dist *)
lemma l_is_s_dist: "u \<in> V \<Longrightarrow> l u = unique_dist s u" sorry


lemma s_node_for_nonempty: "V \<noteq> {} \<Longrightarrow> s \<in> V"
proof -
  assume "V \<noteq> {}"
  then obtain u where "u \<in> V" by blast
  with fully_connected obtain p where "isPath s p u" unfolding connected_def by blast
  then show "s \<in> V"
    using \<open>u \<in> V\<close> connected_inV_iff fully_connected by blast (* TODO prettify *)
qed

lemma only_s_in_layer_zero: "v \<in> V \<Longrightarrow> l v = 0 \<Longrightarrow> v = s"
proof -
  assume "v \<in> V" "l v = 0"
  then obtain p where "isPath s p v" using fully_connected connected_def by blast
  with \<open>l v = 0\<close> s_in_layer_zero have "length p = 0" by fastforce
  with \<open>isPath s p v\<close> show "v = s" by simp
qed
end

locale LayerGraphImplicit = Graph c for c :: "'capacity::linordered_idom graph" +
  assumes layered: "\<exists>l :: node \<Rightarrow> nat. (\<exists>s. l s = 0) \<and> (\<forall>u v. (u, v) \<in> E \<longrightarrow> l u + 1 = l v)"
(* TODO missing connectedness *)
begin
thm layered
end

locale LayerGraphSemiImplicit = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s :: node
  assumes fully_connected: "\<forall>v \<in> V. connected s v"
  assumes layered: "\<exists>l :: node \<Rightarrow> nat. l s = 0 \<and> (\<forall>(u, v) \<in> E. l u + 1 = l v)"
  (* assumes layered: "\<exists>l :: node \<Rightarrow> nat. l s = 0 \<and> (\<forall>u v. (u, v) \<in> E \<longrightarrow> l u + 1 = l v)" *)
  (* assumes fully_connected': "\<forall>v. v \<in> V \<longrightarrow> connected s v" *)
  (*assumes tmp2: "\<forall>(u, v)\<in> E. connected u v"*)
(* TODO missing connectedness *)
begin
thm layered
(*lemma path_ascends_layers: "isPath u p v \<Longrightarrow>*)

lemma source_paths_unique_len: "\<lbrakk>isPath s p1 v; isPath s p2 v\<rbrakk> \<Longrightarrow> len p1 = len p2"
proof (induction p1)
  case Nil
  then have "p2 = []" sorry
  then show ?case by blast
next
  case (Cons a p1)
  then show ?case sorry
qed
end

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
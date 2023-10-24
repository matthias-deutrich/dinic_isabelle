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
  assumes fully_connected: "\<forall>v \<in> V. connected s v"
  assumes s_in_layer_zero: "l s = 0"
  assumes layered: "\<forall>(u, v) \<in> E. l u + 1 = l v"
begin
lemma only_s_in_layer_zero: "l v = 0 \<Longrightarrow> v = s" sorry


(*lemma path_ascends_layers': "isPath u p v \<Longrightarrow> l u \<le> l v" sorry*)

lemma path_ascends_layers': "isPathInductive u p v \<Longrightarrow> l v = l u + length p"
proof (induction rule: isPathInductive.induct)
  case (SelfPath u)
  then show ?case by simp
next
  case (EdgePath u v p w)
  then show ?case using layered by fastforce
qed

lemma path_ascends_layers: "isPath u p v \<Longrightarrow> l v = l u + length p"
  using isPathInductive_correct path_ascends_layers' by blast

(* lemma path_ascends_layers''':
  assumes "isPath u p v"
  shows "l v = l u + length p"
proof -
  thm isPath_custom_induct[OF assms]
  show ?thesis apply (rule isPath_custom_induct[OF assms]) sorry
qed

lemma path_ascends_layers: "isPath u p v \<Longrightarrow> l v = l u + length p"
proof (induction rule: isPath_custom_induct)
  case 1
  then show ?case sorry
next
  case (2 u)
  then show ?case sorry
next
  case (3 u v p w)
  then show ?case sorry
qed

lemma path_ascends_layers': "isPath u p v \<Longrightarrow> l v = l u + length p"
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons e p)
  then show ?case sorry
qed*)

(*lemma path_asends_layers': "isPath u p v \<Longrightarrow> l v = l u + length p"
proof (induction u p v rule: isPath.induct)
  case (1 u v)
  then show ?case sorry
next
  case (2 u x y p v)
  then show ?case sorry
qed*)

lemma source_paths_unique_len': "\<lbrakk>isPathInductive s p1 v; isPathInductive s p2 v\<rbrakk> \<Longrightarrow> length p1 = length p2"
proof (induction rule: isPathInductive.induct)
  case (SelfPath u)
  then show ?case using path_ascends_layers' by fastforce
next
  case (EdgePath u v p w)
  then show ?case sorry
qed

lemma source_paths_unique_len: "\<lbrakk>isPath s p1 v; isPath s p2 v\<rbrakk> \<Longrightarrow> length p1 = length p2"
proof (induction p1)
  case Nil
  then have "s = v" by simp
  then have "p2 = []" using path_ascends_layers[OF \<open>isPath s p2 v\<close>] by simp
  then show ?case by blast
next
  case (Cons a p1)
  then show ?case sorry
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
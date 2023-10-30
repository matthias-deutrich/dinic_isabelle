theory LayerGraph
imports Subgraph 
begin
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
    if connected s u \<and> min_dist s u + 1 = min_dist s v then
      c (u, v)
    else
      0"

(* TODO check whether this is really a good idea, especially the exclamation mark *)
lemma layeringE[elim!]:
  fixes u v
  assumes major: "layering (u, v) \<noteq> 0"
    and minor: "\<lbrakk>(u, v) \<in> E;
                connected s u;
                connected s v;
                \<exists>n. n = min_dist s u \<and> n + 1 = min_dist s v\<rbrakk>
              \<Longrightarrow> P"
  shows P
proof -
  from major have "(u, v) \<in> E" using layering_def
    by (smt (verit) Graph.zero_cap_simp case_prod_conv)
  moreover from major have "connected s u" using layering_def
    by (smt (verit) case_prod_conv)
  moreover from \<open>(u, v) \<in> E\<close> \<open>connected s u\<close> have "connected s v" using connected_append_edge
    by blast
  moreover from major have "\<exists> n. n = min_dist s u \<and> n + 1 = min_dist s v" using layering_def
    by (smt (verit) case_prod_conv)
  ultimately show P using minor by blast
qed

(*lemma tmp:
  fixes u v
  assumes "layering (u, v) \<noteq> 0"
  shows "connected s u"
proof -
  from assms have "c (u, v) \<noteq> 0" using layering_def
    by (smt (verit) case_prod_conv)
  from assms have "connected s u" using layering_def
    by (smt (verit) case_prod_conv)
  from assms have "\<exists> n. n = min_dist s u \<and> n + 1 = min_dist s v" using layering_def
    by (smt (verit) case_prod_conv)
  from assms have "\<exists> n. n = min_dist s u" using layering_def by blast
qed*)


interpretation l: Graph layering .

interpretation l_sub: CapacitySubgraph layering c unfolding layering_def
  by unfold_locales simp

thm l_sub.V_ss


(* TODO check if this is a good idea *)
lemma layer_edgeE[elim]:
  fixes u v
  assumes major: "(u, v) \<in> l.E"
    and minor: "\<lbrakk>(u, v) \<in> E;
                connected s u;
                connected s v;
                \<exists>n. n = min_dist s u \<and> n + 1 = min_dist s v\<rbrakk>
              \<Longrightarrow> P"
  shows P
  using assms l.E_def by blast

(* TODO use transfer_path *)

find_theorems name:isPath
find_theorems isPath
thm isPath.simps
thm isShortestPath_def

lemma l_vertices_connected_in_base: "u \<in> l.V \<Longrightarrow> connected s u" (* TODO necessary? *)
  using l.V_def by blast

thm isShortestPath_level_edge
find_theorems isPath

(*lemma tmp: "\<forall>e \<in> set p"*)

lemma shortest_s_path_remains_path: "isShortestPath s p u \<Longrightarrow> l.isPath s p u" (* TODO NOTE: can't prove this by simple induction on p *)
proof (induction p)
  case Nil
  then show ?case using shortestPath_is_path by fastforce
next
  case (Cons a p)
  then show ?case sorry
qed

lemma shortest_s_path_remains_shortest: "isShortestPath s p u \<Longrightarrow> l.isShortestPath s p u"
  using shortest_s_path_remains_path l_sub.shortest_paths_remain_if_contained by blast


interpretation l: LayerGraphExplicit "layering" s "min_dist s"
proof
  show "\<forall>u\<in>l.V. l.connected s u"
  proof
    fix u
    assume "u \<in> l.V"
    then have "connected s u" by (rule l_vertices_connected_in_base)
    then obtain p where "isShortestPath s p u" by (rule obtain_shortest_path)
    then have "l.isPath s p u" by (rule shortest_s_path_remains_path)
    then show "l.connected s u" unfolding l.connected_def by blast
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
    then have "layering (u, v) \<noteq> 0" unfolding l.E_def by simp
    then have "min_dist s u + 1 = min_dist s v" unfolding layering_def
      by (smt (verit, best) case_prod_conv)
    with \<open>x \<in> l.E\<close> \<open>x = (u, v)\<close> show "case x of (u, v) \<Rightarrow> min_dist s u + 1 = min_dist s v" by blast (* TODO prettify *)
  qed
qed
end
end
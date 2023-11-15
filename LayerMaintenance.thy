theory LayerMaintenance
  imports LayerGraph (*"Flow_Networks.Residual_Graph"*)
begin
(* TODO check if useful *)
(*locale BoundedSourceTargetLayering = ST_Graph c s t for c :: "'capacity::linordered_idom graph" and s t +
  fixes b :: nat
  assumes bounded: "connected s t \<Longrightarrow> min_dist s t \<le> b"*)
(* TODO check which definition is more useful, since stl_path_length_bounded translates between them *)
locale Distance_Bounded_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes b :: nat
  assumes bounded: "dist u n v \<Longrightarrow> n \<le> b"
begin
lemma path_lengths_bounded: "isPath u p v \<Longrightarrow> length p \<le> b" using bounded dist_def by blast
end

(* TODO needed? *)
(*locale Bounded_ST_Graph = ST_Graph c s t + Distance_Bounded_Graph c b for c :: "'capacity::linordered_idom graph" and s t b*)

context ST_Graph
begin
sublocale stl: Distance_Bounded_Graph "st_layering c s t" "min_dist s t"
  unfolding Distance_Bounded_Graph_def
  using stl.dist_def stl_path_length_bounded by metis
end

(* TODO PathFinding *)
(* TODO check if definitions are sound *)
definition rightPassAbstract :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "rightPassAbstract c s \<equiv> \<lambda>(u, v).
    if Graph.connected c s u then
      c (u, v)
    else
      0"

context S_Graph
begin
abbreviation "right_pass \<equiv> rightPassAbstract c s"

sublocale right_pass_graph: Graph right_pass .

sublocale right_pass_subgraph: Subgraph right_pass c
  unfolding Subgraph_def isSubgraph_def rightPassAbstract_def by simp

lemma rightPassAbstract_is_c_if_s_connected[simp]:
  "connected s u \<Longrightarrow> right_pass (u, v) = c (u, v)"
  unfolding rightPassAbstract_def by simp

lemma s_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected s u \<Longrightarrow> (u, v) \<in> right_pass_graph.E"
  using E_def' right_pass_graph.zero_cap_simp by fastforce

lemma rightPassAbstract_keeps_s_paths:
  "isPath s p u \<Longrightarrow> right_pass_graph.isPath s p u"
proof (induction rule: isPath_back_induct)
  case (SelfPath u)
  then show ?case by (simp add: Graph.isPath.simps)
next
  case (EdgePath p u v)
  then show ?case
    by (simp add: Graph.connected_edgeRtc Graph.isPath_append_edge isPath_rtc s_connected_edges_remain)
qed

corollary rightPassAbstract_keeps_s_connected:
  "connected s u \<Longrightarrow> right_pass_graph.connected s u"
  using rightPassAbstract_keeps_s_paths Graph.connected_def by blast

lemma rightPassAbstract_distinct_connected_iff:
  assumes "u \<noteq> v"
  shows "Graph.connected (rightPassAbstract c s) u v \<longleftrightarrow> Graph.connected c s u \<and> Graph.connected c s v \<and> Graph.connected c u v" (is "?pass_con \<longleftrightarrow> ?c_con")
proof
  assume ?pass_con
  then show ?c_con
  proof (intro conjI)
    assume ?pass_con
    from \<open>?pass_con\<close> show "Graph.connected c u v" by (rule right_pass_subgraph.sg_connected_remains_base_connected)
qed oops
end

lemma rightPassAbstract_vertices_s_connected:
  "u \<in> Graph.V (rightPassAbstract c s) \<Longrightarrow> Graph.connected c s u" sorry

thm Graph.connected_inV_iff
thm Graph.distinct_nodes_in_V_if_connected




definition leftPassAbstract :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "leftPassAbstract c t \<equiv> \<lambda>(u, v).
    if Graph.connected c v t then
      c (u, v)
    else
      0"

context T_Graph
begin
abbreviation "left_pass \<equiv> leftPassAbstract c t"

sublocale left_pass_graph: Graph left_pass .

sublocale left_pass_subgraph: Subgraph left_pass c
  unfolding Subgraph_def isSubgraph_def leftPassAbstract_def by simp

lemma leftPassAbstract_is_c_if_s_connected[simp]:
  "connected v t \<Longrightarrow> left_pass (u, v) = c (u, v)"
  unfolding leftPassAbstract_def by simp

lemma t_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected v t \<Longrightarrow> (u, v) \<in> left_pass_graph.E"
  using E_def' left_pass_graph.zero_cap_simp by fastforce

lemma leftPassAbstract_keeps_t_paths':
  "isPath u p t \<Longrightarrow> left_pass_graph.isPath u p t"
proof (induction p arbitrary: u)
  case Nil
  then show ?case by simp
next
  case (Cons e p)
  (*then show ?case using connected_def t_connected_edges_remain isPath_fwd_cases
    by (metis Graph.isPath_head prod.exhaust_sel)*)
  then obtain v where "(u, v) \<in> E" "isPath v p t" using isPath_fwd_cases by blast
  then have "(u, v) \<in> left_pass_graph.E" using connected_def t_connected_edges_remain by blast
  with Cons \<open>isPath v p t\<close> show ?case
    by (metis Graph.isPath_head isPath_fwd_cases list.distinct(1) list.inject)
qed

lemma leftPassAbstract_keeps_t_paths:
  "isPath u p t \<Longrightarrow> left_pass_graph.isPath u p t"
proof (induction rule: isPath_front_induct)
  case (SelfPath u)
  then show ?case by (simp add: Graph.isPath.simps)
next
  case (EdgePath u v p)
  then show ?case using connected_def t_connected_edges_remain sledgehammer
    using left_pass_graph.isPath.simps(2) by blast
    by fastforce
  have "(u, v) \<in> left_pass_graph.E"
    apply (rule t_connected_edges_remain)
    using EdgePath(1) apply simp
    using EdgePath(2)
    using t_connected_edges_remain Graph.connected_def
  with EdgePath(3) show ?case by simp
qed
end





lemma leftPassAbstract_z_iff: "leftPassAbstract c t (u, v) \<noteq> 0 \<longleftrightarrow> c (u, v) \<noteq> 0 \<and> Graph.connected c v t"
  unfolding leftPassAbstract_def by simp

definition cleaningAbstract :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> 'capacity graph"
  where "cleaningAbstract c s t \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t then
      c (u, v)
    else
      0"
lemma cleaningAbstract_is_c_if_doubly_connected[simp]:
  "Graph.connected c s u \<Longrightarrow> Graph.connected c v t \<Longrightarrow> cleaningAbstract c s t (u, v) = c (u, v)"
  unfolding cleaningAbstract_def by simp

context Graph
begin
lemma left_right_pass_is_cleaning: "cleaningAbstract c s t = leftPassAbstract (rightPassAbstract c s) t"
proof (rule ext, unfold split_paired_all)
  fix u v
  (*interpret g: Graph c .*) (* TODO why does this not work *)
  show "cleaningAbstract c s t (u, v) = leftPassAbstract (rightPassAbstract c s) t (u, v)"
  proof (cases "cleaningAbstract c s t (u, v) = 0", clarsimp)
    case True
    then have "c (u, v) = 0 \<or> \<not> connected s u \<or> \<not> connected v t" unfolding cleaningAbstract_def by auto
    then show "leftPassAbstract (rightPassAbstract c s) t (u, v) = 0"
    proof (elim disjE)
      assume "c (u, v) = 0"
      then show ?thesis unfolding leftPassAbstract_def rightPassAbstract_def by simp
    next
      assume "\<not> connected s u"
      then show ?thesis unfolding leftPassAbstract_def rightPassAbstract_def by simp
    next
      assume "\<not> connected v t"
      then have "\<not> Graph.connected (rightPassAbstract c s) v t"
        using right_pass_subgraph.sg_connected_remains_base_connected sorry by blast
      then show ?thesis unfolding leftPassAbstract_def by simp
    qed
  next
    case False
    then have "(u, v) \<in> E" and st_connected: "connected s u" "connected v t"
      unfolding cleaningAbstract_def
      by (smt (verit) case_prod_conv zero_cap_simp)+
    then have "connected s v" using connected_append_edge by blast
    with st_connected have "Graph.connected (rightPassAbstract c s) v t"
      using rightPassAbstract_connected_iff sorry by blast 
    with st_connected show ?thesis by simp
  qed
qed

lemma right_left_pass_is_cleaning: "cleaningAbstract c s t = rightPassAbstract (leftPassAbstract c t) s" sorry

corollary right_left_pass_com: "leftPassAbstract (rightPassAbstract c s) t = rightPassAbstract (leftPassAbstract c t) s"
  using left_right_pass_is_cleaning right_left_pass_is_cleaning by metis
(* TODO maybe make commutativity property prettier *)
end \<comment> \<open>Graph\<close>
end
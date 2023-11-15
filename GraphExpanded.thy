theory GraphExpanded
imports "Flow_Networks.Graph"
begin

section \<open>General utils\<close>
text \<open>Shortcut for the default way of starting an equality proof of edge sets.\<close>
lemma pair_set_eqI:
"\<lbrakk>\<And>a b. (a, b) \<in> A \<Longrightarrow> (a, b) \<in> B; \<And>a b. (a, b) \<in> B \<Longrightarrow> (a, b) \<in> A\<rbrakk> \<Longrightarrow> A = B"
  by (rule set_eqI, unfold split_paired_all, rule iffI)

section \<open>Custom induction rules\<close>
(* TODO check which of these are useful and prettify proofs *)
context Graph
begin
text \<open>This rule allows us to use isPath as if it were an inductive predicate,
which is sometimes more convenient\<close>
lemma isPath_front_induct[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isPath u' p' v'; \<And>u. P u [] u; \<And>u v p w. \<lbrakk>(u, v) \<in> E; isPath v p w; P v p w\<rbrakk> \<Longrightarrow> P u ((u, v) # p) w\<rbrakk> \<Longrightarrow> P u' p' v'"
  by (induction p' arbitrary: u') auto

lemma isPath_back_induct[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isPath u' p' v'; \<And>u. P u [] u; \<And>u p v w. \<lbrakk>(v, w) \<in> E; isPath u p v; P u p v\<rbrakk> \<Longrightarrow> P u (p @ [(v, w)]) w\<rbrakk> \<Longrightarrow> P u' p' v'"
  apply (induction p'  arbitrary: v' rule: rev_induct, simp)
  using isPath_bwd_cases append1_eq_conv by metis

lemma connected_front_induct[consumes 1, case_names Self Edge]:
  "\<lbrakk>connected u' v'; \<And>u. P u u; \<And>u v w. \<lbrakk>(u, v) \<in> E; connected v w; P v w\<rbrakk> \<Longrightarrow> P u w\<rbrakk> \<Longrightarrow> P u' v'"
  unfolding connected_def
  apply clarify
  apply (induct_tac rule: isPath_front_induct)
  by blast+

lemma connected_back_induct[consumes 1, case_names Self Edge]:
  "\<lbrakk>connected u' v'; \<And>u. P u u; \<And>u v w. \<lbrakk>(v, w) \<in> E; connected u v; P u v\<rbrakk> \<Longrightarrow> P u w\<rbrakk> \<Longrightarrow> P u' v'"
  unfolding connected_def
  apply clarify
  apply (induct_tac rule: isPath_back_induct)
  by blast+
end

section \<open>Alternative definition of paths\<close>
inductive isLinked :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" where
  SelfPrePath: "isLinked u [] u"
| StepPrePath: "isLinked v p w \<Longrightarrow> isLinked u ((u, v) # p) w"

lemma (in Graph) isPath_alt: "isPath u p v \<longleftrightarrow>  isLinked u p v \<and> (set p) \<subseteq> E"
proof
  assume "isPath u p v"
  then show "isLinked u p v \<and> (set p) \<subseteq> E"
    by (induction rule: isPath_front_induct) (simp_all add: isLinked.intros)
next
  assume "isLinked u p v \<and> (set p) \<subseteq> E"
  then have "isLinked u p v" "(set p) \<subseteq> E" by blast+
  then show "isPath u p v" by (induction rule: isLinked.induct) simp_all
qed

lemma isLinked_if_isPath: "Graph.isPath c u p v \<Longrightarrow> isLinked u p v"
  using Graph.isPath_alt by blast

section \<open>Path Union\<close>
definition isPathUnion :: "_ graph \<Rightarrow> path set \<Rightarrow> bool"
  where "isPathUnion c p_set \<equiv> Graph.E c = \<Union>(set ` p_set)"

context Graph
begin
definition allShortestPaths :: "node set \<Rightarrow> node set \<Rightarrow> path set"
  where "allShortestPaths s_set t_set \<equiv> {p. \<exists>s \<in> s_set. \<exists>t \<in> t_set. isShortestPath s p t}"

definition shortestSPaths :: "node \<Rightarrow> node set \<Rightarrow> path set"
  where "shortestSPaths s t_set \<equiv> {p. \<exists>t \<in> t_set. isShortestPath s p t}"

definition shortestSTPaths :: "node \<Rightarrow> node \<Rightarrow> path set"
  where "shortestSTPaths s t \<equiv> {p. isShortestPath s p t}"

lemma allShortestPaths_singleton_simps[simp]:
  "allShortestPaths {s} t_set = shortestSPaths s t_set"
  "shortestSPaths s {t} = shortestSTPaths s t"
  unfolding allShortestPaths_def shortestSPaths_def shortestSTPaths_def
  by simp_all

lemma graph_is_all_shortest_paths_union:
  assumes no_self_loop: "\<forall>u. (u, u) \<notin> E"
  shows "isPathUnion c (allShortestPaths V V)" unfolding isPathUnion_def
proof (rule pair_set_eqI)
  fix u v
  assume "(u, v) \<in> E"
  then have "u \<in> V" "v \<in> V" unfolding V_def by blast+
  moreover have "isShortestPath u [(u, v)] v"
  proof -
    from \<open>(u, v) \<in> E\<close> no_self_loop have "u \<noteq> v" by blast
    then have "\<forall>p'. isPath u p' v \<longrightarrow> length [(u, v)] \<le> length p'"
      using not_less_eq_eq by fastforce
    moreover from \<open>(u, v) \<in> E\<close> have "isPath u [(u, v)] v" by simp
    ultimately show ?thesis unfolding isShortestPath_def by simp
  qed
  ultimately show "(u, v) \<in> \<Union> (set ` allShortestPaths V V)" unfolding allShortestPaths_def by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> (set ` allShortestPaths V V)"
  then obtain p u' v' where "isShortestPath u' p v'" and "(u, v) \<in> set p"
    using allShortestPaths_def by auto
  then show "(u, v) \<in> E" using isPath_edgeset shortestPath_is_path by blast
qed
end





(* TODO check and sort from here *)
context Graph
begin


(* TODO check if useful *)
text \<open>Dual to connected_append_edge\<close>
lemma connected_prepend_edge: "(u, v) \<in> E \<Longrightarrow> connected v w \<Longrightarrow> connected u w"
  unfolding connected_def using isPath.simps by blast


(* TODO check whether this is useful *)
lemma E_def': "E = {e. c e \<noteq> 0}" unfolding E_def by blast




(* TODO check if exists *)
lemma vertex_cases[consumes 1]:
  assumes "u \<in> V"
  obtains (outgoing) v where "(u, v) \<in> E"
    | (incoming) v where "(v, u) \<in> E"
  using V_def assms by auto

text \<open>This lemma makes it more convenient to work with split_shortest_path in a common use case.\<close>
thm split_shortest_path
lemma split_shortest_path_around_edge:
  assumes "isShortestPath s (p @ (u, v) # p') t"
  shows "isShortestPath s p u" "isShortestPath u ((u, v) # p') t"
    and "isShortestPath s (p @ [(u, v)]) v" "isShortestPath v p' t"
proof -
  from assms obtain w where "isShortestPath s p w" "isShortestPath w ((u, v) # p') t" using split_shortest_path by blast
  moreover from this have "w = u" unfolding isShortestPath_def by simp
  ultimately show "isShortestPath s p u" "isShortestPath u ((u, v) # p') t" by auto
next
  from assms obtain w where "isShortestPath s (p @ [(u, v)]) w" "isShortestPath w p' t" using split_shortest_path
    by (metis append.assoc append_Cons append_Nil)
  moreover from this have "w = v" unfolding isShortestPath_def
    using isPath_tail by simp
  ultimately show "isShortestPath s (p @ [(u, v)]) v" "isShortestPath v p' t" by auto
qed

lemma distinct_nodes_in_V_if_connected:
  assumes "connected u v" "u \<noteq> v"
  shows "u \<in> V" "v \<in> V" (* TODO is there a better way to prove multiple props at once? *)
  using assms isPath_fwd_cases isPath_bwd_cases unfolding connected_def V_def by fastforce+
end

thm Graph.isPath.elims
thm Graph.isPath_fwd_cases
lemma (in Graph) "isPath u p v \<Longrightarrow> p \<noteq> [] \<Longrightarrow> u \<in> V" (* TODO use or remove *)
  using V_def isPath_fwd_cases by fastforce




end
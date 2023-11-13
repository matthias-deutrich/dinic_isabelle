theory GraphExpanded
imports "Flow_Networks.Graph"
begin

(* TODO check whether useful *)
inductive isLinked :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" where
  SelfPrePath: "isLinked u [] u"
| StepPrePath: "isLinked v p w \<Longrightarrow> isLinked u ((u, v) # p) w"

context Graph
begin
(* TODO would isPath be nicer as an inductive predicate? *)
inductive isPathInductive :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" where
  SelfPath: "isPathInductive u [] u"
| EdgePath: "(u, v) \<in> E \<Longrightarrow> isPathInductive v p w \<Longrightarrow> isPathInductive u ((u, v) # p) w"
print_theorems

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
lemma isPath_custom_induct[consumes 1, case_names SelfPath EdgePath]:
  assumes "isPath u' p' v'"
    and "\<And>u. P u [] u"
    and "\<And>u v p w. \<lbrakk>(u, v) \<in> E; isPath v p w; P v p w\<rbrakk> \<Longrightarrow> P u ((u, v) # p) w"
  shows "P u' p' v'"
  using assms isPathInductive.induct by (simp only: isPathInductive_correct[symmetric]) blast

(* TODO check if useful *)
text \<open>Dual to connected_append_edge\<close>
lemma connected_prepend_edge: "(u, v) \<in> E \<Longrightarrow> connected v w \<Longrightarrow> connected u w"
  unfolding connected_def using isPath.simps by blast

(* TODO check if useful *)
lemma connected_front_induct[consumes 1, case_names Self Edge]:
  assumes "connected u' v'"
    and "\<And>u. P u u"
    and "\<And>u v w. \<lbrakk>(u, v) \<in> E; connected v w; P v w\<rbrakk> \<Longrightarrow> P u w"
  shows "P u' v'"
proof -
  from \<open>connected u' v'\<close> obtain p where "isPath u' p v'" unfolding connected_def by blast
  then show "P u' v'"
  proof (induction rule: isPath_custom_induct)
    case (SelfPath u)
    from assms show ?case by blast
  next
    case (EdgePath u v p w)
    with assms show ?case using connected_def by blast
  qed
qed

(* TODO check if already exists *)
lemma "(\<exists>v. (u, v) \<in> E \<and> connected v w) \<longleftrightarrow> (\<exists>v. connected u v \<and> (v, w) \<in> E)" oops

(*lemma tmp:
  assumes "isPath u' p' v'"
  obtains u where 

thm isPath.induct*)

(* TODO check whether this is useful *)
lemma E_def': "E = {e. c e \<noteq> 0}" unfolding E_def by blast

lemma isPath_alt: "isPath u p v \<longleftrightarrow>  isLinked u p v \<and> (set p) \<subseteq> E"
proof
  assume "isPath u p v"
  then show "isLinked u p v \<and> (set p) \<subseteq> E"
    by (induction rule: isPath_custom_induct) (simp_all add: isLinked.intros)
next
  assume "isLinked u p v \<and> (set p) \<subseteq> E"
  then have "isLinked u p v" "(set p) \<subseteq> E" by blast+
  then show "isPath u p v" by (induction rule: isLinked.induct) simp_all
qed


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
end

lemma isLinked_if_isPath: "Graph.isPath c u p v \<Longrightarrow> isLinked u p v"
  using Graph.isPath_alt by blast

thm Graph.isPath.elims
thm Graph.isPath_fwd_cases
lemma (in Graph) "isPath u p v \<Longrightarrow> p \<noteq> [] \<Longrightarrow> u \<in> V" (* TODO use or remove *)
  using V_def isPath_fwd_cases by fastforce

text \<open>Shortcut for the default way of starting an equality proof of edge sets.\<close>
lemma pair_set_eqI:
"\<lbrakk>\<And>a b. (a, b) \<in> A \<Longrightarrow> (a, b) \<in> B; \<And>a b. (a, b) \<in> B \<Longrightarrow> (a, b) \<in> A\<rbrakk> \<Longrightarrow> A = B"
  by (rule set_eqI, unfold split_paired_all, rule iffI)

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
end
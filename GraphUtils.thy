theory GraphUtils
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
lemma isPath_front_induct'[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isPath u' p' v'; \<And>u. P u [] u; \<And>u v p w. \<lbrakk>(u, v) \<in> E; isPath v p w; P v p w\<rbrakk> \<Longrightarrow> P u ((u, v) # p) w\<rbrakk> \<Longrightarrow> P u' p' v'"
  by (induction p' arbitrary: u') auto

(* TODO is this better? if so, clean up the first*)
lemma isPath_front_induct[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isPath u' p' t; \<And>u. P u [] u; \<And>u v p. \<lbrakk>(u, v) \<in> E; isPath v p t; P v p t\<rbrakk> \<Longrightarrow> P u ((u, v) # p) t\<rbrakk> \<Longrightarrow> P u' p' t"
  by (induction p' arbitrary: u') auto

lemma isPath_back_induct[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isPath s p' v'; \<And>u. P u [] u; \<And>p u v. \<lbrakk>(u, v) \<in> E; isPath s p u; P s p u\<rbrakk> \<Longrightarrow> P s (p @ [(u, v)]) v\<rbrakk> \<Longrightarrow> P s p' v'"
  by (induction p'  arbitrary: v' rule: rev_induct) (auto simp: isPath_tail)

lemma connected_front_induct[consumes 1, case_names Self Edge]:
  "\<lbrakk>connected w t; \<And>u. P u u; \<And>u v. \<lbrakk>(u, v) \<in> E; connected v t; P v t\<rbrakk> \<Longrightarrow> P u t\<rbrakk> \<Longrightarrow> P w t"
  unfolding connected_def
  apply clarify
  apply (induct_tac rule: isPath_front_induct)
  by blast+

lemma connected_back_induct[consumes 1, case_names Self Edge]:
  "\<lbrakk>connected s w; \<And>u. P u u; \<And>u v. \<lbrakk>(u, v) \<in> E; connected s u; P s u\<rbrakk> \<Longrightarrow> P s v\<rbrakk> \<Longrightarrow> P s w"
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

section \<open>Acyclic and distance-bounded graphs\<close>
(* TODO what here is really necessary? *)

context Graph
begin
definition isCycle :: "node \<Rightarrow> path \<Rightarrow> bool"
  where "isCycle u p \<equiv> isPath u p u \<and> p \<noteq> []"

lemma cycle_induces_arbitrary_length_paths: "isCycle u p \<Longrightarrow> \<exists>p'. isPath u p' u \<and> length p' \<ge> n"
proof (induction n)
  case (Suc n)
  then obtain p' where "isPath u p' u" "length p' \<ge> n" by blast
  moreover from Suc.prems have "isPath u p u" "length p \<ge> 1" unfolding isCycle_def by (simp_all add: Suc_leI)
  ultimately have "isPath u (p @ p') u" "length (p @ p') \<ge> Suc n" using isPath_append by auto
  then show ?case by blast
qed (auto simp: isCycle_def)

(* NOTE: this proof is similar to the one for isSPath_pathLE, see if we can't reuse some things *)
lemma split_non_simple_path:
  assumes "isPath s p t"
  assumes "\<not> isSimplePath s p t"
  obtains p\<^sub>1 p\<^sub>2 p\<^sub>3 u where "p = p\<^sub>1 @ p\<^sub>2 @ p\<^sub>3" "isPath s p\<^sub>1 u" "isCycle u p\<^sub>2" "isPath u p\<^sub>3 t"
proof -
  from assms have "\<not> distinct(pathVertices_fwd s p)" unfolding isSimplePath_fwd by blast
  then obtain pv\<^sub>1 pv\<^sub>2 pv\<^sub>3 u where "pathVertices_fwd s p = pv\<^sub>1 @ u # pv\<^sub>2 @ u # pv\<^sub>3" by (auto dest: not_distinct_decomp)
(* NOTE: there is a direct proof, but the automation requires a great deal of help *)
(*then obtain p\<^sub>1 p\<^sub>2 p\<^sub>3 where "p = p\<^sub>1 @ p\<^sub>2 @ p\<^sub>3" "isPath s p\<^sub>1 u" "isPath u p\<^sub>2 u" "isPath u p\<^sub>3 t" "pathVertices_fwd u p\<^sub>2 = u # pv\<^sub>2 @ [u]"
    using split_path_at_vertex_complete[OF assms(1), of pv\<^sub>1 u "pv\<^sub>2 @ u # pv\<^sub>3"] split_path_at_vertex_complete[of u _ t "u # pv\<^sub>2" u pv\<^sub>3] by by (metis Cons_eq_appendI) *)
  with \<open>isPath s p t\<close> obtain p\<^sub>1 p' where "p = p\<^sub>1 @ p'" "isPath s p\<^sub>1 u" "isPath u p' t" "pathVertices_fwd u p' = u # pv\<^sub>2 @ u # pv\<^sub>3"
    using split_path_at_vertex_complete by metis
  then obtain p\<^sub>2 p\<^sub>3 where "p = p\<^sub>1 @ p\<^sub>2 @ p\<^sub>3" "isPath u p\<^sub>2 u" "isPath u p\<^sub>3 t" "pathVertices_fwd u p\<^sub>2 = u # pv\<^sub>2 @ [u]"
    using split_path_at_vertex_complete by (metis Cons_eq_appendI)
  with \<open>isPath s p\<^sub>1 u\<close> show ?thesis using that isCycle_def by fastforce
qed
end

locale Acyclic_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  assumes acyclic: "\<nexists>u p. isCycle u p"
begin
lemma paths_are_simple: "isPath s p t \<Longrightarrow> isSimplePath s p t"
  using split_non_simple_path acyclic by auto
end

locale Distance_Bounded_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes b :: nat
  assumes bounded: "dist u n v \<Longrightarrow> n \<le> b"
begin
lemma path_lengths_bounded: "isPath u p v \<Longrightarrow> length p \<le> b" using bounded dist_def by blast

sublocale Acyclic_Graph unfolding Acyclic_Graph_def
  using cycle_induces_arbitrary_length_paths path_lengths_bounded not_less_eq_eq by blast
end

locale Distance_Bounded_Graph_Ord = Distance_Bounded_Graph c b + le: ordering less_eq less
  for c :: "'capacity::linordered_idom graph" and b :: nat
    (*and less_eq less :: "edge \<Rightarrow> edge \<Rightarrow> bool"*)(* TODO order, how to determine type and keep infix. What kind of ordering do we want (no total preorder)*)
begin
thm Least_def
fun findMaximalPath :: "node \<Rightarrow> path" where
  "findMaximalPath u = undefined"
(* TODO  how to choose arbitrary element *)
(* IDEA: use sorting function as parameter, which may be lexicographic sort of neighbours or max capacity *)
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

lemma distinct_nodes_have_in_out_if_connected:
  assumes "connected u v" "u \<noteq> v"
  shows "outgoing u \<noteq> {}" "incoming v \<noteq> {}"
proof -
  from assms obtain p where PATH: "isPath u p v" "p \<noteq> []" unfolding connected_def by fastforce
  then obtain w where "(u, w) \<in> E" using isPath_fwd_cases by blast
  then show "outgoing u \<noteq> {}" unfolding outgoing_def by blast
  from PATH obtain w' where "(w', v) \<in> E" using isPath_bwd_cases by blast
  then show "incoming v \<noteq> {}" unfolding incoming_def by blast
qed

corollary distinct_nodes_in_V_if_connected:
  assumes "connected u v" "u \<noteq> v"
  shows "u \<in> V" "v \<in> V"
  using assms distinct_nodes_have_in_out_if_connected
  unfolding V_def outgoing_def incoming_def by fastforce+
end

end
theory Graph_Utils
imports "Flow_Networks.Graph"
begin

(* TODO intro for connected, then remove all the unfoldings *)

section \<open>General utils\<close>
text \<open>Shortcut for the default way of starting an equality proof of edge sets.\<close>
lemma pair_set_eqI:
"\<lbrakk>\<And>a b. (a, b) \<in> A \<Longrightarrow> (a, b) \<in> B; \<And>a b. (a, b) \<in> B \<Longrightarrow> (a, b) \<in> A\<rbrakk> \<Longrightarrow> A = B"
  by (rule set_eqI, unfold split_paired_all, rule iffI)

lemma set_emptyI: "(\<And>x. x \<notin> S) \<Longrightarrow> S = {}" by blast

thm converse_empty
lemma converse_empty_simp: "S\<inverse> = {} \<longleftrightarrow> S = {}" by auto

lemma split_list_min_len: "n \<le> length xs \<Longrightarrow> \<exists>ys zs. xs = ys @ zs \<and> n = length ys"
proof (induction n arbitrary: xs)
  case (Suc n)
  then obtain x ys where XS: "xs = x # ys" by (meson Suc_le_length_iff)
  with Suc.prems have "n \<le> length ys" by simp
  with Suc.IH obtain zs1 zs2 where YS: "ys = zs1 @ zs2" "n = length zs1" by blast
  with XS show ?case by (metis append_Cons length_Cons)
qed simp

section \<open>Misc convenience lemmas\<close>
context Graph
begin
lemma connected_trans[trans]: "\<lbrakk>connected u v; connected v w\<rbrakk> \<Longrightarrow> connected u w"
  using dist_trans min_dist_is_dist by blast

text \<open>Dual to connected_append_edge\<close>
lemma connected_prepend_edge: "(u, v) \<in> E \<Longrightarrow> connected v w \<Longrightarrow> connected u w"
  unfolding connected_def using isPath.simps by blast

lemma vertex_cases[consumes 1]:
  assumes "u \<in> V"
  obtains (outgoing) v where "(u, v) \<in> E"
    | (incoming) v where "(v, u) \<in> E"
  using V_def assms by auto

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

lemma in_outgoingD[dest]: "(u', v) \<in> outgoing u \<Longrightarrow> (u, v) \<in> E \<and> u' = u"
  unfolding outgoing_def by blast

lemma in_incomingD[dest]: "(u, v') \<in> incoming v \<Longrightarrow> (u, v) \<in> E \<and> v' = v"
  unfolding incoming_def by blast

lemma pathVertices_reachable: "isPath u p v \<Longrightarrow> set (pathVertices u p) \<subseteq> reachableNodes u"
proof (induction p arbitrary: u)
  case Nil
  then show ?case unfolding reachableNodes_def by auto
next
  case (Cons a p)
  then show ?case unfolding reachableNodes_def
    by (metis connected_def mem_Collect_eq pathVertices_fwd split_path_at_vertex subsetI)
qed
end

lemma min_dist_eqI: (* TODO use this wherever applicable *)
  "\<lbrakk>Graph.isShortestPath c u p v; Graph.isShortestPath c' u p v\<rbrakk> \<Longrightarrow> Graph.min_dist c u v = Graph.min_dist c' u v"
  unfolding Graph.isShortestPath_min_dist_def by simp

section \<open>Empty graph\<close>
context Graph
begin
definition isEmpty where "isEmpty \<equiv> E = {}"

lemma isEmptyV: "isEmpty \<longleftrightarrow> V = {}" unfolding isEmpty_def V_def by auto

lemma empty_connected: "\<lbrakk>isEmpty; connected u v\<rbrakk> \<Longrightarrow> u = v" unfolding connected_def isEmpty_def
  using isPath_fwd_cases by fastforce
end

(* TODO is there a better way to define constant functions? *)
(*definition empty_graph :: "_ graph" where "empty_graph \<equiv> \<lambda>_. 0"*)
(*interpretation empty: Graph empty_graph .*)

section \<open>Custom induction rules\<close>
context Graph
begin
text \<open>This rule allows us to use isPath as if it were an inductive predicate,
      which is sometimes more convenient\<close>
lemma isPath_front_induct[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isPath u' p' t; \<And>u. P u [] u; \<And>u v p. \<lbrakk>(u, v) \<in> E; isPath v p t; P v p t\<rbrakk> \<Longrightarrow> P u ((u, v) # p) t\<rbrakk> \<Longrightarrow> P u' p' t"
  by (induction p' arbitrary: u') auto

lemma isPath_back_induct[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isPath s p' v'; \<And>u. P u [] u; \<And>p u v. \<lbrakk>(u, v) \<in> E; isPath s p u; P s p u\<rbrakk> \<Longrightarrow> P s (p @ [(u, v)]) v\<rbrakk> \<Longrightarrow> P s p' v'"
  by (induction p' arbitrary: v' rule: rev_induct) (auto simp: isPath_tail)

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

lemma shortestPath_prepend_edge:
  "(u, v) \<in> E \<Longrightarrow> isShortestPath v p w \<Longrightarrow> min_dist u w = Suc (min_dist v w) \<Longrightarrow> isShortestPath u ((u, v) # p) w"
  unfolding isShortestPath_min_dist_def by simp

lemma shortestPath_append_edge:
  "isShortestPath u p v \<Longrightarrow> (v, w) \<in> E \<Longrightarrow> Suc (min_dist u v) = min_dist u w \<Longrightarrow> isShortestPath u (p @ [(v, w)]) w"
  unfolding isShortestPath_min_dist_def by (simp add: isPath_append_edge)

lemma shortestPath_front_induct[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isShortestPath u' p' t; \<And>u. P u [] u; \<And>u v p. \<lbrakk>(u, v) \<in> E; min_dist u t = Suc (min_dist v t); isShortestPath v p t; P v p t\<rbrakk> \<Longrightarrow> P u ((u, v) # p) t\<rbrakk> \<Longrightarrow> P u' p' t"
  apply (induction p' arbitrary: u')
   apply (simp add: Graph.isShortestPath_def)
  apply auto
  by (metis isPath.simps(2) isShortestPath_level_edge(5) isShortestPath_min_dist_def length_Cons list.set_intros(1) nat.inject plus_1_eq_Suc) (* TODO *)

lemma shortestPath_back_induct[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isShortestPath s p' v'; \<And>u. P u [] u; \<And>p u v. \<lbrakk>(u, v) \<in> E; Suc (min_dist s u) = min_dist s v; isShortestPath s p u; P s p u\<rbrakk> \<Longrightarrow> P s (p @ [(u, v)]) v\<rbrakk> \<Longrightarrow> P s p' v'"
  apply (induction p' arbitrary: v' rule: rev_induct)
   apply (simp add: Graph.isShortestPath_def)
  apply auto
  by (metis Nil_is_append_conv isPath.simps(2) isPath_bwd_cases isShortestPath_alt length_append_singleton shortestPath_is_path split_shortest_path) (* TODO *)
  (*apply (auto simp: isShortestPath_min_dist_def)*)
end

section \<open>Alternative definition of paths\<close>
inductive isLinked :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" where
  SelfPrePath: "isLinked u [] u"
| StepPrePath: "isLinked v p w \<Longrightarrow> isLinked u ((u, v) # p) w"

lemma (in Graph) isPath_alt: "isPath u p v \<longleftrightarrow>  isLinked u p v \<and> set p \<subseteq> E"
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

lemma isPath_endpoints_eq:
  "\<lbrakk>Graph.isPath c u p v; Graph.isPath c' u' p v'; p \<noteq> []\<rbrakk> \<Longrightarrow> u' = u"
  "\<lbrakk>Graph.isPath c u p v; Graph.isPath c' u' p v'; p \<noteq> []\<rbrakk> \<Longrightarrow> v' = v"
  by (metis Graph.isPath_head neq_Nil_conv) (metis Graph.isPath_tail rev_exhaust)



section \<open>Unifying different kinds of paths\<close>
locale Path_Kind =
  fixes isKindPath :: "_ graph \<Rightarrow> node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool"
  assumes path_kind: "\<And>c u p v. isKindPath c u p v \<Longrightarrow> Graph.isPath c u p v"
begin
lemma connected: "isKindPath c u p v \<Longrightarrow> Graph.connected c u v"
  using Graph.connected_def path_kind by blast
end

locale Splittable_Path_Kind = Path_Kind +
  assumes split_path: "\<And>c u p\<^sub>1 p\<^sub>2 v. isKindPath c u (p\<^sub>1 @ p\<^sub>2) v \<Longrightarrow> \<exists>w. isKindPath c u p\<^sub>1 w \<and> isKindPath c w p\<^sub>2 v"
begin
lemma split_around_edge:
  assumes "isKindPath c s (p @ (u, v) # p') t"
  shows "(u, v) \<in> Graph.E c
        \<and> isKindPath c s p u \<and> isKindPath c u ((u, v) # p') t
        \<and> isKindPath c s (p @ [(u, v)]) v \<and> isKindPath c v p' t"
proof (intro conjI)
  from assms show "(u, v) \<in> Graph.E c"
    by (meson Graph.isPath_edgeset in_set_conv_decomp path_kind)
next
  from assms obtain w where "isKindPath c s p w" "isKindPath c w ((u, v) # p') t"
    using split_path by blast
  moreover from this have "w = u" by (meson Graph.isPath.simps(2) path_kind)
  ultimately show "isKindPath c s p u" "isKindPath c u ((u, v) # p') t" by auto
next
  from assms obtain w where "isKindPath c s (p @ [(u, v)]) w" "isKindPath c w p' t"
    using split_path by (metis append.assoc append_Cons append_Nil)
  moreover from this have "w = v" by (metis Graph.isPath_tail path_kind snd_conv)
  ultimately show "isKindPath c s (p @ [(u, v)]) v" "isKindPath c v p' t" by auto
qed
end

(* TODO is this useful? *)
locale Connecting_Path_Kind = Path_Kind +
  assumes connecting: "\<And>c u v. Graph.connected c u v \<Longrightarrow> \<exists>p. isKindPath c u p v"
begin
lemma obtain_path:
  assumes "Graph.connected c u v"
  obtains p where "isKindPath c u p v"
  using assms connecting by blast
end

locale Shortest_Path_Kind = Path_Kind +
  assumes shortest_path_kind: "\<And>c u p v. isKindPath c u p v \<Longrightarrow> Graph.isShortestPath c u p v"

(* TODO manually prove the interpretations, then replace the corresponding theorems in Graph.thy *)
interpretation isPath: Splittable_Path_Kind Graph.isPath +
    isPath: Connecting_Path_Kind Graph.isPath
  by unfold_locales (auto simp: Graph.isPath_append Graph.connected_def)

interpretation isSimplePath: Splittable_Path_Kind Graph.isSimplePath +
    Connecting_Path_Kind Graph.isSimplePath
  apply unfold_locales
     apply (simp add: Graph.isSimplePath_def)
    apply (simp add: Graph.split_simple_path)
  apply (simp add: Graph.isSimplePath_def)
  using Graph.connected_def Graph.isSPath_pathLE by blast

interpretation isShortestPath: Splittable_Path_Kind Graph.isShortestPath +
    isShortestPath: Connecting_Path_Kind Graph.isShortestPath
  by unfold_locales (auto simp: Graph.shortestPath_is_path Graph.split_shortest_path elim: Graph.obtain_shortest_path)

definition isBoundedShortestPath :: "nat \<Rightarrow> _ graph \<Rightarrow> node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" where
  "isBoundedShortestPath b c u p v \<equiv> Graph.isShortestPath c u p v \<and> length p \<le> b"

interpretation isBoundedShortestPath: Splittable_Path_Kind "isBoundedShortestPath b" +
    isBoundedShortestPath: Shortest_Path_Kind "isBoundedShortestPath b" for b
  unfolding isBoundedShortestPath_def
  by unfold_locales (auto simp: isShortestPath.path_kind isShortestPath.split_path)

section \<open>Acyclic and distance-bounded graphs\<close>
context Graph
begin
definition isCycle :: "node \<Rightarrow> path \<Rightarrow> bool" where
  "isCycle u p \<equiv> isPath u p u \<and> p \<noteq> []"

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
lemma paths_are_simple: "isPath u p v \<Longrightarrow> isSimplePath u p v"
  using split_non_simple_path acyclic by auto

lemma no_parallel_edge: "(u, v) \<in> E \<Longrightarrow> (v, u) \<notin> E"
  using acyclic isCycle_def[where p="((u, v) # [(v, u)])"] by auto
end

locale Distance_Bounded_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes b :: nat
  assumes bounded: "dist u n v \<Longrightarrow> n \<le> b"
begin
lemma path_length_bounded: "isPath u p v \<Longrightarrow> length p \<le> b" using bounded dist_def by blast

sublocale Acyclic_Graph unfolding Acyclic_Graph_def
  using cycle_induces_arbitrary_length_paths path_length_bounded not_less_eq_eq by blast

lemma b_length_paths_are_terminal:
  assumes PATH: "isPath u p v" and LEN: "length p = b"
  shows "incoming u = {}" "outgoing v = {}"
proof -
  show "incoming u = {}"
  proof (rule ccontr)
    assume "incoming u \<noteq> {}"
    then obtain w where "(w, u) \<in> E" unfolding incoming_def by blast
    with PATH have "isPath w ((w, u) # p) v" by simp
    with LEN show False using path_length_bounded by fastforce
  qed

  show "outgoing v = {}"
  proof (rule ccontr)
    assume "outgoing v \<noteq> {}"
    then obtain w where "(v, w) \<in> E" unfolding outgoing_def by blast
    with PATH have "isPath u (p @ [(v, w)]) w" by (rule isPath_append_edge)
    with LEN show False using path_length_bounded by fastforce
  qed
qed

(* TODO can this proof be done without the ugly precondition? *)
lemma ex_front_terminal_path: "isPath u p v \<Longrightarrow> \<exists>u' p'. isPath u' p' v \<and> incoming u' = {}"
proof (induction "b - length p" arbitrary: u p)
  case 0
  then have "length p = b" using path_length_bounded by fastforce
  with \<open>isPath u p v\<close> have "incoming u = {}" by (rule b_length_paths_are_terminal)
  with \<open>isPath u p v\<close> show ?case by blast
next
  case (Suc x)
  then show ?case
  proof (cases "incoming u = {}")
    case True
    with Suc show ?thesis by blast
  next
    case False
    then obtain w where "(w, u) \<in> E" unfolding incoming_def by blast
    with Suc(1)[of "(w, u) # p"] Suc(2-3) show ?thesis by simp
  qed
qed

lemma obtain_front_terminal_path: obtains u p where "isPath u p v" "incoming u = {}"
  using ex_front_terminal_path by (meson Graph.isPath.simps(1))

corollary obtain_front_terminal_connected: obtains u where "connected u v" "incoming u = {}"
  using obtain_front_terminal_path connected_def by metis

lemma ex_back_terminal_path: "isPath u p v \<Longrightarrow> \<exists>v' p'. isPath u p' v' \<and> outgoing v' = {}"
proof (induction "b - length p" arbitrary: v p)
  case 0
  then have "length p = b" using path_length_bounded by fastforce
  with \<open>isPath u p v\<close> have "outgoing v = {}" by (rule b_length_paths_are_terminal)
  with \<open>isPath u p v\<close> show ?case by blast
next
  case (Suc x)
  then show ?case
  proof (cases "outgoing v = {}")
    case True
    with Suc show ?thesis by blast
  next
    case False
    then obtain w where "(v, w) \<in> E" unfolding outgoing_def by blast
    with Suc(1)[of "p @ [(v, w)]"] Suc(2-3) show ?thesis using isPath_append_edge by fastforce
  qed
qed

lemma obtain_back_terminal_path: obtains v p where "isPath u p v" "outgoing v = {}"
  using ex_back_terminal_path by (meson Graph.isPath.simps(1))

corollary obtain_back_terminal_connected: obtains v where "connected u v" "outgoing v = {}"
  using obtain_back_terminal_path connected_def by metis
end

lemma (in Graph) Distance_Bounded_Graph_PathI:
  "(\<And>u p v. isPath u p v \<Longrightarrow> length p \<le> b) \<Longrightarrow> Distance_Bounded_Graph c b"
  unfolding Distance_Bounded_Graph_def dist_def by blast

text \<open>Note that due to the possible existence of cycles, Finite_Graph does not immediately imply
      Distance_Bounded_Graph.\<close>
locale Finite_Bounded_Graph = Finite_Graph + Distance_Bounded_Graph

lemma (in Finite_Graph) bounded_if_acyclic:
  "Acyclic_Graph c \<Longrightarrow> \<exists>b. Distance_Bounded_Graph c b"
proof
  assume "Acyclic_Graph c"
  then interpret Acyclic_Graph c .
  show "Distance_Bounded_Graph c (card V)"
  proof
    fix u n v
    assume "dist u n v"
    then obtain p where "isSimplePath u p v" "length p = n"
      unfolding dist_def using paths_are_simple by blast
    then show "n \<le> card V" (* TODO simplify *)
      (*by (smt (verit, del_insts) Finite_Graph.simplePath_length_less_V Finite_Graph_EI Graph.V_def Graph.dist_cases Graph.dist_def Vfin_imp_Efin \<open>dist u n v\<close> finite_V isPath_fwd_cases le_add1 le_add_same_cancel1 less_or_eq_imp_le mem_Collect_eq)*)
      by (smt (verit, ccfv_SIG) Graph.V_def Graph.isSimplePath_fwd \<open>dist u n v\<close> dist_cases isPath_fwd_cases leD mem_Collect_eq not_less_eq_eq order_less_imp_le simplePath_length_less_V zero_less_Suc)
  qed
qed


section \<open>Reducing Graphs\<close>
(* TODO check if this is useful *)
(* TODO reduction creates equivalence classes, check whether making this explicit helps *)
definition reduce :: "'capacity::linordered_idom graph \<Rightarrow> 'capacity graph"
  where "reduce c \<equiv> \<lambda>(u, v).
    if c (u, v) > c (v, u) then
      c (u, v) - c (v, u)
    else
      0"

definition reduced_cong :: "'capacity::linordered_idom graph \<Rightarrow> 'capacity graph \<Rightarrow> bool" (infix "\<cong>" 50)
  where "reduced_cong c c' \<equiv> \<forall>u v. c (u, v) - c (v, u) = c' (u, v) - c' (v, u)"

lemma reduced_cong_equivp: "equivp reduced_cong"
  unfolding equivp_def reduced_cong_def by (metis (opaque_lifting))
(* TODO how to do this automatically, similar to ord? *)
(* TODO clean this up *)

lemma reduced_eq_trans[trans]: "\<lbrakk>c\<^sub>1 \<cong> c\<^sub>2; c\<^sub>2 \<cong> c\<^sub>3\<rbrakk> \<Longrightarrow> c\<^sub>1 \<cong> c\<^sub>3" by (simp add: reduced_cong_def)

lemma reduce_reduced_cong: "c \<cong> reduce c" unfolding reduce_def reduced_cong_def by simp

lemma reduced_cong_if_eq: "c = c' \<Longrightarrow> c \<cong> c'" unfolding reduced_cong_def by simp

lemma reduced_cong_iff_reduce_eq: "c \<cong> c' \<longleftrightarrow> reduce c = reduce c'"
  apply (intro iffI)
   apply (fastforce simp: reduce_def reduced_cong_def)
  by (metis equivp_def reduce_reduced_cong reduced_cong_equivp)

locale Nonnegative_Graph = Graph +
  assumes cap_non_negative: "\<And>e. 0 \<le> c e"

locale Irreducible_Graph = Nonnegative_Graph +
  assumes no_parallel_edge: "\<And>u v. (u, v) \<in> E \<Longrightarrow> (v, u) \<notin> E"
begin
lemma no_parallel_capacity: "c (u, v) \<noteq> 0 \<Longrightarrow> c (v, u) = 0"
  using no_parallel_edge unfolding E_def by blast

lemma irreducible[simp]: "reduce c = c"
proof (intro ext, unfold split_paired_all)
  fix u v
  consider (EQ) "c (u, v) = 0" | (G) "c (u, v) > 0"
    using cap_non_negative by (metis order_neq_le_trans)
  then show "reduce c (u, v) = c (u, v)" unfolding reduce_def
    by (smt (verit, best) cap_non_negative case_prod_conv diff_0_right leD no_parallel_edge zero_cap_simp)
qed
end

lemma irreducibleI[intro]: "reduce c = c \<Longrightarrow> Irreducible_Graph c"
  apply unfold_locales unfolding reduce_def Graph.E_def
   apply (smt (verit, ccfv_threshold) leI old.prod.case old.prod.exhaust order.asym)
  by (smt (verit) case_prod_conv mem_Collect_eq order.asym)

section \<open>Subtracting graphs\<close>
context Graph
begin
(* TODO is there a more natural way to define this, as it is merely subtraction of functions? *)
definition subtract_graph :: "_ graph \<Rightarrow> _ graph" where
  "subtract_graph c' \<equiv> \<lambda>e. c e - c' e"

lemma subtract_graph_untouched_cap: "e \<notin> Graph.E c' \<Longrightarrow> subtract_graph c' e = c e"
  unfolding Graph.E_def subtract_graph_def by simp

lemma subtract_graph_untouched_edges: "Graph.E (subtract_graph c') - Graph.E c' = E - Graph.E c'"
  unfolding Graph.E_def subtract_graph_def by auto

definition subtract_skew_graph :: "_ graph \<Rightarrow> _ graph" where
  "subtract_skew_graph c' \<equiv> \<lambda>(u, v). c (u, v) - c' (u, v) + c' (v, u)"
end

section \<open>Layerings\<close>
(* deprecated *)
locale Local_Prelayer_Graph = Graph +
  fixes layer :: "node \<Rightarrow> nat" and S
  assumes path_prelayered: "\<And> u p v. \<lbrakk>u \<in> S; v \<in> S; isPath u p v\<rbrakk> \<Longrightarrow> layer v \<le> layer u + length p"
begin
corollary edge_prelayered: "\<lbrakk>u \<in> S; v \<in> S; (u, v) \<in> E\<rbrakk> \<Longrightarrow> layer v \<le> Suc (layer u)"
  using path_prelayered[where p="[(u, v)]"] by simp

corollary dist_prelayered: "\<lbrakk>u \<in> S; v \<in> S; dist u d v\<rbrakk> \<Longrightarrow> layer v \<le> layer u + d"
  unfolding dist_def using path_prelayered by blast
end

locale Generic_Layer_Graph = Graph +
  fixes layer :: "node \<Rightarrow> nat"
  assumes layer_edge[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (layer u) = layer v"
begin
lemma path_ascends_layer: "isPath u p v \<Longrightarrow> layer v = layer u + length p"
  by (induction rule: isPath_front_induct) auto

sublocale Local_Prelayer_Graph c layer UNIV by unfold_locales (simp add: path_ascends_layer)

corollary dist_layer: "dist u d v \<Longrightarrow> layer v = layer u + d"
  unfolding dist_def using path_ascends_layer by blast

sublocale Acyclic_Graph unfolding Acyclic_Graph_def isCycle_def
  using path_ascends_layer by fastforce

lemma paths_unique_len: "\<lbrakk>isPath u p\<^sub>1 v; isPath u p\<^sub>2 v\<rbrakk> \<Longrightarrow> length p\<^sub>1 = length p\<^sub>2"
  by (fastforce dest: path_ascends_layer)

corollary dist_unique: "\<lbrakk>dist u d\<^sub>1 v; dist u d\<^sub>2 v\<rbrakk> \<Longrightarrow> d\<^sub>1 = d\<^sub>2"
  unfolding dist_def using paths_unique_len by blast

lemma path_is_shortest[intro]: "isPath u p v \<Longrightarrow> isShortestPath u p v"
  unfolding isShortestPath_def using paths_unique_len by (metis order_refl)
end \<comment> \<open>Generic_Layer_Graph\<close>

locale Source_Layer_Graph = Graph +
  fixes s
  assumes s_connected[intro]: "u \<in> V \<Longrightarrow> connected s u"
      and s_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist s u) = min_dist s v" (* TODO which direction is better for simp? *)
begin
abbreviation "layer \<equiv> min_dist s"
sublocale Generic_Layer_Graph c layer by unfold_locales simp

lemma s_in_V_if_nonempty: "\<not> isEmpty \<Longrightarrow> s \<in> V"
  using connected_inV_iff isEmptyV by blast

lemma only_s_without_incoming[simp]: "\<lbrakk>u \<in> V; incoming u = {}\<rbrakk> \<Longrightarrow> u = s"
  using distinct_nodes_have_in_out_if_connected by blast

corollary no_incomingD: "incoming u = {} \<Longrightarrow> u \<notin> V \<or> u = s" by simp

lemma front_terminal_path_is_s_path:
  "isPath u p v \<Longrightarrow> v \<in> V \<Longrightarrow> incoming u = {} \<Longrightarrow> isPath s p v"
  using connected_def connected_inV_iff no_incomingD by blast
end \<comment> \<open>Source_Layer_Graph\<close>

locale Target_Layer_Graph = Graph +
  fixes t
  assumes t_connected[intro]: "u \<in> V \<Longrightarrow> connected u t"
      and t_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist v t) = min_dist u t"
begin
lemma t_in_V_if_nonempty: "\<not> isEmpty \<Longrightarrow> t \<in> V"
  using connected_inV_iff isEmptyV by blast

lemma only_t_without_outgoing[simp]: "\<lbrakk>u \<in> V; outgoing u = {}\<rbrakk> \<Longrightarrow> u = t"
  using distinct_nodes_have_in_out_if_connected by blast

corollary no_outgoingD: "outgoing u = {} \<Longrightarrow> u \<notin> V \<or> u = t" by simp

lemma back_terminal_path_is_t_path:
  "isPath u p v \<Longrightarrow> u \<in> V \<Longrightarrow> outgoing v = {} \<Longrightarrow> isPath u p t"
  using connected_def connected_inV_iff no_outgoingD by blast
end \<comment> \<open>Target_Layer_Graph\<close>

locale Dual_Layer_Graph = Graph +
  fixes s t
  assumes st_connected: "u \<in> V \<Longrightarrow> connected s u \<and> connected u t"
      and st_layered[simp]: "(u, v) \<in> E \<Longrightarrow> Suc (min_dist s u + min_dist v t) = min_dist s t"
begin

lemma obtain_shortest_st_path_via_edge:
  assumes "(u, v) \<in> E"
  obtains p p' where "isShortestPath s (p @ (u, v) # p') t"
proof -
  from assms have "u \<in> V" "v \<in> V" unfolding V_def by auto
  then obtain p p' where "isShortestPath s p u" "isShortestPath v p' t"
    by (meson obtain_shortest_path st_connected)
  with assms have "isShortestPath s (p @ (u, v) # p') t"
    using isShortestPath_min_dist_def isPath_append by simp
  then show ?thesis using that by blast (* TODO prettify *)
qed (* TODO this idea is reused, can this be prevented? Maybe set this up as Intro for ST_Layer_Graph *)

sublocale Source_Layer_Graph unfolding Source_Layer_Graph_def
  by (fastforce elim: obtain_shortest_st_path_via_edge
                dest: isShortestPath.split_around_edge st_connected
                simp: isShortestPath_min_dist_def)

sublocale Target_Layer_Graph unfolding Target_Layer_Graph_def
  by (fastforce elim: obtain_shortest_st_path_via_edge
                dest: isShortestPath.split_around_edge st_connected
                simp: isShortestPath_min_dist_def)

lemma layer_bounded_by_t: "u \<in> V \<Longrightarrow> layer u \<le> layer t"
  using connected_by_dist dist_layer t_connected by fastforce

sublocale Distance_Bounded_Graph c "min_dist s t"
proof
  fix u v n
  assume DIST: "dist u n v"
  then show "n \<le> layer t"
  proof (cases "u = v")
    case True
    with DIST show ?thesis using dist_layer by fastforce
  next
    case False
    with DIST have "v \<in> V" using connected_distI distinct_nodes_in_V_if_connected(2) by blast
    with DIST show ?thesis using dist_layer layer_bounded_by_t by fastforce
  qed
qed
end \<comment> \<open>Dual_Layer_Graph\<close>

\<comment> \<open>Layerings\<close>











(* TODO check if useful *)
context Graph
begin


(* TODO check whether this is useful *)
lemma E_def': "E = {e. c e \<noteq> 0}" unfolding E_def by blast





thm list.cases

(* TODO improve, check if useful *)
(*
lemma parallel_edge_cases:
  obtains (NO_EDGE) "(u, v) \<notin> E" "(v, u) \<notin> E"
  | (EDGE) "(u, v) \<in> E" "(v, u) \<notin> E"
  | (REV_EDGE) "(u, v) \<notin> E" "(v, u) \<in> E"
  | (PARALLEL_EDGE) "(u, v) \<in> E" "(v, u) \<in> E"
  by blast

lemma parallel_edge_cases':
  obtains (NO_EDGE) u v where "(u, v) \<notin> E" "(v, u) \<notin> E"
  | (EDGE) u v where "(u, v) \<in> E" "(v, u) \<notin> E"
  | (REV_EDGE) u v where "(u, v) \<notin> E" "(v, u) \<in> E"
  | (PARALLEL_EDGE) u v where "(u, v) \<in> E" "(v, u) \<in> E"
  by blast

lemma parallel_edge_cases [case_names EDGE REV_EDGE NO_EDGE, cases pred]:
  "\<lbrakk>\<lbrakk>(u, v) \<in> E; (v, u) \<notin> E\<rbrakk> \<Longrightarrow> P (u, v);
    \<lbrakk>(u, v) \<notin> E; (v, u) \<in> E\<rbrakk> \<Longrightarrow> P (u, v);
    \<lbrakk>(u, v) \<notin> E; (v, u) \<notin> E\<rbrakk> \<Longrightarrow> P (u, v)\<rbrakk>
  \<Longrightarrow> P (u, v)" using no_parallel_edge by blast*)





section \<open>Set of nodes within a certain distance\<close>
definition boundedReachableNodes :: "nat \<Rightarrow> node \<Rightarrow> node set" where
  "boundedReachableNodes b u \<equiv> {v. connected u v \<and> min_dist u v \<le> b}"

(* TODO prettify proof *)
lemma boundedReachableNodes_alt:
  "boundedReachableNodes (Suc b) u = boundedReachableNodes b u \<union> E `` boundedReachableNodes b u"
  unfolding boundedReachableNodes_def
  apply auto
    apply (metis (no_types, lifting) ImageI le_antisym mem_Collect_eq min_dist_suc not_less_eq_eq)
  using connected_append_edge min_dist_succ le_trans by blast+

lemma boundedReachableNodes_ss: "boundedReachableNodes b u \<subseteq> reachableNodes u"
  unfolding boundedReachableNodes_def reachableNodes_def by blast

lemma self_boundedReachable: "u \<in> boundedReachableNodes b u"
  unfolding boundedReachableNodes_def by simp

lemma boundedReachableNodes_mono: "a \<le> b \<Longrightarrow> boundedReachableNodes a u \<subseteq> boundedReachableNodes b u"
  unfolding boundedReachableNodes_def by auto

definition exactDistNodes :: "nat \<Rightarrow> node \<Rightarrow> node set" where
  "exactDistNodes b u \<equiv> {v. connected u v \<and> min_dist u v = b}"

lemma exactDistNodes_alt:
  "exactDistNodes (Suc b) u = boundedReachableNodes (Suc b) u - boundedReachableNodes b u"
  unfolding exactDistNodes_def boundedReachableNodes_def by auto

lemma exactDistNodes_reachable_ss: "exactDistNodes b u \<subseteq> boundedReachableNodes b u"
  unfolding exactDistNodes_def boundedReachableNodes_def by blast
end


















(* TODO from here on stuff is experimental *)
section \<open>Optional Distance\<close>
context Graph
begin
(* TODO use *)
definition opt_dist :: "node \<Rightarrow> node \<Rightarrow> nat option" where
  "opt_dist u v \<equiv> if connected u v then Some (min_dist u v) else None"

(* TODO option ordering with None as top element *)
end

end
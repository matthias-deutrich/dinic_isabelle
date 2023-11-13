theory LayerMaintenance
  imports LayerGraph "Flow_Networks.Residual_Graph"
begin
(* TODO check if useful *)
locale BoundedSourceTargetLayering = InducedSourceTargetLayering c s t for c :: "'capacity::linordered_idom graph" and s t +
  fixes b :: nat
  assumes bounded: "connected s t \<Longrightarrow> min_dist s t \<le> b"

context InducedSourceTargetLayering
begin
sublocale BoundedSourceTargetLayering c s t "min_dist s t"
  by unfold_locales blast
end

(* TODO PathFinding *)
(* TODO check if definitions are sound *)
definition rightPassAbstract :: "node \<Rightarrow> 'capacity::linordered_idom graph \<Rightarrow> 'capacity graph"
  where "rightPassAbstract s c \<equiv> \<lambda>(u, v).
    if Graph.connected c s u then
      c (u, v)
    else
      0"
lemma rightPassAbstract_is_c_if_s_connected[simp]:
  "Graph.connected c s u \<Longrightarrow> rightPassAbstract s c (u, v) = c (u, v)"
  unfolding rightPassAbstract_def by simp

lemma rightPassAbstract_maintains_s_connected:
  "Graph.connected c s u \<Longrightarrow> Graph.connected (rightPassAbstract s c) s u" sorry
(* need connectedness to t *)

interpretation right_pass_subgraph: Subgraph "rightPassAbstract s c" c
  unfolding Subgraph_def isSubgraph_def rightPassAbstract_def by simp

definition leftPassAbstract :: "node \<Rightarrow> 'capacity::linordered_idom graph \<Rightarrow> 'capacity graph"
  where "leftPassAbstract t c \<equiv> \<lambda>(u, v).
    if Graph.connected c v t then
      c (u, v)
    else
      0"

lemma leftPassAbstract_is_c_if_s_connected[simp]:
  "Graph.connected c v t \<Longrightarrow> leftPassAbstract t c (u, v) = c (u, v)"
  unfolding leftPassAbstract_def by simp

interpretation left_pass_subgraph: Subgraph "leftPassAbstract t c" c
  unfolding Subgraph_def isSubgraph_def leftPassAbstract_def by simp

lemma leftPassAbstract_z_iff: "leftPassAbstract t c (u, v) \<noteq> 0 \<longleftrightarrow> c (u, v) \<noteq> 0 \<and> Graph.connected c v t"
  unfolding leftPassAbstract_def by simp

definition cleaningAbstract :: "node \<Rightarrow> node \<Rightarrow> 'capacity::linordered_idom graph \<Rightarrow> 'capacity graph"
  where "cleaningAbstract s t c \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t then
      c (u, v)
    else
      0"
lemma cleaningAbstract_is_c_if_doubly_connected[simp]:
  "Graph.connected c s u \<Longrightarrow> Graph.connected c v t \<Longrightarrow> cleaningAbstract s t c (u, v) = c (u, v)"
  unfolding cleaningAbstract_def by simp

lemma left_right_pass_is_cleaning: "cleaningAbstract s t = (leftPassAbstract t) \<circ> (rightPassAbstract s)"
proof (rule ext, rule ext, unfold split_paired_all)
  fix c :: "'capacity::linordered_idom graph"
  fix u v :: node
  show "cleaningAbstract s t c (u, v) = (leftPassAbstract t \<circ> rightPassAbstract s) c (u, v)"
  proof (cases "cleaningAbstract s t c (u, v) = 0", clarsimp)
    case True
    then have "c (u, v) = 0 \<or> \<not> Graph.connected c s u \<or> \<not> Graph.connected c v t" unfolding cleaningAbstract_def by auto
    then show "leftPassAbstract t (rightPassAbstract s c) (u, v) = 0"
    proof (elim disjE)
      assume "c (u, v) = 0"
      then show ?thesis unfolding leftPassAbstract_def rightPassAbstract_def by simp
    next
      assume "\<not> Graph.connected c s u"
      then show ?thesis unfolding leftPassAbstract_def rightPassAbstract_def by simp
    next
      assume "\<not> Graph.connected c v t"
      then have "\<not> Graph.connected (rightPassAbstract s c) v t"
        using right_pass_subgraph.sg_connected_remains_base_connected by blast
      then show ?thesis unfolding leftPassAbstract_def by simp
    qed
  next
    case False
    then have "Graph.connected c s u" "Graph.connected c v t"
      unfolding cleaningAbstract_def
      by (smt (verit) case_prod_conv)+
    then show ?thesis using rightPassAbstract_maintains_s_connected[OF \<open>Graph.connected c s u\<close>] apply simp sorry  using right_pass_subgraph.sg_connected_remains_base_connected
  qed
qed

lemma right_left_pass_is_cleaning: "(rightPassAbstract s) \<circ> (leftPassAbstract t) = cleaningAbstract s t" sorry

corollary right_left_pass_com: "(leftPassAbstract t) \<circ> (rightPassAbstract s) = (rightPassAbstract s) \<circ> (leftPassAbstract t)"
  using left_right_pass_is_cleaning right_left_pass_is_cleaning by metis
(* TODO maybe make commutativity property prettier *)

end
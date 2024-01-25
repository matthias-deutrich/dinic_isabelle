theory LayerMaintenance
  imports LayerGraph
begin

(* TODO unify to locales *)

subsection \<open>Right Pass\<close>

definition right_pass :: "_ graph \<Rightarrow> node \<Rightarrow> _ graph"
  where "right_pass c s \<equiv> \<lambda>(u, v).
    if Graph.connected c s u then
      c (u, v)
    else
      0"

lemma right_pass_nz_iff: "right_pass c s (u, v) \<noteq> 0 \<longleftrightarrow> c (u, v) \<noteq> 0 \<and> Graph.connected c s u"
  unfolding right_pass_def by simp

lemma right_pass_Subgraph: "Subgraph (right_pass c s) c"
  unfolding right_pass_def by fastforce

context Graph
begin
context
  fixes s :: node
begin
abbreviation "rp \<equiv> right_pass c s"

interpretation Subgraph rp c using right_pass_Subgraph .

lemma rp_is_c_if_s_connected[simp]: "connected s u \<Longrightarrow> rp (u, v) = c (u, v)"
  unfolding right_pass_def by simp

lemma rp_edges_s_connected: "(u, v) \<in> E' \<Longrightarrow> connected s u"
  unfolding g'.E_def right_pass_nz_iff by blast

lemma rp_vertices_s_connected: "u \<in> V' \<Longrightarrow> connected s u"
  using E'_ss by (auto intro: rp_edges_s_connected connected_append_edge elim!: g'.vertex_cases)

lemma s_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected s u \<Longrightarrow> (u, v) \<in> E'"
  unfolding Graph.E_def right_pass_nz_iff by blast

lemma rp_keeps_s_paths: "isPath s p u \<Longrightarrow> g'.isPath s p u"
proof (induction rule: isPath_back_induct)
  case (SelfPath u)
  then show ?case by (simp add: Graph.isPath.simps)
next
  case (EdgePath p u v)
  then show ?case using s_connected_edges_remain g'.isPath_append_edge connected_def by blast
qed

corollary rp_keeps_s_connected: "connected s u \<Longrightarrow> g'.connected s u"
  using rp_keeps_s_paths Graph.connected_def by blast

lemma rp_distinct_connected_iff:
  assumes "u \<noteq> v"
  shows "g'.connected u v \<longleftrightarrow> connected s u \<and> connected u v"
proof (rule iffI, intro conjI)
  assume pass_con: "g'.connected u v"
  then show "connected u v" by (rule sg_connected_remains_base_connected)
  from pass_con have "u \<in> V'"
    using assms by (rule g'.distinct_nodes_in_V_if_connected)
  then show "connected s u" by (rule rp_vertices_s_connected)
next
  assume "connected s u \<and> connected u v"
  then obtain p p' where "isPath s p u" "isPath u p' v" using connected_def by blast
  then have "g'.isPath s (p @ p') v"
    using isPath_append rp_keeps_s_paths by blast
  moreover from \<open>isPath u p' v\<close> have "isLinked u p' v" by (rule isLinked_if_isPath)
  ultimately show "g'.connected u v"
    using g'.connected_def g'.isPath_alt by auto
qed
end
end

subsection \<open>Left Pass\<close>

definition left_pass :: "_ graph \<Rightarrow> node \<Rightarrow> _ graph"
  where "left_pass c t \<equiv> \<lambda>(u, v).
    if Graph.connected c v t then
      c (u, v)
    else
      0"

lemma left_pass_nz_iff: "left_pass c t (u, v) \<noteq> 0 \<longleftrightarrow> c (u, v) \<noteq> 0 \<and> Graph.connected c v t"
  unfolding left_pass_def by simp

lemma left_pass_Subgraph: "Subgraph (left_pass c s) c"
  unfolding left_pass_def by fastforce

context Graph
begin
context
  fixes t :: node
begin
abbreviation "lp \<equiv> left_pass c t"

interpretation Subgraph lp c using left_pass_Subgraph .

lemma lp_is_c_if_t_connected[simp]: "connected v t \<Longrightarrow> lp (u, v) = c (u, v)"
  unfolding left_pass_def by simp

lemma lp_edges_t_connected: "(u, v) \<in> E' \<Longrightarrow> connected v t"
  unfolding g'.E_def left_pass_nz_iff by blast

lemma lp_vertices_t_connected: "u \<in> V' \<Longrightarrow> connected u t"
  using E'_ss by (auto intro: lp_edges_t_connected connected_prepend_edge elim!: g'.vertex_cases)

lemma t_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected v t \<Longrightarrow> (u, v) \<in> E'"
  unfolding Graph.E_def left_pass_nz_iff by blast

lemma lp_keeps_t_paths: "isPath u p t \<Longrightarrow> g'.isPath u p t"
proof (induction rule: isPath_front_induct)
  case (SelfPath u)
  then show ?case by (simp add: Graph.isPath.simps)
next
  case (EdgePath u v p)
  then show ?case using t_connected_edges_remain connected_def by auto
qed

corollary lp_keeps_t_connected: "connected u t \<Longrightarrow> g'.connected u t"
  using lp_keeps_t_paths Graph.connected_def by blast

lemma lp_distinct_connected_iff:
  assumes "u \<noteq> v"
  shows "g'.connected u v \<longleftrightarrow> connected u v \<and> connected v t"
proof (rule iffI, intro conjI)
  assume pass_con: "g'.connected u v"
  then show "connected u v" by (rule sg_connected_remains_base_connected)
  from pass_con have "v \<in> V'"
    using assms by (rule g'.distinct_nodes_in_V_if_connected)
  then show "connected v t" by (rule lp_vertices_t_connected)
next
  assume "connected u v \<and> connected v t"
  then obtain p p' where "isPath u p v" "isPath v p' t" using connected_def by blast
  then have "g'.isPath u (p @ p') t"
    using isPath_append lp_keeps_t_paths by blast
  moreover from \<open>isPath u p v\<close> have "isLinked u p v" by (rule isLinked_if_isPath)
  ultimately show "g'.connected u v"
    using g'.connected_def g'.isPath_alt by auto
qed
end
end

subsection \<open>Cleaning\<close>

definition cleaning :: "_ graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> _ graph"
  where "cleaning c s t \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t then
      c (u, v)
    else
      0"

lemma cleaning_nz_iff:
  "cleaning c s t (u, v) \<noteq> 0 \<longleftrightarrow> c (u, v) \<noteq> 0 \<and> Graph.connected c s u \<and> Graph.connected c v t"
  unfolding cleaning_def by simp

lemma cleaning_rp_Subgraph: "Subgraph (cleaning c s t) (right_pass c s)"
  unfolding cleaning_def right_pass_def by fastforce

lemma cleaning_lp_Subgraph: "Subgraph (cleaning c s t) (left_pass c t)"
  unfolding cleaning_def left_pass_def by fastforce

context Graph
begin
context
  fixes s t :: node
begin
abbreviation "cl \<equiv> cleaning c s t"

(* TODO necessary subgraphs *)
interpretation Subgraph cl c
  using cleaning_rp_Subgraph right_pass_Subgraph subgraph.order.trans by blast
(*
thm V_ss
interpretation rp: Subgraph cl "rp s" using cleaning_rp_Subgraph .
thm V_ss
thm rp.V_ss
interpretation lp: Subgraph cl "lp t" using cleaning_lp_Subgraph .
thm V_ss
thm lp.V_ss
thm rp.V_ss*)
(* TODO fix *)

lemma cl_is_c_if_st_connected[simp]: "connected s u \<Longrightarrow> connected v t \<Longrightarrow> cl (u, v) = c (u, v)"
  unfolding cleaning_def by simp

lemma cl_edges_st_connected:
  assumes "(u, v) \<in> g'.E"
  shows "connected s u" "connected v t"
  using assms unfolding g'.E_def cleaning_nz_iff by auto
end

lemma cl_vertices_st_connected:
  assumes "u \<in> V'"
  shows "connected s u" "connected u t"
  using assms apply (auto intro!: rp_vertices_s_connected[where s=s] lp_vertices_t_connected[where t=t])sorry
  using cl_right_sg.V_ss cl_left_sg.V_ss rp_vertices_s_connected lp_vertices_t_connected by auto

lemma st_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected s u \<Longrightarrow> connected v t \<Longrightarrow> (u, v) \<in> cl_graph.E"
  using E_def' cl_graph.zero_cap_simp by fastforce
end

locale ST_Graph = S_Graph + T_Graph
begin
abbreviation "cleaned \<equiv> cleaningAbstract c s t"

sublocale cl_graph: Graph cleaned .

sublocale cl_right_sg: Subgraph cleaned right_pass
  unfolding cleaningAbstract_def by fastforce

sublocale cl_left_sg: Subgraph cleaned left_pass
  unfolding cleaningAbstract_def by fastforce

sublocale cl_sg: Subgraph cleaned c
  using cl_left_sg.Subgraph_axioms lp_sg.Subgraph_axioms by force

lemma cl_is_c_if_st_connected[simp]: "connected s u \<Longrightarrow> connected v t \<Longrightarrow> cleaned (u, v) = c (u, v)"
  unfolding cleaningAbstract_def by simp

lemma cl_edges_st_connected: "(u, v) \<in> cl_graph.E \<Longrightarrow> connected s u"
  "(u, v) \<in> cl_graph.E \<Longrightarrow> connected v t"
  using cl_graph.E_def cleaningAbstract_nz_iff by blast+

lemma cl_vertices_st_connected: "u \<in> cl_graph.V \<Longrightarrow> connected s u"
  and "u \<in> cl_graph.V \<Longrightarrow> connected u t"
  using cl_right_sg.V_ss cl_left_sg.V_ss rp_vertices_s_connected lp_vertices_t_connected by auto

lemma st_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected s u \<Longrightarrow> connected v t \<Longrightarrow> (u, v) \<in> cl_graph.E"
  using E_def' cl_graph.zero_cap_simp by fastforce

(*lemma cl_keeps_st_paths:
  "isPath s p t \<Longrightarrow> cl_graph.isPath s p t"
proof (induction rule: isPath_back_induct)
  case (SelfPath u)
  then show ?case by (simp add: Graph.isPath.simps)
next
  case (EdgePath p u v)
  then show ?case
    using st_connected_edges_remain cl_graph.isPath_append_edge connected_def
qed*)

(* TODO *)
end

context ST_Graph
begin
lemma left_right_pass_is_cleaning: "cleaned = leftPassAbstract right_pass t"
proof (rule ext, unfold split_paired_all)
  fix u v
  (*interpret g: Graph c .*) (* TODO why does this not work *)
  show "cleaned (u, v) = leftPassAbstract right_pass t (u, v)"
  proof (cases "cleaned (u, v) = 0", clarsimp)
    case True
    then have "c (u, v) = 0 \<or> \<not> connected s u \<or> \<not> connected v t" unfolding cleaningAbstract_def by auto
    then show "leftPassAbstract right_pass t (u, v) = 0"
      by (auto simp: leftPassAbstract_def rightPassAbstract_def rp_sg.sg_connected_remains_base_connected)
  next
    case False
    then have "(u, v) \<in> E" and st_connected: "connected s u" "connected v t"
      using cl_graph.E_def cl_sg.E'_ss cleaningAbstract_nz_iff by blast+
    then have "connected s v" using connected_append_edge by blast
    with st_connected have "rp_graph.connected v t"
      by (cases "v = t") (simp_all add: S_Graph.rp_distinct_connected_iff)
    with st_connected show ?thesis by (simp add: T_Graph.lp_is_c_if_s_connected)
  qed
qed

lemma right_left_pass_com: "leftPassAbstract right_pass t = rightPassAbstract left_pass s"
proof (rule ext, unfold split_paired_all)
  fix u v
  show "leftPassAbstract right_pass t (u, v) = rightPassAbstract left_pass s (u, v)"
    by (metis Graph.connected_refl S_Graph.rp_is_c_if_s_connected cl_is_c_if_st_connected cleaningAbstract_nz_iff connected_prepend_edge leftPassAbstract_nz_iff left_right_pass_is_cleaning lp_distinct_connected_iff lp_is_c_if_s_connected rightPassAbstract_nz_iff zero_cap_simp)
qed (* TODO prettiffy *)

corollary right_left_pass_is_cleaning: "cleaned = rightPassAbstract left_pass s"
  using left_right_pass_is_cleaning right_left_pass_com by simp
end











locale T_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes t :: node
begin
abbreviation "left_pass \<equiv> leftPassAbstract c t"

sublocale lp_graph: Graph left_pass .

sublocale lp_sg: Subgraph left_pass c unfolding leftPassAbstract_def by fastforce

lemma lp_is_c_if_s_connected[simp]:
  "connected v t \<Longrightarrow> left_pass (u, v) = c (u, v)"
  unfolding leftPassAbstract_def by simp

lemma lp_edges_t_connected: "(u, v) \<in> lp_graph.E \<Longrightarrow> connected v t"
  using lp_graph.E_def leftPassAbstract_nz_iff by blast

lemma lp_vertices_t_connected: "u \<in> lp_graph.V \<Longrightarrow> connected u t"
  apply (elim lp_graph.vertex_cases)
  using lp_edges_t_connected connected_prepend_edge lp_sg.E'_ss by blast+

lemma t_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected v t \<Longrightarrow> (u, v) \<in> lp_graph.E"
  using E_def' lp_graph.zero_cap_simp by fastforce

lemma lp_keeps_t_paths:
  "isPath u p t \<Longrightarrow> lp_graph.isPath u p t"
proof (induction rule: isPath_front_induct)
  case (SelfPath u)
  then show ?case by (simp add: Graph.isPath.simps)
next
  case (EdgePath p u v)
  then show ?case
    using t_connected_edges_remain connected_def by auto
qed

corollary lp_keeps_s_connected:
  "connected u t \<Longrightarrow> lp_graph.connected u t"
  using lp_keeps_t_paths Graph.connected_def by blast

lemma lp_distinct_connected_iff:
  assumes "u \<noteq> v"
  shows "lp_graph.connected u v \<longleftrightarrow> connected u v \<and> connected v t"
proof (rule iffI, intro conjI)
  assume pass_con: "lp_graph.connected u v"
  then show "connected u v" by (rule lp_sg.sg_connected_remains_base_connected)
  from pass_con have "v \<in> lp_graph.V"
    using assms by (rule lp_graph.distinct_nodes_in_V_if_connected)
  then show "connected v t" by (rule lp_vertices_t_connected)
next
  assume "connected u v \<and> connected v t"
  then obtain p p' where "isPath u p v" "isPath v p' t" using connected_def by blast
  then have "lp_graph.isPath u (p @ p') t"
    using isPath_append lp_keeps_t_paths by blast
  moreover from \<open>isPath u p v\<close> have "isLinked u p v" by (rule isLinked_if_isPath)
  ultimately show "lp_graph.connected u v"
    using lp_graph.connected_def lp_graph.isPath_alt by auto
qed
end

(*
locale S_Graph = Graph c for c :: "'capacity::linordered_idom graph" + (* TODO does this make more sense as an anonymous context? *)
  fixes s :: node
begin
abbreviation "right_pass \<equiv> rightPassAbstract c s"

sublocale rp_graph: Graph right_pass .

sublocale rp_sg: Subgraph right_pass c unfolding rightPassAbstract_def by fastforce

lemma rp_is_c_if_s_connected[simp]:
  "connected s u \<Longrightarrow> right_pass (u, v) = c (u, v)"
  unfolding rightPassAbstract_def by simp

lemma rp_edges_s_connected: "(u, v) \<in> rp_graph.E \<Longrightarrow> connected s u"
  using rp_graph.E_def rightPassAbstract_nz_iff by blast

lemma rp_vertices_s_connected: "u \<in> rp_graph.V \<Longrightarrow> connected s u"
  apply (elim rp_graph.vertex_cases)
  using rp_edges_s_connected connected_append_edge rp_sg.E'_ss by blast+

lemma s_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected s u \<Longrightarrow> (u, v) \<in> rp_graph.E"
  using E_def' rp_graph.zero_cap_simp by fastforce

lemma rp_keeps_s_paths:
  "isPath s p u \<Longrightarrow> rp_graph.isPath s p u"
proof (induction rule: isPath_back_induct)
  case (SelfPath u)
  then show ?case by (simp add: Graph.isPath.simps)
next
  case (EdgePath p u v)
  then show ?case
    using s_connected_edges_remain rp_graph.isPath_append_edge connected_def by blast
qed

corollary rp_keeps_s_connected:
  "connected s u \<Longrightarrow> rp_graph.connected s u"
  using rp_keeps_s_paths Graph.connected_def by blast

lemma rp_distinct_connected_iff:
  assumes "u \<noteq> v"
  shows "rp_graph.connected u v \<longleftrightarrow> connected s u \<and> connected u v"
proof (rule iffI, intro conjI)
  assume pass_con: "rp_graph.connected u v"
  then show "connected u v" by (rule rp_sg.sg_connected_remains_base_connected)
  from pass_con have "u \<in> rp_graph.V"
    using assms by (rule rp_graph.distinct_nodes_in_V_if_connected)
  then show "connected s u" by (rule rp_vertices_s_connected)
next
  assume "connected s u \<and> connected u v"
  then obtain p p' where "isPath s p u" "isPath u p' v" using connected_def by blast
  then have "rp_graph.isPath s (p @ p') v"
    using isPath_append rp_keeps_s_paths by blast
  moreover from \<open>isPath u p' v\<close> have "isLinked u p' v" by (rule isLinked_if_isPath)
  ultimately show "rp_graph.connected u v"
    using rp_graph.connected_def rp_graph.isPath_alt by auto
qed
end \<comment> \<open>S_Graph\<close>
*)


(*locale Finite_S_Graph = Finite_Graph c + S_Graph c s
  for c :: "'capacity::linordered_idom graph" and s*)

(*
definition leftPassAbstract :: "_ graph \<Rightarrow> node \<Rightarrow> _ graph"
  where "leftPassAbstract c t \<equiv> \<lambda>(u, v).
    if Graph.connected c v t then
      c (u, v)
    else
      0"

lemma leftPassAbstract_nz_iff: "leftPassAbstract c t (u, v) \<noteq> 0 \<longleftrightarrow> c (u, v) \<noteq> 0 \<and> Graph.connected c v t"
  unfolding leftPassAbstract_def by simp

locale T_Graph = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes t :: node
begin
abbreviation "left_pass \<equiv> leftPassAbstract c t"

sublocale lp_graph: Graph left_pass .

sublocale lp_sg: Subgraph left_pass c unfolding leftPassAbstract_def by fastforce

lemma lp_is_c_if_s_connected[simp]:
  "connected v t \<Longrightarrow> left_pass (u, v) = c (u, v)"
  unfolding leftPassAbstract_def by simp

lemma lp_edges_t_connected: "(u, v) \<in> lp_graph.E \<Longrightarrow> connected v t"
  using lp_graph.E_def leftPassAbstract_nz_iff by blast

lemma lp_vertices_t_connected: "u \<in> lp_graph.V \<Longrightarrow> connected u t"
  apply (elim lp_graph.vertex_cases)
  using lp_edges_t_connected connected_prepend_edge lp_sg.E'_ss by blast+

lemma t_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected v t \<Longrightarrow> (u, v) \<in> lp_graph.E"
  using E_def' lp_graph.zero_cap_simp by fastforce

lemma lp_keeps_t_paths:
  "isPath u p t \<Longrightarrow> lp_graph.isPath u p t"
proof (induction rule: isPath_front_induct)
  case (SelfPath u)
  then show ?case by (simp add: Graph.isPath.simps)
next
  case (EdgePath p u v)
  then show ?case
    using t_connected_edges_remain connected_def by auto
qed

corollary lp_keeps_s_connected:
  "connected u t \<Longrightarrow> lp_graph.connected u t"
  using lp_keeps_t_paths Graph.connected_def by blast

lemma lp_distinct_connected_iff:
  assumes "u \<noteq> v"
  shows "lp_graph.connected u v \<longleftrightarrow> connected u v \<and> connected v t"
proof (rule iffI, intro conjI)
  assume pass_con: "lp_graph.connected u v"
  then show "connected u v" by (rule lp_sg.sg_connected_remains_base_connected)
  from pass_con have "v \<in> lp_graph.V"
    using assms by (rule lp_graph.distinct_nodes_in_V_if_connected)
  then show "connected v t" by (rule lp_vertices_t_connected)
next
  assume "connected u v \<and> connected v t"
  then obtain p p' where "isPath u p v" "isPath v p' t" using connected_def by blast
  then have "lp_graph.isPath u (p @ p') t"
    using isPath_append lp_keeps_t_paths by blast
  moreover from \<open>isPath u p v\<close> have "isLinked u p v" by (rule isLinked_if_isPath)
  ultimately show "lp_graph.connected u v"
    using lp_graph.connected_def lp_graph.isPath_alt by auto
qed
end \<comment> \<open>T_Graph\<close>

*)
subsection \<open>Cleaning\<close>

definition cleaningAbstract :: "_ graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> _ graph"
  where "cleaningAbstract c s t \<equiv> \<lambda>(u, v).
    if Graph.connected c s u \<and> Graph.connected c v t then
      c (u, v)
    else
      0"

lemma cleaningAbstract_nz_iff:
  "cleaningAbstract c s t (u, v) \<noteq> 0 \<longleftrightarrow> c (u, v) \<noteq> 0 \<and> Graph.connected c s u \<and> Graph.connected c v t"
  unfolding cleaningAbstract_def by simp

locale ST_Graph = S_Graph + T_Graph
begin
abbreviation "cleaned \<equiv> cleaningAbstract c s t"

sublocale cl_graph: Graph cleaned .

sublocale cl_right_sg: Subgraph cleaned right_pass
  unfolding cleaningAbstract_def by fastforce

sublocale cl_left_sg: Subgraph cleaned left_pass
  unfolding cleaningAbstract_def by fastforce

sublocale cl_sg: Subgraph cleaned c
  using cl_left_sg.Subgraph_axioms lp_sg.Subgraph_axioms by force

lemma cl_is_c_if_st_connected[simp]: "connected s u \<Longrightarrow> connected v t \<Longrightarrow> cleaned (u, v) = c (u, v)"
  unfolding cleaningAbstract_def by simp

lemma cl_edges_st_connected: "(u, v) \<in> cl_graph.E \<Longrightarrow> connected s u"
  "(u, v) \<in> cl_graph.E \<Longrightarrow> connected v t"
  using cl_graph.E_def cleaningAbstract_nz_iff by blast+

lemma cl_vertices_st_connected: "u \<in> cl_graph.V \<Longrightarrow> connected s u"
  and "u \<in> cl_graph.V \<Longrightarrow> connected u t"
  using cl_right_sg.V_ss cl_left_sg.V_ss rp_vertices_s_connected lp_vertices_t_connected by auto

lemma st_connected_edges_remain: "(u, v) \<in> E \<Longrightarrow> connected s u \<Longrightarrow> connected v t \<Longrightarrow> (u, v) \<in> cl_graph.E"
  using E_def' cl_graph.zero_cap_simp by fastforce

(*lemma cl_keeps_st_paths:
  "isPath s p t \<Longrightarrow> cl_graph.isPath s p t"
proof (induction rule: isPath_back_induct)
  case (SelfPath u)
  then show ?case by (simp add: Graph.isPath.simps)
next
  case (EdgePath p u v)
  then show ?case
    using st_connected_edges_remain cl_graph.isPath_append_edge connected_def
qed*)

(* TODO *)
end

context ST_Graph
begin
lemma left_right_pass_is_cleaning: "cleaned = leftPassAbstract right_pass t"
proof (rule ext, unfold split_paired_all)
  fix u v
  (*interpret g: Graph c .*) (* TODO why does this not work *)
  show "cleaned (u, v) = leftPassAbstract right_pass t (u, v)"
  proof (cases "cleaned (u, v) = 0", clarsimp)
    case True
    then have "c (u, v) = 0 \<or> \<not> connected s u \<or> \<not> connected v t" unfolding cleaningAbstract_def by auto
    then show "leftPassAbstract right_pass t (u, v) = 0"
      by (auto simp: leftPassAbstract_def rightPassAbstract_def rp_sg.sg_connected_remains_base_connected)
  next
    case False
    then have "(u, v) \<in> E" and st_connected: "connected s u" "connected v t"
      using cl_graph.E_def cl_sg.E'_ss cleaningAbstract_nz_iff by blast+
    then have "connected s v" using connected_append_edge by blast
    with st_connected have "rp_graph.connected v t"
      by (cases "v = t") (simp_all add: S_Graph.rp_distinct_connected_iff)
    with st_connected show ?thesis by (simp add: T_Graph.lp_is_c_if_s_connected)
  qed
qed

lemma right_left_pass_com: "leftPassAbstract right_pass t = rightPassAbstract left_pass s"
proof (rule ext, unfold split_paired_all)
  fix u v
  show "leftPassAbstract right_pass t (u, v) = rightPassAbstract left_pass s (u, v)"
    by (metis Graph.connected_refl S_Graph.rp_is_c_if_s_connected cl_is_c_if_st_connected cleaningAbstract_nz_iff connected_prepend_edge leftPassAbstract_nz_iff left_right_pass_is_cleaning lp_distinct_connected_iff lp_is_c_if_s_connected rightPassAbstract_nz_iff zero_cap_simp)
qed (* TODO prettiffy *)

corollary right_left_pass_is_cleaning: "cleaned = rightPassAbstract left_pass s"
  using left_right_pass_is_cleaning right_left_pass_com by simp
end

subsection \<open>Maintenance when removing paths\<close>
(*thm ST_Graph.cl_sg.Subgraph_axioms*)
(*
lemma cleaning_cap_comp: "CapacityCompatibleGraphs (cleaningAbstract c s t) c"
   unfolding CapacityCompatibleGraphs_def cleaningAbstract_def by auto
*)
context ST_Graph
begin
(*
lemma cleaning_subgraph: "Subgraph (cleaningAbstract c s t) c"
  using cleaning_right_subgraph right_pass_subgraph subgraph.order.trans by blast
*)

lemma cleaning_layered: "Generic_Layer_Graph c l \<Longrightarrow> Generic_Layer_Graph (cleaningAbstract c s t) l"
  unfolding Generic_Layer_Graph_def using cl_sg.edge'_if_edge by blast


(* TODO there are now two abbreviations for the same thing: cl_sg.E' = cl_graph.E *)
(* TODO this is congruent to Shortest_Path_Union, except with all paths. use extra locale? *)
lemma cleaning_edge_set: "cl_graph.E = \<Union>{set p | p. isPath s p t}"
proof (intro pair_set_eqI)
  fix u v
  assume "(u, v) \<in> cl_graph.E"
  then have "connected s u" "connected v t" "(u, v) \<in> E"
    by (auto intro: cl_edges_st_connected cl_sg.edge'_if_edge)
  then obtain p\<^sub>s p\<^sub>t where "isPath s (p\<^sub>s @ (u, v) # p\<^sub>t) t"
    using connected_def isPath_append by auto
  then show "(u, v) \<in> \<Union> {set p |p. isPath s p t}"
    by fastforce
next
  fix u v
  assume "(u, v) \<in> \<Union> {set p |p. isPath s p t}"
  then show "(u, v) \<in> cl_graph.E" (* TODO *)
    by (smt (verit) Graph.isPath_edgeset UnionE lp_edges_t_connected lp_keeps_t_paths mem_Collect_eq rp_edges_s_connected rp_keeps_s_paths st_connected_edges_remain)
qed


lemma layered_cleaning_shortest_path_union:
  "\<exists>l. Generic_Layer_Graph c l \<Longrightarrow> ST_Shortest_Path_Union cleaned c s t"
proof
  assume "\<exists>l. Generic_Layer_Graph c l"
  then obtain l where "Generic_Layer_Graph c l" by blast
  then interpret Generic_Layer_Graph c l .

  show "cl_graph.E = \<Union> {set p |p. isShortestPath s p t}"
    using shortestPath_is_path cleaning_edge_set by fastforce
qed
end


(*
lemma (in Generic_Layer_Graph) cleaning_shortest_path_union:
  "ST_Shortest_Path_Union (cleaningAbstract c s t) c s t" apply unfold_locales
   apply (metis ST_Graph.cl_is_c_if_st_connected cleaningAbstract_nz_iff)
  by (smt (verit, best) Collect_cong ST_Graph.cleaning_edge_set path_is_shortest shortestPath_is_path)
*)

(*
context
  fixes c' c :: "'capacity::linordered_idom graph"
begin
interpretation g': Graph c' .
interpretation Graph c .

lemma "\<forall>p. isShortestPath s p t \<longrightarrow> g'.isPath s p t \<Longrightarrow> ST_Shortest_Path_Union (cleaningAbstract c' s t) c s t"
proof unfold_locales
  assume CONTAINS_SP: "\<forall>p. isShortestPath s p t \<longrightarrow> g'.isPath s p t"
  fix u v
  show "c (u, v) = 0 \<or> cleaningAbstract c' s t (u, v) = 0 \<or> c (u, v) = cleaningAbstract c' s t (u, v)"
    unfolding cleaningAbstract_def apply auto using CONTAINS_SP sorry
  have "Subgraph (cleaningAbstract c' s t) c" sorry
  show "CapacityCompatibleGraphs (cleaningAbstract c' s t) c" sorry
  then h
qed
end
*)

(*
context
  fixes c c' s t p
  assumes PATH: "Graph.isPath c' s p t"
      and NONNEGATIVE: "Nonnegative_Graph c"
      and B_UNION: "Bounded_ST_Shortest_Path_Union c' c s t (Graph.min_dist c s t)"
begin
interpretation Bounded_ST_Shortest_Path_Union c' c s t "Graph.min_dist c s t" using B_UNION .
interpretation Nonnegative_Graph c using NONNEGATIVE .
interpretation g': Nonnegative_Graph c' using sg_Nonnegative_Graph[OF NONNEGATIVE] .

(* TODO does this hold?  NO! due to potential dead ends in g' *)
lemma "Bounded_ST_Shortest_Path_Union (g'.subtract_path p) (subtract_path p) s t b" oops

abbreviation "maintained \<equiv> cleaningAbstract (g'.subtract_path p) s t"

theorem "Bounded_ST_Shortest_Path_Union maintained (subtract_path p) s t (min_dist s t)" oops
end
*)
end
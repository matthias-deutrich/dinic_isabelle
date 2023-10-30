theory Subgraph
imports "Flow_Networks.Graph"
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

text \<open>This rule allows us to use isPath as if it were an inductive predicate,
which is sometimes more convenient\<close>
lemma isPath_custom_induct[consumes 1, case_names SelfPath EdgePath]:
  "\<lbrakk>isPath u' p' v';
    \<And>u. P u [] u;
    \<And>u v p w. \<lbrakk>(u, v) \<in> E; isPath v p w; P v p w\<rbrakk> \<Longrightarrow> P u ((u, v) # p) w\<rbrakk>
  \<Longrightarrow> P u' p' v'"
  using isPathInductive.induct by (simp only: isPathInductive_correct[symmetric]) blast

(* TODO check whether this is useful *)
lemma E_def': "E = {e. c e \<noteq> 0}" unfolding E_def by blast
end

locale Subgraph = g': Graph c' + g: Graph c for c' :: "'capacity::linordered_idom graph" and c :: "'capacity graph" +
  assumes E_ss: "g'.E \<subseteq> g.E"
begin
notation g.E ("E")
notation g'.E ("E''")
notation g.V ("V")
notation g'.V ("V''")

lemma V_ss: "V' \<subseteq> V" unfolding g.V_def g'.V_def using E_ss by blast

lemma sg_paths_are_base_paths: "g'.isPath u p v \<Longrightarrow> g.isPath u p v"
proof (induction rule: g'.isPath_custom_induct)
  case (SelfPath u)
  then show ?case by simp
next
  case (EdgePath u v p w)
  then show ?case using E_ss by auto
qed

lemma shortest_paths_remain_if_contained: "\<lbrakk>g.isShortestPath u p v; g'.isPath u p v\<rbrakk> \<Longrightarrow> g'.isShortestPath u p v"
  using sg_paths_are_base_paths by (meson Graph.isShortestPath_def)

(* TODO use transfer_path *)
end

locale CapacitySubgraph = g': Graph c' + g: Graph c for c' :: "'capacity::linordered_idom graph" and c :: "'capacity graph" +
  assumes cap_abs_le: "\<forall>e.\<bar>c' e\<bar> \<le> \<bar>c e\<bar>" (* TODO assure sign is the same? *)
begin
definition isNode :: "node \<Rightarrow> bool" where "isNode u \<equiv> u \<in> g'.V" (* TODO remove *)
thm isNode_def
end

find_theorems "{x. ?P x} \<subseteq> {y. ?Q y}"
thm Collect_mono

find_theorems "(?P \<Longrightarrow> ?Q) \<Longrightarrow> ?P \<longrightarrow> ?Q"
thm impI

thm mp
thm spec

sublocale CapacitySubgraph \<subseteq> Subgraph
  unfolding Subgraph_def g.E_def' g'.E_def'
  by (rule Collect_mono) (metis abs_0 abs_le_zero_iff cap_abs_le)

context CapacitySubgraph
begin
thm isNode_def
end

locale PosCapacitySubgraph = CapacitySubgraph +
  assumes caps_non_negative: "\<forall>e. c e \<ge> 0 \<and> c' e \<ge> 0"
begin
lemma cap_le: "\<forall>e. c' e \<le> c e" using cap_abs_le caps_non_negative by simp
end


end
theory Subgraph
imports GraphExpanded
begin

locale Subgraph = g': Graph c' + g: Graph c for c' :: "'capacity::linordered_idom graph" and c :: "'capacity graph" +
  assumes E_ss: "g'.E \<subseteq> g.E"
begin
notation g.E ("E")
notation g'.E ("E''")
notation g.V ("V")
notation g'.V ("V''")

lemma V_ss: "V' \<subseteq> V" unfolding g.V_def g'.V_def using E_ss by blast

lemma sg_paths_are_base_paths: "g'.isPath u p v \<Longrightarrow> g.isPath u p v"
(* TODO use transfer_path *)
proof (induction rule: g'.isPath_custom_induct)
  case (SelfPath u)
  then show ?case by simp
next
  case (EdgePath u v p w)
  then show ?case using E_ss by auto
qed

lemma shortest_paths_remain_if_contained: "\<lbrakk>g'.isPath u p v; g.isShortestPath u p v\<rbrakk> \<Longrightarrow> g'.isShortestPath u p v"
  using sg_paths_are_base_paths by (meson Graph.isShortestPath_def)
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
theory Subgraph
imports GraphExpanded
begin

definition isSubgraph :: "_ graph \<Rightarrow> _ graph \<Rightarrow> bool"
  where "isSubgraph c' c \<equiv> \<forall>e. c' e = c e \<or> c' e = 0"

definition isTrueSubgraph :: "_ graph \<Rightarrow> _ graph \<Rightarrow> bool"
  where "isTrueSubgraph c' c \<equiv> isSubgraph c' c \<and> (\<exists>e. c' e \<noteq> c e)"

find_theorems "?P ?A ?B \<Longrightarrow> ?P ?B ?C \<Longrightarrow> ?P ?A ?C"

interpretation subgraph: order isSubgraph isTrueSubgraph
  unfolding isSubgraph_def isTrueSubgraph_def
  apply unfold_locales
  apply metis
  apply force+
  done

locale CapacityLeSubgraph = g': Graph c' + g: Graph c for c' :: "'capacity::linordered_idom graph" and c :: "'capacity graph" +
  assumes cap_abs_le: "\<forall>e.\<bar>c' e\<bar> \<le> \<bar>c e\<bar>" (* TODO assure sign is the same? *)

locale Subgraph = g': Graph c' + g: Graph c for c' :: "'capacity::linordered_idom graph" and c :: "'capacity graph" +
  assumes c'_sg_c: "isSubgraph c' c"
begin
notation g.E ("E")
notation g'.E ("E''")
notation g.V ("V")
notation g'.V ("V''")

lemma E_ss: "E' \<subseteq> E" using c'_sg_c unfolding g.E_def g'.E_def isSubgraph_def by force

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

sublocale Subgraph \<subseteq> CapacityLeSubgraph
  using c'_sg_c
  unfolding CapacityLeSubgraph_def isSubgraph_def
  by (metis abs_ge_zero abs_zero dual_order.refl)


(* locale PosCapacitySubgraph = CapacitySubgraph +
  assumes caps_non_negative: "\<forall>e. c e \<ge> 0 \<and> c' e \<ge> 0"
begin
lemma cap_le: "\<forall>e. c' e \<le> c e" using cap_abs_le caps_non_negative by simp
end *)

end
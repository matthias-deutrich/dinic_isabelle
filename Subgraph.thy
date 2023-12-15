theory Subgraph
imports GraphUtils
begin

definition isSubgraph :: "_ graph \<Rightarrow> _ graph \<Rightarrow> bool"
  where "isSubgraph c' c \<equiv> \<forall>e. c' e = c e \<or> c' e = 0"

definition isProperSubgraph :: "_ graph \<Rightarrow> _ graph \<Rightarrow> bool"
  where "isProperSubgraph c' c \<equiv> isSubgraph c' c \<and> (\<exists>e. c' e \<noteq> c e)"

find_theorems "?P ?A ?B \<Longrightarrow> ?P ?B ?C \<Longrightarrow> ?P ?A ?C"

interpretation subgraph: order isSubgraph isProperSubgraph
  unfolding isSubgraph_def isProperSubgraph_def
  apply unfold_locales
  apply metis
  apply force+
  done
thm subgraph.order_trans
thm subgraph.order_refl

(* TODO is there a way to automatically rename all constants in g' by appending a prime symbol? *)
locale GraphTransfer = g': Graph c' + g: Graph c
  for c' :: "'capacity::linordered_idom graph" and c :: "'capacity graph"
begin
notation g.E ("E")
notation g'.E ("E''")
notation g.V ("V")
notation g'.V ("V''")
end


locale CapacityLeSubgraph = GraphTransfer +
  (* assumes cap_abs_le: "\<forall>e.\<bar>c' e\<bar> \<le> \<bar>c e\<bar>"*)
  assumes cap_abs_le: "\<forall>e. (0 \<le> c' e \<and> c' e \<le> c e) \<or> (c e \<le> c' e \<and> c' e \<le> 0)"

locale Subgraph = GraphTransfer +
  assumes c'_sg_c: "isSubgraph c' c"
begin
lemma E_ss: "E' \<subseteq> E" using c'_sg_c unfolding g.E_def g'.E_def isSubgraph_def by force

lemma V_ss: "V' \<subseteq> V" unfolding g.V_def g'.V_def using E_ss by blast

lemma sg_paths_are_base_paths: "g'.isPath u p v \<Longrightarrow> g.isPath u p v"
  apply (induction rule: g'.isPath_front_induct)
  using E_ss by auto
(* TODO use transfer_path *)

lemma sg_connected_remains_base_connected: "g'.connected u v \<Longrightarrow> g.connected u v"
  unfolding Graph.connected_def using sg_paths_are_base_paths by blast

lemma shortest_paths_remain_if_contained: "\<lbrakk>g'.isPath u p v; g.isShortestPath u p v\<rbrakk> \<Longrightarrow> g'.isShortestPath u p v"
  using sg_paths_are_base_paths by (meson Graph.isShortestPath_def)

(* TODO is this the right location for this? *)
lemma sg_Distance_Bounded: "Distance_Bounded_Graph c b \<Longrightarrow> Distance_Bounded_Graph c' b"
  using sg_paths_are_base_paths by (metis Distance_Bounded_Graph_def Graph.dist_def)
end

locale Proper_Subgraph = GraphTransfer + 
  assumes c'_psg_c: "isProperSubgraph c' c"
begin
sublocale Subgraph
  using c'_psg_c unfolding isProperSubgraph_def Subgraph_def by blast

lemma E_pss: "E' \<subset> E"
proof (rule psubsetI)
  from c'_psg_c obtain e where "c' e = 0" "c e \<noteq> 0"
    unfolding isProperSubgraph_def isSubgraph_def by metis
  then show "E' \<noteq> E" unfolding Graph.E_def' by blast
  show "E' \<subseteq> E" by (rule E_ss)
qed
end


sublocale Subgraph \<subseteq> CapacityLeSubgraph
  using c'_sg_c
  unfolding CapacityLeSubgraph_def isSubgraph_def
  by (metis linorder_le_cases)


locale PosCapacityLeSubgraph = CapacityLeSubgraph +
  assumes caps_non_negative: "\<forall>e. 0 \<le> c e \<and> 0 \<le> c' e"
begin
lemma cap_le: "\<forall>e. c' e \<le> c e" using cap_abs_le caps_non_negative by (meson order.trans)
end

end
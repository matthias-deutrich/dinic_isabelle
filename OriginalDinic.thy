theory OriginalDinic
imports LayerMaintenance "Flow_Networks.Ford_Fulkerson"
begin

context NPreflow
begin
abbreviation "stl \<equiv> induced_st_layering cf s t"
sublocale stl: Graph stl .

interpretation stl': ST_Shortest_Path_Union "induced_st_layering cf s t" cf s t (* TODO name *)
  by (rule induced_st_shortest_path_union)

definition isSTLayeredPath where "isSTLayeredPath p \<equiv> stl.isPath s p t"

lemma st_layered_path_is_augmenting: "isSTLayeredPath p \<Longrightarrow> isAugmentingPath p"
  unfolding isSTLayeredPath_def isAugmentingPath_def
  using cf.shortestPath_is_simple stl'.shortest_path_transfer by blast

lemma shortest_augmenting_path_is_st_layered:
  "\<lbrakk>isAugmentingPath p; cf.isShortestPath s p t\<rbrakk> \<Longrightarrow> isSTLayeredPath p"
  by (simp add: stl.shortestPath_is_path isSTLayeredPath_def stl'.shortest_ST_path_transfer)
end

context NFlow
begin
lemma dinic_ford_fulkerson: "\<not> Ex isSTLayeredPath \<longleftrightarrow> isMaxFlow f"
  using ford_fulkerson shortest_augmenting_path_is_st_layered st_layered_path_is_augmenting
  by (metis cf.connected_def cf.isSimplePath_fwd cf.obtain_shortest_path cf.shortestPath_is_simple isAugmentingPath_def) (* TODO prettify *)
end








(*
GOALS:
- Show that any (augmenting) path in the layer graph is also one in the original
- Show that there can be no augmenting paths in the original graph that are shorter than the s-t
  distance in the layer graph (need the network context for this)
*)
end
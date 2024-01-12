theory OriginalDinic
imports LayerMaintenance "Flow_Networks.Ford_Fulkerson"
begin

context NPreflow
begin
abbreviation "stl \<equiv> induced_st_layering cf s t"
sublocale stl: Graph stl .
sublocale st_union: ST_Shortest_Path_Union "induced_st_layering cf s t" cf s t (* TODO name *)
  by (rule induced_st_shortest_path_union)

definition isSTLayeredPath where "isSTLayeredPath p \<equiv> stl.isPath s p t"

lemma st_layered_path_is_augmenting: "isSTLayeredPath p \<Longrightarrow> isAugmentingPath p"
  unfolding isSTLayeredPath_def isAugmentingPath_def
  using cf.shortestPath_is_simple st_union.shortest_path_transfer by blast

lemma shortest_augmenting_path_is_st_layered:
  "\<lbrakk>isAugmentingPath p; cf.isShortestPath s p t\<rbrakk> \<Longrightarrow> isSTLayeredPath p"
  by (simp add: stl.shortestPath_is_path isSTLayeredPath_def st_union.shortest_ST_path_transfer)
end

(*
definition bounded_st_layering where (* TODO necessary? *)
  "bounded_st_layering c s t b \<equiv> if Graph.min_dist c s t \<le> b
    then induced_st_layering c s t
    else empty_graph"
*)

(* NOTE: while the setup for applying augmenting paths already exists, they are always directly
   applied to the residual graph, which is unfit for our purpose *)

(* TODO check whether this simple definition is best, or whether a more in-depth setup is needed *)
context Graph
begin
definition pathCap :: "path \<Rightarrow> 'capacity"
  where "pathCap p \<equiv> Min {c e | e. e \<in> set p}"

definition subtract_path :: "path \<Rightarrow> _ graph"
  where "subtract_path p \<equiv> \<lambda>(u, v).
    if (u, v) \<in> (set p) then
      c (u, v) - pathCap p
    else
      c (u, v)"
end

context NFlow
begin

text \<open>Start an anonymous context with a fixed path p, allowing us to show auxiliary lemma and interpretations.\<close>
context
  fixes p b cfl
  assumes ST_PATH: "isSTLayeredPath p"
      and CF_LAYERING: "Bounded_ST_Shortest_Path_Union cfl cf s t b"
begin
interpretation Bounded_ST_Shortest_Path_Union cfl cf s t b by (rule CF_LAYERING)

abbreviation "cfl' \<equiv> cleaningAbstract (g'.subtract_path p) s t"

(* interpretation stl': ST_Layer_Graph stl' s t sorry *)

interpretation f': NFlow c s t "augment (augmentingFlow p)"
  unfolding NFlow_def using ST_PATH
  by (fastforce intro: Flow.axioms(1) NPreflow.intro Network_axioms augFlow_resFlow augment_flow_presv st_layered_path_is_augmenting)

theorem layer_maintenance_perfect: "Bounded_ST_Shortest_Path_Union cfl' f'.cf s t b"
proof (unfold_locales)
  oops



lemma residual_dist_increases_if_stl_empty:
  "stl'.isEmpty \<Longrightarrow> cf.min_dist s t < f'.cf.min_dist s t" sorry

text \<open>If removing p from the layer graph does not disconnect s and t (which causes the cleaned graph
      to be empty), the updated layer network is identical to a newly built one.\<close>
lemma layer_maintenance_perfect:
  "\<not> stl'.isEmpty \<Longrightarrow> stl' = f'.stl" oops

thm if_split
find_theorems "(?Q \<Longrightarrow> ?P) \<Longrightarrow> (\<not> ?Q \<Longrightarrow> ?R) \<Longrightarrow> if ?Q then ?P else ?R"
lemma "(Q \<Longrightarrow> P) \<Longrightarrow> (\<not> Q \<Longrightarrow> R) \<Longrightarrow> if Q then P else R" oops
theorem layer_maintenance_perfect:
  "if stl'.isEmpty
    then cf.min_dist s t < f'.cf.min_dist s t
    else stl' = f'.stl"
  apply auto (* TODO how to do this manually *)
proof -
  oops

end


(*
theorem layer_maintenance_perfect:
  assumes "isSTLayeredPath p"
  defines "stl' \<equiv> cleaningAbstract (stl.subtract_path p) s t"
      and "f' \<equiv> augment (augmentingFlow p)"
  shows "if Graph.isEmpty stl' then "
*)
end

(*
fun remove_path_aux :: "'capacity::linordered_idom graph \<Rightarrow> path \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph"
  where "remove_path_aux c [] _ = c"
  | "remove_path_aux c (e # es) cap = remove_path_aux (c(e := c e - cap)) es cap"

definition (in Graph) remove_path :: "path \<Rightarrow> _ graph" where
  "remove_path p \<equiv> remove_path_aux c p (pathCap p)"
*)


context NFlow
begin
(*
lemma dinic_ford_fulkerson': "\<not> Ex isSTLayeredPath \<longleftrightarrow> isMaxFlow f"
  using ford_fulkerson shortest_augmenting_path_is_st_layered st_layered_path_is_augmenting
  by (metis cf.connected_def cf.isSimplePath_fwd cf.obtain_shortest_path cf.shortestPath_is_simple isAugmentingPath_def) (* TODO prettify *)
*)

(* TODO prettify *)
lemma dinic_ford_fulkerson: "stl.isEmpty \<longleftrightarrow> isMaxFlow f"
proof
  assume "stl.isEmpty"
  then have "\<not> Ex isSTLayeredPath"
    using isSTLayeredPath_def stl.connected_def stl.distinct_nodes_in_V_if_connected(1) stl.isEmptyV by blast
  then show "isMaxFlow f" using ford_fulkerson shortest_augmenting_path_is_st_layered
    by (metis cf.connected_def cf.isSimplePath_fwd cf.obtain_shortest_path cf.shortestPath_is_simple isAugmentingPath_def)
next
  assume "isMaxFlow f"
  then have "\<not> Ex isSTLayeredPath" using ford_fulkerson st_layered_path_is_augmenting by blast
  then show "stl.isEmpty" unfolding isSTLayeredPath_def
    using st_union.s_in_V_if_nonempty stl.connected_def by blast
qed
end








(*
GOALS:
- Show that any (augmenting) path in the layer graph is also one in the original
- Show that there can be no augmenting paths in the original graph that are shorter than the s-t
  distance in the layer graph (need the network context for this)
*)
end
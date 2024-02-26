theory Layering_Algo
  imports
    Refinement
    EdmondsKarp_Maxflow.Augmenting_Path_BFS
begin

subsection \<open>Extended BFS\<close>
text \<open>In this section, we present an extended version of breadth-first search, which builds a graph
      consisting of all shortest paths starting at a source node, instead of only a single shortest
      path to a specified destination.

      While we loosely follow the verified implementation of BFS developed for the implementation
      of Edmonds-Karp, there are multiple significant differences. First, unlike standard BFS, we
      care about the capacity of edges as we build a graph instead of a path. Second, we use two
      working sets, since we need to distinguish between nodes in the graph that were added in the
      current phase (which are still eligible edge endpoints) and older nodes.\<close>

(* TODO make the successor function parametric or enable inverting graphs*)
definition (in Graph) inverted where "inverted \<equiv> c \<circ> prod.swap"
find_consts "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<times> 'a) \<Rightarrow> 'c"

(* TODO check whether such a thing exists *)
definition update_edge :: "'capacity graph \<Rightarrow> edge \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph" where
  "update_edge c e cap \<equiv> c(e := cap)"

context Graph
begin

definition ebfs_node :: "node \<Rightarrow> _ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfs_node u c' Q' \<equiv> do {
    let S = (E``{u}) - (Graph.V c' - Q');
    c' \<leftarrow> foreach S (\<lambda>v c'. RETURN (update_edge c' (u, v) (c (u, v)))) c';
    let Q' = Q' \<union> S;
    RETURN (c', Q')
  }"

definition ebfs_phase :: "_ graph \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) nres" where
  "ebfs_phase c' Q \<equiv> foreach Q (\<lambda>u (c', Q'). ebfs_node u c' Q') (c', {})"

definition ebfs_phase_invar :: "node \<Rightarrow> nat \<Rightarrow> node set \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_phase_invar s n Q \<equiv> \<lambda>(c', Q').
    S_Shortest_Path_Union c' c s (boundedReachableNodes (n + 1) s - Q)
    \<and> True" (* TODO Q' property *)

lemma ebfs_phase_step:
  assumes "u \<in> Q" and "Q \<subseteq> exactDistNodes (Suc n) s" and "ebfs_phase_invar s n Q (c', Q')"
  shows "ebfs_node u c' Q' \<le> SPEC (ebfs_phase_invar s n (Q - {u}))"
  sorry

lemma ebfs_phase_final:
  assumes INVAR: "ebfs_phase_invar s "

lemma ebfs_phase_final: oops

lemma ebfs_phase_correct:
  fixes s c' Q n
  assumes "S_Shortest_Path_Union c' c s (boundedReachableNodes n s)"
    and "finite (exactDistNodes (Suc n) s)"
  shows "ebfs_phase c' (exactDistNodes (Suc n) s) \<le> SPEC(\<lambda>(c'', Q'). S_Shortest_Path_Union c'' c s (boundedReachableNodes (Suc n) s) \<and> Q' = exactDistNodes (n + 2) s)"
  unfolding ebfs_phase_def
  apply (refine_vcg FOREACH_rule[where I="ebfs_phase_invar s n"])
  using assms apply blast
  using assms apply (simp add: ebfs_phase_invar_def exactDistNodes_alt boundedReachableNodes_mono double_diff)
  using ebfs_phase_step apply simp

thm FOREACH_rule
(* TODO somewhere we need the fact that the set of reachable nodes (from s) is finite *)

(* TODO is it better to remove any notion of Bounded locales from this part and rely entirely on restricted reachable sets? *)
(*
lemma ebfs_phase_correct:
  fixes s c' Q n
  assumes "Bounded_S_Shortest_Path_Union c' c s V n"
    and "Q = {u. connected s u \<and> min_dist s u = n + 1}"
    and "finite Q"
  shows "ebfs_phase c' Q \<le> SPEC(\<lambda>(c'', Q'). Bounded_S_Shortest_Path_Union c'' c s V (n + 1) \<and> Q' = {u. connected s u \<and> min_dist s u = n + 2})"
  unfolding ebfs_phase_def
  apply (rule FOREACH_rule, clarsimp_all)
proof (refine_vcg)
*)



definition ebfs :: "node \<Rightarrow> _ graph nres" where
  "ebfs s \<equiv> do {
    (c', _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, Q). Q \<noteq> {})
      (uncurry ebfs_phase)
      ((\<lambda>_. 0), {s});
    RETURN c'
  }"


(* TODO the n exists only for analysis purposes, can we remove it? *)
definition ebfs' :: "node \<Rightarrow> _ graph nres" where
  "ebfs' s \<equiv> do {
    (c', _, _) \<leftarrow> WHILE
      (\<lambda>(_, Q, _). Q \<noteq> {})
      (uncurry ebfs_phase)
      ((\<lambda>_. 0), {s});
    RETURN c'
  }"

(*
thm WHILET_rule
thm FOREACH_rule
lemma ebfs_phase_correct: "ebfs_phase_invar s n Q c' \<Longrightarrow> ebfs_phase Q c' \<le> SPEC (uncurry (\<lambda>Q' c'. ebfs_phase_invar s (n + 1) Q' c'))"
thm FOREACH_rule[where I="ebfs_phase_invar s n"]
  unfolding ebfs_phase_def
  apply (refine_vcg FOREACH_rule[where I="ebfs_phase_invar s n"])
*)

(*definition ebfs_phase_invar :: *)

(*
definition ebfs_invar :: "node \<Rightarrow> nat \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_invar s n \<equiv> \<lambda>(c', Q).
    Bounded_S_Shortest_Path_Union c' c s V n
    \<and> Q = {u. connected s u \<and> min_dist s u = n + 1}"
*)

(* TODO use or remove *)
definition ebfs_invar' :: "node \<Rightarrow> (nat \<times> _ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_invar' s \<equiv> \<lambda>(n, c', Q).
    Bounded_S_Shortest_Path_Union c' c s V n
    \<and> Q = {u. connected s u \<and> min_dist s u = n + 1}"

definition ebfs_invar :: "node \<Rightarrow> (_ graph \<times> node set) \<Rightarrow> bool" where
  "ebfs_invar s \<equiv> \<lambda>(c', Q). \<exists> n.
    Bounded_S_Shortest_Path_Union c' c s V n
    \<and> Q = {u. connected s u \<and> min_dist s u = n + 1}"

lemma ebfs_phase_correct': "ebfs_invar' s (n, c', Q) \<Longrightarrow> ebfs_phase c' Q \<le> SPEC (\<lambda>x. ebfs_invar' s (Suc n, x))" sorry

lemma ebfs_phase_correct: "ebfs_invar s (c', Q) \<Longrightarrow> ebfs_phase c' Q \<le> SPEC (\<lambda>x. ebfs_invar s x)" sorry

thm WHILE_rule
theorem ebfs'_correct: "ebfs' s \<le> (spec x. S_Shortest_Path_Union c' c s V)"
  unfolding ebfs'_def
  apply (refine_vcg WHILE_rule[where I="ebfs_invar s"])




  thm WHILE_rule[where I="ebfs_invar s" and f="uncurry ebfs_phase"]
  apply (rule WHILE_rule[where I="ebfs_invar s"])
  prefer 3
  apply refine_vcg
  apply (rule WHILE_rule)
  thm WHILE_rule
  thm WHILE_rule[where I="ebfs_invar s" and \<Phi>="\<lambda>c'. S_Shortest_Path_Union c' c s V"]
  sorry apply (refine_vcg WHILE_rule[where I="ebfs_invar s"])
end
end
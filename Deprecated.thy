theory Deprecated
  imports Original_Dinitz_Impl
begin


subsection \<open>PathFinding\<close>

context Graph
begin
text \<open>Used primitives:
  - RES (outgoing u) / checking outgoing u for emptyness
  - list append\<close>

(* TODO tail recursive version using Cons rather than append *)
definition pathFindingRefine_partial :: "node \<Rightarrow> path nres" where
  "pathFindingRefine_partial s \<equiv> do {
    (p, _) \<leftarrow> WHILE (\<lambda>(p, u). outgoing u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> RES (outgoing u);
      let p = p @ [e];
      let u = snd e;
      RETURN (p, u)
    }) ([], s);
    RETURN p
  }"

definition pathFinding_invar :: "node \<Rightarrow> (path \<times> node) \<Rightarrow> bool" where
  "pathFinding_invar s \<equiv> \<lambda>(p, u). isPath s p u"

lemma pathFinding_finds_maximal_path: "pathFindingRefine_partial s \<le> SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
  unfolding pathFindingRefine_partial_def
  apply (refine_vcg WHILE_rule[where I="pathFinding_invar s"])
  unfolding pathFinding_invar_def outgoing_def by (auto simp: isPath_append_edge)
end \<comment> \<open>Graph\<close>

subsubsection \<open>Total correctness\<close>

definition (in Graph) pathFindingRefine_total :: "node \<Rightarrow> path nres" where
  "pathFindingRefine_total s \<equiv> do {
    (p, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(p, u). outgoing u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> RES (outgoing u);
      let p = p @ [e];
      let u = snd e;
      RETURN (p, u)
    }) ([], s);
    RETURN p
  }"

context Distance_Bounded_Graph
begin
(* TODO redo with bounded measure *)
term "measure (\<lambda>p. b - length p)"
thm wf_bounded_measure

(*definition bounded_path_measure :: "path rel" where "bounded_path_measure \<equiv> measure (\<lambda>p. b - length p)"
definition bounded_path_measure' where "bounded_path_measure \<equiv> measure (\<lambda>p. b - length p)"
term bounded_path_measure
term "pathFindingRefine_total s"
term "SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
term b
thm WHILET_rule*)

lemma pathFinding_total_correct:
  "pathFindingRefine_total s \<le> SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
  unfolding pathFindingRefine_total_def
  apply (refine_vcg WHILET_rule[where
          R="inv_image (measure (\<lambda>p. b - length p)) fst"
          and I="pathFinding_invar s"])
unfolding pathFinding_invar_def outgoing_def apply (auto intro: isPath_append_edge)
  by (metis Distance_Bounded_Graph_def Graph.dist_suc Graph.isPath_distD diff_less_mono2 lessI less_eq_Suc_le local.Distance_Bounded_Graph_axioms)
(* TODO fix this *)

(*  apply (refine_vcg WHILET_rule[where I="pathFinding_invar s" and R="inv_image bounded_path_measure fst"])
      apply (auto simp:pathFinding_invar_def bounded_path_measure_def dest!: in_outgoingD)[]
     apply (auto simp:pathFinding_invar_def bounded_path_measure_def dest!: in_outgoingD)[]
    defer
  defer
apply (auto simp:pathFinding_invar_def bounded_path_measure_def dest!: in_outgoingD)[]*)
(*
proof (intro WHILET_rule[where I="pathFinding_invar s"] refine_vcg, clarsimp_all dest!: in_outgoingD)
  show "wf (inv_image bounded_path_measure fst)" unfolding bounded_path_measure_def by blast
next
  fix p u v
  assume STEP: "pathFinding_invar s (p, u)" "(u, v) \<in> E"
  then have "isPath s p u" and PATH': "isPath s (p @ [(u, v)]) v"
    unfolding pathFinding_invar_def by (simp_all add: isPath_append_edge)
  then have "((p @ [(u, v)]), p) \<in> bounded_path_measure" unfolding bounded_path_measure_def
    using path_length_bounded by fastforce
  with PATH' show "pathFinding_invar s (p @ [(u, v)], v) \<and> ((p @ [(u, v)], v), p, u) \<in> inv_image bounded_path_measure fst"
    unfolding pathFinding_invar_def by simp
qed (auto simp: pathFinding_invar_def)
*)

end \<comment> \<open>Distance_Bounded_Graph\<close>




(*context ST_Graph
begin
lemma back_terminal_s_path_is_st_path:
  "stl.outgoing u = {} \<Longrightarrow> stl.connected s t\<Longrightarrow> stl.isPath s p u \<Longrightarrow> stl.isPath s p t"
proof (drule stl.no_outgoingD, elim disjE)
  assume PATH: "stl.isPath s p u" and CON: "stl.connected s t" and "u \<notin> stl.V"
  then have "s \<notin> stl.V" "p = []"
    using stl.acyclic stl.isCycle_def
    by (metis stl.connected_def stl.distinct_nodes_in_V_if_connected(2))+
  with PATH CON show "stl.isPath s p t"
    using Graph.distinct_nodes_in_V_if_connected(1) Graph.isPath.simps(1) by blast
qed (auto intro: stl_sub_c.sg_paths_are_base_paths) (* TODO cleanup *)

thm order_trans
thm nrec.leq_trans

lemma pathFinding_partial_finds_st_path:
  assumes "connected s t"
  shows "stl.pathFindingRefine_partial s \<le> SPEC (\<lambda>p. isPath s p t)"
  apply (rule order_trans[OF stl.pathFinding_finds_maximal_path], rule SPEC_rule)
  using stl_maintains_st_connected[OF \<open>connected s t\<close>] back_terminal_s_path_is_st_path stl_sub_c.sg_paths_are_base_paths by blast
(* TODO cleanup *)
end \<comment> \<open>ST_Graph\<close>

locale TMPLoc = ST_Graph + Distance_Bounded_Graph
begin
lemma pathFinding_total_finds_st_path:
  assumes "connected s t"
  shows "stl.pathFindingRefine_total s \<le> SPEC (\<lambda>p. isPath s p t)"
proof -
  note stl.pathFinding_total_correct
  also have "SPEC (\<lambda>p. \<exists>u. stl.outgoing u = {} \<and> stl.isPath s p u) \<le> SPEC (\<lambda>p. isPath s p t)"
    apply (rule SPEC_rule)
    using stl_maintains_st_connected[OF \<open>connected s t\<close>] back_terminal_s_path_is_st_path stl_sub_c.sg_paths_are_base_paths by blast
  finally show ?thesis .
qed
end*)

context ST_Layer_Graph
begin
lemma pathFinding_partial_finds_st_path:
  "s \<in> V \<Longrightarrow> pathFindingRefine_partial s \<le> SPEC (\<lambda>p. isPath s p t)"
  apply (intro order_trans[OF pathFinding_finds_maximal_path] SPEC_rule)
  using back_terminal_path_is_t_path by blast

lemma pathFinding_total_finds_st_path:
  "s \<in> V \<Longrightarrow> pathFindingRefine_total s \<le> SPEC (\<lambda>p. isPath s p t)"
  apply (intro order_trans[OF pathFinding_total_correct] SPEC_rule)
  using back_terminal_path_is_t_path by blast
end

\<comment> \<open>PathFinding\<close>

(* This is the exact definition, using the edge set*)
definition rightPassRefine_original :: "_ graph \<Rightarrow> edge set \<Rightarrow> (_ graph) nres" where
  "rightPassRefine_original c Q \<equiv> do {
    (c, _) \<leftarrow> WHILE (\<lambda>(_, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      e \<leftarrow> RES Q;
      let Q = Q - {e};
      let v = snd e;
      if Graph.incoming c v = {} then do {
        let R = Graph.outgoing c v;
        let Q = Q \<union> R;
        let c = removeEdges c R;
        RETURN (c, Q)}
      else RETURN (c, Q)
    }) (c, Q);
    RETURN c
  }"
end
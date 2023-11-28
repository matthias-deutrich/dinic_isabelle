theory Refinement
  imports "Collections.Refine_Dflt_Only_ICF" LayerMaintenance
begin

subsection \<open>PathFinding\<close>

context Graph
begin
definition pathFindingRefine :: "node \<Rightarrow> path nres" where
  "pathFindingRefine s \<equiv> do {
    (p, _) \<leftarrow> WHILE (\<lambda>(p, u). outgoing u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> SPEC (\<lambda>e. e \<in> outgoing u);
      let p = p @ [e];
      let u = snd e;
      RETURN (p, u)
    }) ([], s);
    RETURN p
  }"

definition pathFinding_invar :: "node \<Rightarrow> (path \<times> node) \<Rightarrow> bool" where
  "pathFinding_invar s \<equiv> \<lambda>(p, u). isPath s p u"

lemma pathFinding_invar_step:
  "\<lbrakk>e \<in> outgoing u; pathFinding_invar s (p, u)\<rbrakk> \<Longrightarrow> pathFinding_invar s (p @ [e], snd e)"
  unfolding pathFinding_invar_def by (auto simp: isPath_tail outgoing_def)

lemma pathFinding_finds_maximal_path: "pathFindingRefine s \<le> SPEC (\<lambda>p. \<exists>u. outgoing u = {} \<and> isPath s p u)"
  unfolding pathFindingRefine_def
  apply (intro WHILE_rule[where I="pathFinding_invar s"] refine_vcg)
    apply (auto intro: pathFinding_invar_step)
  unfolding pathFinding_invar_def by auto
end \<comment> \<open>Graph\<close>

context ST_Graph
begin
(* TODO useful? then move *)
lemma stl_no_outD: "stl.outgoing u = {} \<Longrightarrow> u = t \<or> u \<notin> stl.V"
  using only_t_without_stl_outgoing by blast


find_theorems "(?A :: _ nres) \<le> ?B \<Longrightarrow> ?B \<le> ?C \<Longrightarrow> ?A \<le> ?C"
thm SPEC_trans
thm nrec.leq_trans


find_theorems "SPEC ?A \<le> SPEC ?B"
thm SPEC_rule
thm iSPEC_rule
(* TODO why are there two? *)

lemma pathFinding_finds_st_path:
  assumes "connected s t"
  shows "stl.pathFindingRefine s \<le> SPEC (\<lambda>p. isPath s p t)"
proof (rule nrec.leq_trans[OF stl.pathFinding_finds_maximal_path], rule SPEC_rule)
  fix p
  assume "\<exists>u. stl.outgoing u = {} \<and> stl.isPath s p u"
  then obtain u where NO_OUT: "stl.outgoing u = {}" and PATH: "stl.isPath s p u" by blast
  then have "u = t \<or> u \<notin> stl.V" using stl_no_outD by simp
  with PATH show "isPath s p t"
  proof (elim disjE)
    assume "u \<notin> stl.V"
    with PATH have "u = s" "p = []"
      using stl.acyclic stl.isCycle_def
      by (metis stl.connected_def stl.distinct_nodes_in_V_if_connected(2))+
    with NO_OUT have "s = t \<or> s \<notin> stl.V" using stl_no_outD by blast
    with assms have "s = t"
      using stl.distinct_nodes_in_V_if_connected stl_maintains_st_connected by blast
    with \<open>p = []\<close> show ?thesis by simp
  qed (auto intro: stl_sub_c.sg_paths_are_base_paths)
qed (* TODO prettify *)
end \<comment> \<open>ST_Graph\<close>

\<comment> \<open>PathFinding\<close>

subsection \<open>RightPass\<close>

definition removeEdge :: "_ graph \<Rightarrow> edge \<Rightarrow> _ graph" where
  "removeEdge c e \<equiv> c(e := 0)"

(* TODO check definition *)
definition rightPassRefine :: "_ graph \<Rightarrow> edge set \<Rightarrow> (_ graph) nres" where
  "rightPassRefine c Q \<equiv> do {
    (c, _) \<leftarrow> WHILE (\<lambda>(c, Q). Q \<noteq> {}) (\<lambda>(c, Q). do {
      e \<leftarrow> SPEC (\<lambda>e. e \<in> Q);
      let Q = Q - {e};
      let v = snd e;
      if Graph.incoming c v = {} then do {
        let Q = Q \<union> Graph.outgoing c v;
        let c = removeEdge c e;
        RETURN (c, Q)}
      else RETURN (c, Q)
    }) (c, Q);
    RETURN c
  }"

\<comment> \<open>RightPass\<close>

end
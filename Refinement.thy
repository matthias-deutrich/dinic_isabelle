theory Refinement
  imports "Collections.Refine_Dflt_Only_ICF" LayerMaintenance
begin

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

(*
definition pathFindingRefine :: "_ graph  \<Rightarrow> node \<Rightarrow> path nres" where
  "pathFindingRefine c s \<equiv> do {
    (p, _) \<leftarrow> WHILE (\<lambda>(p, u). Graph.outgoing c u \<noteq> {}) (\<lambda>(p, u). do {
      e \<leftarrow> SPEC (\<lambda>e. e \<in> Graph.outgoing c u);
      let p = p @ [e];
      let u = snd e;
      RETURN (p, u)
    }) ([], s);
    RETURN p
  }"

definition pathFinding_invar :: "_ graph \<Rightarrow> node \<Rightarrow> (path \<times> node) \<Rightarrow> bool" where
  "pathFinding_invar c s \<equiv> \<lambda>(p, u). Graph.isPath c s p u"

lemma pathFinding_invar_step:
  "\<lbrakk>e \<in> Graph.outgoing c u; pathFinding_invar c s (p, u)\<rbrakk> \<Longrightarrow> pathFinding_invar c s (p @ [e], snd e)"
  unfolding pathFinding_invar_def using Graph.isPath_tail Graph.outgoing_def
  by (smt (verit, best) case_prod_conv fst_conv mem_Collect_eq)

lemma pathFinding_finds_path: "pathFindingRefine c s \<le> SPEC (\<lambda>p. \<exists>u. Graph.isPath c s p u)"
  unfolding pathFindingRefine_def
  apply (intro WHILE_rule[where I="pathFinding_invar c s"] refine_vcg)
    apply (auto intro: pathFinding_invar_step)
  unfolding pathFinding_invar_def
   apply (auto simp: Graph.isPath.simps)
  done
*)

thm it_step_insert_iff


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

(*
lemma pathFinding_invar_step:
  "\<lbrakk>e \<in> outgoing u; pathFinding_invar s (p, u)\<rbrakk> \<Longrightarrow> pathFinding_invar s (p @ [e], snd e) \<and> snd e \<in> V"
  unfolding pathFinding_invar_def V_def using isPath_tail outgoing_def by fastforce
*)

lemma pathFinding_invar_step:
  "\<lbrakk>e \<in> outgoing u; pathFinding_invar s (p, u)\<rbrakk> \<Longrightarrow> pathFinding_invar s (p @ [e], snd e)"
  unfolding pathFinding_invar_def by (auto simp: isPath_tail outgoing_def)

lemma tmp: 
  "\<lbrakk>e \<in> outgoing u; pathFinding_invar s (p, u)\<rbrakk> \<Longrightarrow> snd e \<in> V"
  unfolding pathFinding_invar_def V_def using outgoing_def by fastforce

lemma pathFinding_finds_path: "pathFindingRefine s \<le> SPEC (\<lambda>p. \<exists>u. isPath s p u)"
  unfolding pathFindingRefine_def
  apply (intro WHILE_rule[where I="pathFinding_invar s"] refine_vcg)
    apply (auto intro: pathFinding_invar_step)
  unfolding pathFinding_invar_def by auto
end

thm if_split
thm case_split

(*
lemma (in Graph) tmp':
  assumes "isPath u p v" "v \<notin> V"
  obtains "u \<notin> V" "p = []"
  using assms sledgehammer
*)

context ST_Graph
begin
(* TODO useful? then move *)
lemma stl_no_outD: "stl.outgoing u = {} \<Longrightarrow> u = t \<or> u \<notin> stl.V"
  using only_t_without_stl_outgoing by blast


lemma pathFinding_finds_st_path:
  assumes "connected s t"
  shows "stl.pathFindingRefine s \<le> SPEC (\<lambda>p. isPath s p t)"
  unfolding stl.pathFindingRefine_def
proof (intro WHILE_rule[where I="stl.pathFinding_invar s"] refine_vcg, simp_all)
  show "stl.pathFinding_invar s ([], s)" unfolding stl.pathFinding_invar_def by simp
next
  fix p u e
  assume "e \<in> stl.outgoing u" "stl.pathFinding_invar s (p, u)"
  then show "stl.pathFinding_invar s (p @ [e], snd e)" by (rule stl.pathFinding_invar_step)
next
  fix p u
  assume "stl.outgoing u = {}" "stl.pathFinding_invar s (p, u)"
  then have "u = t \<or> u \<notin> stl.V" "stl.isPath s p u" unfolding stl.pathFinding_invar_def
    using stl_no_outD by auto
  then show "isPath s p t"
  proof (elim disjE)
    assume "u = t"
    with \<open>stl.isPath s p u\<close> show "isPath s p t" using stl_sub_c.sg_paths_are_base_paths by blast
  next
    assume "u \<notin> stl.V"
    with \<open>stl.isPath s p u\<close> have "u = s" "p = []"
      using stl.acyclic stl.isCycle_def
      by (metis stl.connected_def stl.distinct_nodes_in_V_if_connected(2))+
    with \<open>stl.outgoing u = {}\<close> have "s = t \<or> s \<notin> stl.V" using stl_no_outD by blast
    with assms have "s = t"
      using stl.distinct_nodes_in_V_if_connected stl_maintains_st_connected by blast
    with \<open>p = []\<close> show ?thesis by simp
  qed
qed (* TODO prettify *)
end





(* v \<leftarrow> SPEC (\<lambda>v. v \<in> snd ` Q); *)


find_consts "'a set \<Rightarrow> 'a \<Rightarrow> bool"
thm contains_def
thm if_split
thm prod.splits

end
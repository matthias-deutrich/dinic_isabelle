theory GraphExpanded
imports "Flow_Networks.Graph"
begin

(* TODO check whether useful *)
inductive isPrePath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" where
  SelfPrePath: "isPrePath u [] u"
| StepPrePath: "isPrePath v p w \<Longrightarrow> isPrePath u ((u, v) # p) w"

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

thm isPath.induct

(* TODO check whether this is useful *)
lemma E_def': "E = {e. c e \<noteq> 0}" unfolding E_def by blast

lemma isPath_alt: "isPath u p v \<longleftrightarrow>  isPrePath u p v \<and> (set p) \<subseteq> E"
proof
  assume "isPath u p v"
  then show "isPrePath u p v \<and> (set p) \<subseteq> E"
    by (induction rule: isPath_custom_induct) (simp_all add: isPrePath.intros)
next
  assume "isPrePath u p v \<and> (set p) \<subseteq> E"
  then have "isPrePath u p v" "(set p) \<subseteq> E" by blast+
  then show "isPath u p v" by (induction rule: isPrePath.induct) simp_all
qed
end

lemma isPrePath_if_isPath_in_some_graph: "\<exists>c. Graph.isPath c u p v \<Longrightarrow> isPrePath u p v"
  using Graph.isPath_alt by blast

thm Graph.isPath.elims
thm Graph.isPath_fwd_cases
lemma (in Graph) "isPath u p v \<Longrightarrow> p \<noteq> [] \<Longrightarrow> u \<in> V" (* TODO use or remove *)
  using V_def isPath_fwd_cases by fastforce
end
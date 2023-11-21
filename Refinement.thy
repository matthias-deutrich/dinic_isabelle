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

(* v \<leftarrow> SPEC (\<lambda>v. v \<in> snd ` Q); *)


find_consts "'a set \<Rightarrow> 'a \<Rightarrow> bool"
thm contains_def
thm if_split
thm prod.splits

end
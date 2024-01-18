theory Dinic_Algo
  imports Refinement "Flow_Networks.Ford_Fulkerson"
begin

(*
definition "edka \<equiv> do {
  let f = (\<lambda>_. 0);

  (f,_) \<leftarrow> while\<^sub>T\<^bsup>fofu_invar\<^esup>
    (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,_). do {
      p \<leftarrow> find_shortest_augmenting_spec f;
      case p of 
        None \<Rightarrow> return (f,True)
      | Some p \<Rightarrow> do {
          assert (p\<noteq>[]);
          assert (NPreflow.isAugmentingPath c s t f p);
          assert (Graph.isShortestPath (residualGraph c f) s p t);
          let f = NFlow.augment_with_path c f p;
          assert (NFlow c s t f);
          return (f, False)
        }  
    })
    (f,False);
  assert (NFlow c s t f);
  return f 
}"
*)

context Network
begin

(* The second parameter n means "there cannot be st-paths with length \<le> n" *)
(* TODO where can we wildcard f/n*)
(*
definition dinic :: "_ flow nres" where
  "dinic \<equiv> do {
    (f, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, n). n < card V)
      (\<lambda>(f, _). do {
        ASSERT (NFlow c s t f);
        let stl = induced_st_layering (residualGraph c f) s t;
        if Graph.connected stl s t
          then do {
            let n = Graph.min_dist stl s t;
            (f, _) \<leftarrow> WHILE\<^sub>T
              (\<lambda>(_, stl). Graph.connected stl s t)
              (\<lambda>(f, stl). do {
                p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
                ASSERT (Nonnegative_Graph stl);
                let stl = Nonnegative_Graph.subtract_path stl p;
                ASSERT (NFlow c s t f);
                let f = NFlow.augment c f (NPreflow.augmentingFlow c f p);
                RETURN (f, stl)})
              (f, stl);
            RETURN (f, n)}
          else RETURN (f, (card V))})
      ((\<lambda>_. 0), 0);
    RETURN f}"
*)

definition dinic :: "_ flow nres" where
  "dinic \<equiv> do {
    (f, _) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(_, n). n < card V)
      (\<lambda>(f, _). do {
        let stl = induced_st_layering (residualGraph c f) s t;
        if Graph.connected stl s t
          then do {
            let n = Graph.min_dist stl s t;
            (f, _) \<leftarrow> WHILE\<^sub>T
              (\<lambda>(_, stl). Graph.connected stl s t)
              (\<lambda>(f, stl). do {
                p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
                let stl = Nonnegative_Graph.subtract_path stl p;
                let f = NFlow.augment c f (NPreflow.augmentingFlow c f p);
                RETURN (f, stl)})
              (f, stl);
            RETURN (f, n)}
          else RETURN (f, (card V))})
      ((\<lambda>_. 0), 0);
    RETURN f}"

theorem dinic_correct: "dinic \<le> SPEC (\<lambda>f. isMaxFlow f)" oops
end

context NFlow
begin
definition dinic_inner :: "(_ flow \<times> nat) nres" where
  "dinic_inner \<equiv> do {
    let stl = induced_st_layering (residualGraph c f) s t;
    if Graph.connected stl s t
      then do {
        let n = Graph.min_dist stl s t;
        (f', _) \<leftarrow> WHILE\<^sub>T
          (\<lambda>(_, stl). Graph.connected stl s t)
          (\<lambda>(f', stl). do {
            p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
            let stl = Nonnegative_Graph.subtract_path stl p;
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl)})
          (f, stl);
        RETURN (f', n)}
      else RETURN (f, (card V))}"

(* TODO do we need to show the fact that n increases here, or can it be done in the outer loop? *)
lemma dinic_inner_correct:
  "dinic_inner \<le> SPEC (\<lambda>(f', n). NFlow c s t f' \<and> \<not> (\<exists>p. NPreflow.isAugmentingPath c s t f' p \<and> length p \<le> n))"
  oops

(*
(* TODO the n is merely dragged through the loop for verification purposes, can this be simplified? *)
definition dinic_inner_partial :: "(_ flow \<times> nat) nres" where
  "dinic_inner_partial \<equiv> do {
    let stl = induced_st_layering (residualGraph c f) s t;
    if Graph.connected stl s t
      then do {
        let n = Graph.min_dist stl s t;
        (f', _, _) \<leftarrow> WHILE
          (\<lambda>(_, stl, _). Graph.connected stl s t)
          (\<lambda>(f', stl, n). do {
            p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
            let stl = Nonnegative_Graph.subtract_path stl p;
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl, n)})
          (f, stl, n);
        RETURN (f', n)}
      else RETURN (f, (card V))}"

definition dinic_inner_partial_invar :: "(_ flow \<times> _ graph \<times> nat) \<Rightarrow> bool" where
  "dinic_inner_partial_invar \<equiv> \<lambda>(f', stl, n). NFlow c s t f'
                                 \<and> Bounded_ST_Shortest_Path_Union stl (NPreflow.cf c f') s t n"
*)
definition dinic_inner_partial :: "(_ flow \<times> nat) nres" where
  "dinic_inner_partial \<equiv> do {
    let stl = induced_st_layering (residualGraph c f) s t;
    if Graph.connected stl s t
      then do {
        let n = Graph.min_dist stl s t;
        (f', _) \<leftarrow> WHILE
          (\<lambda>(_, stl). Graph.connected stl s t)
          (\<lambda>(f', stl). do {
            p \<leftarrow> SPEC (\<lambda>p. Graph.isPath stl s p t);
            let stl = Nonnegative_Graph.subtract_path stl p;
            let f' = NFlow.augment c f' (NPreflow.augmentingFlow c f' p);
            RETURN (f', stl)})
          (f, stl);
        RETURN (f', n)}
      else RETURN (f, (card V))}"

definition dinic_inner_partial_invar :: "(_ flow \<times> _ graph) \<Rightarrow> bool" where
  "dinic_inner_partial_invar \<equiv> \<lambda>(f', stl). NFlow c s t f'
                                 \<and> Bounded_ST_Shortest_Path_Union stl (NPreflow.cf c f') s t (cf.min_dist s t)"

thm min_st_dist_bound

(* TODO do we need to show the fact that n increases here, or can it be done in the outer loop? *)
lemma dinic_inner_partial_correct:
  "dinic_inner_partial \<le> SPEC (\<lambda>(f', n). NFlow c s t f' \<and> \<not> (\<exists>p. NPreflow.isAugmentingPath c s t f' p \<and> length p \<le> n))"
  unfolding dinic_inner_partial_def
proof (refine_vcg WHILE_rule[where I=dinic_inner_partial_invar], clarsimp_all)
  interpret ST_Shortest_Path_Union "induced_st_layering cf s t" cf s t
    using induced_st_shortest_path_union .
  show "dinic_inner_partial_invar (f, induced_st_layering cf s t)"
    unfolding dinic_inner_partial_invar_def
    by (auto simp: min_st_dist_bound intro: NFlow_axioms ST_Shortest_Path_Union_axioms)

  show "NFlow c s t f" using NFlow_axioms .

  show "\<And>p. \<lbrakk>\<not> g'.connected s t; isAugmentingPath p\<rbrakk> \<Longrightarrow> False"
    using st_connected_iff
    unfolding isAugmentingPath_def Graph.connected_def cf.isSimplePath_def by blast

end
end
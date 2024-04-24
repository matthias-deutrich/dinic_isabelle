theory Original_Dinitz_Impl
  imports Original_Dinitz_Refine Refine_Imperative_HOL.Sepref_Foreach
begin
text \<open>This theory starts from the refined version of the Original Dinitz and refines
      it further towards an actual executable version.\<close>

(* TODO *)
lemmas nfoldli_to_fold =
  foldli_eq_nfoldli[where c="\<lambda>_. True", symmetric, unfolded foldli_foldl foldl_conv_fold]
(*
definition (in Graph) path_cap_algo :: "path \<Rightarrow> 'capacity nres" where
  "path_cap_algo p \<equiv> case p of
    [] \<Rightarrow> RETURN 0
  | (e # p) \<Rightarrow> nfoldli p (\<lambda>_. True) (\<lambda>e cap. RETURN (min (c e) cap)) (c e)"
*)

end
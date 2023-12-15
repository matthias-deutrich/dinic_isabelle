theory HelpfulNotes
imports "Flow_Networks.Ford_Fulkerson"
begin
subsection \<open>For proofs on edges:\<close>
text \<open>Use "unfold split_paired_all" or clarify to directly fix edge endpoints.\<close>
thm split_paired_all

subsection \<open>For elim rules:\<close>
text \<open>Use "obtains" syntax to create lemmas suitable for elim rules with less boilerplate. For cases, give case names before variables in brackets.\<close>

subsection \<open>Locales:\<close>
text \<open>"interpretation" only works for the current context, "sublocale" is the same but persistent.\<close>

text \<open>Use the following and/or congruence rules in case the simplifier simplifies too much, especially for locale assumptions.\<close>
declare [[show_abbrevs=false]]
declare [[show_abbrevs=true]]

text \<open>Use "using [[rule_trace]] apply rule" to find which rule is being applied by the standard proof method.\<close>

text \<open>When depending on large sessions like the Collections framework, open isabelle using:\<close>
text \<open>isabelle jedit -l Collections <filename>.thy\<close>
(* TODO find out how to make these logic images appear in the jedit session selector dropdown *)

text \<open>To find out whether the locale hierarchy can be instantiated, use the following on top level:\<close>
text \<open>interpretation ST_Layer_Graph undefined undefined undefined sorry\<close>
end
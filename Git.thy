theory Git
  imports Graph
begin

type_synonym commit = nat
type_synonym git = "commit graph"

definition commit_next :: "commit \<Rightarrow> commit"
  where "commit_next \<equiv> Suc"

lemma [simp]: "(commit_next ^^ n) (commit_next r) = (commit_next ^^ Suc n) r"
  unfolding commit_next_def by simp

end
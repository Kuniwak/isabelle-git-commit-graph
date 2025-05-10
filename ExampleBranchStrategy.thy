theory ExampleBranchStrategy
  imports Git
begin
type_synonym release = nat

definition release_next :: "release \<Rightarrow> release"
  where "release_next \<equiv> Suc"

lemma [simp]: "(release_next ^^ n) (release_next r) = (release_next ^^ Suc n) r"
  unfolding release_next_def by simp

type_synonym feature = nat

definition feature_next :: "feature \<Rightarrow> feature"
  where "feature_next \<equiv> Suc"

lemma [simp]: "(feature_next ^^ n) (feature_next r) = (feature_next ^^ Suc n) r"
  unfolding feature_next_def by simp

type_synonym "fix" = nat

definition fix_next :: "fix \<Rightarrow> fix"
  where "fix_next \<equiv> Suc"

lemma [simp]: "(fix_next ^^ n) (fix_next r) = (fix_next ^^ Suc n) r"
  unfolding fix_next_def by simp

type_synonym repo = "git \<times> commit \<times> (release \<Rightarrow> commit option) \<times> (feature \<Rightarrow> commit option) \<times> (fix \<Rightarrow> commit option) \<times> commit \<times> release \<times> feature \<times> fix"

definition repo_git :: "repo \<Rightarrow> git"
  where "repo_git \<equiv> fst"

lemma repo_git_simp[simp]: "repo_git (x, y) = x" unfolding repo_git_def by simp

definition repo_main :: "repo \<Rightarrow> commit"
  where "repo_main \<equiv> fst \<circ> snd"

lemma repo_main_simp[simp]: "repo_main (x, y, z) = y" unfolding repo_main_def by simp

definition repo_release :: "repo \<Rightarrow> release \<Rightarrow> commit option"
  where "repo_release \<equiv> fst \<circ> snd \<circ> snd"

lemma repo_release_simp[simp]: "repo_release (x, y, z, u) = z" unfolding repo_release_def by simp

definition repo_feature :: "repo \<Rightarrow> feature \<Rightarrow> commit option"
  where "repo_feature \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"

lemma repo_feature_simp[simp]: "repo_feature (x, y, z, u, w) = u" unfolding repo_feature_def by simp

definition repo_fix :: "repo \<Rightarrow> fix \<Rightarrow> commit option"
  where "repo_fix \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

lemma repo_fix_simp[simp]: "repo_fix (x, y, z, u, w, a) = w" unfolding repo_fix_def by simp

definition repo_develop :: "repo \<Rightarrow> commit"
  where "repo_develop \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

lemma repo_develop_simp[simp]: "repo_develop (x, y, z, u, w, a, b) = a" unfolding repo_develop_def by simp

definition repo_release_next :: "repo \<Rightarrow> release"
  where "repo_release_next \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

lemma repo_release_next_simp[simp]: "repo_release_next (x, y, z, u, w, a, b, c) = b" unfolding repo_release_next_def by simp

definition repo_feature_next :: "repo \<Rightarrow> feature"
  where "repo_feature_next \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

lemma repo_feature_next_simp[simp]: "repo_feature_next (x, y, z, u, w, a, b, c, d) = c" unfolding repo_feature_next_def by simp

definition repo_fix_next :: "repo \<Rightarrow> fix"
  where "repo_fix_next \<equiv> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

lemma repo_fix_next_simp[simp]: "repo_fix_next (x, y, z, u, w, a, b, c, d) = d" unfolding repo_fix_next_def by simp

definition merge_commit :: "commit graph \<Rightarrow> commit \<Rightarrow> bool"
  where "merge_commit g c \<equiv> \<exists>c1 c2. (c, c1) \<in> (graph_edges g) \<and> (c, c2) \<in> (graph_edges g) \<and> c1 \<noteq> c2"

definition repo :: "repo \<Rightarrow> bool"
  where "repo x \<equiv> git (repo_git x)
    \<and> repo_main x \<in> graph_nodes (graph (repo_git x))
    \<and> repo_develop x \<in> graph_nodes (graph (repo_git x))
    \<and> (\<forall>r. repo_release x r \<noteq> None \<longrightarrow> the (repo_release x r) \<in> graph_nodes (graph (repo_git x)))
    \<and> (\<forall>f. repo_fix x f \<noteq> None \<longrightarrow> the (repo_fix x f) \<in> graph_nodes (graph (repo_git x)))
    \<and> (\<forall>f. repo_feature x f \<noteq> None \<longrightarrow> the (repo_feature x f) \<in> graph_nodes (graph (repo_git x)))
    \<and> (\<forall>n. repo_release x ((release_next ^^ n) (repo_release_next x)) = None)
    \<and> (\<forall>n. repo_fix x ((fix_next ^^ n) (repo_fix_next x)) = None)
    \<and> (\<forall>n. repo_feature x ((feature_next ^^ n) (repo_feature_next x)) = None)"

lemma repo_git:
  assumes repo: "repo x"
  shows "git (repo_git x)"
  using assms unfolding repo_def by simp

lemma repo_main_mem:
  assumes repo: "repo x"
  shows "repo_main x \<in> graph_nodes (graph (repo_git x))"
  using repo unfolding repo_def by simp

lemma repo_develop_mem:
  assumes repo: "repo x"
  shows "repo_develop x \<in> graph_nodes (graph (repo_git x))"
  using repo unfolding repo_def by simp

lemma repo_release_eqE[elim]:
  assumes repo: "repo x"
      and repo_release_eq: "repo_release x r = Some y"
  shows "y \<in> graph_nodes (graph (repo_git x))"
  proof -
    have "repo_release x r \<noteq> None \<Longrightarrow> (the (repo_release x r)) \<in> graph_nodes (graph (repo_git x))" using repo unfolding repo_def by simp
    thus ?thesis unfolding repo_release_eq by simp
  qed

lemma repo_fix_eqE[elim]:
  assumes repo: "repo x"
      and repo_fix_eq: "repo_fix x r = Some y"
  shows "y \<in> graph_nodes (graph (repo_git x))"
  proof -
    have "repo_fix x r \<noteq> None \<Longrightarrow> (the (repo_fix x r)) \<in> graph_nodes (graph (repo_git x))" using repo unfolding repo_def by simp
    thus ?thesis unfolding repo_fix_eq by simp
  qed

lemma repo_feature_eqE[elim]:
  assumes repo: "repo x"
      and repo_feature_eq: "repo_feature x r = Some y"
  shows "y \<in> graph_nodes (graph (repo_git x))"
  proof -
    have "repo_feature x r \<noteq> None \<Longrightarrow> (the (repo_feature x r)) \<in> graph_nodes (graph (repo_git x))" using repo unfolding repo_def by simp
    thus ?thesis unfolding repo_feature_eq by simp
  qed

lemma repo_release_funpow_eqI[intro]:
  assumes repo: "repo x"
  shows "repo_release x ((release_next ^^ n) (repo_release_next x)) = None"
  using repo unfolding repo_def by simp

lemma repo_fix_funpow_eqI[intro]:
  assumes repo: "repo x"
  shows "repo_fix x ((fix_next ^^ n) (repo_fix_next x)) = None"
  using repo unfolding repo_def by simp

lemma repo_feature_funpow_eqI[intro]:
  assumes repo: "repo x"
  shows "repo_feature x ((feature_next ^^ n) (repo_feature_next x)) = None"
  using repo unfolding repo_def by simp

definition repo_init :: "repo"
  where "repo_init \<equiv> (Git.init, 0, Map.empty, Map.empty, Map.empty, 0, 0, 0, 0)"

lemma repo_init: "repo repo_init"
  using git_init unfolding repo_def repo_init_def repo_git_simp init_def by auto

definition new_release_branch_from_develop :: "repo \<Rightarrow> repo"
  where "new_release_branch_from_develop x \<equiv>
    (
      repo_git x,
      repo_main x,
      (repo_release x)(repo_release_next x := Some (repo_develop x)),
      repo_feature x,
      repo_fix x,
      repo_develop x,
      release_next (repo_release_next x),
      repo_feature_next x,
      repo_fix_next x
    )"

lemma new_release_branch_from_develop_closed:
  assumes repo: "repo x"
      and x'_eq: "x' = new_release_branch_from_develop x"
  shows "repo x'"
  proof -
    show ?thesis unfolding x'_eq repo_def new_release_branch_from_develop_def  proof (auto intro: repo_git[OF repo] repo_main_mem[OF repo] repo_develop_mem[OF repo] repo_release_funpow_eqI[OF repo] repo_fix_funpow_eqI[OF repo] repo_feature_funpow_eqI[OF repo] simp add: repo_release_eqE[OF repo] repo_fix_eqE[OF repo] repo_feature_eqE[OF repo])
      fix n
      assume "release_next ((release_next ^^ n) (repo_release_next x)) = repo_release_next x"
      thus False unfolding release_next_def by simp
    next
      fix n
      have 1: "release_next ((release_next ^^ n) (repo_release_next x)) = (release_next ^^ (Suc n)) (repo_release_next x)" using release_next_def by auto
      show "repo_release x (release_next ((release_next ^^ n) (repo_release_next x))) = None" unfolding 1 using repo_release_funpow_eqI[OF repo] .
    qed
  qed

definition merge_release_branch_into_main :: "repo \<Rightarrow> release \<Rightarrow> repo option"
  where "merge_release_branch_into_main x r \<equiv>
    if repo_release x r = None \<or> merge (repo_git x) {repo_main x, the (repo_release x r)} = None
    then None
    else Some (
      snd (the (merge (repo_git x) {repo_main x, the (repo_release x r)})),
      fst (the (merge (repo_git x) {repo_main x, the (repo_release x r)})),
      repo_release x,
      repo_feature x,
      repo_fix x,
      repo_develop x,
      repo_release_next x,
      repo_feature_next x,
      repo_fix_next x
    )"

lemma merge_release_branch_into_main_closed:
  assumes repo: "repo x"
      and merge_release_branch_into_main_eq: "merge_release_branch_into_main x r = Some x'"
  shows "repo x'"
  proof -
    obtain c where repo_release_eq: "repo_release x r = Some c" using merge_release_branch_into_main_eq unfolding merge_release_branch_into_main_def by fastforce
    have merge_eq: "merge (repo_git x) {repo_main x, the (repo_release x r)} = Some (
        commit_next (repo_git x),
        (
          insert (commit_next (repo_git x)) (graph_nodes (graph (repo_git x))),
          Pair (commit_next (repo_git x)) ` {repo_main x, the (repo_release x r)} \<union> graph_edges (graph (repo_git x))
        ),
        Suc (commit_next (repo_git x))
      )" using merge_release_branch_into_main_eq unfolding merge_release_branch_into_main_def by (metis merge_def option.simps(3))
    have x'_eq: "x' = (
      (
        (
          insert (commit_next (repo_git x)) (graph_nodes (graph (repo_git x))),
          Pair (commit_next (repo_git x)) ` {repo_main x, c} \<union> graph_edges (graph (repo_git x))
        ),
        Suc (commit_next (repo_git x))
      ),
      commit_next (repo_git x),
      repo_release x,
      repo_feature x,
      repo_fix x,
      repo_develop x,
      repo_release_next x,
      repo_feature_next x,
      repo_fix_next x
    )" using merge_release_branch_into_main_eq repo_release_eq unfolding merge_release_branch_into_main_def merge_eq by simp
    show ?thesis unfolding x'_eq repo_def repo_release_eq proof (auto intro: repo_main_mem[OF repo] repo_develop_mem[OF repo] repo_release_funpow_eqI[OF repo] repo_fix_funpow_eqI[OF repo] repo_feature_funpow_eqI[OF repo] simp add: repo_release_eqE[OF repo] repo_fix_eqE[OF repo] repo_feature_eqE[OF repo])
      show "git ((insert (commit_next (repo_git x)) (graph_nodes (Git.graph (repo_git x))), insert (commit_next (repo_git x), repo_main x) (insert (commit_next (repo_git x), c) (graph_edges (Git.graph (repo_git x))))),
         Suc (commit_next (repo_git x)))" using merge_closed[OF repo_git[OF repo] merge_eq] unfolding repo_release_eq by simp
    qed
  qed

definition new_fix_branch_from_release :: "repo \<Rightarrow> release \<Rightarrow> repo option"
  where "new_fix_branch_from_release x r \<equiv>
    if repo_release x r = None
    then None
    else Some (
      repo_git x,
      repo_main x,
      repo_release x,
      repo_feature x,
      (repo_fix x)(repo_fix_next x := Some (the (repo_release x r))),
      repo_develop x,
      repo_release_next x,
      repo_feature_next x,
      fix_next (repo_fix_next x)
    )"

lemma new_fix_branch_from_release_closed:
    assumes repo: "repo x"
        and eq: "new_fix_branch_from_release x r = Some x'"
    shows "repo x'"
  proof -
    obtain c where repo_release_eq: "repo_release x r = Some c" using eq unfolding new_fix_branch_from_release_def by fastforce
    have x'_eq: "x' = (
      repo_git x,
      repo_main x,
      repo_release x,
      repo_feature x,
      (repo_fix x)(repo_fix_next x := Some c),
      repo_develop x,
      repo_release_next x,
      repo_feature_next x,
      fix_next (repo_fix_next x)
    )" using eq unfolding new_fix_branch_from_release_def by (auto simp add: repo_release_eq)
    show ?thesis unfolding x'_eq repo_def repo_release_eq proof (auto intro: repo_git[OF repo] repo_main_mem[OF repo] repo_develop_mem[OF repo] repo_release_funpow_eqI[OF repo] repo_fix_funpow_eqI[OF repo] repo_feature_funpow_eqI[OF repo] repo_release_eqE[OF repo] repo_release_eqE[OF repo repo_release_eq] repo_feature_eqE[OF repo] repo_fix_eqE[OF repo])
      fix n
      assume "fix_next ((fix_next ^^ n) (repo_fix_next x)) = repo_fix_next x"
      thus False unfolding fix_next_def by simp
    next
      fix n
      have 1: "fix_next ((fix_next ^^ n) (repo_fix_next x)) = (fix_next ^^ (Suc n)) (repo_fix_next x)" unfolding fix_next_def by simp
      show "repo_fix x (fix_next ((fix_next ^^ n) (repo_fix_next x))) = None" unfolding 1 using repo_fix_funpow_eqI[OF repo] .
    qed
  qed

definition commit_on_fix_branch :: "repo \<Rightarrow> fix \<Rightarrow> repo option"
  where "commit_on_fix_branch x f \<equiv> if repo_fix x f = None
  then None
  else Some (
    snd (the (commit (repo_git x) (the (repo_fix x f)))),
    repo_main x,
    repo_release x,
    repo_feature x,
    (repo_fix x)(f := Some (fst (the (commit (repo_git x) (the (repo_fix x f)))))),
    repo_develop x,
    repo_release_next x,
    repo_feature_next x,
    repo_fix_next x
  )"

lemma commit_on_fix_branch_closed:
  assumes repo: "repo x"
      and eq: "commit_on_fix_branch x f = Some x'"
  shows "repo x'"
  proof -
    obtain c where repo_fix_eq: "repo_fix x f = Some c" using eq unfolding commit_on_fix_branch_def by fastforce
    have commit_eq: "commit (repo_git x) c = Some (
        commit_next (repo_git x),
        (
          (
            insert (commit_next (repo_git x)) (graph_nodes (graph (repo_git x))),
            insert (commit_next (repo_git x), c) (graph_edges (graph (repo_git x)))
          ),
          Suc (commit_next (repo_git x))
        )
      )" using eq unfolding commit_on_fix_branch_def  using commit_def repo repo_fix_eq repo_fix_eqE by presburger
    have x'_eq: "x' = (
      (
        (
          insert (commit_next (repo_git x)) (graph_nodes (graph (repo_git x))),
          insert (commit_next (repo_git x), c) (graph_edges (graph (repo_git x)))
        ),
        Suc (commit_next (repo_git x))
      ),
      repo_main x,
      repo_release x,
      repo_feature x,
      (repo_fix x)(f := Some (commit_next (repo_git x))),
      repo_develop x,
      repo_release_next x,
      repo_feature_next x,
      repo_fix_next x
    )" using eq using commit_eq commit_on_fix_branch_def eq repo_fix_eq by auto
    show ?thesis unfolding x'_eq repo_def new_release_branch_from_develop_def repo_fix_eq proof (auto intro: repo_main_mem[OF repo] repo_develop_mem[OF repo] repo_release_funpow_eqI[OF repo] repo_fix_funpow_eqI[OF repo] repo_feature_funpow_eqI[OF repo] simp add: repo_release_eqE[OF repo] repo_fix_eqE[OF repo] repo_feature_eqE[OF repo])
      show "git ((insert (commit_next (repo_git x)) (graph_nodes (Git.graph (repo_git x))), insert (commit_next (repo_git x), c) (graph_edges (Git.graph (repo_git x)))), Suc (commit_next (repo_git x)))" using repo_git[OF repo] proof (rule commit_closed)
        show "commit (repo_git x) c = Some (commit_next (repo_git x), (insert (commit_next (repo_git x)) (graph_nodes (Git.graph (repo_git x))), insert (commit_next (repo_git x), c) (graph_edges (Git.graph (repo_git x)))), Suc (commit_next (repo_git x)))" using commit_eq by simp
      qed
    next
      fix n
      assume "f = (fix_next ^^ n) (repo_fix_next x)"
      hence 1: "repo_fix x ((fix_next ^^ n) (repo_fix_next x)) = Some c" using repo_fix_eq by simp
      have 2: "repo_fix x ((fix_next ^^ n) (repo_fix_next x)) = None" using repo_fix_funpow_eqI[OF repo] .
      thus False using 1 2 by simp
    qed
  qed

definition merge_fix_branch_into_release :: "repo \<Rightarrow> fix \<Rightarrow> release \<Rightarrow> repo option"
  where "merge_fix_branch_into_release  x f r \<equiv>
    if repo_fix x f = None \<or> repo_release x r = None \<or> merge (repo_git x) {the (repo_release x r), the (repo_fix x f)} = None
    then None
    else Some (
      snd (the (merge (repo_git x) {the (repo_release x r), the (repo_fix x f)})),
      repo_main x,
      (repo_release x)(r := Some (fst (the (merge (repo_git x) {the (repo_release x r), the (repo_fix x f)})))),
      repo_feature x,
      repo_fix x,
      repo_develop x,
      repo_release_next x,
      repo_feature_next x,
      repo_fix_next x
    )"

lemma merge_fix_branch_into_release_closed:
  assumes repo: "repo x"
      and merge_fix_branch_into_release_eq: "merge_fix_branch_into_release  x f r = Some x'"
  shows "repo x'"
  proof -
    obtain c where repo_fix_eq: "repo_fix x f = Some c" using merge_fix_branch_into_release_eq unfolding merge_fix_branch_into_release_def by fastforce
    obtain c' where repo_release_eq: "repo_release x r = Some c'" using merge_fix_branch_into_release_eq unfolding merge_fix_branch_into_release_def by fastforce
    have merge_eq: "merge (repo_git x) {c', c} = Some (
      commit_next (repo_git x),
      (
        (
          insert (commit_next (repo_git x)) (graph_nodes (graph (repo_git x))),
          Pair (commit_next (repo_git x)) ` {c', c} \<union> graph_edges (graph (repo_git x))
        ),
        Suc (commit_next (repo_git x))
      )
    )" using merge_fix_branch_into_release_eq unfolding merge_fix_branch_into_release_def merge_def repo_fix_eq repo_release_eq by (metis (lifting) merge_fix_branch_into_release_eq option.distinct(1) option.sel)
    have x'_eq: "x' = (
      (
        (
          insert (commit_next (repo_git x)) (graph_nodes (graph (repo_git x))),
          Pair (commit_next (repo_git x)) ` {c', c} \<union> graph_edges (graph (repo_git x))
        ),
        Suc (commit_next (repo_git x))
      ),
      repo_main x,
      (repo_release x)(r := Some (commit_next (repo_git x))),
      repo_feature x,
      repo_fix x,
      repo_develop x,
      repo_release_next x,
      repo_feature_next x,
      repo_fix_next x
    )" using merge_fix_branch_into_release_eq by (simp add: merge_fix_branch_into_release_def repo_fix_eq repo_release_eq merge_eq)
    show ?thesis unfolding x'_eq repo_def proof (auto intro:  repo_main_mem[OF repo] repo_develop_mem[OF repo] repo_release_funpow_eqI[OF repo] repo_fix_funpow_eqI[OF repo] repo_feature_funpow_eqI[OF repo] simp add: repo_release_eqE[OF repo] repo_fix_eqE[OF repo] repo_feature_eqE[OF repo])
      show "git ((insert (commit_next (repo_git x)) (graph_nodes (Git.graph (repo_git x))), insert (commit_next (repo_git x), c') (insert (commit_next (repo_git x), c) (graph_edges (Git.graph (repo_git x))))),
         Suc (commit_next (repo_git x)))" using repo_git[OF repo] proof (rule merge_closed)
        show "merge (repo_git x) {c', c} = Some (commit_next (repo_git x), (insert (commit_next (repo_git x)) (graph_nodes (Git.graph (repo_git x))), insert (commit_next (repo_git x), c') (insert (commit_next (repo_git x), c) (graph_edges (Git.graph (repo_git x))))), Suc (commit_next (repo_git x)))" unfolding merge_eq by simp
      qed
    next
      fix n
      assume "r = (release_next ^^ n) (repo_release_next x)"
      hence 1: "repo_release x ((release_next ^^ n) (repo_release_next x)) = Some c'" using repo_release_eq by simp
      have 2: "repo_release x ((release_next ^^ n) (repo_release_next x)) = None" using repo_release_funpow_eqI[OF repo] .
      show False using 1 2 by simp
    qed
  qed

definition new_feature_branch_from_develop :: "repo \<Rightarrow> repo"
  where "new_feature_branch_from_develop x \<equiv> (
    repo_git x,
    repo_main x,
    repo_release x,
    (repo_feature x)(repo_feature_next x := Some (repo_develop x)),
    repo_fix x,
    repo_develop x,
    repo_release_next x,
    feature_next (repo_feature_next x),
    repo_fix_next x
  )"

lemma new_feature_branch_from_develop_closed:
    assumes repo: "repo x"
      and x'_eq: "x' = new_feature_branch_from_develop x"
  shows "repo x'"
  proof -
    show ?thesis unfolding x'_eq repo_def new_feature_branch_from_develop_def proof (auto intro: repo_git[OF repo] repo_main_mem[OF repo] repo_develop_mem[OF repo] repo_release_funpow_eqI[OF repo] repo_fix_funpow_eqI[OF repo] repo_feature_funpow_eqI[OF repo] simp add: repo_release_eqE[OF repo] repo_fix_eqE[OF repo] repo_feature_eqE[OF repo])
      fix n
      have 1: "feature_next ((feature_next ^^ n) (repo_feature_next x)) = (feature_next ^^ Suc n) (repo_feature_next x)" by simp
      show "repo_feature x (feature_next ((feature_next ^^ n) (repo_feature_next x))) = None" unfolding 1 using repo_feature_funpow_eqI[OF repo] .
    next
      fix n
      assume "feature_next ((feature_next ^^ n) (repo_feature_next x)) = repo_feature_next x"
      thus False unfolding feature_next_def by simp
    qed
  qed

definition commit_on_feature_branch :: "repo \<Rightarrow> feature \<Rightarrow> repo option"
  where "commit_on_feature_branch x f \<equiv>
    if repo_feature x f = None
    then None
    else Some (
      snd (the (commit (repo_git x) (the (repo_feature x f)))),
      repo_main x,
      repo_release x,
      (repo_feature x)(f := Some (fst (the (commit (repo_git x) (the (repo_feature x f)))))),
      repo_fix x,
      repo_develop x,
      repo_release_next x,
      repo_feature_next x,
      repo_fix_next x
    )"

lemma commit_on_feature_branch_closed:
  assumes repo: "repo x"
      and eq: "commit_on_feature_branch x f = Some x'"
  shows "repo x'"
  proof -
    obtain c where repo_feature_eq: "repo_feature x f = Some c" using eq unfolding commit_on_feature_branch_def by fastforce
    have commit_eq: "commit (repo_git x) c = Some (
      commit_next (repo_git x),
      (
        (
          insert (commit_next (repo_git x)) (graph_nodes (graph (repo_git x))),
          insert (commit_next (repo_git x), c) (graph_edges (graph (repo_git x)))
        ),
        Suc (commit_next (repo_git x))
      )
    )" using eq by (auto intro: repo_feature_eqE[OF repo repo_feature_eq] simp add: commit_on_feature_branch_def commit_def repo_feature_eq)
    have x'_eq: "x' = (
      (
        (
          insert (commit_next (repo_git x)) (graph_nodes (graph (repo_git x))),
          insert (commit_next (repo_git x), c) (graph_edges (graph (repo_git x)))
        ),
        Suc (commit_next (repo_git x))
      ),
      repo_main x,
      repo_release x,
      (repo_feature x)(f := Some (commit_next (repo_git x))),
      repo_fix x,
      repo_develop x,
      repo_release_next x,
      repo_feature_next x,
      repo_fix_next x
    )" using eq by (simp add: repo_feature_eq commit_on_feature_branch_def commit_eq)
    show ?thesis unfolding x'_eq repo_def new_release_branch_from_develop_def repo_feature_eq proof (auto intro: repo_main_mem[OF repo] repo_develop_mem[OF repo] repo_release_funpow_eqI[OF repo] repo_fix_funpow_eqI[OF repo] repo_feature_funpow_eqI[OF repo] simp add: repo_release_eqE[OF repo] repo_fix_eqE[OF repo] repo_feature_eqE[OF repo])
      show "git ((insert (commit_next (repo_git x)) (graph_nodes (Git.graph (repo_git x))), insert (commit_next (repo_git x), c) (graph_edges (Git.graph (repo_git x)))), Suc (commit_next (repo_git x)))" using repo_git[OF repo] proof (rule commit_closed)
        show "commit (repo_git x) c = Some (commit_next (repo_git x), (insert (commit_next (repo_git x)) (graph_nodes (Git.graph (repo_git x))), insert (commit_next (repo_git x), c) (graph_edges (Git.graph (repo_git x)))), Suc (commit_next (repo_git x)))" unfolding commit_eq by simp
      qed
    next
      fix n
      assume "f = (feature_next ^^ n) (repo_feature_next x)"
      hence 1: "repo_feature x ((feature_next ^^ n) (repo_feature_next x)) = Some c" using repo_feature_eq by simp
      have 2: "repo_feature x ((feature_next ^^ n) (repo_feature_next x)) = None" using repo_feature_funpow_eqI[OF repo] .
      thus False using 1 2 by simp
    qed
  qed

definition merge_feature_branch_into_develop :: "repo \<Rightarrow> feature \<Rightarrow> repo option"
  where "merge_feature_branch_into_develop x f \<equiv>
    if repo_feature x f = None \<or> merge (repo_git x) {repo_develop x, the (repo_feature x f)} = None
    then None
    else Some (
      snd (the (merge (repo_git x) {repo_develop x, the (repo_feature x f)})),
      repo_main x,
      repo_release x,
      repo_feature x,
      repo_fix x,
      fst (the (merge (repo_git x) {repo_develop x, the (repo_feature x f)})),
      repo_release_next x,
      repo_feature_next x,
      repo_fix_next x
    )"

lemma merge_feature_branch_into_develop_closed:
  assumes repo: "repo x"
      and eq: "merge_feature_branch_into_develop x f = Some x'"
  shows "repo x'"
  proof -
    obtain c where repo_feature_eq: "repo_feature x f = Some c" using eq unfolding merge_feature_branch_into_develop_def by fastforce
    have merge_eq: "merge (repo_git x) {repo_develop x, c} = Some (
      commit_next (repo_git x),
      (
        (
          insert (commit_next (repo_git x)) (graph_nodes (graph (repo_git x))),
          Pair (commit_next (repo_git x)) ` {repo_develop x, c} \<union> graph_edges (graph (repo_git x))
        ),
        Suc (commit_next (repo_git x))
      )
    )" using eq by (metis merge_def merge_feature_branch_into_develop_def option.sel option.simps(3) repo_feature_eq)
    have x'_eq: "x' = (
      snd (the (merge (repo_git x) {repo_develop x, c})),
      repo_main x,
      repo_release x,
      repo_feature x,
      repo_fix x,
      fst (the (merge (repo_git x) {repo_develop x, c})),
      repo_release_next x,
      repo_feature_next x,
      repo_fix_next x
    )" using eq by (simp add: repo_feature_eq merge_feature_branch_into_develop_def merge_eq)
    show ?thesis unfolding x'_eq repo_def proof (auto intro: repo_main_mem[OF repo] repo_develop_mem[OF repo] repo_release_funpow_eqI[OF repo] repo_fix_funpow_eqI[OF repo] repo_feature_funpow_eqI[OF repo])
      show "git (snd (the (merge (repo_git x) {repo_develop x, c})))" using repo_git[OF repo] proof (rule merge_closed)
        show "merge (repo_git x) {repo_develop x, c} = Some (fst (the (merge (repo_git x) {repo_develop x, c})), snd (the (merge (repo_git x) {repo_develop x, c})))" unfolding merge_def using merge_def merge_eq by auto
      qed
    next
      show "repo_main x \<in> graph_nodes (Git.graph (snd (the (merge (repo_git x) {repo_develop x, c}))))" using repo_main_mem[OF repo] unfolding merge_eq by simp
    next
      show "fst (the (merge (repo_git x) {repo_develop x, c})) \<in> graph_nodes (Git.graph (snd (the (merge (repo_git x) {repo_develop x, c}))))" unfolding merge_eq by simp
    next
      fix r y
      assume eq: "repo_release x r = Some y"
      show "y \<in> graph_nodes (Git.graph (snd (the (merge (repo_git x) {repo_develop x, c}))))" unfolding merge_eq by (auto intro: repo_release_eqE[OF repo eq])
    next
      fix f y
      assume eq: "repo_feature x f = Some y"
      show "y \<in> graph_nodes (Git.graph (snd (the (merge (repo_git x) {repo_develop x, c}))))" unfolding merge_eq by (auto intro: repo_feature_eqE[OF repo eq])
    next
      fix f y
      assume eq: "repo_fix x f = Some y"
      show "y \<in> graph_nodes (Git.graph (snd (the (merge (repo_git x) {repo_develop x, c}))))" unfolding merge_eq by (auto intro: repo_fix_eqE[OF repo eq])
    qed
  qed

datatype merge_state = Conflict | NoConflict | Merged

type_synonym release_pr = "release \<Rightarrow> merge_state option"
type_synonym feature_pr = "feature \<Rightarrow> merge_state option"
type_synonym fix_pr = "fix \<Rightarrow> release \<Rightarrow> merge_state option"
type_synonym lifetime_for_fairness = nat
type_synonym state = "repo \<times> release_pr \<times> feature_pr \<times> fix_pr"

definition state_repo :: "state \<Rightarrow> repo"
  where "state_repo \<equiv> fst"

lemma [simp]: "state_repo (x, y) \<equiv> x" unfolding state_repo_def by simp

definition state_release_pr :: "state \<Rightarrow> release \<Rightarrow> merge_state option"
  where "state_release_pr \<equiv> fst \<circ> snd"

lemma state_release_pr_simp[simp]: "state_release_pr (x, y, z) \<equiv> y" unfolding state_release_pr_def by simp

definition state_feature_pr :: "state \<Rightarrow> feature \<Rightarrow> merge_state option"
  where "state_feature_pr \<equiv> fst \<circ> snd \<circ> snd"

lemma state_feature_pr_simp[simp]: "state_feature_pr (x, y, z, u) \<equiv> z" unfolding state_feature_pr_def by simp

definition state_fix_pr :: "state \<Rightarrow> fix \<Rightarrow> release \<Rightarrow> merge_state option"
  where "state_fix_pr \<equiv> snd \<circ> snd \<circ> snd"

lemma state_fix_pr_simp[simp]: "state_fix_pr (x, y, z, u) \<equiv> u" unfolding state_fix_pr_def by simp

definition state :: "state \<Rightarrow> bool"
  where "state s \<equiv> repo (state_repo s)
    \<and> (\<forall>r. state_release_pr s r \<noteq> None \<longrightarrow> repo_release (state_repo s) r \<noteq> None)
    \<and> (\<forall>f. state_feature_pr s f \<noteq> None \<longrightarrow> repo_feature (state_repo s) f \<noteq> None)
    \<and> (\<forall>f r. state_fix_pr s f r \<noteq> None \<longrightarrow> repo_fix (state_repo s) f \<noteq> None \<and> repo_release (state_repo s) r \<noteq> None)"

lemma state_repo:
  assumes "state s"
  shows "repo (state_repo s)" using assms unfolding state_def by simp

lemma state_release_pr_eqE:
  assumes "state s"
    and "state_release_pr s r = Some m"
  obtains c where "repo_release (state_repo s) r = Some c" using assms unfolding state_def by blast

lemma state_release_pr_neqE:
  assumes "state s"
    and "state_release_pr s r \<noteq> None"
  shows "repo_release (state_repo s) r \<noteq> None" using assms unfolding state_def by simp

lemma state_fix_pr_eqE:
  assumes "state s"
    and "state_fix_pr s f r = Some m"
  obtains c c' where "repo_fix (state_repo s) f = Some c" and "repo_release (state_repo s) r = Some c'" using assms unfolding state_def by blast

lemma state_fix_pr_neqE:
  assumes "state s"
    and "state_fix_pr s f r \<noteq> None"
  shows "repo_fix (state_repo s) f \<noteq> None" and "repo_release (state_repo s) r \<noteq> None" using assms unfolding state_def by simp_all

lemma state_feature_pr_eqE:
  assumes "state s"
    and "state_feature_pr s f = Some m"
  obtains c where "repo_feature (state_repo s) f = Some c" using assms unfolding state_def by blast

lemma state_feature_pr_neqE:
  assumes "state s"
    and "state_feature_pr s f \<noteq> None"
  shows "repo_feature (state_repo s) f \<noteq> None" using assms unfolding state_def by simp

lemma stateI:
  assumes "repo x"
      and "\<And>r m. state_release_pr s r = Some m \<Longrightarrow> \<exists>c. repo_release x r = Some c"
      and "\<And>f m. state_feature_pr s f = Some m \<Longrightarrow> \<exists>c. repo_feature x f = Some c"
      and "\<And>f m r. state_fix_pr s f r = Some m \<Longrightarrow> (\<exists>c. repo_fix x f = Some c) \<and> (\<exists>c. repo_release x r = Some c)"
      and "s = (x, y, z, u)"
  shows "state s" using assms(2, 3, 4) unfolding assms(5) state_release_pr_simp state_fix_pr_simp state_feature_pr_simp state_def by (auto intro: assms(1))

definition state_init :: "state"
  where "state_init \<equiv> (repo_init, Map.empty, Map.empty, (\<lambda>_. Map.empty))"

lemma state_init: "state state_init"
  unfolding state_def state_init_def using repo_init by simp

definition new_release_pr :: "state \<Rightarrow> release \<Rightarrow> state \<Rightarrow> bool"
  where "new_release_pr s r s' \<equiv>
    repo_release (state_repo s) r \<noteq> None
    \<and> mergable (repo_git (state_repo s)) {repo_main (state_repo s), the (repo_release (state_repo s) r)}
    \<and> (s' = (state_repo s, (state_release_pr s)(r := Some NoConflict), state_feature_pr s, state_fix_pr s)
      \<or> s' = (state_repo s, (state_release_pr s)(r := Some Conflict), state_feature_pr s, state_fix_pr s))"

lemma new_release_pr_closed:
  assumes state: "state s"
    and new_release_pr: "new_release_pr s r s'"
  shows "state s'"
  using new_release_pr unfolding new_release_pr_def proof auto
    fix c
    assume 1: "repo_release (state_repo s) r = Some c"
    show "state (state_repo s, (state_release_pr s)(r \<mapsto> NoConflict), state_feature_pr s, state_fix_pr s)" proof (rule stateI, auto intro: state_repo[OF state] state_release_pr_eqE[OF state] state_feature_pr_eqE[OF state] state_fix_pr_eqE[OF state])
      fix r' m
      assume "(if r' = r then Some NoConflict else state_release_pr s r') = Some m"
      thus "\<exists>c. repo_release (state_repo s) r' = Some c" by (cases "r' = r"; auto intro: 1 elim: state_release_pr_eqE[OF state])
    qed
  next
    fix c
    assume 1: "repo_release (state_repo s) r = Some c"
    show "state (state_repo s, (state_release_pr s)(r \<mapsto> Conflict), state_feature_pr s, state_fix_pr s)" proof (rule stateI, auto intro: state_repo[OF state] state_release_pr_eqE[OF state] state_feature_pr_eqE[OF state] state_fix_pr_eqE[OF state])
      fix r' m
      assume "(if r' = r then Some Conflict else state_release_pr s r') = Some m"
      thus "\<exists>c. repo_release (state_repo s) r' = Some c" by (cases "r' = r"; auto intro: 1 elim: state_release_pr_eqE[OF state])
    qed
  qed


definition new_fix_pr :: "state \<Rightarrow> fix \<Rightarrow> release \<Rightarrow> state \<Rightarrow> bool"
  where "new_fix_pr s f r s' \<equiv>
    repo_fix (state_repo s) f \<noteq> None
    \<and> repo_release (state_repo s) r \<noteq> None
    \<and> mergable (repo_git (state_repo s)) {the (repo_release (state_repo s) r), the (repo_fix (state_repo s) r)}
    \<and> (s' = (state_repo s, state_release_pr s, state_feature_pr s, (state_fix_pr s)(f := (\<lambda>r'. if r = r' then Some NoConflict else None)))
      \<or> s' = (state_repo s, state_release_pr s, state_feature_pr s, (state_fix_pr s)(f := (\<lambda>r'. if r = r' then Some Conflict else None))))"

lemma new_fix_pr_closed:
  assumes state: "state s"
    and new_fix_pr: "new_fix_pr s f r s'"
  shows "state s'"
  using new_fix_pr unfolding new_fix_pr_def proof auto
    fix c c'
    assume 1: "repo_fix (state_repo s) f = Some c"
      and 2: "repo_release (state_repo s) r = Some c'"
    show "state (state_repo s, state_release_pr s, state_feature_pr s, (state_fix_pr s)(f := \<lambda>r'. if r = r' then Some NoConflict else None))" proof (rule stateI, auto intro: state_repo[OF state] state_release_pr_eqE[OF state] state_feature_pr_eqE[OF state] state_fix_pr_eqE[OF state])
      fix f' m r'
      assume "(if f' = f then \<lambda>r'. if r = r' then Some NoConflict else None else state_fix_pr s f') r' = Some m"
      thus "\<exists>c. repo_fix (state_repo s) f' = Some c" by (cases "f' = f"; auto intro: 1 elim: state_fix_pr_eqE[OF state])
    next
      fix f' m r'
      assume "(if f' = f then \<lambda>r'. if r = r' then Some NoConflict else None else state_fix_pr s f') r' = Some m"
      thus "\<exists>c. repo_release (state_repo s) r' = Some c" proof (cases "f' = f"; auto elim: state_fix_pr_eqE[OF state])
        assume "(if r = r' then Some NoConflict else None) = Some m"
        thus "\<exists>c. repo_release (state_repo s) r' = Some c" by (cases "r' = r"; auto intro: 2)
      qed
    qed
  next
    fix c c'
    assume 1: "repo_fix (state_repo s) f = Some c"
      and 2: "repo_release (state_repo s) r = Some c'"
    show "state (state_repo s, state_release_pr s, state_feature_pr s, (state_fix_pr s)(f := \<lambda>r'. if r = r' then Some Conflict else None))" proof (rule stateI, auto intro: state_repo[OF state] state_release_pr_eqE[OF state] state_feature_pr_eqE[OF state] state_fix_pr_eqE[OF state])
      fix f' m r'
      assume "(if f' = f then \<lambda>r'. if r = r' then Some Conflict else None else state_fix_pr s f') r' = Some m"
      thus "\<exists>c. repo_fix (state_repo s) f' = Some c" by (cases "f' = f"; auto intro: 1 elim: state_fix_pr_eqE[OF state])
    next
      fix f' m r'
      assume "(if f' = f then \<lambda>r'. if r = r' then Some Conflict else None else state_fix_pr s f') r' = Some m"
      thus "\<exists>c. repo_release (state_repo s) r' = Some c" proof (cases "f' = f"; auto elim: state_fix_pr_eqE[OF state])
        assume "(if r = r' then Some Conflict else None) = Some m"
        thus "\<exists>c. repo_release (state_repo s) r' = Some c" by (cases "r' = r"; auto intro: 2)
      qed
    qed
  qed


definition new_feature_pr :: "state \<Rightarrow> feature \<Rightarrow> state \<Rightarrow> bool"
  where "new_feature_pr s r s' \<equiv>
    repo_feature (state_repo s) r \<noteq> None
    \<and> mergable (repo_git (state_repo s)) {repo_develop (state_repo s), the (repo_feature (state_repo s) r)}
    \<and> (s' = (state_repo s, state_release_pr s, (state_feature_pr s)(r := Some NoConflict), state_fix_pr s)
      \<or> s' = (state_repo s, state_release_pr s, (state_feature_pr s)(r := Some Conflict), state_fix_pr s))"

lemma new_feature_pr_closed:
  assumes state: "state s"
    and new_feature_pr: "new_feature_pr s f s'"
  shows "state s'"
  proof -
    show ?thesis using new_feature_pr unfolding new_feature_pr_def proof auto
      fix c
      assume 1: "repo_feature (state_repo s) f = Some c"
      show "state (state_repo s, state_release_pr s, (state_feature_pr s)(f \<mapsto> NoConflict), state_fix_pr s)" proof (rule stateI, auto intro: state_repo[OF state] state_release_pr_eqE[OF state] state_feature_pr_eqE[OF state] state_fix_pr_eqE[OF state])
        fix f' m
        assume "(if f' = f then Some NoConflict else state_feature_pr s f') = Some m"
        thus "\<exists>c. repo_feature (state_repo s) f' = Some c" by (cases "f' = f"; auto intro: 1 elim: state_feature_pr_eqE[OF state])
      qed
    next
      fix c
      assume 1: "repo_feature (state_repo s) f = Some c"
      show "state (state_repo s, state_release_pr s, (state_feature_pr s)(f \<mapsto> Conflict), state_fix_pr s)" proof (rule stateI, auto intro: state_repo[OF state] state_release_pr_eqE[OF state] state_feature_pr_eqE[OF state] state_fix_pr_eqE[OF state])
        fix f' m
        assume "(if f' = f then Some Conflict else state_feature_pr s f') = Some m"
        thus "\<exists>c. repo_feature (state_repo s) f' = Some c" by (cases "f' = f"; auto intro: 1 elim: state_feature_pr_eqE[OF state])
      qed
    qed
  qed

definition trans :: "state \<Rightarrow> state \<Rightarrow> bool"
  where "trans s s' \<equiv>
    s' = (new_release_branch_from_develop (state_repo s), state_release_pr s, state_feature_pr s, state_fix_pr s)
    \<or> (\<exists>r. new_release_pr s r s')
    \<or> (\<exists>r x'. Some x' = merge_release_branch_into_main (state_repo s) r \<and> s' = (x', (state_release_pr s)(r := Some Merged), state_feature_pr s, state_fix_pr s))
    \<or> (\<exists>r x'. Some x' = new_fix_branch_from_release (state_repo s) r \<and> s' = (x', state_release_pr s, state_feature_pr s, state_fix_pr s))
    \<or> (\<exists>f x'. Some x' = commit_on_fix_branch (state_repo s) f \<and> s' = (x', state_release_pr s, state_feature_pr s, state_fix_pr s))
    \<or> (\<exists>f r. new_fix_pr s f r s')
    \<or> (\<exists>f r x'. Some x' = merge_fix_branch_into_release (state_repo s) f r \<and> s' = (x', state_release_pr s, state_feature_pr s, (state_fix_pr s)(f := (\<lambda>r'. if r = r' then Some Merged else None))))
    \<or> s' = (new_feature_branch_from_develop (state_repo s), state_release_pr s, state_feature_pr s, state_fix_pr s)
    \<or> (\<exists>f x'. Some x' = commit_on_feature_branch (state_repo s) f \<and> s' = (x', state_release_pr s, state_feature_pr s, state_fix_pr s))
    \<or> (\<exists>f. new_feature_pr s f s')
    \<or> (\<exists>f x'. Some x' = merge_feature_branch_into_develop (state_repo s) f \<and> s' = (x', state_release_pr s, (state_feature_pr s)(f := Some Merged), state_fix_pr s))"

lemma trans_closed:
  assumes state: "state s"
      and trans: "trans s s'"
  shows "state s'"
  using trans unfolding trans_def proof (elim disjE exE conjE)
    assume 1: "s' = (new_release_branch_from_develop (state_repo s), state_release_pr s, state_feature_pr s, state_fix_pr s)"
    show "state s'" unfolding 1 using new_release_branch_from_develop_closed[OF state_repo[OF state]] by (rule stateI; auto intro: state_release_pr_eqE[OF state] state_fix_pr_eqE[OF state] state_feature_pr_eqE[OF state] simp add: new_release_branch_from_develop_def)
  next
    fix r
    assume 1: "new_release_pr s r s'"
    show "state s'" using new_release_pr_closed[OF state 1] .
  next
    fix f r
    assume 1: "new_fix_pr s f r s'"
    show "state s'" using new_fix_pr_closed[OF state 1] .
  next
    fix f
    assume 1: "new_feature_pr s f s'"
    show "state s'" using new_feature_pr_closed[OF state 1] .
  next
    fix r x'
    assume 1[symmetric]: "Some x' = merge_release_branch_into_main (state_repo s) r"
      and s'_eq: "s' = (x', (state_release_pr s)(r \<mapsto> Merged), state_feature_pr s, state_fix_pr s)"
    have x'_eq: "x' = (
      snd (the (merge (repo_git (state_repo s)) {repo_main (state_repo s), the (repo_release (state_repo s) r)})),
      fst (the (merge (repo_git (state_repo s)) {repo_main (state_repo s), the (repo_release (state_repo s) r)})),
      repo_release (state_repo s),
      repo_feature (state_repo s),
      repo_fix (state_repo s),
      repo_develop (state_repo s),
      repo_release_next (state_repo s),
      repo_feature_next (state_repo s),
      repo_fix_next (state_repo s)
    )" using 1 unfolding merge_release_branch_into_main_def by (metis option.distinct(1) option.inject)
    obtain c where 2: "repo_release (state_repo s) r = Some c" using 1 unfolding merge_release_branch_into_main_def by fastforce
    show ?thesis unfolding s'_eq using merge_release_branch_into_main_closed[OF state_repo[OF state] 1] proof (rule stateI; auto simp add: x'_eq elim: state_release_pr_eqE[OF state] state_fix_pr_eqE[OF state] state_feature_pr_eqE[OF state])
      fix r' m
      assume "(if r' = r then Some Merged else state_release_pr s r') = Some m"
      thus " \<exists>c. repo_release (state_repo s) r' = Some c" proof (cases "r' = r"; auto intro: 2 state_release_pr_eqE)
        fix r' m
        assume 1: "state_release_pr s r' = Some m"
        show "\<exists>c. repo_release (state_repo s) r' = Some c" using state_release_pr_eqE[OF state 1] by blast
      qed
    qed
  next
    fix r x'
    assume 1: "Some x' = new_fix_branch_from_release (state_repo s) r"
      and s'_eq: "s' = (x', state_release_pr s, state_feature_pr s, state_fix_pr s)"
    have  x'_eq: "x' = (
      repo_git (state_repo s),
      repo_main (state_repo s),
      repo_release (state_repo s),
      repo_feature (state_repo s),
      (repo_fix (state_repo s))(repo_fix_next (state_repo s) := Some (the (repo_release (state_repo s) r))),
      repo_develop (state_repo s),
      repo_release_next (state_repo s),
      repo_feature_next (state_repo s),
      fix_next (repo_fix_next (state_repo s))
    )" using 1 unfolding new_fix_branch_from_release_def by (meson option.discI option.inject)
    obtain c where 2: "repo_release (state_repo s) r = Some c" using 1 unfolding new_fix_branch_from_release_def by fastforce
    show ?thesis unfolding s'_eq x'_eq using new_fix_branch_from_release_closed[OF state_repo[OF state] 1[symmetric]] by (rule stateI; auto simp add: x'_eq elim: state_release_pr_eqE[OF state] state_fix_pr_eqE[OF state] state_feature_pr_eqE[OF state]) 
  next
    assume s'_eq: "s' = (new_feature_branch_from_develop (state_repo s), state_release_pr s, state_feature_pr s, state_fix_pr s)"
    show ?thesis unfolding s'_eq using new_feature_branch_from_develop_closed[OF state_repo[OF state]] proof (rule stateI)
      fix r m
      assume 1: "state_release_pr (new_feature_branch_from_develop (state_repo s), state_release_pr s, state_feature_pr s, state_fix_pr s) r = Some m"
      show "\<exists>c. repo_release (new_feature_branch_from_develop (state_repo s)) r = Some c" unfolding new_feature_branch_from_develop_def repo_release_simp using 1 state_release_pr_eqE[OF state] unfolding state_release_pr_simp by blast
    next
      fix f m r
      assume 1: "state_fix_pr (new_feature_branch_from_develop (state_repo s), state_release_pr s, state_feature_pr s, state_fix_pr s) f r = Some m"
      show "(\<exists>c. repo_fix (new_feature_branch_from_develop (state_repo s)) f = Some c) \<and> (\<exists>c. repo_release (new_feature_branch_from_develop (state_repo s)) r = Some c)" unfolding new_feature_branch_from_develop_def repo_fix_simp using 1 state_fix_pr_eqE[OF state] unfolding state_fix_pr_simp proof simp
        show "(\<exists>c. repo_fix (state_repo s) f = Some c) \<and> (\<exists>c. repo_release (state_repo s) r = Some c)" using 1 \<open>\<And>thesis r m f. \<lbrakk>state_fix_pr s f r = Some m; \<And>c c'. \<lbrakk>repo_fix (state_repo s) f = Some c; repo_release (state_repo s) r = Some c'\<rbrakk> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close> by fastforce
      qed
    next
      fix f m r
      assume 1: "state_feature_pr (new_feature_branch_from_develop (state_repo s), state_release_pr s, state_feature_pr s, state_fix_pr s) f = Some m"
      show "\<exists>c. repo_feature (new_feature_branch_from_develop (state_repo s)) f = Some c" unfolding new_feature_branch_from_develop_def repo_feature_simp using 1 state_feature_pr_eqE[OF state] unfolding state_feature_pr_simp by (metis fun_upd_apply)
    next
      show " (new_feature_branch_from_develop (state_repo s), state_release_pr s, state_feature_pr s, state_fix_pr s) = (new_feature_branch_from_develop (state_repo s), state_release_pr s, state_feature_pr s, state_fix_pr s)" by simp
    next
      show "new_feature_branch_from_develop (state_repo s) = new_feature_branch_from_develop (state_repo s)" by simp
    qed
  next
    fix f x'
    assume 1: "Some x' = commit_on_fix_branch (state_repo s) f"
      and s'_eq: " s' = (x', state_release_pr s, state_feature_pr s, state_fix_pr s)"
    have x'_eq: "x' = (
      snd (the (commit (repo_git (state_repo s)) (the (repo_fix (state_repo s) f)))),
      repo_main (state_repo s),
      repo_release (state_repo s),
      repo_feature (state_repo s),
      (repo_fix (state_repo s))(f := Some (fst (the (commit (repo_git (state_repo s)) (the (repo_fix (state_repo s) f)))))),
      repo_develop (state_repo s),
      repo_release_next (state_repo s),
      repo_feature_next (state_repo s),
      repo_fix_next (state_repo s)
    )" using 1 unfolding commit_on_fix_branch_def by (meson not_None_eq option.inject)
    obtain c where 2: "repo_fix (state_repo s) f = Some c" using 1 unfolding commit_on_fix_branch_def by fastforce
    show ?thesis unfolding s'_eq x'_eq using commit_on_fix_branch_closed[OF state_repo[OF state] 1[symmetric]] by (rule stateI; auto elim!: state_release_pr_eqE[OF state] state_fix_pr_eqE[OF state] state_feature_pr_eqE[OF state] simp add: x'_eq)
  next
    fix f x'
    assume 1: "Some x' = commit_on_feature_branch (state_repo s) f"
      and s'_eq: "s' = (x', state_release_pr s, state_feature_pr s, state_fix_pr s)"
    have x'_eq: "x' = (
      snd (the (commit (repo_git (state_repo s)) (the (repo_feature (state_repo s) f)))),
      repo_main (state_repo s),
      repo_release (state_repo s),
      (repo_feature (state_repo s))(f := Some (fst (the (commit (repo_git (state_repo s)) (the (repo_feature (state_repo s) f)))))),
      repo_fix (state_repo s),
      repo_develop (state_repo s),
      repo_release_next (state_repo s),
      repo_feature_next (state_repo s),
      repo_fix_next (state_repo s)
    )" using 1 unfolding commit_on_feature_branch_def by (meson option.discI option.inject)
    obtain c where 2: "repo_feature (state_repo s) f = Some c" using 1 unfolding commit_on_feature_branch_def by fastforce
    show ?thesis unfolding s'_eq x'_eq using commit_on_feature_branch_closed[OF state_repo[OF state] 1[symmetric]] by (rule stateI; auto elim!: state_release_pr_eqE[OF state] state_fix_pr_eqE[OF state] state_feature_pr_eqE[OF state] simp add: x'_eq)
  next
    fix f r x'
    assume 1: "Some x' = merge_fix_branch_into_release (state_repo s) f r"
      and s'_eq: "s' = (x', state_release_pr s, state_feature_pr s, (state_fix_pr s)(f := \<lambda>r'. if r = r' then Some Merged else None))"
    have x'_eq: "x' = (
      snd (the (merge (repo_git (state_repo s)) {the (repo_release (state_repo s) r), the (repo_fix (state_repo s) f)})),
      repo_main (state_repo s),
      (repo_release (state_repo s))(r := Some (fst (the (merge (repo_git (state_repo s)) {the (repo_release (state_repo s) r), the (repo_fix (state_repo s) f)})))),
      repo_feature (state_repo s),
      repo_fix (state_repo s),
      repo_develop (state_repo s),
      repo_release_next (state_repo s),
      repo_feature_next (state_repo s),
      repo_fix_next (state_repo s)
    )" using 1 unfolding merge_fix_branch_into_release_def by (meson option.discI option.inject)
    obtain c where 2: "repo_release (state_repo s) r = Some c" using 1 unfolding merge_fix_branch_into_release_def by fastforce
    obtain c' where 3: "repo_fix (state_repo s) f = Some c'" using 1 unfolding merge_fix_branch_into_release_def by fastforce
    show ?thesis unfolding s'_eq x'_eq using merge_fix_branch_into_release_closed[OF state_repo[OF state] 1[symmetric]] proof (rule stateI; auto elim!: state_release_pr_eqE[OF state] state_feature_pr_eqE[OF state] simp add: x'_eq)
      fix f' m
      assume "(if f' = f then \<lambda>r'. if r = r' then Some Merged else None else state_fix_pr s f') r = Some m"
      thus "\<exists>c. repo_fix (state_repo s) f' = Some c" by (cases "f' = f"; auto intro: 3 elim!: state_fix_pr_eqE[OF state])
    next
      fix f' m r''
      assume "(if f' = f then \<lambda>r'. if r = r' then Some Merged else None else state_fix_pr s f') r'' = Some m"
      thus "\<exists>c. repo_fix (state_repo s) f' = Some c" by (cases "f' = f"; auto intro: 3 elim!: state_fix_pr_eqE[OF state])
    next
      fix f' m r''
      assume "(if f' = f then \<lambda>r'. if r = r' then Some Merged else None else state_fix_pr s f') r'' = Some m"
      thus "\<exists>c. repo_release (state_repo s) r'' = Some c" proof (cases "f' = f \<or> r'' = r"; auto intro: 2 elim!: state_fix_pr_eqE[OF state])
        assume "(if r = r'' then Some Merged else None) = Some m"
        hence r''_eq: "r'' = r" by (metis option.distinct(1))
        show "\<exists>c. repo_release (state_repo s) r'' = Some c" unfolding r''_eq using 2 by simp
      qed
    qed
  next
    fix f x'
    assume 1: "Some x' = merge_feature_branch_into_develop (state_repo s) f"
      and s'_eq: "s' = (x', state_release_pr s, (state_feature_pr s)(f \<mapsto> Merged), state_fix_pr s)"
    have x'_eq: "x' = (
      snd (the (merge (repo_git (state_repo s)) {repo_develop (state_repo s), the (repo_feature (state_repo s) f)})),
      repo_main (state_repo s),
      repo_release (state_repo s),
      repo_feature (state_repo s),
      repo_fix (state_repo s),
      fst (the (merge (repo_git (state_repo s)) {repo_develop (state_repo s), the (repo_feature (state_repo s) f)})),
      repo_release_next (state_repo s),
      repo_feature_next (state_repo s),
      repo_fix_next (state_repo s)
    )" using 1 unfolding merge_feature_branch_into_develop_def by (meson option.discI option.inject)
    obtain c where 2: "repo_feature (state_repo s) f = Some c" using 1 unfolding merge_feature_branch_into_develop_def by fastforce
    show ?thesis unfolding s'_eq x'_eq using merge_feature_branch_into_develop_closed[OF state_repo[OF state] 1[symmetric]] proof (rule stateI; auto elim!: state_release_pr_eqE[OF state] state_fix_pr_eqE[OF state] simp add: x'_eq)
      fix f' m
      assume "(if f' = f then Some Merged else state_feature_pr s f') = Some m"
      thus "\<exists>c. repo_feature (state_repo s) f' = Some c" by (cases "f' = f"; auto intro: 2 elim!: state_feature_pr_eqE[OF state])
    qed
  qed

inductive_set trans_edges :: "state rel"
  where "trans state_init s' \<Longrightarrow> (state_init, s') \<in> trans_edges"
      | "\<lbrakk> (s, s') \<in> trans_edges; trans s' s'' \<rbrakk> \<Longrightarrow> (s', s'') \<in> trans_edges"

lemma trans_edgesE:
  assumes "(s, s') \<in> trans_edges"
  shows "trans s s'"
using assms proof induct
  case (1 s')
  thus ?case .
next
  case (2 s s' s'')
  thus ?case by simp
qed

lemma state_trans_edges:
  assumes "(s, s') \<in> trans_edges"
  shows "state s"
    and "state s'"
  proof -
    show "state s" using assms proof induct
      case (1 s')
      show ?case by (rule state_init)
    next
      case (2 s s' s'')
      show ?case using trans_closed[OF 2(2) trans_edgesE[OF 2(1)]] .
    qed
  next
    show "state s'" using assms proof induct
      case (1 s')
      show ?case using trans_closed[OF state_init 1] .
    next
      case (2 s s' s'')
      show ?case using trans_closed[OF 2(2) 2(3)] .
    qed
  qed
end
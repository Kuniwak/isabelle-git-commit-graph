theory Git
  imports Graph
begin

type_synonym commit = nat
type_synonym git = "commit graph \<times> commit"

definition graph :: "git \<Rightarrow> commit graph"
  where "graph \<equiv> fst"

lemma graph_simp[simp]: "graph (x, y) = x"
  unfolding graph_def by simp

definition commit_next :: "git \<Rightarrow> commit"
  where "commit_next \<equiv> snd"

lemma commit_next_simp[simp]: "commit_next (x, y) = y"
  unfolding commit_next_def by simp

definition git :: "git \<Rightarrow> bool"
  where "git g \<equiv> dag (graph g) \<and> ex_min (graph g) \<and> (\<forall>n. (Suc ^^ n) (commit_next g) \<notin> graph_nodes (graph g))"

lemma git_dag:
  assumes "git g"
  shows "dag (graph g)" using assms unfolding git_def by simp

lemma git_ex_min:
  assumes "git g"
  shows "ex_min (graph g)" using assms unfolding git_def by simp

lemma git_Suc_funpow_nmemI:
  assumes "git g"
  shows "(Suc ^^ n) (commit_next g) \<notin> graph_nodes (graph g)" using assms unfolding git_def by simp

lemma git_Suc_funpow_memE[elim!]:
  assumes git: "git g"
      and mem: "(Suc ^^ n) (commit_next g) \<in> graph_nodes (graph g)"
  shows False
  using assms git_Suc_funpow_nmemI by simp

definition init :: "git"
  where "init \<equiv> (({0}, {}), 1)"

lemma git_init: "git init"
  unfolding git_def init_def by (auto intro: dag_singleton ex_min_singleton)

definition commit :: "git \<Rightarrow> commit \<Rightarrow>(commit \<times> git) option"
  where "commit g parent \<equiv>
    if parent \<in> graph_nodes (graph g)
    then Some (
      commit_next g,
      (
        (
          insert (commit_next g) (graph_nodes (graph g)),
          insert (commit_next g, parent) (graph_edges (graph g))
        ),
        Suc (commit_next g)
      )
    )
    else None"

lemma commit_eq_SomeE:
  assumes "commit g c = Some (c', g')"
  shows "c \<in> graph_nodes (graph g)" using assms unfolding commit_def by (meson option.distinct(1))

lemma commit_closed:
  assumes git: "git g"
    and commit_eq: "commit g c = Some (c', g')"
  shows "git g'" proof -
    have g'_eq: "g' = (
      (
        insert (commit_next g) (graph_nodes (graph g)),
        insert (commit_next g, c) (graph_edges (graph g))
      ),
      Suc (commit_next g)
    )" using commit_eq unfolding commit_def by (metis not_None_eq option.inject prod.sel(2))
    have c'_eq: "c' = commit_next g" using commit_eq unfolding commit_def by (metis fst_conv option.distinct(1) option.sel)
    have 1: "insert (commit_next g, c) (graph_edges (Git.graph g)) = Pair (commit_next g) ` {c} \<union> graph_edges (Git.graph g)" by blast
    show ?thesis unfolding git_def g'_eq proof auto
      show "dag (insert (commit_next g) (graph_nodes (Git.graph g)), insert (commit_next g, c) (graph_edges (Git.graph g)))" unfolding 1 using git_dag[OF git] proof (rule dag_insert_new_edges)
        show "{c} \<subseteq> graph_nodes (Git.graph g)" using commit_eq_SomeE[OF commit_eq] by simp
      next
        show "commit_next g \<notin> graph_nodes (Git.graph g)" using git_Suc_funpow_nmemI[where ?n=0, OF git] by simp
      qed
    next
      show "ex_min (insert (commit_next g) (graph_nodes (Git.graph g)), insert (commit_next g, c) (graph_edges (Git.graph g)))" unfolding 1 using dag_graph[OF git_dag[OF git]] git_ex_min[OF git] proof (rule ex_min_insert_new_edges)
        show "{c} \<noteq> {}" by simp
      next
        show "{c} \<subseteq> graph_nodes (Git.graph g)" using commit_eq_SomeE[OF commit_eq] by simp
      next
        show "commit_next g \<notin> graph_nodes (Git.graph g)" using git_Suc_funpow_nmemI[where ?n=0, OF git] by simp
      qed
    next
      fix n
      assume "Suc (n + commit_next g) \<in> graph_nodes (Git.graph g)"
      thus False using git_Suc_funpow_nmemI[where ?n="Suc n", OF git] by fastforce
    qed
  qed

definition ancestors :: "git \<Rightarrow> commit \<Rightarrow> commit set"
  where "ancestors g c \<equiv> (graph_edges (graph g))\<^sup>* `` {c}"

lemma ancestors_eq: "ancestors g c = insert c ((graph_edges (graph g))\<^sup>+ `` {c})" unfolding ancestors_def rtrancl_trancl_reflcl by blast

lemma ancestors_commit:
  assumes git: "git g"
      and c_mem: "c \<in> graph_nodes (graph g)"
  shows "ancestors (snd (the (commit g c))) c = ancestors g c"
  proof -
    have fst_eq: "fst (the (commit g c)) = commit_next g" unfolding commit_def using c_mem by simp
    have snd_eq: "snd (the (commit g c)) = (
        (
          insert (commit_next g) (graph_nodes (graph g)),
          insert (commit_next g, c) (graph_edges (graph g))
        ),
        Suc (commit_next g)
      )" unfolding commit_def using c_mem by simp
    show ?thesis unfolding ancestors_eq snd_eq fst_eq proof auto
      fix c'
      assume 1: "(c, c') \<in> (insert (commit_next g, c) (graph_edges (Git.graph g)))\<^sup>+"
        and neq: "c' \<noteq> c"
      have "(c, c') \<in> (graph_edges (Git.graph g))\<^sup>*" using mem_tranclE[OF 1] by (metis Suc_funpow add.left_neutral c_mem git git_def)
      thus "(c, c') \<in> (graph_edges (Git.graph g))\<^sup>+" using neq by (metis rtrancl_eq_or_trancl)
    next
      fix c'
      assume 1: "(c, c') \<in> (graph_edges (Git.graph g))\<^sup>+"
      thus "(c, c') \<in> (insert (commit_next g, c) (graph_edges (Git.graph g)))\<^sup>+" by (simp add: trancl_insert)
    qed
  qed

definition mergable :: "git \<Rightarrow> commit set \<Rightarrow> bool"
  where "mergable g C \<equiv> (\<exists>c1 \<in> C. \<exists>c2 \<in> C. c1 \<noteq> c2) \<and> (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 \<longrightarrow> c2 \<notin> ancestors g c1 \<and> c1 \<notin> ancestors g c2) \<and> C \<subseteq> graph_nodes (graph g)"

lemma mergableI:
  assumes c1_mem: "c1 \<in> C"
      and c2_mem: "c2 \<in> C"
      and neq: "c1 \<noteq> c2"
      and no_ancestors: "\<And>c1 c2. \<lbrakk> c1 \<in> C; c2 \<in> C; c1 \<noteq> c2 \<rbrakk> \<Longrightarrow> c1 \<notin> ancestors g c2"
      and subset: "C \<subseteq> graph_nodes (graph g)"
  shows "mergable g C"
  using assms unfolding mergable_def by blast

lemma mergableE1:
  assumes "mergable g C"
  obtains c1 c2 where "c1 \<in> C" and "c2 \<in> C" and "c1 \<noteq> c2" using assms unfolding mergable_def by blast

lemma mergableE2:
  assumes mergable: "mergable g C"
      and "c1 \<in> C"
      and "c2 \<in> C"
      and "c1 \<noteq> c2"
  shows "c1 \<notin> ancestors g c2"
    and "C \<subseteq> graph_nodes (graph g)"
  using assms unfolding mergable_def by simp_all

definition merge :: "git \<Rightarrow> commit set \<Rightarrow> (commit \<times> git) option"
  where "merge g parents \<equiv> if mergable g parents
    then Some (
      commit_next g,
      (
        (
          insert (commit_next g) (graph_nodes (graph g)),
          Pair (commit_next g) ` parents \<union> graph_edges (graph g)
        ),
        Suc (commit_next g)
      )
    )
    else None"

lemma merge_eq_SomeE:
  assumes "merge g C = Some (c, g')"
  shows "mergable g C"
  using assms unfolding merge_def by (meson option.distinct(1))

lemma merge_closed:
  assumes git: "git g"
    and merge_eq: "merge g C = Some (c, g')"
  shows "git g'"
  proof -
    have g'_eq: "g' = (
      (
        insert (commit_next g) (graph_nodes (graph g)),
        Pair (commit_next g) ` C \<union> graph_edges (graph g)
      ),
      Suc (commit_next g)
    )" using merge_eq unfolding merge_def by (metis option.distinct(1) option.inject prod.sel(2))
    show ?thesis unfolding git_def g'_eq proof auto
      show "dag (insert (commit_next g) (graph_nodes (Git.graph g)), Pair (commit_next g) ` C \<union> graph_edges (Git.graph g))" using git_dag[OF git] proof (rule dag_insert_new_edges)
        show "C \<subseteq> graph_nodes (Git.graph g)" using merge_eq_SomeE[OF merge_eq] unfolding mergable_def by simp
      next
        show "commit_next g \<notin> graph_nodes (Git.graph g)" using git_Suc_funpow_nmemI[OF git, where ?n=0] by simp
      qed
    next      
      show "ex_min (insert (commit_next g) (graph_nodes (Git.graph g)), Pair (commit_next g) ` C \<union> graph_edges (Git.graph g))" using dag_graph[OF git_dag[OF git]] git_ex_min[OF git] proof (rule ex_min_insert_new_edges)
        show "C \<noteq> {}" using merge_eq_SomeE[OF merge_eq] unfolding mergable_def by blast
      next
        show "C \<subseteq> graph_nodes (Git.graph g)" using merge_eq_SomeE[OF merge_eq] unfolding mergable_def by simp
      next
        show "commit_next g \<notin> graph_nodes (Git.graph g)" using git_Suc_funpow_nmemI[OF git, where ?n=0] by simp
      qed
    next
      fix n
      assume "Suc (n + commit_next g) \<in> graph_nodes (Git.graph g)"
      thus False using git_Suc_funpow_nmemI[OF git, where ?n="Suc n"] by simp
    qed
  qed

end
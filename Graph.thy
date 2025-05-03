theory Graph
  imports Main
begin

type_synonym 'a graph = "'a set \<times> 'a rel"

definition graph_nodes :: "'a graph \<Rightarrow> 'a set"
  where "graph_nodes \<equiv> fst"

lemma [simp]: "graph_nodes (a, b) = a"
  unfolding graph_nodes_def by simp

definition graph_edges :: "'a graph \<Rightarrow> 'a rel"
  where "graph_edges \<equiv> snd"

lemma [simp]: "graph_edges (a, b) = b"
  unfolding graph_edges_def by simp

definition graph :: "'a graph \<Rightarrow> bool"
  where "graph g \<equiv> Field (graph_edges g) \<subseteq> graph_nodes g \<and> finite (graph_nodes g)"

lemma finite_graph_nodes:
  assumes graph: "graph g"
  shows "finite (graph_nodes g)"
  using assms unfolding graph_def by simp

lemma finite_graph_edges:
  assumes graph: "graph g"
  shows "finite (graph_edges g)"
  proof -
    have "graph_edges g \<subseteq> (graph_nodes g) \<times> (graph_nodes g)" using graph unfolding graph_def by (metis r_into_trancl' subsetI subset_trans times_subset_iff trancl_subset_Field2)
    thus ?thesis using finite_cartesian_product by (metis graph_def finite_subset graph)
  qed

lemma nmem_graph_edgesI:
  assumes graph: "graph g"
    and nmem: "n \<notin> graph_nodes g"
  shows "\<And>n'. (n, n') \<notin> graph_edges g"
    and "\<And>n'. (n', n) \<notin> graph_edges g"
  proof -
    fix n'
    show "(n, n') \<notin> graph_edges g" using graph nmem unfolding graph_def graph_edges_def graph_nodes_def by (meson FieldI1 subset_iff)
  next
    fix n'
    show "(n', n) \<notin> graph_edges g" using graph nmem unfolding graph_def graph_edges_def graph_nodes_def by (meson FieldI2 subset_iff)
  qed

definition less_set :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "less_set g c \<equiv> (graph_edges g)\<^sup>+ `` {c}"

definition less_eq_set :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "less_eq_set g c \<equiv> (graph_edges g)\<^sup>* `` {c}"
definition ex_min :: "'a graph \<Rightarrow> bool"
  where "ex_min g \<equiv> \<exists>c. \<forall>c' \<in> graph_nodes g. (c', c) \<in> (graph_edges g)\<^sup>*"

lemma ex_min_insert_new_edges:
  assumes graph: "graph g"
      and ex_min: "ex_min g"
      and nempty: "N \<noteq> {}"
      and N_subset: "N \<subseteq> graph_nodes g"
      and nmem: "n \<notin> graph_nodes g"
  shows "ex_min (insert n (graph_nodes g), Pair n ` N \<union> graph_edges g)"
  unfolding ex_min_def proof auto
    obtain m where m_m'_mem: "\<And>m'. m' \<in> graph_nodes g \<Longrightarrow> (m', m) \<in> (graph_edges g)\<^sup>*" using ex_min unfolding ex_min_def by blast
    show "\<exists>c. (n, c) \<in> (Pair n ` N \<union> graph_edges g)\<^sup>* \<and> (\<forall>c'\<in>graph_nodes g. (c', c) \<in> (Pair n ` N \<union> graph_edges g)\<^sup>*)" proof (rule exI[where ?x=m], auto)
      show "(n, m) \<in> (Pair n ` N \<union> graph_edges g)\<^sup>*" proof -
        obtain n' where n'_mem: "n' \<in> N" and n'_m_mem: "(n', m) \<in> (graph_edges g)\<^sup>*" using nempty N_subset m_m'_mem by blast
        hence "(n', m) \<in> (graph_edges g)\<^sup>*" using m_m'_mem N_subset by blast
        thus "(n, m) \<in> (Pair n ` N \<union> graph_edges g)\<^sup>*" using n'_mem by (meson Un_upper1 converse_rtrancl_into_rtrancl image_subset_iff in_rtrancl_UnI)
      qed
    next
      fix c'
      assume "c' \<in> graph_nodes g"
      hence "(c', m) \<in> (graph_edges g)\<^sup>*" using m_m'_mem by blast
      thus "(c', m) \<in> (Pair n ` N \<union> graph_edges g)\<^sup>*" using in_rtrancl_UnI by blast
    qed
  qed

definition dag :: "'a graph \<Rightarrow> bool"
  where "dag g \<equiv> graph g \<and> acyclic (graph_edges g)"

lemma acyclic_dag:
  assumes "dag g"
  shows "acyclic (graph_edges g)"
  using assms unfolding dag_def by simp

lemma dag_graph:
  assumes "dag g"
  shows "graph g"
  using assms unfolding dag_def by simp

lemma empty_dag: "dag ({}, {})"
  unfolding dag_def graph_def using wf_iff_acyclic_if_finite by force

lemma Id_nmem_trancl_un1:
  assumes "\<And>n'. (n', n) \<notin> X1"
      and "\<And>n'. (n', n) \<notin> X2"
  shows "(n, n) \<notin> (X1 \<union> X2)\<^sup>+"
  by (meson UnE assms tranclD2)

lemma Id_nmem_trancl_un2:
  assumes "\<And>n'. (n, n') \<notin> X1"
      and "\<And>n'. (n, n') \<notin> X2"
  shows "(n, n) \<notin> (X1 \<union> X2)\<^sup>+"
  by (meson UnE assms tranclD)

lemma dag_insert_new_edges:
  assumes dag: "dag g"
    and N_subset: "N \<subseteq> graph_nodes g"
    and n'_nmem: "n \<notin> graph_nodes g"
  shows "dag (insert n (graph_nodes g), Pair n ` N \<union> (graph_edges g))"
  proof -
    have "(n, n) \<notin> (Pair n ` N \<union> (graph_edges g))\<^sup>+" proof (rule Id_nmem_trancl_un1)
      fix n'
      show "(n', n) \<notin> Pair n ` N" using N_subset n'_nmem by blast
    next
      fix n'
      show "(n', n) \<notin> graph_edges g" unfolding graph_def by (simp add: n'_nmem dag_graph[OF dag] nmem_graph_edgesI(2))
    qed
    show "dag (insert n (graph_nodes g), (Pair n ` N) \<union> (graph_edges g))" unfolding dag_def proof auto
      show "graph (insert n (graph_nodes g), Pair n ` N \<union> graph_edges g)" unfolding graph_def proof auto
        fix x
        assume x_mem: "x \<in> Field (Pair n ` N)"
          and x_nmem_nodes: "x \<notin> graph_nodes g"
        have x_nmem_N: "x \<notin> N" using x_nmem_nodes N_subset by (metis subsetD)
        thus "x = n" using x_mem unfolding Field_def by auto
      next
        fix x
        assume x_mem: "x \<in> Field (graph_edges g)"
           and x_nmem: "x \<notin> graph_nodes g"
        thus "x = n" using dag_graph[OF dag] unfolding dag_def graph_def by blast
      next
        show "finite (graph_nodes g)" using dag_graph[OF dag] unfolding graph_def by simp
      qed
    next
      have "finite N" using N_subset finite_graph_nodes[OF dag_graph[OF dag]] finite_subset by blast
      thus "acyclic (Pair n ` N \<union> graph_edges g)" using assms proof (induct N)
        case empty
        thus ?case using acyclic_dag[OF dag] by simp
      next
        case (insert x N')
        hence step: "acyclic (Pair n ` N' \<union> graph_edges g)" by simp
        have x_neq_n: "x \<noteq> n" using insert by blast
        have 1: "(Pair n ` insert x N' \<union> graph_edges g) = insert (n, x) (Pair n ` N' \<union> graph_edges g)" by simp
        show ?case unfolding 1 acyclic_insert proof auto
          show "acyclic (Pair n ` N' \<union> graph_edges g)" using insert by simp
        next
          assume 1: "(x, n) \<in> (Pair n ` N' \<union> graph_edges g)\<^sup>*"
          have "(x, n) \<notin> Pair n ` N'" using x_neq_n by blast
          hence "(x, n) \<in> (graph_edges g)\<^sup>+" using 1 x_neq_n by (smt (verit) f_inv_into_f prod.sel(1) rtrancl_Un_separatorE rtrancl_eq_or_trancl sup_commute)
          hence "n \<in> graph_nodes g" by (meson dag dag_graph nmem_graph_edgesI(2) tranclD2)
          thus False using insert(6) by simp
        qed
      qed
    qed
  qed
end
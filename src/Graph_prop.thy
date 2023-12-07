theory Graph_prop
  imports Graph Bfs Dfs
begin


\<comment> \<open>some other graph properties\<close>

fun reverse_edges :: "edge list => edge list" where
  "reverse_edges [] = []" |
  "reverse_edges (((a,b),w)#es) = ((b,a),w) # (reverse_edges es)"

(*reverse a graph*)
definition reverse :: "graph => graph" where
  "reverse g = (fst g, reverse_edges (snd g))"

lemma reverse_reverse_edges_eq: "reverse_edges (reverse_edges es) = es"
  by (induction es) (auto)
lemma reverse_reverse_eq: "reverse (reverse g) = g"
  by (auto simp: reverse_def reverse_reverse_edges_eq)

(*only suited for union nodes !*)
fun union_list :: "'a list => 'a list => 'a list" where
  "union_list xs [] = xs" |
  "union_list xs (y#ys) = (if y \<in> set xs then union_list xs ys else
    union_list (xs @ [y]) ys)"

lemma distinct_union_list: "distinct xs ==> distinct ys ==> 
  distinct (union_list xs ys)"
  by (induction xs ys rule: union_list.induct) auto

(*different weights are ignored!!!*)
fun union_edges :: "edge list => edge list => edge list" where
  "union_edges es [] = es" |
  "union_edges es (e#ys) = (let es' = e # es in
    if distinct_edges es' then union_edges es' ys else
    union_edges es ys
  )"

(*union 2 graphs*)
definition union_graph :: "graph => graph => graph" where
  "union_graph g1 g2 = ((union_list (fst g1) (fst g2)), (union_edges (snd g1) (snd g2)))"

lemma union_edges: "es' = union_edges e1 e2 ==>
  e \<in> set es' ==> e \<in> set e1 \<or> e \<in> set e2"
  apply (induction e1 e2 rule: union_edges.induct)
  apply (auto split: if_splits)
  done

lemma union_graph: "g1 = (ns1, es1) ==> g2 = (ns2, es2) ==>
  g3 = union_graph g1 g2 ==> e \<in> set (snd g3) ==>
  e \<in> set es1 \<or> e \<in> set es2"
  apply (induction es1 es2 arbitrary: e ns1 ns2 rule: union_edges.induct)
  apply (auto simp:union_graph_def)
  apply (smt (verit, best) old.prod.inject set_ConsD union_edges)+
  done

  
definition undirected :: "graph => bool" where
  "undirected g = (reverse g = g)"

(*make the graph undirected by combing the reverse graph*)
definition to_undi :: "graph => graph" where
  "to_undi g = (union_graph g (reverse g))"

(*if a dfs can explore all the nodes*)
definition connected :: "graph => bool" where
  "connected g = (length (dfs (to_undi g) 0) = length (fst g))"

\<comment> \<open>some properties with paths, not really useful :/ \<close>
type_synonym path = "edge list"

fun path :: "path => bool" where
  "path [] = False" |
  "path [e] = True" |
  "path (((a,b),w1) # ((c,d),w2) # es) = (b = c \<and> path (((c,d),w2)# es))"

fun path_end :: "path => nat" where
  "path_end [] = undefined" |
  "path_end [((_,b), _)] = b" |
  "path_end (p#ps) = path_end ps"
fun path_start :: "path => nat" where
  "path_start [] = undefined" |
  "path_start (((a,_),_)#ps) = a"
fun path_weight :: "path => int" where
  "path_weight [] = 0" |
  "path_weight (((_,_),w)#ps) = w + path_weight ps"

fun step :: "path list => adj_list => path list" where
  "step [] g = []" |
  "step (p#ps) g = (let l = path_end p in
    let ed = map (%(b,w). ((l,b),w)) (get_neighbors l g) in
      map (%n. p @ [n]) ed
  )"
fun steps :: "path list => nat => adj_list => path list" where
  "steps ps 0 _ = ps" |
  "steps ps (Suc n) g = steps (step ps g) n g"
  
lemma path_step_path_aux: "path es ==> a = path_end es ==> 
  (b,w) \<in> set (get_neighbors a g) ==> path (es @ [((a,b),w)])"
  by (induction es rule: path.induct) (auto)

lemma path_step_path: "\<forall>p \<in> set ps. path p ==> \<forall>p' \<in> set (step ps g). path p'"
  apply (induction ps g rule: step.induct)
  apply (auto simp add: Let_def path_step_path_aux)
  done

definition paths_as_edges :: "path list => edge list" where
  "paths_as_edges ps = map (%p. ((path_start p, path_end p), path_weight p)) ps"

definition init_path :: "node list => path list" where
  "init_path ns = map (%n. [((n,n),0)]) ns"

(*every node only has an edge to itself*)  
definition power_of_0 :: "graph => graph" where
  "power_of_0 g = (fst g, paths_as_edges (map (%n. [((n,n),1)]) (fst g)))"

(*edges reachable by n steps*)
definition power_of :: "graph => nat => graph" where
  "power_of g n = (fst g, paths_as_edges (steps (init_path (fst g)) n (to_adj_list g)))"

fun plus_aux :: "graph => nat => graph" where
  "plus_aux g 0 = g" |
  "plus_aux g (Suc n) = (let g' = power_of g (Suc n) in
    union_graph g' (plus_aux g n)
  )"

(*transitive*)
definition g_plus :: "graph => graph" where
  "g_plus g = plus_aux g (length (fst g) - 1)"
(*reflexive + transitive*)
definition g_star :: "graph => graph" where
  "g_star g = union_graph (power_of_0 g) (g_plus g)"

lemma step_2_plus_aux: 
  assumes "distinct_edges wes \<and> edges_in_range wes ns"
    and "g = (ns, wes) \<and> es = map fst wes"
    and "(a,b) \<in> set es \<and> (b,c) \<in> set es"
    and "n = 2 \<and> g' = plus_aux g n"
    and "es' = map fst (snd g')"
  shows "(a,c) \<in> set es'"
  using assms
  apply (induction g n arbitrary: a b c wes ns rule: plus_aux.induct)
  apply (auto simp: Let_def union_graph_def)
  sorry

lemma step_2_plus: 
  assumes "distinct_edges wes \<and> edges_in_range wes ns"
    and "g = (ns, wes) \<and> es = map fst wes"
    and "(a,b) \<in> set es \<and> (b,c) \<in> set es"
    and "g' = g_plus g"
    and "es' = map fst (snd g')"
  shows "(a,c) \<in> set es'"
  using assms apply (induction g arbitrary: a b c ns wes)
  apply (auto simp: g_plus_def step_2_plus_aux)
  sorry

(*all other functions are defined with weighted graph for simplicity*)
definition unweighted_equivalence :: "graph => graph => bool" where
  "unweighted_equivalence g1 g2 = (fst g1 = fst g2 \<and>
    (let e1 = map fst (snd g1); e2 = map fst (snd g2) in
      set e1 = set e2
    ))"

lemma edge_step_two: "distinct_edges wes ==> edges_in_range wes ns ==> 
  g = (ns, wes) ==> es = map fst wes ==>
  (a,b) \<in> set es \<and> (b,c) \<in> set es ==> g' = g_star g ==>
  es' = map fst (snd g') ==> (a,c) \<in> set es'"
  apply (induction g)
  apply (auto simp add: g_plus_def g_star_def step_2_plus_aux)
  sorry

(*trivial due to definition*)
theorem plus_star: "unweighted_equivalence (g_star g) (union_graph (power_of_0 g) (plus_aux g (length (fst g) - 1)))"
  by (auto simp: unweighted_equivalence_def g_plus_def g_star_def)


\<comment> \<open>a graph is bipartite iff the graph can be colored with 2 colors\<close>
datatype color = NONE | RED | BLUE

definition initialize_color :: "node list => (node \<times> color) list" where
  "initialize_color ns = map (%n. (n, NONE)) ns"

fun node_color ::"nat => (node \<times> color) list  => color" where
  "node_color _ [] = NONE" |
  "node_color x ((n, c) # ns) = (if x = n then c else node_color x ns)"

fun change_color :: "nat => color => (node \<times> color) list => (node \<times> color) list" where
  "change_color _ _ [] = []" |
  "change_color n c ((a,c')#ns) = (if n = a then (a,c)#ns else (a,c')#(change_color n c ns))"

(*equivalent to dfs, es and exs are purely for the termination prove*)
function bipartite_aux :: "nat => color => nat => int => adj_list => (node \<times> color) list => edge list => edge list => bool" where
  "bipartite_aux a c n w g cs es exs= (
    let c' = node_color n cs in
    if c' ~= NONE \<or> (length es - length exs = 0) then c ~= c' else
      let neighbors = get_neighbors n g in
        let (cs', nc) = if c = RED then (change_color n BLUE cs, BLUE) else (change_color n RED cs, RED) in
          foldl (%l b. l \<and> bipartite_aux n nc (fst b) (snd b) g cs' es (exs @ [((n, fst b), w)])) True neighbors
  )"
by pat_completeness auto
termination bipartite_aux
  apply (relation "measure (%(a,c,b,w,g,cs,es,exs). length es - length exs)")
  apply (auto split: if_splits)
  done

(*only assumes that the graph is connected*)
(*not connected graph is bipartite iff every connected component in it is bipartite*)
definition bipartite :: "graph => bool" where
  "bipartite g = (connected g \<and> (let g' = union_graph g (reverse g) in
    bipartite_aux 0 NONE 0 0 (to_adj_list g') (initialize_color (fst g')) (snd g') []))"

value "(let g = ([0,1,2,3,4,5], [((0,1),1), ((1,2),1), ((3,2),1), ((4,3),1), ((4,5),1)]) in
  bipartite g)"


end
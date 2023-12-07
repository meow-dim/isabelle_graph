theory Graph
  imports Main
begin

type_synonym edge = "(nat \<times> nat) \<times> int"
type_synonym node = "nat"

type_synonym graph = "(node list \<times> edge list)"
type_synonym adj_list = "(nat \<times> int) list list"

fun distinct_edges :: "edge list => bool" where
  "distinct_edges [] = True" |
  "distinct_edges (((a,b),_)#es) = ((a,b) \<notin> set (map fst es) \<and> distinct_edges es)"
fun edges_in_range :: "edge list => node list => bool" where
  "edges_in_range [] _ = True" |
  "edges_in_range (((a,b),_)#es) ns = (a \<in> set ns \<and> b \<in> set ns \<and> edges_in_range es ns)"
value "distinct_edges [((0, 0), 2), ((0, 0), 0)]"

(*weight is also updated*)
fun update_aux :: "nat => int => (nat \<times> int) list => (nat \<times> int) list" where
  "update_aux b w [] = [(b, w)]" |
  "update_aux b w ((x,y)#xs) = 
    (if b = x then (x,w)#xs 
    else (x,y)#(update_aux b w xs))"

definition update :: "nat => nat => int => adj_list => adj_list" where
[simp]:  "update a b w g = list_update g a (update_aux b w (g!a))"
value "(list_update [1,2,3::nat] 2 5)!2"

fun cons_nodes :: "nat => adj_list" where
  "cons_nodes 0 = []" |
  "cons_nodes (Suc n) = [[]] @ cons_nodes n"

fun to_adj_aux:: "edge list => adj_list => adj_list" where
  "to_adj_aux [] g = g" |
  "to_adj_aux (((a,b),w)#es) g = to_adj_aux es (update a b w g)"

(*convert graph to adjacency list representation*)  
fun to_adj_list :: "graph => adj_list" where
  "to_adj_list (ns, es) = to_adj_aux es (cons_nodes (length ns))"

value "to_adj_list ([0,1,2,3,4,5],[((0,3),1), ((0,5),2), ((0,5),1), ((5,0), 1)])"

lemma update_aux[simp]: "(b,w) \<in> set (update_aux b w xs)"
  by (induction xs) (auto)

lemma update_in[simp]: "a < length g ==> g = update a b w adj ==>
  (b,w) \<in> set (g!a)"
  by (induction g) (auto) 

lemma to_adj_aux[simp]: "distinct_edges es ==> a < length gs \<and> b < length gs ==>
  g = to_adj_aux es gs ==> ((a,b),w) \<in> set es ==> 
  (b,w) \<in> set (g ! a)"
proof (induction es gs arbitrary: a b w rule: to_adj_aux.induct)
  case (1 g)
  then show ?case by simp
next
  case (2 a b w es gs)
  then have "to_adj_aux (((a,b),w)#es) gs = to_adj_aux es (update a b w gs)"
    by auto
  then have "(b,w) \<in> set ((list_update gs a (update_aux b w (gs!a)))!a)"
    using update_in "2.prems" by auto
  then show ?case sorry
qed
  
definition get_neighbors :: "nat => adj_list => (nat \<times> int) list" where
  "get_neighbors n g = g ! n"

end

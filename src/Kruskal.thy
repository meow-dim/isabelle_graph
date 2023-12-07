theory Kruskal
  imports Graph
begin

\<comment> \<open>kruskal\<close>
(*union find data structure, no time to realize it*)
fun init_disj :: "nat => nat list" where
  "init_disj 0 = [0]" |
  "init_disj (Suc n) = (Suc n) # (init_disj n)"

fun find :: "nat => nat list => nat" where
  "find a parent = a"

fun union_disj :: "nat => nat => nat list => nat list" where
  "union_disj a b parent = parent"

fun remove_edges_unweighted :: "nat => nat => edge list => edge list" where
  "remove_edges_unweighted _ _ [] = []" |
  "remove_edges_unweighted a b (((c,d),w)#es) = (
    if (a = c \<and> b = d) \<or> (a = d \<and> b = c) then
      remove_edges_unweighted a b es else
      ((c,d),w) # (remove_edges_unweighted a b es)
  )"


fun kruskal_aux :: "edge list => nat list => edge list => edge list" where
  "kruskal_aux [] d rs = rs" |
  "kruskal_aux (((a,b),w)#es) d rs = (
    if find a d ~= find b d then
      (let d' = union_disj a b d in
        kruskal_aux es d' (rs @ [((a,b),w)]))
    else kruskal_aux es d rs
  )"

abbreviation sort_edges :: "graph => graph" where
  "sort_edges g \<equiv> (fst g, sort_key (%((a,b),w). w) (snd g))"

(*should work, just union find is not completed*)
fun kruskal :: "graph => graph" where
  "kruskal g = (let g' = sort_edges g in
    (fst g, kruskal_aux (snd g') (init_disj (length (fst g') - 1)) [])
  )"
value "kruskal ([0,1,2,3,4,5,6], 
  [((0, 5), 2), ((4, 3), 2), ((3, 2), 2), ((2, 1), 5), ((5, 6), 1), ((4, 6), 4), ((2, 6), 1), ((1, 6), 7), ((0, 6), 3), ((6, 0), 3), ((6, 1), 7), ((6, 2), 1), ((6, 4), 4), ((6, 5), 1), ((1, 2), 5), ((2, 3), 2), ((3, 4), 2), ((5, 0), 2)])"
  
end
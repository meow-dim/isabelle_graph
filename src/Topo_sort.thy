theory Topo_sort
  imports Graph
begin

\<comment> \<open>topological sort\<close>
(*has some bugs, order not correct*)
(*should be similar to dfs, but in other order, bug is not found :/ *)
function topo_rec :: "nat => nat => int => adj_list => nat list => edge list => edge list => nat list => nat list" where
  "topo_rec a n w g xs es exs rs = (if n \<in> set xs \<or> (length es - length exs = 0) then rs else
    let neighbors = get_neighbors n g in
      let rs' = foldl (%l b. topo_rec n (fst b) (snd b) g l es (exs @ [((n, (fst b)),w)]) rs) (xs @ [n]) neighbors in
        if n \<in> set rs' then rs' else n # rs'
    )"
by pat_completeness auto
termination topo_rec
  apply (relation "measure (%(a,n,w,g,xs,es,exs,rs). (length es - length exs))")
  apply (auto)
  done

fun topo_aux :: "graph => nat => nat list => nat list" where
  "topo_aux g 0 xs = topo_rec 0 0 0 (to_adj_list g) xs (snd g) [] xs" |
  "topo_aux g (Suc n) xs = (let xs' = topo_rec n n 0 (to_adj_list g) xs (snd g) [] xs in
    topo_aux g n xs'
  )"

(*bugs exist*)
definition topo_sort :: "graph => nat list" where
  "topo_sort g = topo_aux g (length (fst g)) []"
value "topo_aux ([0,1,2,3,4,5], [((5,2),1), ((5,0),1), ((4,0),1), ((4,1),1), ((2,3),1), ((3,1),1)]) 5 []"
value "topo_sort ([0,1,2,3,4,5], [((5,2),1), ((5,0),1), ((4,0),1), ((4,1),1), ((2,3),1), ((3,1),1)])"
value "topo_sort ([0,1], [((0,1),1), ((1,0),1)])"

end
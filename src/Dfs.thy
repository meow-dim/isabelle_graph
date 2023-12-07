theory Dfs
  imports Graph
begin



\<comment> \<open>dfs\<close>
(*simple dfs*)
function dfs_fold :: "nat => adj_list => nat list => nat list" where
  "dfs_fold n g xs = (if n \<in> set xs then xs else
    let neighbors = get_neighbors n g in
      foldl (%l b. dfs_fold (fst b) g l) (xs @ [n]) neighbors
    )"
by pat_completeness auto
termination dfs_fold
  sorry

(*A simple dfs with fold is hard to prove termination*)
(*es and exs are just arbitrary values that can be used to prove termination with little use*)
(*must be used with the dfs defintion!*)
(*If the arguments are wrongly used, it can lead to early termintation!*)
function dfs_aux :: "nat => nat => int => adj_list => nat list => edge list => edge list => nat list" where
  "dfs_aux a n w g xs es exs = (if n \<in> set xs \<or> (length es - length exs = 0) then xs else
    let neighbors = get_neighbors n g in
      foldl (%l b. dfs_aux n (fst b) (snd b) g l es (exs @ [((n, (fst b)),w)])) (xs @ [n]) neighbors
    )"
by pat_completeness auto
termination dfs_aux
  apply (relation "measure (%(a,n,w,g,xs,es,exs). (length es - length exs))")
  apply (auto)
  done

definition dfs :: "graph => nat => nat list" where
  "dfs g n = dfs_aux n n 0 (to_adj_list g) [] (snd g) []"



end
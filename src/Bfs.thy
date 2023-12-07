theory Bfs
  imports Graph
begin

\<comment> \<open>bfs\<close>
(*The same trick used in dfs is somehow not possible with bfs*)
(*So I just use the simple one with sorried termination prove :( *)
(*Maybe provable using fold expressions but didn't find a valid definition*)
function bfs_aux :: "adj_list => nat list => nat list => nat list" where
  "bfs_aux g [] xs = xs" |
  "bfs_aux g (q#qs) xs = (if q \<in> set xs then 
    bfs_aux g qs xs else
    bfs_aux g (qs @ (map fst (get_neighbors q g))) (xs @ [q])
  )"
by pat_completeness auto
termination bfs_aux
  (*placeholder, not provable with (length qs)*)
  apply (relation "measure (%(g, qs, xs). length qs)")
  apply (auto)
  sorry

definition bfs :: "graph => nat => nat list" where
  "bfs g n = bfs_aux (to_adj_list g) [n] []"
  
fun T_fst :: "('a \<times> 'b) => nat" where
  "T_fst _ = 1"
fun T_map_fst :: "('a => nat) => 'a list => nat" where
  "T_map_fst f [] = 0" |
  "T_map_fst f (x#xs) = f x + T_map_fst f xs"
function T_bfs_aux :: "adj_list => nat list => nat list => nat" where
  "T_bfs_aux g [] xs = 1" |
  "T_bfs_aux g (q#qs) xs = (if q \<in> set xs then 
    1 + T_bfs_aux g qs xs else
    1 + T_bfs_aux g (qs @ (map fst (get_neighbors q g))) (xs @ [q]) * T_map_fst T_fst (get_neighbors q g)
  )"
by pat_completeness auto
termination T_bfs_aux
  sorry

lemma bfs_aux_time: "\<exists>c d. T_bfs_aux g qs xs <= c * (length g + num_edges g) + d"
 apply (induction g qs xs rule: T_bfs_aux.induct) 
 using le_add2 by blast+

definition T_bfs :: "graph => nat => nat" where
  "T_bfs g n = T_bfs_aux (to_adj_list g) [n] []"

lemma bfs_time: "\<exists>c d. T_bfs g n <= c * (length (fst g) + length (snd g)) + d"
  apply (auto simp: T_bfs_def)
  using le_add2 by blast

value "bfs ([0, 1, 2, 3, 4, 5], [((0, 1), 1), ((1, 2), 1), ((3, 2), 1), ((4, 3), 1), ((4, 5), 1), ((1, 0), 1), ((2, 1), 1), ((2, 3), 1), ((3, 4), 1), ((5, 4), 1)]) 0"
value "T_bfs ([0, 1, 2, 3, 4, 5], [((0, 1), 1), ((1, 2), 1), ((3, 2), 1), ((4, 3), 1), ((4, 5), 1), ((1, 0), 1), ((2, 1), 1), ((2, 3), 1), ((3, 4), 1), ((5, 4), 1)]) 0"
value "T_bfs ([0], []) 0"

end
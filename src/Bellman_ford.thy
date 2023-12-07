theory Bellman_ford
  imports Graph
begin

\<comment> \<open>bellman-ford\<close>
fun bell_ford_visit_list :: "nat => (nat \<times> int) list => nat list => int list => (nat list \<times> int list)" where
  "bell_ford_visit_list a [] qs ds = (qs, ds)" |
  "bell_ford_visit_list a (x#xs) qs ds = (
    let b = fst x; w = snd x in
      if ds!b = -1 \<or> (ds!a + w < ds!b) then
        let ds' = list_update ds b (ds!a + w) in
          if b \<notin> set qs then 
            bell_ford_visit_list a xs (qs@[b]) ds' else 
            bell_ford_visit_list a xs qs ds'
      else bell_ford_visit_list a xs qs ds
  )"

function bell_ford_aux :: "adj_list => nat list => int list => int list" where
  "bell_ford_aux g [] ds = ds" |
  "bell_ford_aux g (q#qs) ds = (
    let neighbors = get_neighbors q g in
      let (qs', ds') = bell_ford_visit_list q neighbors qs ds in
        bell_ford_aux g qs' ds'
  )"
by pat_completeness auto
termination bell_ford_aux sorry

fun init_distance :: "nat => nat => int list" where
  "init_distance 0 _ = []" |
  "init_distance (Suc n) a = (if n = a then 0 else -1) # init_distance n a"

(*should work as expected ^_^ *)
definition bellman_ford :: "graph => nat => int list" where
  "bellman_ford g n = bell_ford_aux (to_adj_list g) [n] (init_distance (length (fst g)) (length (fst g) - n -1))"

value "bellman_ford ([0,1,2],[((0,1),1), ((1,2),2)]) 0"

value "to_undi ([0,1,2,3,4,5,6], [((6,0),3), ((6,1),7), ((6,2),1), ((6,4),4), ((6,5),1), ((1,2),5), ((2,3),2), ((3,4),2), ((5,0),2)])"
value "to_adj_list ([0,1,2,3,4,5,6], 
  [((0, 5), 2), ((4, 3), 2), ((3, 2), 2), ((2, 1), 5), ((5, 6), 1), ((4, 6), 4), ((2, 6), 1), ((1, 6), 7), ((0, 6), 3), ((6, 0), 3), ((6, 1), 7), ((6, 2), 1), ((6, 4), 4), ((6, 5), 1), ((1, 2), 5), ((2, 3), 2), ((3, 4), 2), ((5, 0), 2)])"
value "bellman_ford ([0,1,2,3,4,5,6], 
  [((0, 5), 2), ((4, 3), 2), ((3, 2), 2), ((2, 1), 5), ((5, 6), 1), ((4, 6), 4), ((2, 6), 1), ((1, 6), 7), ((0, 6), 3), ((6, 0), 3), ((6, 1), 7), ((6, 2), 1), ((6, 4), 4), ((6, 5), 1), ((1, 2), 5), ((2, 3), 2), ((3, 4), 2), ((5, 0), 2)]) 6"

end
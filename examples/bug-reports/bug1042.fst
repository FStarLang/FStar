module Bug1042

open FStar.List
open FStar.Pervasives.Native

assume val pairs_with_sum (n: nat) : list (p: (nat * nat){fst p + snd p = n})

assume val product (a: Type) (l1: list a) (l2: list a) : list (a * a)

type bin_tree =
| Leaf
| Node of bin_tree * bin_tree

let rec trees_of_size (s: nat) : list bin_tree =
  if s = 0 then
    [Leaf]
  else
    List.Tot.concatMap //#(p:(nat*nat){ fst p + snd p = s - 1 })
                        (fun (s1, s2) -> List.Tot.map Node (product _ (trees_of_size s1) (trees_of_size s2)))
                        (pairs_with_sum (s - 1))

module Main
open List


val prefix : p:list nat -> str:list nat -> Tot bool
let rec prefix p str = match p with 
| [] -> true
| a::q -> 
     (match str with 
      | [] -> false 
      | a'::q' -> if a = a' then prefix q q' else false
     )


val prefix_propr : p : list nat 
                    -> str : list nat 
                    -> Lemma( prefix p str = true <==> (exists (l:list nat). append p l = str)) 

let rec prefix_propr p str = match p with 
| [] -> ()
| a::q -> 
    (match str with 
     | [] -> () 
     | a'::q' -> if a = a' then prefix_propr q q' else ()
    )

val remove_elem_from_list : p : list nat 
                         -> i : nat { i < length p} 
                         -> Tot (list nat)
let rec remove_elem_from_list p i =
match p with 
| a :: q -> if i = 0 then q else a::(remove_elem_from_list q (i-1)) 

val test_prefix : p : list nat -> n : nat{n < length p} -> str : list nat -> Tot bool
let rec test_prefix p n str =
match n with 
| 0 -> prefix (remove_elem_from_list p n) str 
| n -> prefix (remove_elem_from_list p n) str || test_prefix p (n-1) str


val test_prefix_propr : p : list nat 
                         -> n : nat {n < length p} 
                         -> str : list nat 
                         -> Lemma(test_prefix p n str = true <==> (exists (i:nat). i <= n /\ prefix (remove_elem_from_list p i) str))
let rec test_prefix_propr p n str =
match n with | 0 -> () | n -> test_prefix_propr p (n-1) str

val test_relaxed_prefix : p : list nat -> str : list nat -> Tot bool
let test_relaxed_prefix p str = prefix p str || (if length p > 0 then test_prefix p ((length p) -1) str else false)

val test_relaxed_prefix_propr : p : list nat 
                             -> str : list nat 
                             -> Lemma(test_relaxed_prefix p str = true 
                                <==> (prefix p str \/ (exists (i:nat). i < length p /\ prefix (remove_elem_from_list p i) str)))
let test_relaxed_prefix_propr p str = 
if length p = 0 then () 
else test_prefix_propr p (length p - 1) str


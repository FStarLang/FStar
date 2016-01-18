(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Relational.fst
--*)

module Monotonicity
open FStar.Relational
open FStar.RelationalState
open FStar.Comp
open FStar.Heap

(******************************** Example 1 ********************************)

(* A simple pure function *)
val inc_n : int -> int -> Tot int
let inc_n n x = x + n


(* As the function is pure, we can write an extrinsic lemma about it *)
val inc_n_monotone : n:int -> x:int -> y:int 
                  -> Lemma (requires (x <= y)) 
                           (ensures  (inc_n n x <= inc_n n y)) 
let inc_n_monotone n x y = ()


(******************************** Example 2 ********************************)

(* We can also write it as a function on relational pairs *)
val inc_n_rel : eq int -> x:double int{R.l x <= R.r x} -> Tot (y:double int{R.l y <= R.r y})
let inc_n_rel n x = n ^+ x


(******************************** Example 3 ********************************)

(* A pure specification of a stateful function using heap passing *)
val inc_n_st_spec : h:heap -> int -> ref int -> Tot heap
let inc_n_st_spec h n x = upd h x ((sel h x) + n) 


(* A stateful version of inc_n *)
val inc_n_st : n:int -> x:ref int -> ST unit 
                                        (requires (fun h -> True))
                                        (ensures  (fun h1 r h2 -> equal h2 (inc_n_st_spec h1 n x)))
let inc_n_st n x = x := !x + n


(* A proof of monotonicity using the pure specification *)
val inc_n_st_spec_monotone' : h1:heap -> h2:heap -> n:int -> x:ref int 
                  -> Lemma (requires (sel h1 x <= sel h2 x))
                           (ensures  (sel (inc_n_st_spec h1 n x) x <= sel (inc_n_st_spec h2 n x) x))
let inc_n_st_spec_monotone' h1 h2 n x = ()


(* A proof that the stateful function foo3 is monotone using compose2 *)
val inc_n_st_monotone : int -> x:ref int -> ST2 (double unit) 
                                            (requires (fun h -> sel (R.l h) x <= sel (R.r h) x))
                                            (ensures  (fun h1 r h2 -> sel (R.l h2) x <= sel (R.r h2) x))
let inc_n_st_monotone n x = compose2_self (inc_n_st n) (twice x)


(******************************** Example 4 ********************************)

(* A stateful variant operating on relational pairs *)
val inc_n_st_rel : eq int -> x:ref int -> ST2 (double unit) 
                                   (requires (fun h -> sel (R.l h) x <= sel (R.r h) x))
                                   (ensures  (fun h1 r h2 -> sel (R.l h2) x <= sel (R.r h2) x))
let inc_n_st_rel n x = assign_rel1 x ((read_rel1 x) ^+ n)

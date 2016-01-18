(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15 --print_effect_args;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Relational.fst
  --*)

module Test

open FStar.Comp
open FStar.Relational
open FStar.Heap

(* Test cases for project_{l,r} *)
val foo : a:ref int -> double unit -> ST2 (double unit) 
                                      (requires (fun h -> equal (R.l h) (R.r h)))
                                      (ensures  (fun h _ h' -> equal (R.l h') (upd (R.l h) a 0)
                                                            /\ equal (R.r h') (R.l h')))
let foo a tu = compose2_self (fun _ -> a := 0) tu

val foo_l : a:ref int -> unit  -> ST unit 
                                  (requires (fun h -> True))
                                  (ensures  (fun h _ h' -> equal h' (upd h a 0)))
(* Eta expansion is necessary here *)
let foo_l a () = (project_l (foo a)) ()

val foo_r : a:ref int -> unit  -> ST unit 
                                  (requires (fun h -> True))
                                  (ensures  (fun h _ h' -> equal h' (upd h a 0)))
(* Eta expansion is necessary here *)
let foo_r a () = (project_r (foo a)) ()

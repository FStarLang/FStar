(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 5 --project_module TEST --project_module TEST2 --project_module TEST3;
    variables:LIB=../../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst projection.fst TEST_projected.fst
  --*)

module TEST_exptected
open TEST
open Projection
open FStar.Relational
open FStar.Comp
open FStar.Heap

let r_expected = 0 

val r_verify : sem_equiv int
let r_verify tu = compose2 (fun () -> r) (fun () -> r_expected) tu

let test_l_expected x = -x

//val test_l_verify : int -> Tot (sem_equiv int)
(* Unfolding because of #377 *)
val test_l_verify : int -> 
                    double unit -> ST2 (double int) 
                                       (requires (fun h -> equal (R.l h) (R.r h)))
                                       (ensures  (fun h1 r h2 -> (equal (R.l h2) (R.r h2)) /\ (R.l r) = (R.r r)))

let test_l_verify x tu = compose2 (fun a -> test_l x) (fun a -> test_l_expected x) tu


let test2_l_expected a b = a + b

//val test2_l_verify : int -> int -> Tot (sem_equiv int)
(* Unfolding because of #377 *)
val test2_l_verify : int -> int ->
                    double unit -> ST2 (double int) 
                                       (requires (fun h -> equal (R.l h) (R.r h)))
                                       (ensures  (fun h1 r h2 -> (equal (R.l h2) (R.r h2)) /\ (R.l r) = (R.r r)))

let test2_l_verify a b tu = compose2 (fun x -> test2_l a b) (fun x -> test2_l_expected a b) tu


let test3_l_expected a b c = (a + b) * c

//val test3_l_verify : int -> int -> int -> Tot (sem_equiv int)
(* Unfolding because of #377 *)
val test3_l_verify : int -> int -> int ->
                    double unit -> ST2 (double int) 
                                       (requires (fun h -> equal (R.l h) (R.r h)))
                                       (ensures  (fun h1 r h3 -> (equal (R.l h3) (R.r h3)) /\ (R.l r) = (R.r r)))

let test3_l_verify a b c tu = compose2 (fun x -> test3_l a b c) (fun x -> test3_l_expected a b c) tu

let test4_l_expected a b = 
  match a + b with
  | 0 -> 0
  | 1 -> 1
  | x -> x

//val test4_l_verify : int -> int -> Tot (sem_equiv int)
(* Unfolding because of #377 *)
val test4_l_verify : int -> int -> 
                    double unit -> ST2 (double int) 
                                       (requires (fun h -> equal (R.l h) (R.r h)))
                                       (ensures  (fun h1 r h4 -> (equal (R.l h4) (R.r h4)) /\ (R.l r) = (R.r r)))

let test4_l_verify a b tu = compose2 (fun x -> test4_l a b) (fun x -> test4_l_expected a b) tu

let test5_l_expected a b c = c := !a + !b

//val test5_l_verify : ref int -> ref int -> ref int -> Tot (sem_equiv int)
(* Unfolding because of #377 *)
val test5_l_verify : a:ref int -> b:ref int{a <> b} -> c:ref int{c <> a /\ c <> b} -> 
                    double unit -> ST2 (double unit) 
                                       (requires (fun h -> equal (R.l h) (R.r h)))
                                       (ensures  (fun h1 r h5 -> (equal (R.l h5) (R.r h5)) /\ (R.l r) = (R.r r)))

let test5_l_verify a b c tu = compose2 (fun x -> test5_l a b c) (fun x -> test5_l_expected a b c) tu

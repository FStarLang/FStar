(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 5 --project_module TEST --project_module TEST2 --project_module TEST3;
    variables:LIB=../../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst projection.fst
  --*)

module TestPre
open FStar.Relational
open FStar.Comp

let add_rel a b = a ^+ b 
let r2 = R 0 1 
let test x = rel_map1 (fun y -> -y) x

let test2 a b = rel_map2 (fun x y -> x + y) a b

let test3 a b c = rel_map3 (fun x y  z-> (x + y) * z) a b c

let test4 a b  =  let r = rel_map2 (fun x y -> x + y) a b in
                  let bar = (R.l a) + (R.r a) + (R.l b) + (R.r b) in 
                  let test = if R.l a = R.l b then 0 else 1 in 
                  let result  = match r with 
                                | R 0 0 -> R 0 0 
                                | R 1 1 -> R 1 1 
                                | R 0 1 -> R 1 0 
                                | x -> x  
                                | _ -> R 1 9 in 
                  result

let test5 a b c = compose2_self (fun () -> c := !a + !b) (twice ())


module TEST

open TestPre
open Projection
open FStar.Heap
open FStar.Relational
open FStar.Comp

let r = l_PROJECT (iNLINE r2)

(* Refining the return type causes problems with test_l verify due to
   relational subtyping *)
//val test_l : x:int -> Tot (y:int{y= -x})
//val test_l : x:int -> Tot int
let test_l = l_PROJECT (iNLINE test)

//val test2_l : x:int -> y:int -> Tot (z:int{z = x + y})
//val test2_l : x:int -> y:int -> Tot int
let test2_l = l_PROJECT (iNLINE test2)

//val test3_l : x:int -> y:int -> z:int -> Tot (r:int{r = (x + y) * z})
//val test3_l : x:int -> y:int -> z:int -> Tot int
let test3_l = l_PROJECT (iNLINE test3)

//val test4_l : x:int -> y:int -> Tot (z:int{z = x + y})
//val test4_l : x:int -> y:int -> Tot int
let test4_l = l_PROJECT (iNLINE test4)

(*
val test5_l : a:ref int -> b:ref int -> c:ref int
  -> ST unit (requires (fun h -> a <> b /\ a <> c /\ b <> c))
             (ensures  (fun h r h' -> sel h' c = sel h' a + sel h' b))
*)
//val test5_l : a:ref int -> b:ref int -> c:ref int -> St unit
let test5_l = l_PROJECT (iNLINE test5)

module TEST2

open TestPre
open FStar.Heap
open Projection

let r = r_PROJECT (iNLINE r2)

val test_r : x:int -> Tot (y:int{y= -x})
let test_r = r_PROJECT (iNLINE test)

val test2_r : x:int -> y:int -> Tot (z:int{z = x + y})
let test2_r = r_PROJECT (iNLINE test2)

val test3_r : x:int -> y:int -> z:int -> Tot (r:int{r = (x + y) * z})
let test3_r = r_PROJECT (iNLINE test3)

val test4_r : x:int -> y:int -> Tot (z:int{z = x + y})
let test4_r = r_PROJECT (iNLINE test4)

val test5_r : a:ref int -> b:ref int -> c:ref int
  -> ST unit (requires (fun h -> a <> b /\ a <> c /\ b <> c))
             (ensures  (fun h r h' -> sel h' c = sel h' a + sel h' b))
             (* TODO: requires and ensures do not get translates... *)
let test5_r = r_PROJECT (iNLINE test5)

module TEST3

open Projection

type t = int 
type ty : Type =
  | Bla0 : ty
  | Bla1 : x:ty -> ty
  | Bla2 : x:ty -> y:ty -> ty
  | Bla3 : x:ty -> y:ty -> z:ty -> ty



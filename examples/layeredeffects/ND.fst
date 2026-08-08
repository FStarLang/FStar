module ND

(* This example used to present nondeterminism as a layered effect.  The
   effect system no longer has WPs/layering, so this file now keeps just the
   underlying demonic nondeterminism monad: lists. *)

open FStar.Tactics.V2
open FStar.List.Tot

// m is a monad. In this particular example, lists.
val m (a : Type u#a) : Type u#a
let m a = list a

val m_return (#a : Type) : a -> m a
let m_return x = [x]

val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b
let m_bind l f = concatMap f l

let (let!) (#a #b : Type) (v : m a) (f : a -> m b) : m b =
  m_bind v f

val test_f : unit -> m int
let test_f () = [3; 5]

let l () : list int = test_f ()

val choose : #a:Type0 -> x:a -> y:a -> m a
let choose #a x y = [x;y]

val fail : #a:Type0 -> unit -> m a
let fail #a () = []

let flip () : m bool = choose true false

let test () : m int =
  let! x = choose 0 1 in
  let! y = choose 2 3 in
  let! z = choose 4 5 in
  m_return (x + y + z)

let guard (b:bool) : m unit =
  if b
  then m_return ()
  else fail ()
  
let rec pick_from #a (l : list a) : m a =
  match l with
  | [] -> fail ()
  | x::xs ->
    let! b = flip () in
    if b
    then m_return x
    else pick_from xs

let pyths () : m (int & int & int) =
  let l = [1;2;3;4;5;6;7;8;9;10] in
  let! x = pick_from l in
  let! y = pick_from l in
  let! z = pick_from l in
  let! _ = guard (x*x + y*y = z*z) in
  m_return (x,y,z)

(* Extracted code for pyths:

let (pyths_norm : unit -> (Prims.int * Prims.int * Prims.int) Prims.list) =
  fun uu____1038  ->
    [((Prims.parse_int "3"), (Prims.parse_int "4"), (Prims.parse_int "5"));
    ((Prims.parse_int "4"), (Prims.parse_int "3"), (Prims.parse_int "5"));
    ((Prims.parse_int "6"), (Prims.parse_int "8"), (Prims.parse_int "10"));
    ((Prims.parse_int "8"), (Prims.parse_int "6"), (Prims.parse_int "10"))]
*)
let pyths_norm () = normalize_term (pyths ())

(* ^ Try it in emacs: C-c C-s C-e pyths_norm ():
Reducing ‘pyths_norm ()’…
pyths_norm () ↓βδιζr [3, 4, 5; 4, 3, 5; 6, 8, 10; 8, 6, 10] <: list ((int * int) * int)
*)

//
// The following usage of ND was reported in #2293
//
let test_u (t1:Type u#a) (t2:Type u#b) : (_:t1 -> m t2) = admit()

class ml (t:Type) = { mldummy: unit }

instance ml_totarrow (t1:Type u#a) (t2:Type u#b) {| ml t1 |} {| ml t2 |} : ml (t1 -> Tot t2) =
  { mldummy = () }

instance ml_ndarrow (t1:Type u#a) (t2:Type u#b) {| ml t1 |} {| ml t2 |} : ml (t1 -> m t2) =
  { mldummy = () }

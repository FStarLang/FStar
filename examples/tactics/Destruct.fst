module Destruct

open FStar.Tactics

let intros' () = let _ = intros () in ()
let destruct tm = let _ = t_destruct tm in ()
let destruct_intros tm = seq (fun () -> let _ = t_destruct tm in ()) intros'

let dump m =
    (* Tactics.dump m; *)
    ()

(* An enum *)
type t1 =
 | A1
 | B1
 | C1

let f1 (x:t1) : int =
    synth_by_tactic (fun () -> destruct (quote x);
                               dump "11"; exact (`1);
                               dump "12"; exact (`2);
                               dump "13"; exact (`3))

let _ = assert_norm (f1 A1 == 1)
let _ = assert_norm (f1 B1 == 2)
let _ = assert_norm (f1 C1 == 3)

(* Arguments in ctors *)
type t2 =
 | A2 of int
 | B2 of bool * int
 | C2 : nat -> int -> string -> t2

let fst (a,b) = a
let snd (a,b) = b

let f2 (x:t2) : int =
    synth_by_tactic (fun () -> destruct (quote x);
                               dump "21"; let b = intro () in
                                          exact (binder_to_term b);
                               dump "22"; let b = intro () in
                                          let t = binder_to_term b in // TODO: should be let-bound automatically?
                                          exact (`(snd (`#t)));
                               dump "23"; intros' (); exact (`3))

let _ = assert_norm (f2 (A2 1) == 1)
let _ = assert_norm (f2 (B2 (false, 33)) == 33)
let _ = assert_norm (f2 (C2 8 (-1) "hi") == 3)

(* Params *)
type t3 (i:int) =
 | A3 : t3 i
 | B3 : int * string -> t3 i
 | C3 : bool -> nat -> t3 i

let f3 (x:t3 8) : int =
    synth_by_tactic (fun () -> destruct_intros (quote x);
                               dump "31"; exact (`1);
                               dump "32"; exact (`2);
                               dump "33"; exact (`3))

let _ = assert_norm (f3  A3 == 1)
let _ = assert_norm (f3 (B3 (2, "hello")) == 2)
let _ = assert_norm (f3 (C3 false 25) == 3)

(* Type param, which means universe polymorphism *)
type t4 a =
 | A4 of a
 | B4 of a * int
 | C4 : nat -> a -> string -> t4 a

(* Not using Type0 gives a universe unification error, why? *)
let f4 (#a:Type0) (x:t4 a) : int =
    synth_by_tactic (fun () -> destruct_intros (quote x);
                               dump "41"; exact (`1);
                               dump "42"; exact (`2);
                               dump "43"; exact (`3))

let _ = assert_norm (f4 (A4 1) == 1)
let _ = assert_norm (f4 (B4 (false, 44)) == 2)
let _ = assert_norm (f4 (C4 8 (-1) "hi") == 3)

(* Both *)
(* Implicits *)
(* dependency *)

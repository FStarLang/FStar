(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module UnitTests

open FStar.Tactics

let _ = assert True by trivial ()
let _ = assert (1 + 1 = 2) by trivial ()
let _ = assert (1 + 1 == 2) by trivial ()
let _ = assert ("a" ^ "b" = "ab") by trivial ()
let _ = assert ("a" ^ "b" == "ab") by trivial ()

let phi = True

let _ = assert phi by trivial ()

let rec fib n =
    if n < 2
    then n
    else fib (n-1) + fib (n-2)

let _ = assert (fib 5 = 5) by trivial ()
let _ = assert (fib 5 == 5) by trivial ()

let _ =
    let x = 1 in
    assert (1 == x) by trefl ()

let va1    = assert (1 == 1) by trefl ()
let va2 () = assert (1 == 1) by trefl ()
let va3    = fun () -> assert (1 == 1) by trefl ()

type t =
    | A : t
    | B : t
    | C : t
    | D : x:int -> t

let f x =
    match x with
    | A -> A
    | B -> B
    | C -> C
    | D x -> D x

let g (x : t) = f (f (f (f (f (f x)))))

let _ = assert (g A == (f (g A))) by trivial ()
let _ = assert (f B == B) by trivial ()

let _ = assert (A? A == true) by trivial ()
let _ = assert (D? (D 5) == true) by trivial ()
let _ = assert (D?.x (D 5) == 5) by trivial ()

assume val p1 : Type
assume val p2 : Type
assume val proof_1 : squash p1
assume val l : unit -> unit -> Lemma (requires p1) (ensures p2)

let _ =
    assert p2 by (apply_lemma (quote l); exact (quote proof_1))

let _ =
    assert p2 by (apply_lemma (quote (l ())); exact (quote proof_1))

(* This fails, since when we fully apply `l` we get a Pure *)
(* let _ = *)
(*     assert p2 by (apply_lemma (quote (l () ())); *)
(*                   exact (quote proof_1)) *)

assume val pp1 : Type0

val l2 : x:(squash pp1) -> Lemma pp1
let l2 x =
    assert pp1 by assumption ()

type r = {x : int}
let xx : r = {x = 4}

let _ = assert (xx.x = 4) by trivial ()
let _ = assert (xx.x == 4) by trivial ()

assume val dlem : squash True -> squash True -> squash True

let _ = assert True
            by (apply (quote dlem);
                let _ = divide 1 (fun () -> trivial (); qed ())
                                 (fun () -> trivial (); qed ()) in
                qed ())

let _ = assert True
            by (apply (quote dlem);
                let _ = divide 1 (fun () -> trivial (); qed ())
                                 (fun () -> trivial (); qed ()) in
                qed ())

open FStar.Order

let _ = assert (Lt = Lt) by trivial ()
let _ = assert (Gt = Gt) by trivial ()
let _ = assert (Eq = Eq) by trivial ()
let _ = assert (Lt <> Eq) by trivial ()
let _ = assert (Gt <> Lt) by trivial ()
let _ = assert (Eq <> Gt) by trivial ()
let _ = assert (ge Gt) by trivial ()
let _ = assert (ge Eq) by trivial ()
let _ = assert (le Lt) by trivial ()
let _ = assert (le Eq) by trivial ()
let _ = assert (ne Lt) by trivial ()
let _ = assert (ne Gt) by trivial ()

let _ = assert (exists (n:int). n == 5)
            by (witness (quote 5); norm []; trefl (); qed ())

// This one doesn't work, currently, as 5 gets typed as int, and not as nat
// Fixing this seemss non-trivial, after some attempts...
(* let _ = assert (exists (n:nat). n == 5) *)
(*             by (witness (quote 5); trefl (); qed ()) *)

assume val l' : nat -> unit -> Lemma p1
let _ =
    assert p1 by (apply_lemma (quote (l' 5)))

(* Testing pointwise over matches *)
noeq
type tt =
    | CC : int -> bool -> tt
    | BB : tt

let pwtest x =
    assert (match x with | CC a b -> a == a /\ (b == true \/ b == false) | BB -> true)
        by (pointwise trefl)

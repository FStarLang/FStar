module UnitTests

open FStar.Tactics

let _ = assert_by_tactic True
                         trivial
let _ = assert_by_tactic (1 + 1 = 2)
                         trivial
let _ = assert_by_tactic (1 + 1 == 2)
                         trivial
let _ = assert_by_tactic ("a" ^ "b" = "ab")
                         trivial
let _ = assert_by_tactic ("a" ^ "b" == "ab")
                         trivial

let phi = True

let _ = assert_by_tactic phi
                         trivial

let rec fib n =
    if n < 2
    then n
    else fib (n-1) + fib (n-2)

let _ = assert_by_tactic (fib 5 = 5)
                         trivial
let _ = assert_by_tactic (fib 5 == 5)
                         trivial

let _ =
    let x = 1 in
    assert_by_tactic (1 == x) trefl

let va1    = assert_by_tactic (1 == 1) trefl
let va2 () = assert_by_tactic (1 == 1) trefl
let va3    = fun () -> assert_by_tactic (1 == 1) trefl

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

let _ = assert_by_tactic (g A == (f (g A))) trivial
let _ = assert_by_tactic (f B == B) trivial

let _ = assert_by_tactic (A? A == true) trivial
let _ = assert_by_tactic (D? (D 5) == true) trivial
let _ = assert_by_tactic (D?.x (D 5) == 5) trivial

assume val p1 : Type
assume val p2 : Type
assume val proof_1 : squash p1
assume val l : unit -> unit -> Lemma (requires p1) (ensures p2)

let _ =
    assert_by_tactic p2
                     (apply_lemma (quote l);; exact (quote proof_1))

let _ =
    assert_by_tactic p2
                     (apply_lemma (quote (l ()));; exact (quote proof_1))

(* This fails, since when we fully apply `l` we get a Pure *)
(* let _ = *)
(*     assert_by_tactic p2 *)
(*                      (apply_lemma (quote (l () ()));; *)
(*                       exact (quote proof_1)) *)

assume val pp1 : Type0

val l2 : x:(squash pp1) -> Lemma pp1
let l2 x =
    assert_by_tactic pp1 assumption

type r = {x : int}
let xx : r = {x = 4}

let _ = assert_by_tactic (xx.x = 4) trivial
let _ = assert_by_tactic (xx.x == 4) trivial

assume val dlem : squash True -> squash True -> squash True

let _ = assert_by_tactic True (apply (quote dlem);; divide 1 (trivial;; qed) (trivial;; qed);; qed)
let _ = assert_by_tactic True (apply (quote dlem);; focus (trivial;; qed);; focus (trivial;; qed);; qed)

open FStar.Order

let _ = assert_by_tactic (Lt = Lt) trivial
let _ = assert_by_tactic (Gt = Gt) trivial
let _ = assert_by_tactic (Eq = Eq) trivial
let _ = assert_by_tactic (Lt <> Eq) trivial
let _ = assert_by_tactic (Gt <> Lt) trivial
let _ = assert_by_tactic (Eq <> Gt) trivial
let _ = assert_by_tactic (ge Gt) trivial
let _ = assert_by_tactic (ge Eq) trivial
let _ = assert_by_tactic (le Lt) trivial
let _ = assert_by_tactic (le Eq) trivial
let _ = assert_by_tactic (ne Lt) trivial
let _ = assert_by_tactic (ne Gt) trivial

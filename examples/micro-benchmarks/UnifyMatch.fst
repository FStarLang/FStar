module UnifyMatch

open FStar.Tactics

noeq
type t =
    | C : x:int -> y:int -> t

noeq
type s =
    | D : f:(int -> int) -> s

assume val x : s
assume val y : s
assume val ff : int -> int

type unat = | Z : unat | S : unat -> unat
let rec nat2unary (n: nat) : Tot unat = if n = 0 then Z else S (nat2unary (n - 1))
type even : unat -> Type = | Even_Z : even Z | Even_SS : #n: unat -> even n -> even (S (S n))

let tests () : Tac (list (term * term * bool)) = [
  // These tests do not go through now, since we fail to
  // typecheck the when-clauses
  (* (`(fun (x:t) -> match x with | C x y when x > 0 -> y), *)
  (*  `(fun (x:t) -> match x with | C y x when y > 0 -> x), *)
  (*  true); *)

  (* (`(fun (x:t) -> match x with | C x y when x > 0 -> y), *)
  (*  `(fun (x:t) -> match x with | C y x            -> x), *)
  (*  false); *)

  (* (`(fun (x:t) -> match x with | C x y            -> y), *)
  (*  `(fun (x:t) -> match x with | C y x when x > 0 -> x), *)
  (*  false); *)

  (`(fun (x:t) -> match x with | C x y            -> y),
   `(fun (x:t) -> match x with | C x y            -> x),
   false);

  (`(fun (x:t) -> match x with | C x y            -> y),
   `(fun (x:t) -> match x with | C y x            -> x),
   true);

  (`(C?.x),
   norm_term [delta] (`(C?.x)),
   true);

  (`(x.f 2),
   norm_term [delta] (`(x.f 2)),
   true);

  (`(ff (x.f 2)),
   norm_term [delta] (`(ff (x.f 2))),
   true);

  (`(y.f 2),
   norm_term [delta] (`(x.f 2)),
   false);

  (`(ff (y.f 2)),
   norm_term [delta] (`(ff (x.f 2))),
   false);

  (* (`(nat2unary 10), *)
  (*  `(S (nat2unary 9)), *)
  (*  true); *)

  (* (`(nat2unary 9), *)
  (*  `(S (nat2unary 9)), *)
  (*  false); *)

  (* (`(nat2unary 10), *)
  (*  norm_term [delta;zeta;primops] (`(nat2unary 10)), *)
  (*  true); *)

  (* (`(nat2unary 11), *)
  (*  norm_term [delta;zeta;primops] (`(nat2unary 10)), *)
  (*  false); *)

  (`((match D (fun x -> x) with D f -> f) 5),
   `5,
   true);

  (`((match (fun x -> x) with f -> f) 5),
   `5,
   true);

  (`((match D (match D (fun x -> x) with D f -> f) with | D g -> g) 5),
   `5,
   true);
  ]

let test1 tb  : Tac unit =
    let (t1, t2, b) = tb in
    debug ("testing: " ^ term_to_string (quote tb));
    if unify t1 t2 <> b
    then fail ("test failed: " ^ term_to_string (quote tb))
    else ()

let _ = assert_by_tactic True
        (fun () -> let _ = Tactics.Util.map test1 (tests ()) in
                   ())

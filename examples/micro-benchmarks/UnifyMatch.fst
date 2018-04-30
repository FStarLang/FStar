module UnifyMatch

open FStar.Tactics

type t =
    | C : int -> int -> t

let tests : list (term * term * bool) = [
  (`(fun (x:t) -> match x with | C x y when x > 0 -> y),
   `(fun (x:t) -> match x with | C y x when y > 0 -> x),
   true);

  (`(fun (x:t) -> match x with | C x y when x > 0 -> y),
   `(fun (x:t) -> match x with | C y x            -> x),
   false);

  (`(fun (x:t) -> match x with | C x y            -> y),
   `(fun (x:t) -> match x with | C y x when x > 0 -> x),
   false);

  (`(fun (x:t) -> match x with | C x y            -> y),
   `(fun (x:t) -> match x with | C x y            -> x),
   false);

  (`(fun (x:t) -> match x with | C x y            -> y),
   `(fun (x:t) -> match x with | C y x            -> x),
   true);
  ]

let test1 tb  : Tac unit =
    let (t1, t2, b) = tb in
    if unify t1 t2 <> b
    then fail ("test failed: " ^ term_to_string (quote tb))
    else ()

let _ = assert_by_tactic True
        (fun () -> let _ = Tactics.Util.map test1 tests in
                   ())

module UnifyReify

open FStar.Tactics

let test1 tb  : Tac unit =
    let (t1, t2, b) = tb in
    debug ("testing: " ^ term_to_string (quote tb));
    if unify t1 t2 <> b
    then fail ("test failed: " ^ term_to_string (quote tb))
    else ()

let id (a:Type) = unit -> M a
let return_id (a:Type) (x:a) : id a = fun () -> x

let bind_id (a:Type) (b:Type) (x:id a) (f:(a -> id b)) : id b =
  fun () ->
    let x = x () in
    f x ()

total reifiable reflectable new_effect {
  ID : a:Type -> Effect
  with repr   = id
     ; bind   = bind_id
     ; return = return_id
  }

let c1 () : ID int (fun () p -> p 5) = 5

let rc1 () : Tot int = reify (c1 ()) ()

let r1 () : Tot int = 5

let _ =
    assert_norm (rc1 () == 5)

let tests () : Tac (list (term * term * bool)) = [

  (`(rc1),
   `(r1),
   true);

  ]

let _ = assert True
            by (let _ = Tactics.Util.map test1 (tests ()) in ())

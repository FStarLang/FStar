module LambdaImplicits

val id0 : #a:Type -> a -> a
let id0 #a x = x

val id1 : #a:Type -> a -> a
let id1 x = x

val id2 : a:Type -> a -> a
[@(expect_failure [189])]
let id2 x = x

val id3 : a:Type -> a -> a
[@(expect_failure [91])]
let id3 #a x = x

val id4 : #a:Type -> a -> a

(* This should fail, but the error is awful:
 *
 * Test.fst(22,14-22,15): (Error 66) Failed to resolve implicit argument ?1 of
 * type Type introduced for user-provided implicit term at Test.fst(22,14-22,15)
 *
 * Coming from the fact that `fun #_ a x -> x <: #a:Type -> a -> a`
 * (almost) succeeds phase 1 checking, but then the implicit type
 * for `x` cannot be solved. This is the case even before allowing
 * implicit instantiation in lambdas. *)
[@(expect_failure [66])]
let id4 a x = x

val fst0 : #a:Type -> a & a -> a
let fst0 (x, _) = x

val fst : #a:Type -> #b:Type -> a & b -> a
let fst (x, _) = x

val safe_hd : #a:Type -> list a -> option a
let safe_hd = function
              | [] -> None
              | h::_ -> Some h

val bind_opt : #a:Type -> #b:Type -> option a -> (a -> option b) -> option b
let bind_opt o f =
  match o with
  | None -> None
  | Some x -> f x

val bind_opt' : #a:_ -> #b:_ -> (option a & (a -> option b)) -> option b
let bind_opt' =
  function
  | None, _ -> None
  | Some x, f -> f x

(* Can't have a val, see #604 *)
let poly2 (f : (#a:Type -> a -> list a)) : list int & list bool = f 1, f true

let call_poly2 = poly2 (fun x -> [x])

val dep : #a:Type -> (#l : list a) -> unit -> int
let dep () = 1

val app_pure : #a:Type -> #req:_ -> #ens:_
               -> (unit -> Pure a req ens) -> squash req -> Tot a
let app_pure f _ = f ()

val app_pure2 : #a:Type -> #req:_ -> #ens:_
               -> (unit -> Pure a req ens) -> Tot a
let app_pure2 #_ #req f = assume req; f ()

(* Doesn't work due to the arity check for let recs *)
(* val rev : #a:Type -> list a -> list a *)
(* let rec rev xs = *)
(*     match xs with *)
(*     | h :: t-> rev t @ [h] *)
(*     | [] -> [] *)

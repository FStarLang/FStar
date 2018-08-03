module PatAnnot
open FStar.List.Tot

let id x = x
let f () = (), ()

[@expect_failure]
let whoops : squash False =
  match f () with
  | _, (x : squash False) -> x

[@expect_failure]
let whoops2 : squash False =
  let _, (x:unit{False}) = f () in
  assert False

[@expect_failure]
let sub_bv : squash False =
  let _, (l:list int{False}) = splitAt 0 [1;2;3] in
  assert False

[@expect_failure]
let s : squash False =
    match () with
    | x -> let x : squash False = x in x

(* Should fail, we're annotating `x` as a nat which, even if not really
 * taken into account by the typechecker, is wrong. *)
[@expect_failure]
let test1 (i:int) : int =
    match i with
    | (x : nat) -> 1 + x

let test2 (i:int) (_ : squash (i >= 0)) : nat =
    match i with
    | (x : nat) -> x

[@expect_failure]
let test3 : int -> int =
    id (let f : int -> int = fun (x:nat) -> x in f)

let test4 i =
    match i with
    | Some (i:nat)
    | Some i -> 1
    | None -> 2

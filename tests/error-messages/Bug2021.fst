module Bug2021

[@(expect_failure [66])]
let test0 () =
  let x = (fun r -> 2) in
  ()

[@(expect_failure [66])]
let test1 () =
  let x r = 2 in
  ()

[@(expect_failure [66])]
let test2 () =
  ();
  let blah #r : int =
    2
  in
  ()

(* Reports over `f` *)
[@(expect_failure [66])]
let test3 (f : (#x:int -> unit -> unit -> unit)) =
  let blah = f () () in
  ()

(* Reports over `f ()` *)
[@(expect_failure [66])]
let test4 (f : (unit -> #x:int -> unit -> unit)) =
  let blah = f () () in
  ()

(* Reports over `f`, since it raises that error first
 * and then typechecking is aborted. *)
[@(expect_failure [66])]
let test5 (f : (#i:int -> unit -> #x:int -> unit -> unit)) =
  let blah = f () () in
  ()

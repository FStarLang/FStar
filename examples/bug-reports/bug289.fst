module Bug289

open FStar.ST

val foo : unit -> St unit
let foo () = ()

(* val test : unit -> unit *)
(* let test () = () *)

(* val bar : unit -> St unit -- adding this causes assertion failure *)
let bar () = let u = foo () in assert(False) (*; test () -- this too *)

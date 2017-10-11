module Bug377

open FStar.Relational.Comp
open FStar.Relational.Relational

type ni_exp (l:unit) = unit -> St2 (double int)

val expr : unit -> Tot (ni_exp ())
(* The inlined version works *)
(* val expr : unit -> Tot (unit -> St2 (double int)) *)
let expr () = fun () -> compose2 (fun _ -> 0) (fun _ -> 0) (twice ())

(* This also works *)
val expr' : unit -> Tot (ni_exp ())
let expr' () = (fun () -> compose2 (fun _ -> 0) (fun _ -> 0) (twice ()))

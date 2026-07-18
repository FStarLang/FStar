module SolveUnderscore

open FStar.Class.Eq.Raw

let f (#a:Type) (x:a) {| deq a |} (y:a) = x = y

let test0 = f 1 2
let test1 = f #_ 1 2
let test2 = f #int 1 2

let test3 = f 1 #int_has_eq 2

(* An underscore for an implicit that has a meta arg
is solved by the tactic, instead of the unifier. *)
let test4 = f 1 #_ 2

(* This allows to specify only the relevant args for disambiguation
in some cases. See this artificial example *)

let g (#a:Type) {| deq a |} (#b:Type) {| deq b |} (x:a) : b -> a = (fun _ -> x)

let use_g = g #_ #_ #int 5

(* Otherwise, we'd have to provide the dicitionary in the second _, or
call solve. *)
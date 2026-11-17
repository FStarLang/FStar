module TcSquashInstArg

(* Implicit squash arguments of instances are solved by resolution, also
   when it is called through the [solve] tactic. *)

class cls (n : int) = { x : int }

instance cls_pos (n : int) (#_ : squash (n > 0)) : cls n = { x = n }

let d1 : cls 3 = FStar.Tactics.Typeclasses.solve

let d2 (n : int{n > 5}) : cls n = FStar.Tactics.Typeclasses.solve

let f (n : int) {| cls n |} : int = x #n

let d3 (n : int{n > 5}) : int = f n

[@@expect_failure [19]]
let d4 : cls 0 = FStar.Tactics.Typeclasses.solve

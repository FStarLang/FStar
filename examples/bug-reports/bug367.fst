module Bug367

val f : int -> Tot unit
let f = function x | _ -> ()
(*
Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Invalid_argument("for_all2: Different_list_size")
*)

(*
val f : int * int -> Tot unit
let f p = match p with 
| x,y
| x,_ -> ()
Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Invalid_argument("for_all2: Different_list_size")
*)

(*
val f : int -> Tot unit
let f = function x | y -> ()
/home/hritcu/Projects/fstar/pub/examples/bug-reports/bug367.fst(22,16-22,22) : Error
Each branch of this pattern binds different variables: x;
y
*)

module Bug734

type dir =
| Bool | Int | Fun

let arg_type (d:dir) : Tot Type0 =
  match d with
  | Bool   -> bool
  | Int    -> int
  | Fun    -> int -> Tot int

let def_value (d:dir) : Tot (arg_type d) =
  match d with
  | Bool -> true
  | Int -> 42
  | Fun -> (fun (x:int) -> x)

let example_works = def_value Bool

let example_fails = def_value Fun 42

(*
Extracting module Bug
./bug.fst(20,20-20,36): Ill-typed application: application is (Bug.def_value Bug.Fun 42) 
 remaining args are 42
ml type of head is Obj.t
[..]
Error: Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Failure("Ill-typed application: application is (Bug.def_value Bug.Fun 42) \n remaining args are 42\nml type of head is Obj.t\n")
*)

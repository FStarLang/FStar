module OvlShadowing
open OvlInt
open OvlBool

(* A local binder is never overloaded: it shadows every top-level
   candidate, whatever its type. *)
let local_wins (f : string -> string) : string = f "x"

let let_bound_wins =
  let g (x:string) = x in
  g "y"

(* Including when the local is a function argument that could not
   possibly typecheck as one of the top-level candidates -- we must get
   the local's type error, not a resolution error. *)
let lambda_wins = (fun (mk : unit -> unit) -> mk ())

(* A recursive binding is a local too. *)
let rec id (x:string) : string = if true then x else id x

(* Qualification bypasses overloading entirely. *)
let qualified_int  : int  = OvlInt.f 0
let qualified_bool : bool = OvlBool.f true

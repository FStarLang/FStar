type 'a ref' = 'a ref[@@deriving yojson,show]
type 'a ref = 'a ref'[@@deriving yojson,show]

let op_Bang (r:'a ref) = !r
let op_Colon_Equals x y = x := y
let alloc x = ref x
let mk_ref = alloc
let raise = raise
let raise_notrace = raise_notrace
let exit i = exit (Z.to_int i)
exception Failure = Failure (* NB: reusing OCaml's native Failure. *)
(* Normally try_with is compiled by Custard into a native OCaml try...with.
   This definition exists as a fallback in case that does not fire. *)
let try_with f1 f2 = try f1 () with | e -> f2 e
(* let failwith x = raise (Failure x) *)
let failwith (x:string) = raise (Failure x)

type 'a ref' = 'a ref[@@deriving yojson,show]
type 'a ref = 'a ref'[@@deriving yojson,show]

let op_Bang (r:'a ref) = !r
let op_Colon_Equals x y = x := y
let alloc x = ref x
let raise = raise
let exit i = exit (Z.to_int i)
exception Failure = Failure (* NB: reusing OCaml's native Failure. *)
(* Not used: handled specially by extraction. If used,
   you will get all sorts of weird failures (e.g. an incomplete match
   on f2!). *)
(* let try_with f1 f2 = try f1 () with | e -> f2 e *)
(* let failwith x = raise (Failure x) *)

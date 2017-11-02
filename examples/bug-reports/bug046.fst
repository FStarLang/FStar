module Bug046

(* having this type abbreviation seems crucial for reproducing this *)
type env = int -> Tot (option int)

val empty : env
let empty _ = None

assume val xxx : g:env -> Lemma (ensures (Some? (g 45)))

val yyy : unit -> Tot unit
let yyy () =
 match 42 with
 _ -> xxx empty

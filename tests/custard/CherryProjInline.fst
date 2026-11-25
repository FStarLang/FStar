module CherryProjInline
module U32 = FStar.UInt32
open FStar.All

(* A definition that only reads a field of its one parameter is inlined under
   Cherry (cherry.md, "Borrow inference"), so the record of references it
   returns is read from the borrowed [e] without being counted. *)
noeq type tbl = { a: ref int; b: ref int }
noeq type env = { name: string; t: tbl }

let get_t (e: env) : tbl = e.t
let get_t_ml (e: env) : ML tbl = e.t

let use (e: env) : ML int = !(get_t e).a + !(get_t_ml e).b

let main () : ML U32.t =
  let e = { name = "x"; t = { a = alloc 1; b = alloc 2 } } in
  if use e = 3 then 0ul else 1ul

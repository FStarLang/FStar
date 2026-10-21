module CherryAnyIf
(* A conditional whose branches have the types [fname] and [string], equal
   only up to the abbreviation, is a [string]: not an [any] that Cherry boxes
   both arms into.  FStarC.Range.Ops.refind_rng is the shape. *)
module U32 = FStar.UInt32
open FStar.All

type fname = string
type rng = { file_name: fname; start_pos: int; end_pos: int }

let enabled (s:string) : ML bool = s = "on"
let refind (s:string) : ML string = s ^ "!"

let refind_rng (flag:string) (r:rng) : ML rng =
  { r with file_name =
      if enabled flag
      then r.file_name
      else refind r.file_name }

let main () : ML U32.t =
  let r = { file_name = "a"; start_pos = 1; end_pos = 2 } in
  let r1 = refind_rng "on" r in
  let r2 = refind_rng "off" r in
  if r1.file_name = "a" && r2.file_name = "a!" then 0ul else 1ul

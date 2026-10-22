module CherryInitScope
module U32 = FStar.UInt32
open FStar.All

(* All global initializers are printed into one C function.  Their locals
   must not clash, even when the source names coincide and their types
   differ. *)
let twice (x:int) : ML int = x + x
let dup (s:string) : ML string = s ^ s

let g1 : int = let set = twice 3 in set + twice set
let g2 : string = let set = dup "ab" in set ^ dup set
let log : ref (list string) = alloc []
let _ = let set = dup "x" in log := set :: !log
let _ = let set = twice 2 in log := string_of_int set :: !log

let main () : ML U32.t =
  if g1 = 18 && g2 = "abababababab" && !log = ["4"; "xx"] then 0ul else 1ul

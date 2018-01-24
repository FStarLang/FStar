module FStar.HyperStack.IO

open FStar.HyperStack.All

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()

let print_string (s:Prims.string) =
  discard (FStar.IO.debug_print_string s)

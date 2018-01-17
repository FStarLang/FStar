module FStar.HyperStack.IO

open FStar.HyperStack.All

let print_string (s:Prims.string) : Dv unit =
  let _ = FStar.IO.debug_print_string s in ()

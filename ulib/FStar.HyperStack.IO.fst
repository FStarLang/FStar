module FStar.HyperStack.IO

open FStar.HyperStack.All

let print_string (s:Prims.string) : Dv unit =
  FStar.IO.print_string s

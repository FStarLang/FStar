module FStar_HyperStack_IO

open Prims

let print_string : Prims.string -> Prims.unit =
  FStar_IO.print_string

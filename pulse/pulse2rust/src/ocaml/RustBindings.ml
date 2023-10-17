type i64 = Int64.t

let one = Int64.one

module Rust = struct
  (* external add_2 : i64 -> string = "rust_add_2"

  external dflt : i64 option -> string = "rust_dflt" *)
  external fn_to_string : Pulse2Rust_Rust_Syntax.fn -> string = "rust_fn_to_syn_string"
end
(* let add_2 (x:i64) = Rust.add_2 x
let dflt (x:i64 option) = Rust.dflt x *)

let fn_to_string f = Rust.fn_to_string f
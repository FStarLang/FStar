type i64 = Int64.t

let one = Int64.one

module Rust = struct
  (* external add_2 : i64 -> string = "rust_add_2"

  external dflt : i64 option -> string = "rust_dflt" *)
  external fn_to_rust : Pulse2Rust_Rust_Syntax.fn -> string = "rust_fn_to_syn_string"
  external fn_to_string : Pulse2Rust_Rust_Syntax.fn -> string = "rust_fn_to_string"
  external expr_to_string : Pulse2Rust_Rust_Syntax.expr -> string = "rust_expr_to_string"
  external typ_to_string : Pulse2Rust_Rust_Syntax.typ -> string = "rust_typ_to_string"
end
(* let add_2 (x:i64) = Rust.add_2 x
let dflt (x:i64 option) = Rust.dflt x *)

let fn_to_rust f = Rust.fn_to_rust f
let fn_to_string f = Rust.fn_to_string f
let expr_to_string e = Rust.expr_to_string e
let typ_to_string t = Rust.typ_to_string t
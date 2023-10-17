module RustBindings

open FStar.Compiler.Effect

open Pulse2Rust.Rust.Syntax

// val i64 : Type0

// val one : i64

// val add_2 (x:i64) : string

// val dflt (x:option i64) : string

val fn_to_string (f:fn) : string
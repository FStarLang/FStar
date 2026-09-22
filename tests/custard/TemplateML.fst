module TemplateML

open FStar.Attributes

/// Section 69.  A template-id is a C++ construction, so a templated external
/// type is refused by the OCaml backend rather than being emitted with its
/// arguments silently dropped.

[@@custard_extern "tpl_bitset({0})"]
assume val bitset (n : nat) : Type0

[@@custard_extern "tpl_mask"]
assume val mask (_ : unit) : FStar.All.ML (bitset 64)

let main () : FStar.All.ML FStar.Int32.t =
  let _ = mask () in 0l

#light "off"
module FStar.Tactics.Native

open FStar.Tactics.Basic
open FStar.Syntax.Syntax
open FStar.Range

type itac = proofstate -> args -> option<term>

type native_primitive_step =
    { name: FStar.Ident.lid;
      arity: Prims.int;
      strong_reduction_ok: bool;
      tactic: itac}

let list_all () = []

let is_native_tactic t = false
#light "off"
module FStar.Tactics.Native

open FStar.Tactics.Types
open FStar.Tactics.Basic
open FStar.Syntax.Syntax
open FStar.Range
module N = FStar.TypeChecker.Normalize
module EMB = FStar.Syntax.Embeddings

type itac = N.psc -> EMB.norm_cb -> args -> option<term>

type native_primitive_step =
    { name: FStar.Ident.lid;
      arity: Prims.int;
      strong_reduction_ok: bool;
      tactic: itac}

let list_all : unit -> list<native_primitive_step> = fun () -> []

let is_native_tactic : FStar.Ident.lid -> bool = fun _ -> false

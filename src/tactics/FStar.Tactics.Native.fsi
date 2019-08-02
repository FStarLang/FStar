#light "off"
module FStar.Tactics.Native

open FStar.Tactics.Types
open FStar.Tactics.Basic
open FStar.Syntax.Syntax
open FStar.Range
module Cfg = FStar.TypeChecker.Cfg
module N = FStar.TypeChecker.Normalize

type itac = Cfg.psc -> FStar.Syntax.Embeddings.norm_cb -> args -> option<term>

type native_primitive_step =
    { name: FStar.Ident.lid;
      arity: Prims.int;
      strong_reduction_ok: bool;
      tactic: itac}

val list_all: unit -> list<native_primitive_step>
val is_native_tactic: FStar.Ident.lid -> bool

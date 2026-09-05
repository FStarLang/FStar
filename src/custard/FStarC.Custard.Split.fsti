(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(** Output splitting; see doc/ref/custard.md, section 12.9.

    F\*'s hand-written OCaml realizations reference modules Custard compiles,
    so a single output file gives OCaml a reference cycle -- and OCaml
    compilation units must form a DAG.  There is no real cycle: F\*'s module
    graph is one, and every realization sits at a node of it.  The cycle is
    created by emitting one file and removed by emitting several.

    This is *not* separate compilation (sections 12.1-12.8).  It is one
    whole-program run, one monomorphization, one specialization table; all
    that happens here is that the already-topologically-sorted declaration
    list is cut into one piece per F\* source module. *)
module FStarC.Custard.Split

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

module Dep = FStarC.Parser.Dep

(** [run deps prog] partitions [prog] into one piece per F\* source module,
    ordered so that every piece only refers backwards.

    A declaration normally goes to its own module.  Monomorphization breaks
    that: [fStar_List_map__term] is born in [FStar.List] but mentions
    [FStarC.Syntax.Syntax], while [FStarC.Syntax.Syntax] refers to
    [FStar.List].  Such a declaration is **relocated** to the latest module,
    in F\*'s own dependency order, among its own and those of everything it
    references.  A slot always exists: a specialization is created because
    some module instantiated it, and that module depends on every module the
    specialization mentions.

    The result never contains an empty piece, so a module realized by hand --
    whose declarations all print as nothing -- contributes no file. *)
val run : Dep.deps -> list string -> program -> ML (list (string & program))

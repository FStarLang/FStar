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

(** On-demand loading of checked modules for Custard.

    See doc/ref/custard.md, sections 4.1 and 4.2.  The two things that make
    this different from the loading the driver already does:

      - modules are loaded when the extraction loop first reaches them, not
        eagerly from the dependency graph;
      - when a module has both an interface and an implementation, we load the
        *implementation*, since an abstract [val] is useless to an extractor. *)
module FStarC.Custard.Loader

open FStarC
open FStarC.Effect

module Dep   = FStarC.Parser.Dep
module TcEnv = FStarC.TypeChecker.Env

(** The files whose checked file we might load for a module, best first: its
    implementation if it has one, then its interface.  The interface is a real
    fallback -- a module realized by hand in OCaml has an implementation that
    nothing checks, so only its interface is in the cache. *)
val candidate_files : Dep.deps -> string -> ML (list string)

(** [module_is_loaded deps env m] is true when the sigelts Custard needs from
    [m] are already in [env]: its *implementation*, or its interface when it
    has no implementation.  The driver has already loaded the interface of
    every module the entry point depends on, so a test that accepted an
    interface would never load anything. *)
val module_is_loaded : Dep.deps -> TcEnv.env -> string -> ML bool

(** [ensure_loaded deps env m] returns an environment in which [m]'s
    definitions are visible, loading [m]'s checked file if needed.  Fails if
    the module cannot be found or its checked file cannot be read. *)
val ensure_loaded : Dep.deps -> TcEnv.env -> string -> ML TcEnv.env

(** Every file whose checked module this run loaded, with its digest.  A unit
    interface records these (section 12.2) so that linking against a stale unit
    is an error rather than a miscompilation.  The *source* files are what is
    hashed, and the list covers every module the extraction reached, not only
    those that contributed an emitted declaration: a unit that inlines an
    upstream [inline_for_extraction] definition depends on a body that appears
    in no interface at all. *)
val loaded_digests : unit -> ML (list (string & string))

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

(** [module_is_loaded env m] is true when [m]'s sigelts are already in [env],
    i.e. when the driver loaded it as part of the dependency closure. *)
val module_is_loaded : TcEnv.env -> string -> ML bool

(** The file whose checked file we should load for a module: its
    implementation if it has one, otherwise its interface. *)
val implementation_or_interface_of : Dep.deps -> string -> ML (option string)

(** [ensure_loaded deps env m] returns an environment in which [m]'s
    definitions are visible, loading [m]'s checked file if needed.  Fails if
    the module cannot be found or its checked file cannot be read. *)
val ensure_loaded : Dep.deps -> TcEnv.env -> string -> ML TcEnv.env

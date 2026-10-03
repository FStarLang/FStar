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

(** Plugin registration.

    See doc/ref/custard.md section 13.  A definition marked [@@plugin] is
    compiled like any other, and in addition gets a *registration*: a module
    initializer that installs it in the normalizer as a primitive step, with
    the embeddings that convert between F* terms and the compiled function's
    own arguments and result.

    This is the Custard counterpart of {!FStarC.Extraction.ML.RegEmb}, and the
    generated code is the same code -- but it is generated as F* syntax and
    handed to {!FStarC.Custard.Extract}, so that everything the registration
    refers to is requested, specialized and translated by the ordinary
    extraction loop rather than by a second, untyped copy of it. *)
module FStarC.Custard.RegEmb

open FStarC
open FStarC.Effect

module Extract = FStarC.Custard.Extract
module S       = FStarC.Syntax.Syntax

(** Generate the registrations for every [@@plugin] declaration in a module,
    if the module is one of [roots] -- a plugin is registered because the
    program asked for it by name, not because its module happened to be
    loaded.  Called by {!FStarC.Custard.Extract.run} once per loaded module. *)
val handle_module : Extract.state -> list Ident.lident -> S.modul -> ML unit

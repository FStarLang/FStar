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
module FStarC.Tactics.Native

open FStarC.Effect
open FStarC.Syntax.Syntax

module POB = FStarC.TypeChecker.Primops.Base

let compiled_tactics : ref (list native_primitive_step) = mk_ref []

let list_all () =
  if FStarC.Options.no_plugins ()
  then []
  else !compiled_tactics

let register_plugin s arity t n =
  FStarC.TypeChecker.Cfg.register_plugin {
    POB.name = FStarC.Ident.lid_of_str s;
    POB.arity = arity;
    POB.univ_arity = 0;
    POB.auto_reflect = None;
    POB.strong_reduction_ok = true;
    POB.requires_binder_substitution = false;
    POB.renorm_after = false;
    POB.unrepresentable_result = false;
    POB.interpretation = (fun psc cb us args -> t psc cb us args);
    POB.interpretation_nbe = (fun cb us args -> n cb us args);
  }

let register_tactic s arity t =
  let step = {
    name = FStarC.Ident.lid_of_str s;
    arity = arity;
    strong_reduction_ok = true;
    tactic = t;
  } in
  compiled_tactics := step :: !compiled_tactics

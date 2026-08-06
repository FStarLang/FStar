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
module FStarC.Custard.Loader

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Errors.Msg
open FStarC.Syntax.Syntax
open FStarC.Class.Show

module Ch    = FStarC.CheckedFiles
module Dep   = FStarC.Parser.Dep
module DsEnv = FStarC.Syntax.DsEnv
module E     = FStarC.Errors
module Ident = FStarC.Ident
module N     = FStarC.TypeChecker.Normalize
module Tc    = FStarC.TypeChecker.Tc
module U     = FStarC.Syntax.Util
module TcEnv = FStarC.TypeChecker.Env

(* "Loaded" means *the implementation* is loaded.  Checking only that the name
   is known would be wrong in exactly the case that matters: by the time
   Custard runs, every module the entry point depends on has already been
   loaded through its *interface*, whose [val]s say nothing about how anything
   is computed.  Section 4.2. *)
let loaded (env:TcEnv.env) (m:string) (want_impl:bool) : ML bool =
  let m = String.lowercase m in
  TcEnv.modules env |> List.existsb (fun md ->
    String.lowercase (Ident.string_of_lid md.name) = m
    && not (want_impl && md.is_interface))

(* Section 4.2: an abstract [val] in an interface tells an extractor nothing,
   so we go for the implementation whenever there is one.  Loading it pulls in
   the interface anyway (see FStarC.CheckedFiles.fst:341), which is what we
   want: what matters is only that lookup_definition sees the bodies. *)
let implementation_or_interface_of (deps:Dep.deps) (m:string) : ML (option string) =
  (* [Parser.Dep]'s file system map is keyed by *lowercase* module names. *)
  let m = String.lowercase m in
  match Dep.implementation_of deps m with
  | Some fn -> Some fn
  | None -> Dep.interface_of deps m

let module_is_loaded (deps:Dep.deps) (env:TcEnv.env) (m:string) : ML bool =
  loaded env m (Some? (Dep.implementation_of deps (String.lowercase m)))

let ensure_loaded (deps:Dep.deps) (env:TcEnv.env) (m:string) : ML TcEnv.env =
  if module_is_loaded deps env m then env
  else
    match implementation_or_interface_of deps m with
    | None ->
      E.raise_error0 E.Error_CustardEntryNotFound [
        text ("Custard needs module " ^ m ^ ", but it is not in the dependency graph.");
        text "Add the module (or a module that depends on it) to the command line."
      ]
    | Some fn ->
      match Ch.load_module_from_cache env fn with
      | None ->
        E.raise_error0 E.Error_CustardEntryNotFound [
          text ("Custard needs module " ^ m ^ ", but " ^ fn ^ " has no usable checked file.");
          text "Verify the module first, or pass --already_cached appropriately."
        ]
      | Some tcr ->
        (* If the driver already registered this module's *interface*, its
           names are in the desugaring environment; adding them again is an
           Error 47 (duplicate top-level name).  Custard resolves everything
           through lids anyway, so the desugaring environment only needs to be
           extended for a module it has never seen. *)
        let dsenv =
          if loaded env m false then env.dsenv
          else
            let _, dsenv =
              FStarC.ToSyntax.ToSyntax.add_modul_to_env
                tcr.checked_module
                tcr.mii
                (N.erase_universes env)
                env.dsenv
            in
            dsenv
        in
        let env = Tc.load_checked_module { env with dsenv } tcr.checked_module in
        (* [Tc.load_checked_module] deliberately skips every sigelt of an
           implementation whose name already came from that module's
           *interface* -- which is exactly the [val]s Custard is here to
           replace by their definitions (section 4.2).  So push the
           implementation's declarations again, this time forcing them over
           whatever the interface contributed.  As in [Tc], each name is
           looked up right away to populate the environment's cache. *)
        if tcr.checked_module.is_interface then env
        else
          tcr.checked_module.declarations |> List.fold_left (fun env se ->
            let env = TcEnv.push_sigelt_force env se in
            U.lids_of_sigelt se |> List.iter (fun l ->
              ignore (TcEnv.lookup_sigelt env l));
            env) env

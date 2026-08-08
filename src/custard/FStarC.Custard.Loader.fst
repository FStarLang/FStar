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
module SMap  = FStarC.SMap
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
   want: what matters is only that lookup_definition sees the bodies.

   The interface is a *fallback*, not just a last resort: a module realized by
   hand in OCaml has a source implementation that nothing ever checks, so its
   cache holds only the interface, and the interface is all Custard needs --
   the definitions are supplied by the realization (section 8.2), and it is the
   [val]s that describe them. *)
let candidate_files (deps:Dep.deps) (m:string) : ML (list string) =
  (* [Parser.Dep]'s file system map is keyed by *lowercase* module names. *)
  let m = String.lowercase m in
  match Dep.implementation_of deps m, Dep.interface_of deps m with
  | Some i, Some j -> [i; j]
  | Some i, None   -> [i]
  | None,   o      -> (match o with Some j -> [j] | None -> [])

(* A checked file's tc data is only validated against the *digests* of its
   dependences' checked files, and [FStarC.CheckedFiles.hash_dependences] reads
   those digests out of the cache rather than recomputing them (#1668).  The
   dependency scan leaves every checked file in the cache in the [Unknown]
   state, and only [load_module_from_cache] advances one to [Valid]; a
   dependence still [Unknown] when its dependent is loaded is a hard
   [failwith].  Batch mode never hits this because it walks the dependency
   graph in order.  Custard loads modules in *demand* order, which is not a
   topological order of anything, so it has to validate a module's dependences
   itself before asking for the module.  Loading from the cache does not touch
   the type-checking environment, so this stays compatible with section 4.2's
   laziness: it reads checked files, it does not push their declarations. *)
let cache_primed : SMap.t unit = SMap.create 100

let rec prime_cache (deps:Dep.deps) (env:TcEnv.env) (fn:string) : ML unit =
  match SMap.try_find cache_primed fn with
  | Some _ -> ()
  | None ->
    SMap.add cache_primed fn ();
    Dep.deps_of deps fn |> List.iter (prime_cache deps env);
    ignore (Ch.load_module_from_cache env fn)

(* Modules whose implementation is in the dependency graph but has no usable
   checked file, so the interface is the best we will ever get.  Without this,
   [module_is_loaded] would keep demanding an implementation that cannot be
   loaded and [ensure_loaded] would register the interface again on every
   request -- an Error 47 the second time around. *)
let iface_only : SMap.t unit = SMap.create 10

let module_is_loaded (deps:Dep.deps) (env:TcEnv.env) (m:string) : ML bool =
  let m' = String.lowercase m in
  let want_impl = Some? (Dep.implementation_of deps m') && None? (SMap.try_find iface_only m') in
  loaded env m want_impl

let ensure_loaded (deps:Dep.deps) (env:TcEnv.env) (m:string) : ML TcEnv.env =
  if module_is_loaded deps env m then env
  else
    let rec first_usable (fns:list string) : ML (string & Ch.tc_result) =
      match fns with
      | [] ->
        E.raise_error0 E.Error_CustardEntryNotFound [
          text ("Custard needs module " ^ m ^ ", but no usable checked file for \
                it is in the dependency graph.");
          text "Verify the module first, or pass --already_cached appropriately."
        ]
      | fn :: fns ->
        prime_cache deps env fn;
        match Ch.load_module_from_cache env fn with
        | None -> first_usable fns
        | Some tcr -> (fn, tcr)
    in
    let fn, tcr = first_usable (candidate_files deps m) in
    (* We asked for an implementation and got an interface: the implementation
       is realized by hand and nothing ever checked it (section 8.2).  Record
       that, so later requests for this module stop asking.  If the driver had
       already loaded that interface -- which it has, for every module the
       entry point depends on -- there is nothing left to do, and pushing its
       sigelts a second time would be an Error 47. *)
    if not (Dep.is_implementation fn) then
      SMap.add iface_only (String.lowercase m) ();
    if not (Dep.is_implementation fn) && loaded env m false then env
    else begin
        (* If the driver already registered this module's *interface*, its
           names are in the desugaring environment; adding them again is an
           Error 47 (duplicate top-level name).  Custard resolves everything
           through lids anyway, so the desugaring environment only needs to be
           extended for a module it has never seen -- and that question has to
           be asked of the desugaring environment itself, because a module can
           be registered there without appearing among [TcEnv.modules]. *)
        let dsenv =
          if DsEnv.open_modules env.dsenv |> List.existsb (fun (l, _) ->
               String.lowercase (Ident.string_of_lid l) = String.lowercase m)
          then env.dsenv
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
    end

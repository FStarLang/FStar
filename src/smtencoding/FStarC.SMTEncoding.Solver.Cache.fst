(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStarC.SMTEncoding.Solver.Cache

open FStar open FStarC
open FStarC
open FStarC.Effect
open FStarC.TypeChecker.Env
open FStarC.Syntax.Syntax

module BU = FStarC.Util
open FStarC.RBSet

open FStarC.Class.Show
open FStarC.Class.Hashable

(* import instances *)
open FStarC.Syntax.Hash {}

instance hashable_lident : hashable Ident.lident = {
  hash = (fun l -> hash (show l));
}

instance hashable_ident : hashable Ident.ident = {
  hash = (fun i -> hash (show i));
}

instance hashable_binding : hashable binding = {
  hash = (function
          | Binding_var bv -> hash bv.sort
          | Binding_lid (l, (us, t)) -> hash l `mix` hash us `mix` hash t
          | Binding_univ u -> hash u);
}

instance hashable_bv : hashable bv = {
  // hash name?
  hash = (fun b -> hash b.sort);
}

instance hashable_fv : hashable fv = {
  hash = (fun f -> hash f.fv_name.v);
}

instance hashable_binder : hashable binder = {
  hash = (fun b -> hash b.binder_bv);
}

instance hashable_letbinding : hashable letbinding = {
  hash = (fun lb -> hash lb.lbname `mix` hash lb.lbtyp `mix` hash lb.lbdef);
}

instance hashable_pragma : hashable pragma = {
  hash = (function
          | ShowOptions -> hash 1
          | SetOptions s -> hash 2 `mix` hash s
          | ResetOptions s -> hash 3 `mix` hash s
          | PushOptions s -> hash 4 `mix` hash s
          | PopOptions -> hash 5
          | RestartSolver -> hash 6
          | PrintEffectsGraph -> hash 7);
}

let rec hash_sigelt (se:sigelt) : hash_code =
  hash_sigelt' se.sigel

and hash_sigelt' (se:sigelt') : hash_code =
  match se with
  | Sig_inductive_typ {lid; us; params; num_uniform_params; t; mutuals; ds; injective_type_params} ->
    hash 0 `mix`
    hash lid `mix`
    hash us `mix`
    hash params `mix`
    hash num_uniform_params `mix`
    hash t `mix`
    hash mutuals `mix`
    hash ds `mix`
    hash injective_type_params
  | Sig_bundle {ses; lids} ->
    hash 1 `mix`
    (hashable_list #_ {hash=hash_sigelt}).hash ses // sigh, reusing hashable instance when we don't have an instance
    `mix` hash lids
  | Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals; injective_type_params} ->
    hash 2 `mix`
    hash lid `mix`
    hash us `mix`
    hash t `mix`
    hash ty_lid `mix`
    hash num_ty_params `mix`
    hash mutuals `mix`
    hash injective_type_params
  | Sig_declare_typ {lid; us; t} ->
    hash 3 `mix`
    hash lid `mix`
    hash us `mix`
    hash t
  | Sig_let {lbs; lids} ->
    hash 4 `mix`
    hash lbs `mix`
    hash lids
  | Sig_assume {lid; us; phi} ->
    hash 5 `mix`
    hash lid `mix`
    hash us `mix`
    hash phi
  | Sig_pragma p ->
    hash 6 `mix`
    hash p
  | _ ->
    (* FIXME: hash is not completely faithful. In particular
    it ignores effect decls and hashes them the same. *)
    hash 0

instance hashable_sigelt : hashable sigelt = {
  hash = hash_sigelt;
}

(* All that matters for the query cache. *)
instance hashable_env : hashable env = {
  hash = (fun e ->
    hash e.gamma `mix`
    hash e.gamma_sig `mix`
    hash e.proof_ns `mix`
    hash e.admit
  );
}

let query_cache_ref : ref (RBSet.t hash_code) =
  BU.mk_ref (empty ())

let on () =
  Options.query_cache () && Options.ide ()

let query_cache_add (g:env) (q:term) : unit =
  if on () then (
    let h = hash (g, q) in
//     BU.print1 "Adding query cache for %s\n" (show h);
    query_cache_ref := add h !query_cache_ref
  )

let try_find_query_cache (g:env) (q:term) : bool =
  if on () then (
    let h = hash (g, q) in
    let r = mem h !query_cache_ref in
//     BU.print2 "Looked up query cache for %s, r = %s\n" (show h) (show r);
    r
  ) else
    false

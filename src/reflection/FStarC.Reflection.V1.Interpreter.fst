(*
   Copyright 2008-2022 Microsoft Research

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
module FStarC.Reflection.V1.Interpreter

module Cfg   = FStarC.TypeChecker.Cfg
module EMB   = FStarC.Syntax.Embeddings
module NBET  = FStarC.TypeChecker.NBETerm
module NRE   = FStarC.Reflection.V1.NBEEmbeddings
module PO    = FStarC.TypeChecker.Primops
module RB    = FStarC.Reflection.V1.Builtins
module RE    = FStarC.Reflection.V1.Embeddings
open FStarC
open FStarC.List
open FStarC.Ident
open FStarC.Syntax.Syntax
open FStarC.Reflection.V1.Constants
open FStarC.Class.Monad

(* NB: assuming uarity = 0 for these three. Also, they are homogenous in KAM and NBE. *)

val mk1 :
  string ->
  {| EMB.embedding 't1 |} ->
  {| EMB.embedding 'res |} ->
  {| NBET.embedding 't1 |} ->
  {| NBET.embedding 'res |} ->
  ('t1 -> 'res) ->
  PO.primitive_step
let mk1 nm f =
  let lid = fstar_refl_builtins_lid nm in
  PO.mk1' 0 lid
    (fun x -> f x |> Some)
    (fun x -> f x |> Some)

val mk2 :
  string ->
  {| EMB.embedding 't1 |} ->
  {| EMB.embedding 't2 |} ->
  {| EMB.embedding 'res |} ->
  {| NBET.embedding 't1 |} ->
  {| NBET.embedding 't2 |} ->
  {| NBET.embedding 'res |} ->
  ('t1 -> 't2 -> 'res) ->
  PO.primitive_step
let mk2 nm f =
  let lid = fstar_refl_builtins_lid nm in
  PO.mk2' 0 lid
    (fun x y -> f x y |> Some)
    (fun x y -> f x y |> Some)

val mk3 :
  string ->
  {| EMB.embedding 't1 |} ->
  {| EMB.embedding 't2 |} ->
  {| EMB.embedding 't3 |} ->
  {| EMB.embedding 'res |} ->
  {| NBET.embedding 't1 |} ->
  {| NBET.embedding 't2 |} ->
  {| NBET.embedding 't3 |} ->
  {| NBET.embedding 'res |} ->
  ('t1 -> 't2 -> 't3 -> 'res) ->
  PO.primitive_step
let mk3 nm f =
  let lid = fstar_refl_builtins_lid nm in
  PO.mk3' 0 lid
    (fun x y z -> f x y z |> Some)
    (fun x y z -> f x y z |> Some)
    
(* Use these instances in this module *)

instance _ = RE.e_term
instance _ = RE.e_term_view
instance _ = RE.e_fv
instance _ = RE.e_bv
instance _ = RE.e_bv_view
instance _ = RE.e_comp
instance _ = RE.e_comp_view
instance _ = RE.e_universe
instance _ = RE.e_universe_view
instance _ = RE.e_sigelt
instance _ = RE.e_sigelt_view
instance _ = RE.e_binder
instance _ = RE.e_binder_view
instance _ = RE.e_binders
instance _ = RE.e_letbinding
instance _ = RE.e_lb_view
instance _ = RE.e_env
instance _ = RE.e_aqualv
instance _ = RE.e_attributes
instance _ = RE.e_qualifiers
(* And NBE *)
instance _ = NRE.e_term
instance _ = NRE.e_term_view
instance _ = NRE.e_fv
instance _ = NRE.e_bv
instance _ = NRE.e_bv_view
instance _ = NRE.e_comp
instance _ = NRE.e_comp_view
instance _ = NRE.e_universe
instance _ = NRE.e_universe_view
instance _ = NRE.e_sigelt
instance _ = NRE.e_sigelt_view
instance _ = NRE.e_binder
instance _ = NRE.e_binder_view
instance _ = NRE.e_binders
instance _ = NRE.e_letbinding
instance _ = NRE.e_lb_view
instance _ = NRE.e_env
instance _ = NRE.e_aqualv
instance _ = NRE.e_attributes
instance _ = NRE.e_qualifiers

(*
 * NOTE: all primitives must be carefully inspected to make sure they
 * do not break the abstraction barrier imposed by the term_view.
 * Otherwise, the pack_inspect_inv and inspect_pack_inv lemmas could
 * likely be used to derive a contradiction.
 *
 * The way to go about adding new primitives is to implement them in the
 * FStarC.Reflection.V1.Builtins module and implement them using the (internal)
 * inspect_ln and pack_ln functions, which means they should not break
 * the view abstraction.
 *
 * _Any_ call to functions elsewhere, say term_to_string or
 * Util.term_eq, will _very likely_ be inconsistent with the view.
 * Exceptions to the "way to go" above should be well justified.
 *)
let reflection_primops : list PO.primitive_step = [
  (****** Inspecting/packing various kinds of syntax ******)
  mk1 "inspect_ln" RB.inspect_ln ;
  mk1 "pack_ln" RB.pack_ln ;

  mk1 "inspect_fv" RB.inspect_fv;
  mk1 "pack_fv"    RB.pack_fv;

  mk1 "inspect_comp" RB.inspect_comp ;
  mk1 "pack_comp" RB.pack_comp ;

  mk1 "inspect_universe" RB.inspect_universe ;
  mk1 "pack_universe" RB.pack_universe ;
  mk1 "inspect_sigelt" RB.inspect_sigelt ;
  mk1 "pack_sigelt" RB.pack_sigelt ;
  mk1 "inspect_lb" RB.inspect_lb ;
  mk1 "pack_lb" RB.pack_lb ;
  mk1 "inspect_bv" RB.inspect_bv ;
  mk1 "pack_bv" RB.pack_bv ;

  (* TODO: Make this consistent with others? No good reason for it to be "exploded" *)
  mk1 "inspect_binder" RB.inspect_binder;
  mk1 "pack_binder" RB.pack_binder;

  (****** Actual primitives ******)

  mk1 "sigelt_opts" RB.sigelt_opts;

  (* This exposes the embedding of vconfig since it is useful to create attributes *)
  mk1 "embed_vconfig" RB.embed_vconfig;

  mk1 "sigelt_attrs" RB.sigelt_attrs;
  mk2 "set_sigelt_attrs" RB.set_sigelt_attrs;
  mk1 "sigelt_quals" RB.sigelt_quals;
  mk2 "set_sigelt_quals" RB.set_sigelt_quals;
  mk3 "subst" RB.subst;
  mk2 "close_term" RB.close_term;
  mk2 "compare_bv" RB.compare_bv;
  mk2 "lookup_attr" RB.lookup_attr;
  mk1 "all_defs_in_env" RB.all_defs_in_env;
  mk2 "defs_in_module" RB.defs_in_module;

  mk2 "term_eq" RB.term_eq;
  mk1 "moduleof" RB.moduleof;
  mk1 "binders_of_env" RB.binders_of_env;
  mk2 "lookup_typ" RB.lookup_typ;
  mk1 "env_open_modules" RB.env_open_modules;

  (* See note in ulib/FStarC.Reflection.V1.Builtins.fsti: we expose these
     three to reduce dependencies. *)
  mk1 "implode_qn" RB.implode_qn;

  mk1 "explode_qn" RB.explode_qn;
  mk2 "compare_string" RB.compare_string;
  mk2 "push_binder" RB.push_binder;
  mk1 "range_of_term" RB.range_of_term;
  mk1 "range_of_sigelt" RB.range_of_sigelt;
]

let _ = List.iter FStarC.TypeChecker.Cfg.register_extra_step reflection_primops

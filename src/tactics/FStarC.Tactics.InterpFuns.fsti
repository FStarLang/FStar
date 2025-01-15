(*
   Copyright 2008-2016 Microsoft Research

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

module FStarC.Tactics.InterpFuns

(* This module is awful, don't even look at it please. *)

open FStar open FStarC
open FStarC.Effect

open FStarC.Syntax.Embeddings
open FStarC.Tactics.Monad

module Cfg   = FStarC.TypeChecker.Cfg
module NBET  = FStarC.TypeChecker.NBETerm
module PO    = FStarC.TypeChecker.Primops

val max_tac_arity : int // = 20

val interp_ctx : string -> (unit -> 'a) -> 'a

// The mk_tot_step functions use lids in FStar.Stubs.Tactics.Types,
// while mk_tac_step ones go to FStar.Stubs.Tactics.V2.Builtins.
// For V1 there's a pass over the result to change the V2 to V1.

val mk_tot_step_1 :
  univ_arity:int ->
  string ->
  {| embedding 't1 |} ->
  {| embedding 'res |} ->
  {| NBET.embedding 'nt1 |} ->
  {| NBET.embedding 'nres |} ->
  ('t1 -> 'res) ->
  ('nt1 -> 'nres) ->
  PO.primitive_step

val mk_tot_step_2 :
  univ_arity:int ->
  string ->
  {| embedding 't1 |} ->
  {| embedding 't2 |} ->
  {| embedding 'res |} ->
  {| NBET.embedding 'nt1 |} ->
  {| NBET.embedding 'nt2 |} ->
  {| NBET.embedding 'nres |} ->
  ('t1 -> 't2 -> 'res) ->
  ('nt1 -> 'nt2 -> 'nres) ->
  PO.primitive_step

// Step with access to normalizer PSC
val mk_tot_step_1_psc :
  univ_arity:int ->
  string ->
  {| embedding 't1 |} ->
  {| embedding 'res |} ->
  {| NBET.embedding 'nt1 |} ->
  {| NBET.embedding 'nres |} ->
  (PO.psc -> 't1 -> 'res) ->
  (PO.psc -> 'nt1 -> 'nres) ->
  PO.primitive_step

val mk_tac_step_1 :
  univ_arity:int ->
  string ->
  {| embedding 't1 |} ->
  {| embedding 'res |} ->
  {| NBET.embedding 'nt1 |} ->
  {| NBET.embedding 'nres |} ->
  ('t1 -> tac 'res) ->
  ('nt1 -> tac 'nres) ->
  PO.primitive_step

val mk_tac_step_2 :
  univ_arity:int ->
  string ->
  {| embedding 't1 |} ->
  {| embedding 't2 |} ->
  {| embedding 'res |} ->
  {| NBET.embedding 'nt1 |} ->
  {| NBET.embedding 'nt2 |} ->
  {| NBET.embedding 'nres |} ->
  ('t1 -> 't2 -> tac 'res) ->
  ('nt1 -> 'nt2 -> tac 'nres) ->
  PO.primitive_step

val mk_tac_step_3 :
  univ_arity:int ->
  string ->
  {| embedding 't1 |} ->
  {| embedding 't2 |} ->
  {| embedding 't3 |} ->
  {| embedding 'res |} ->
  {| NBET.embedding 'nt1 |} ->
  {| NBET.embedding 'nt2 |} ->
  {| NBET.embedding 'nt3 |} ->
  {| NBET.embedding 'nres |} ->
  ('t1 -> 't2 -> 't3 -> tac 'res) ->
  ('nt1 -> 'nt2 -> 'nt3 -> tac 'nres) ->
  PO.primitive_step

val mk_tac_step_4 :
  univ_arity:int ->
  string ->
  {| embedding 't1 |} ->
  {| embedding 't2 |} ->
  {| embedding 't3 |} ->
  {| embedding 't4 |} ->
  {| embedding 'res |} ->
  {| NBET.embedding 'nt1 |} ->
  {| NBET.embedding 'nt2 |} ->
  {| NBET.embedding 'nt3 |} ->
  {| NBET.embedding 'nt4 |} ->
  {| NBET.embedding 'nres |} ->
  ('t1 -> 't2 -> 't3 -> 't4 -> tac 'res) ->
  ('nt1 -> 'nt2 -> 'nt3 -> 'nt4 -> tac 'nres) ->
  PO.primitive_step

val mk_tac_step_5 :
  univ_arity:int ->
  string ->
  {| embedding 't1 |} ->
  {| embedding 't2 |} ->
  {| embedding 't3 |} ->
  {| embedding 't4 |} ->
  {| embedding 't5 |} ->
  {| embedding 'res |} ->
  {| NBET.embedding 'nt1 |} ->
  {| NBET.embedding 'nt2 |} ->
  {| NBET.embedding 'nt3 |} ->
  {| NBET.embedding 'nt4 |} ->
  {| NBET.embedding 'nt5 |} ->
  {| NBET.embedding 'nres |} ->
  ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> tac 'res) ->
  ('nt1 -> 'nt2 -> 'nt3 -> 'nt4 -> 'nt5 -> tac 'nres) ->
  PO.primitive_step

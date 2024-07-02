(*
   Copyright 2023 Microsoft Research

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

module Pulse.Checker.Prover.Explode

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.PP

open Pulse.Checker.Base
open Pulse.Checker.Prover.Base
open Pulse.Typing.Combinators

let has_structure (q:vprop) : bool =
  match inspect_term q with
  | Tm_Star _ _ -> true
  | _ -> false

val vprop_as_list_roundtrip (g:env) (v:vprop)
  : vprop_equiv g v (list_as_vprop (vprop_as_list v))
let vprop_as_list_roundtrip g v = admit()

let __explode1
  (g:env)
  (q:vprop)
: T.Tac (option (qs: list vprop & vprop_equiv g q (list_as_vprop qs)))
=
  // info_doc pst.pg None [
  //   text "Trying to explode" ^/^ pp q_ss;
  //   text "pst.ss = " ^/^ pp pst.ss;
  //   text "pst.uvs = " ^/^ pp pst.uvs;
  //   text "q= " ^/^ pp q;
  //   text "q_ss= " ^/^ pp q_ss;
  // ];
  if has_structure q
  then (
    // info_doc pst.pg None [
    //   text "Exploding" ^/^ pp q_ss;
    //   text "into" ^/^ pp (vprop_as_list q_ss);
    // ];
    Some (| vprop_as_list q, vprop_as_list_roundtrip _ _ |)
  ) else None

let explode1
  (#preamble:_)
  (pst:prover_state preamble)
  (q:vprop)
: T.Tac (option (qs: list vprop & vprop_equiv (push_env pst.pg pst.uvs) pst.ss.(q) (list_as_vprop qs)))
=
  let q_ss = pst.ss.(q) in
  __explode1 (push_env pst.pg pst.uvs) q_ss

let rec explode_aux
  (#preamble:_)
  (pst:prover_state preamble)
  (prog : bool)
  (acc : list vprop) (todo : list vprop) : T.Tac (list vprop & bool)
=
  match todo with
  | [] -> acc, prog
  | q::qs ->
    let acc', prog' =
      match explode1 pst q with
      | Some (|qs, _|) -> qs, true
      | None -> [q], false
    in
    explode_aux pst (prog || prog') (acc @ acc') qs

let explode
  (#preamble:_) (pst:prover_state preamble)
: T.Tac (pst':prover_state preamble {pst' `pst_extends` pst})
=
  let remaining_ctxt, p1 = explode_aux pst false [] pst.remaining_ctxt in
  let unsolved', p2 = explode_aux pst false [] pst.unsolved in
  { pst with
    unsolved = unsolved';
    goals_inv = magic();
    remaining_ctxt = remaining_ctxt;
    remaining_ctxt_frame_typing = magic();
    k = (admit(); pst.k);
    progress = p1 || p2;
  }

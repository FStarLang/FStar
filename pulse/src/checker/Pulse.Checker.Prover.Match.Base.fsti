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

module Pulse.Checker.Prover.Match.Base

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Prover.Base

module T  = FStar.Tactics.V2
module PS = Pulse.Checker.Prover.Substs

(* Move? *)
let slprop_list_equiv (g:env) (vs1 vs2 : list slprop) : Type =
  slprop_equiv g (list_as_slprop vs1) (list_as_slprop vs2)

let ( $$ ) (ss : PS.ss_t) (ts : list slprop) : list slprop =
  ts |> List.Tot.map (fun t -> PS.ss_term t ss)

(* All of these should be easy. *)
val slprop_list_equiv_refl (g:env) (vs:list slprop) : slprop_list_equiv g vs vs
val slprop_list_equiv_append (g:env) (vs1 vs2 vs3 vs4 : list slprop)
  (d1 : slprop_list_equiv g vs1 vs2)
  (d2 : slprop_list_equiv g vs3 vs4)
  : slprop_list_equiv g (vs1 @ vs3) (vs2 @ vs4)
val slprop_list_equiv_trans (g:env) (vs1 vs2 vs3 : list slprop)
  (d1 : slprop_list_equiv g vs1 vs2)
  (d2 : slprop_list_equiv g vs2 vs3)
  : slprop_list_equiv g vs1 vs3
val slprop_list_equiv_assoc_l (g:env) (vs1 vs2 vs3 : list slprop)
  : slprop_list_equiv g (vs1 @ (vs2 @ vs3)) ((vs1 @ vs2) @ vs3)
val slprop_list_equiv_assoc_r (g:env) (vs1 vs2 vs3 : list slprop)
  : slprop_list_equiv g ((vs1 @ vs2) @ vs3) (vs1 @ (vs2 @ vs3))

val slprop_list_equiv_elim_append (g:env) (vs1 vs2 : list slprop)
  : slprop_equiv g (list_as_slprop (vs1 @ vs2)) (list_as_slprop vs1 * list_as_slprop vs2)
val slprop_list_equiv_elim_append' (g:env) (vs1 vs2 : list slprop)
  : slprop_equiv g (list_as_slprop (vs1 @ vs2)) (list_as_slprop vs2 * list_as_slprop vs1)
val slprop_list_equiv_cons (g:env) (p q : slprop) (ps qs : list slprop)
  (d1 : slprop_equiv g p q)
  (d2 : slprop_list_equiv g ps qs)
  : slprop_list_equiv g (p::ps) (q::qs)

(* The result of a matching pass. Essentially equating part of the context
and goals ("unsolved") and proving it. Essentially:

  ctxt0        = ctxt_matched     + ctxt1
  unsolved0    = unsolved_matched + unsolved1
  ctxt_matched = unsolved_matched

  The ss is the substitution that defines some uvars in the goal/unsolved set.
  We do not need it for the ctxt slprops, those do not mention them.
*)
noeq
type match_pass_result (g:env) (ss:PS.ss_t) (ctxt0 unsolved0 : list slprop) = {
  ss' : (ss' : PS.ss_t {ss' `ss_extends` ss});

  ctxt_matched     : list slprop;
  ctxt1            : list slprop;
  ctxt_ok          : slprop_list_equiv g ctxt0 (ctxt_matched @ ctxt1);

  unsolved_matched : list slprop;
  unsolved1        : list slprop;
  unsolved_ok      : slprop_list_equiv g (unsolved0) (unsolved_matched @ unsolved1);
  
  match_ok         : slprop_list_equiv g ctxt_matched (ss' $$ unsolved_matched);
}

(* A zero for the match pass result, no progress at all.
Copilot wrote this almost correctly in one shot! *)
let mpr_zero (#g #ss #ctxt0 #unsolved0 :_) : match_pass_result g ss ctxt0 unsolved0 =
  { ss' = ss;
    
    ctxt_matched = [];
    ctxt1        = ctxt0;
    ctxt_ok      = slprop_list_equiv_refl _ _;
    
    unsolved_matched = [];
    unsolved1        = unsolved0;
    unsolved_ok      = slprop_list_equiv_refl _ _;
    
    match_ok = slprop_list_equiv_refl _ _;
  }

(* FIXME: probably do not have to be in this interface, and can
be moved to a separate module anyway. *)
val star_flip (g:env) (p q r : slprop) : slprop_equiv g (p * (q * r)) (q * (p * r))
val slprop_list_equiv_flip (g:env) (p q : slprop) (ps : list slprop)
  : slprop_list_equiv g (p :: q :: ps) (q :: p :: ps)
val slprop_list_equiv_push_append (g:env) (p : slprop) (ps qs : list slprop)
  : slprop_list_equiv g (p :: ps @ qs) (ps @ (p :: qs))
val slprop_list_equiv_append_r (g:env) (ps qs rs : list slprop)
  (pf : slprop_list_equiv g qs rs)
  : slprop_list_equiv g (ps @ qs) (ps @ rs)
val subst_append (ss : PS.ss_t) (ps qs : list slprop)
  : Lemma (ensures ss $$ ps @ qs == (ss $$ ps) @ (ss $$ qs))
val subst_append_equiv (g:env) (ss : PS.ss_t) (ps qs : list slprop)
  : slprop_list_equiv g (ss $$ ps @ qs) ((ss $$ ps) @ (ss $$ qs))
val subst_list_as_slprop (ss : PS.ss_t) (ps : list slprop)
  : Lemma (ensures list_as_slprop (ss $$ ps) == ss.(list_as_slprop ps))
val subst_star (ss : PS.ss_t) (p q : slprop)
  : Lemma (ensures ss.(p * q) == ss.(p) * ss.(q))

(* Compose two match pass results. *)

val compose_mpr (g:env) (ss : PS.ss_t) (ctxt0 unsolved0 ctxt1 unsolved1 : list slprop)
  (mpr1 : match_pass_result g ss ctxt0 unsolved0)
  (mpr2 : match_pass_result g mpr1.ss' mpr1.ctxt1 mpr1.unsolved1)
  : match_pass_result g ss ctxt0 unsolved0

(* Just an alias: match_pass_result for a given prover state *)
type mpr_t (#preamble:_) (pst:prover_state preamble) =
  match_pass_result (push_env pst.pg pst.uvs) pst.ss pst.remaining_ctxt pst.unsolved

(* Apply a match pass result to the prover state. *)
val apply_mpr
  (#preamble:_) (pst:prover_state preamble)
  (mpr : mpr_t pst)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst })

(******************************************************************)
(******************************************************************)
(******************************************************************)

(* A matcher can raise this to signal a graceful failure. *)
exception NoMatch of string

(* Ambig (q, p1, p2): q (in goals) can be matched by p1 or p2 (in ctx). *)
exception Ambig of (slprop & slprop & slprop)

let match_success_t
  (#preamble:_) (pst : prover_state preamble)
  (p q : slprop) : Type =
  ss:PS.ss_t & slprop_equiv pst.pg p ss.(q)

(* The type of a 1-to-1 matcher. The pst is "read-only". If there's
no match, it should raise NoMatch. Other exceptions are not caught. *)
type matcher_t =
  (#preamble:_) ->
  (pst : prover_state preamble) ->
  (p : slprop) -> (q : slprop) ->
  T.Tac (match_success_t pst p q)

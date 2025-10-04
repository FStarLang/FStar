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

module Pulse.Checker.Prover.Match.Comb

open FStar.Tactics.V2
open FStar.List.Tot
open FStar.Ghost

open Pulse.Typing.Combinators
open Pulse.Syntax
open Pulse.Typing
open Pulse.PP
open Pulse.Show
open Pulse.VC

module RU = Pulse.RuntimeUtils
module PS = Pulse.Checker.Prover.Substs


(* Ambig (q, p1, p2): q (in goals) can be matched by p1 or p2 (in ctx).
This is internal to this module, which is in charge of calling the matchers
1 by 1 and detecting ambiguity. *)
exception Ambig of (slprop & slprop & slprop)

(* local aliases *)
let (>>>) #g #t0 #t1 #t2 = VE_Trans g t0 t1 t2
let (>>*) #g #t0 #t1 #t2 = slprop_list_equiv_trans g t0 t1 t2
let cong_r #g #t0 #t1 #t2 (d : slprop_equiv g t1 t2) : slprop_equiv g (t0 * t1) (t0 * t2) =
  VE_Ctxt _ _ _ _ _ (VE_Refl _ _) d
let cong_l #g #t0 #t1 #t2 (d : slprop_equiv g t1 t2) : slprop_equiv g (t1 * t0) (t2 * t0) =
  VE_Ctxt _ _ _ _ _ d (VE_Refl _ _)
let ve_refl_pf (#g:env) (p q : slprop) (s : squash (p == q)) : slprop_equiv g p q = VE_Refl g p

let wrap_matcher
  (label : string)
  (matcher : matcher_t)
  (#preamble:_) (pst : prover_state preamble)
  (p q : slprop)
  : T.Tac (match_res_t pst p q)
=
  if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
    info_doc pst.pg (Some <| range_of_env pst.pg) [
      text "Trying to match";
      prefix 2 1 (doc_of_string "p =") (pp p);
      prefix 2 1 (doc_of_string "q =") (pp pst.ss.(q));
      text <| "with matcher: " ^ label;
    ];
  let res = try matcher pst p q with | ENoMatch s -> NoMatch s | e -> raise e in
  if RU.debug_at_level (fstar_env pst.pg) "prover.match" then begin
    info_doc pst.pg (Some <| range_of_env pst.pg) [
      text "Result:" ^/^
        (match res with
         | NoMatch s -> text "No match: " ^/^ text s
         | Matched _ _ _ -> text "Matched (with some guard)")
    ]
  end;
  res

(* The type of a match of q from something in a context ps. *) noeq
type match_from_context_t
  (#preamble:_) (pst : prover_state preamble)
  (q : slprop)
  (ps : list slprop)
= {
    p          : slprop;
    rest       : list slprop;
    rest_ok    : slprop_list_equiv pst.pg ps (p::rest);
    ss'        : PS.ss_t;
    ss_extends : squash (ss' `ss_extends` pst.ss);
    proof      : guarded (slprop_equiv pst.pg p ss'.(q));
}

(* If we matched q from ps, we can match it from any extension of ps. *)
let frame_match_from_context 
  (#preamble:_) (pst : prover_state preamble)
  (q : slprop)
  (ps : list slprop)
  (mm : match_from_context_t pst q ps)
  (frame : list slprop)
  : match_from_context_t pst q (frame @ ps)
= {
    p          = mm.p;
    rest       = frame @ mm.rest;
    rest_ok    = slprop_list_equiv_append _ _ _ _ _ (VE_Refl _ _) mm.rest_ok >>>
                 VE_Sym _ _ _ (slprop_list_equiv_push_append _ _ _ _);
    ss'        = mm.ss';
    ss_extends = mm.ss_extends;
    proof      = mm.proof;
}

#push-options "--z3rlimit_factor 4"
(* The result of a match pass, trying to match all of ctxt to all of unsolved. *)
(* Returns all successful matches of q in ps. *)
let rec get_all_matches_aux
  (label : string)
  (matcher : matcher_t)
  (#preamble:_) (pst : prover_state preamble)
  (q : slprop)
  (ps0 ps : list slprop)
  : T.Tac (list (match_from_context_t pst q (List.rev ps0 @ ps)))
=
  match ps with
  | [] -> []
  | p::ps' ->
    let thisone : list (match_from_context_t pst q (List.rev ps0 @ ps)) =
      match wrap_matcher label matcher pst p pst.ss.(q) with
      | NoMatch s -> []
      | Matched ss_ext vc ff ->
        assume (Set.disjoint (PS.dom pst.ss) (PS.dom ss_ext));
        let ss' = PS.push_ss pst.ss ss_ext in
        assume (ss'.(q) == ss_ext.(pst.ss.(q))); (* this should be true since it's just composing substs? *)

        if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
          info_doc pst.pg (Some <| range_of_env pst.pg) [
            text ("Matched with " ^ label);
            prefix 2 1 (doc_of_string "p =") (pp p);
            prefix 2 1 (doc_of_string "q =") (pp pst.ss.(q));
            prefix 2 1 (doc_of_string "ss' =") (pp ss');
            prefix 2 1 (doc_of_string "ss'.(q) =") (pp ss'.(q));
          ];

        let ff : with_vc vc (slprop_equiv pst.pg p ss_ext.(pst.ss.(q))) = ff in
        let ff : with_vc vc (slprop_equiv pst.pg p ss'.(q)) = coerce_eq () ff in
        (* ^ FIXME: why is the coerce needed? *)

        let mm : match_from_context_t pst q ps = {
          p          = p;
          rest       = ps';
          rest_ok    = slprop_list_equiv_refl _ _;
          ss'        = ss';
          ss_extends = ();
          proof      = Guarded vc ff;
        }
        in
        let mm = frame_match_from_context pst q ps mm (List.rev ps0) in
        [mm]
    in
    let rest : list (match_from_context_t pst q (List.rev ps0 @ ps)) =
      assume (List.rev (p::ps0) @ ps' == List.rev ps0 @ (p::ps')); // boring
      get_all_matches_aux label matcher pst q (p::ps0) ps'
    in
    thisone @ rest
#pop-options 

let get_all_matches
  (label : string)
  (matcher : matcher_t)
  (#preamble:_) (pst : prover_state preamble)
  (q : slprop)
  (ps : list slprop)
  : T.Tac (list (match_from_context_t pst q ps))
= get_all_matches_aux label matcher pst q [] ps

let rec coallesce_equal_matches
  (#preamble:_) (#pst : prover_state preamble)
  (#q : slprop)
  (#ps : list slprop)
  (ms : list (match_from_context_t pst q ps))
  : list (match_from_context_t pst q ps)
=
  match ms with
  | [] -> []
  | m1::ms' ->
    let ms' = coallesce_equal_matches ms' in
    match ms' with
    | [] -> [m1]
    | m2::ms'' ->
      if FStar.Reflection.TermEq.term_eq m1.p m2.p then
        m1::ms''
      else
        m1::m2::ms''

(* Returns the slprop that was matched, the remaining context, the
   needed substitution and a **guarded** proof of the match. This basically
   turns the list returned by get_all_matches into a single match, failing
   if any ambiguity is detected.
   
   In the error case (Inl) it can add some messages for the user, for example
   explaning why ambiguity was detected.
*)
let match_f_1n
  (label : string)
  (matcher : matcher_t)
  (#preamble:_) (pst : prover_state preamble)
  (q : slprop)
  (ps : list slprop)
  : T.Tac (either (list document) (match_from_context_t pst q ps))
= let ms = get_all_matches label matcher pst q ps in
  let ms = coallesce_equal_matches ms in
  match ms with
  | [] -> Inl [] (* no matches *)
  | [m] ->
    if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
      info_doc pst.pg (Some <| range_of_env pst.pg) [
        text ("Successful unambiguous match pass with " ^ label);
        prefix 2 1 (doc_of_string "q =") (pp q);
        prefix 2 1 (doc_of_string "m.p =") (pp m.p);
        prefix 2 1 (doc_of_string "m.ss' =") (pp m.ss');
        prefix 2 1 (doc_of_string "m.ss'.(q) =") (pp m.ss'.(q));
      ];
    Inr m (* yay! *)
  | m1::m2::_ ->
    if pst.allow_ambiguous
    then (
      if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
        info_doc pst.pg (Some <| range_of_env pst.pg) [
          text ("Successful AMBIGUOUS Match pass with " ^ label);
          prefix 2 1 (doc_of_string "q =") (pp q);
          prefix 2 1 (doc_of_string "m.p =") (pp m1.p);
          prefix 2 1 (doc_of_string "m.ss' =") (pp m1.ss');
          prefix 2 1 (doc_of_string "m.ss'.(q) =") (pp m1.ss'.(q));
        ];
      Inr m1
    ) else
      Inl [
        text "Ambiguous match for resource:" ^^
          indent (pp q);
        text "It can be matched by both:" ^^
          indent (pp m1.p) ^^ hardline ^^
        text "and:" ^^
          indent (pp m2.p) ^^ hardline ^^
        text "in the context.";
      ]

let weaken_slprop_equiv_env
      (#g1 : env)
      (#g2 : env{g2 `env_extends` g1})
      (#p #q : slprop)
      (pf : slprop_equiv g1 p q) : slprop_equiv g2 p q = magic()

(* Tries to match all of ctxt to all of unsolved, and returns the mpr *)
let rec match_f_nn
  (label : string)
  (matcher_f : matcher_t)
  (#preamble:_) (pst : prover_state preamble)
  (ctxt:list slprop) (unsolved:list slprop)
  : T.Tac (match_pass_result (push_env pst.pg pst.uvs) pst.ss ctxt unsolved)
= match unsolved with
  | [] ->
    (* Done *)
    mpr_zero
  | q::qs ->
    (* Try to match the tail. We get back some possibly reduced ctxt. *)
    let mpr = match_f_nn label matcher_f pst ctxt qs in
    (* Now, try to match q, in the reduced context. *)
    let pst' = { pst with
      ss = mpr.ss';
      nts = None;
      k = coerce_eq (magic()) pst.k;
      solved_inv = magic();
    } in
    if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
      T.print ("Trying to match goal " ^ show q ^ " from context (" ^ label ^ ")");

    match match_f_1n label matcher_f pst' q mpr.ctxt1 with
    | Inl docs ->
      (* If that fails we're done, just adding q as unsolved. *)
      let mpr' = { mpr with
        unsolved_matched = mpr.unsolved_matched;
        unsolved1 = q::mpr.unsolved1;
        unsolved_ok =
          slprop_list_equiv_cons _ q q _ _ (VE_Refl _ _) mpr.unsolved_ok >>>
          slprop_list_equiv_push_append _ _ _ _;

        msgs = docs :: mpr.msgs;
      }
      in mpr'

    | Inr { p; rest; rest_ok; ss'; ss_extends; proof } ->
      (* conditionally matched, try to discharge *)

      match unguard proof with
      | Inl iss ->
        fail_doc_with_subissues pst.pg (Some <| range_of_env pst.pg) iss [
          text "Failed to discharge match guard for goal:" ^^
            indent (pp q) ^^ hardline ^^
          text "with resource from context:" ^^
            indent (pp p);
        ]

      | Inr pq ->
        (* Got another match, extend the mpr. FIXME: We could accumulate all guards
        instead of discharging here. *)
        let unsolved_ok : slprop_list_equiv (push_env pst.pg pst.uvs) qs (mpr.unsolved_matched @ mpr.unsolved1) =
          mpr.unsolved_ok
        in
        let ctxt_ok () : slprop_list_equiv (push_env pst.pg pst.uvs) ctxt ((p :: mpr.ctxt_matched) @ rest) =
          mpr.ctxt_ok >>>
          weaken_slprop_equiv_env (slprop_list_equiv_append_r _ _ _ _ rest_ok) >>>
          VE_Sym _ _ _ (slprop_list_equiv_push_append _ p mpr.ctxt_matched rest)
        in
        let unsolved_ok : slprop_list_equiv (push_env pst.pg pst.uvs) (q::qs) ((q :: mpr.unsolved_matched) @ mpr.unsolved1) =
          slprop_list_equiv_cons _ q q _ _ (VE_Refl _ _) unsolved_ok
        in
        let mpr1 : match_pass_result (push_env pst.pg pst.uvs) pst.ss ctxt unsolved = {
          ss' = ss';

          ctxt_matched = p :: mpr.ctxt_matched;
          ctxt1        = rest;
          ctxt_ok = ctxt_ok ();

          unsolved_matched = q :: mpr.unsolved_matched;
          unsolved1        = coerce_eq () mpr.unsolved1;
          unsolved_ok      = unsolved_ok;

          match_ok = (
            slprop_list_equiv_cons _ _ _ _ _ (weaken_slprop_equiv_env pq) mpr.match_ok >>*
            ve_refl_pf _ _ (admit())
          );

          msgs = mpr.msgs;
        }
        in
        mpr1

let match_with
  (label : string)
  (matcher : matcher_t)
  (#preamble:_) (pst:prover_state preamble)
  : T.Tac (list (list document) & pst':prover_state preamble { pst' `pst_extends` pst })
=
  let mpr : mpr_t pst = match_f_nn label matcher pst pst.remaining_ctxt pst.unsolved in
  mpr.msgs, apply_mpr pst mpr

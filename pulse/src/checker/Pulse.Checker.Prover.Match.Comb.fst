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

module RU = Pulse.RuntimeUtils
module PS = Pulse.Checker.Prover.Substs

(* local aliases *)
let (>>>) #g #t0 #t1 #t2 = VE_Trans g t0 t1 t2
let (>>*) #g #t0 #t1 #t2 = vprop_list_equiv_trans g t0 t1 t2
let cong_r #g #t0 #t1 #t2 (d : vprop_equiv g t1 t2) : vprop_equiv g (t0 * t1) (t0 * t2) =
  VE_Ctxt _ _ _ _ _ (VE_Refl _ _) d
let cong_l #g #t0 #t1 #t2 (d : vprop_equiv g t1 t2) : vprop_equiv g (t1 * t0) (t2 * t0) =
  VE_Ctxt _ _ _ _ _ d (VE_Refl _ _)
let ve_refl_pf (#g:env) (p q : vprop) (s : squash (p == q)) : vprop_equiv g p q = VE_Refl g p

let wrap_matcher
  (label : string)
  (matcher : matcher_t)
  (#preamble:_) (pst : prover_state preamble)
  (p q : vprop)
=
  if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
    T.print ("Trying matcher " ^ label);
  try
    Some (matcher pst p q)
  with
  | NoMatch s ->
    if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
      T.print ("NoMatch: " ^ s);
    None
  | e -> raise e

let rec match_f_1n
  (label : string)
  (matcher : matcher_t)
  (#preamble:_) (pst : prover_state preamble)
  (q : vprop)
  (ctxt0 : list vprop)
  (* Returns new shrunk ctxt, proving the equivalence. *)
  : T.Tac (option (
             p        : vprop &
             ctxt1    : list vprop &
             ctxt1_ok : vprop_list_equiv pst.pg ctxt0 (p::ctxt1) &
             ss'      : (ss' : PS.ss_t {ss' `ss_extends` pst.ss}) &
             pq_ok    : vprop_equiv pst.pg p ss'.(q)
    ))
= match ctxt0 with
  | [] -> None
  | p::ps ->
    if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
      info_doc pst.pg (Some <| range_of_env pst.pg) [
        text ("Trying to match");
        prefix 2 1 (doc_of_string "p =") (pp p);
        prefix 2 1 (doc_of_string "q =") (pp pst.ss.(q));
      ];
    match wrap_matcher label matcher pst p pst.ss.(q) with
    | Some (| ss_extension, pq |) -> (
      (* ambiguity check *)
      if not pst.allow_ambiguous then begin
        if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
          T.print "Checking for ambiguity";
        match match_f_1n label matcher pst q ps with
        | Some (| p', _, _, _, _ |) ->
          if not (FStar.Reflection.V2.TermEq.term_eq p p') then
            raise (Ambig (q, p, p'))
        | None -> ()
      end;
      assume (Set.disjoint (PS.dom pst.ss) (PS.dom ss_extension));
      let ss' = PS.push_ss pst.ss ss_extension in
      if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
        info_doc pst.pg (Some <| range_of_env pst.pg) [
          text ("Matched with " ^ label);
          prefix 2 1 (doc_of_string "p =") (pp p);
          prefix 2 1 (doc_of_string "q =") (pp pst.ss.(q));
          prefix 2 1 (doc_of_string "ss' =") (pp ss');
          prefix 2 1 (doc_of_string "ss'.(q) =") (pp ss'.(q));
        ];
      assume (ss'.(q) == ss_extension.(pst.ss.(q)));
      (* ^ should be trivial from the definition of ss' + some missing lemmas in Prover.Substs *)
      let pq' : vprop_equiv pst.pg p (ss'.(q)) =
        coerce_eq () pq (* weird that we need to coerce? *)
      in
      Some (| p, ps, vprop_list_equiv_refl _ _, ss', pq' |)
    )
    | None -> (
      match match_f_1n label matcher pst q ps with
      | None -> None
      | Some (| p', ctxt1, ctxt1_ok, ss', p'q |) ->
        Some (| p',
                p::ctxt1,
                vprop_list_equiv_cons _ _ _ _ _ (VE_Refl _ _) ctxt1_ok >>>
                  vprop_list_equiv_flip _ _ _ _,
                ss',
                p'q |)
    )

let weaken_vprop_equiv_env
      (#g1 : env)
      (#g2 : env{g2 `env_extends` g1})
      (#p #q : vprop)
      (pf : vprop_equiv g1 p q) : vprop_equiv g2 p q = magic()

let report_ambig (#a:Type) (g:env) (q p p' :  vprop) : T.Tac a =
  fail_doc_env true g (Some <| range_of_env g) [
    text "Ambiguous match for resource:" ^^
      indent (pp q);
    text "It can be matched by both:" ^^
      indent (pp p) ^^ hardline ^^
    text "and:" ^^
      indent (pp p') ^^ hardline ^^
    text "in the context.";
  ]

(* Tries to match all of ctxt to all of unsolved, and returns the mpr *)
let rec match_f_nn
  (label : string)
  (matcher_f : matcher_t)
  (#preamble:_) (pst : prover_state preamble)
  (ctxt:list vprop) (unsolved:list vprop)
  : T.Tac (match_pass_result (push_env pst.pg pst.uvs) pst.ss ctxt unsolved)
= match unsolved with
  | [] ->
    (* Done *)
    mpr_zero
  | q::qs ->
    (* Try to match the tail. We get back some possibly reduced ctxt. *)
    let mpr = match_f_nn label matcher_f pst ctxt qs in
    (* Now, try to match q, in the reduced context. *)
    admit();
    let pst' = { pst with ss = mpr.ss' } in
    if RU.debug_at_level (fstar_env pst.pg) "prover.match" then
      T.print ("Trying to match goal " ^ show q ^ " from context");
    match
      try
        match_f_1n label matcher_f pst' q mpr.ctxt1
      with
      | Ambig (q, p, p') ->
        if RU.debug_at_level (fstar_env pst.pg) "prover.match" then (
          T.print "Ambiguity detected... continuing to another goal";
          T.print ("q = " ^ show q);
          T.print ("p = " ^ show p);
          T.print ("p' = " ^ show p')
        );
        None
    with
    | None ->
      (* If that fails we're done, just adding q as unsolved. *)
      let mpr' = { mpr with
        unsolved_matched = mpr.unsolved_matched;
        unsolved1 = q::mpr.unsolved1;
        unsolved_ok =
          vprop_list_equiv_cons _ q q _ _ (VE_Refl _ _) mpr.unsolved_ok >>>
          vprop_list_equiv_push_append _ _ _ _;
      }
      in mpr'

    | Some (| p, ctxt1, ctxt1_ok, ss', pq |) ->
      (* Got another match, extend the mpr. *)
      let mpr1 : match_pass_result (push_env pst.pg pst.uvs) pst.ss ctxt unsolved = {
        ss' = ss';

        ctxt_matched = p :: mpr.ctxt_matched;
        ctxt1        = ctxt1;
        ctxt_ok      = mpr.ctxt_ok >>>
                       weaken_vprop_equiv_env (vprop_list_equiv_append_r _ _ _ _ ctxt1_ok) >>>
                       VE_Sym _ _ _ (vprop_list_equiv_push_append _ p mpr.ctxt_matched ctxt1);

        unsolved_matched = q :: mpr.unsolved_matched;
        unsolved1        = mpr.unsolved1;
        unsolved_ok      = vprop_list_equiv_cons _ q q _ _ (VE_Refl _ _) mpr.unsolved_ok;
        
        match_ok = (
          // assume (list_as_vprop (ss'.(q) :: (mpr.ss' $$ mpr.unsolved_matched)) ==
          //         list_as_vprop (ss' $$ q :: mpr.unsolved_matched));
          vprop_list_equiv_cons _ _ _ _ _ (weaken_vprop_equiv_env pq) mpr.match_ok >>*
          ve_refl_pf _ _ (admit())
        );
      }
      in
      mpr1

(* Do a pass over all unsolved goals to see if any can be matched syntactically. *)
let match_with
  (label : string)
  (matcher : matcher_t)
  (#preamble:_) (pst:prover_state preamble)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst })
  = admit();
    // try
      let mpr : mpr_t pst = match_f_nn label matcher pst (List.rev pst.remaining_ctxt) (List.rev pst.unsolved) in
      apply_mpr pst mpr
    // with
    // | Ambig (q, p, p') ->
    //   report_ambig pst.pg q p p'
    // | e -> raise e

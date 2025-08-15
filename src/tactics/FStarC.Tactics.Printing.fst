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
module FStarC.Tactics.Printing

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Ident
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Tactics.Types
open FStarC.Class.Show
open FStarC.Pprint
open FStarC.Class.PP

module Range   = FStarC.Range
module Options = FStarC.Options
module Print   = FStarC.Syntax.Print
module SS      = FStarC.Syntax.Subst
module S       = FStarC.Syntax.Syntax
module Env     = FStarC.TypeChecker.Env
module PO      = FStarC.TypeChecker.Primops

let dbg_Imp = Debug.get_toggle "Imp"

let term_to_doc (e:Env.env) (t:term) : document =
    group <| Print.term_to_doc' e.dsenv t

let term_to_string (e:Env.env) (t:term) : string =
    Print.term_to_string' e.dsenv t

let unshadow (bs : binders) (t : term) : binders & term =
    (* string name of a bv *)
    let sset bv s = S.gen_bv s (Some (range_of_id bv.ppname)) bv.sort in
    let fresh_until b f =
        let rec aux i =
            let t = b ^ "'" ^ show i in
            if f t then t else aux (i+1)
        in
        if f b then b else aux 0
    in
    let rec go seen subst bs bs' t =
        match bs with
        | [] -> List.rev bs', SS.subst subst t
        | b::bs -> begin
            let b = match SS.subst_binders subst [b] with
                    | [b] -> b
                    | _ -> failwith "impossible: unshadow subst_binders"
            in
            let (bv0, q) = b.binder_bv, b.binder_qual in
            let nbs = fresh_until (show bv0.ppname) (fun s -> not (List.mem s seen)) in
            let bv = sset bv0 nbs in
            let b = S.mk_binder_with_attrs bv q b.binder_positivity b.binder_attrs in
            go (nbs::seen) (subst @ [NT (bv0, S.bv_to_name bv)]) bs (b :: bs') t
            end
    in
    go [] [] bs [] t

let maybe_rename_binders (ps : proofstate) (bs : binders) (t : term) : binders & term =
 let rename_binders subst bs =
   bs |> List.map (function b ->
     let x = b.binder_bv in
     let y = SS.subst subst (S.bv_to_name x) in
     match (SS.compress y).n with
     | Tm_name y ->
       // We don't want to change the type
       { b with binder_bv = { b.binder_bv with sort = SS.subst subst x.sort } }
     | _ -> failwith "Not a renaming")
 in
 if Options.tactic_raw_binders()
 then bs, t
 else (
   let subst = PO.psc_subst ps.psc in
   let bs = rename_binders subst bs in
   let t = SS.subst subst t in
   bs, t
 )

let goal_to_doc (kind : string) (maybe_num : option (int & int)) (ps:proofstate) (g:goal) : document =
  let w =
    if Options.print_implicits ()
    then term_to_doc (goal_env g) (goal_witness g)
    else match check_goal_solved' g with
         | None -> doc_of_string "_"
         | Some t -> term_to_doc (goal_env g) (goal_witness g) (* shouldn't really happen that we print a solved goal *)
  in
  let num =
    match maybe_num with
    | None -> empty
    | Some (i, n) -> pp i ^^ slash ^^ pp n
  in
  let maybe_label = if g.label = "" then empty else break_ 1 ^^ parens (doc_of_string g.label) in
  let goal_binders, goal_ty = g.goal_ctx_uvar.ctx_uvar_binders, goal_type g in
  let goal_binders, goal_ty = maybe_rename_binders ps goal_binders goal_ty in
  let goal_binders, goal_ty = unshadow goal_binders goal_ty in
  let pp_binder (b:binder) : document =
    group <| hang 2 <| parens (group (pp b.binder_bv ^/^ colon) ^/^ pp b.binder_bv.sort)
  in
  hang 2 <| group (doc_of_string kind ^/^ num) ^^ maybe_label ^/^
            separate_map (comma ^^ break_ 1) pp_binder goal_binders
            ^/^ group (doc_of_string "|-" ^/^ w ^/^ colon ^/^ term_to_doc (goal_env g) goal_ty)

let goal_to_string (kind : string) (maybe_num : option (int & int)) (ps:proofstate) (g:goal) : string =
  Pprint.render (goal_to_doc kind maybe_num ps g) ^ "\n"

(* This is really just for reporting crashes. *)
let goal_to_string_verbose (g:goal) : string =
  Pprint.render (pp g.goal_ctx_uvar.ctx_uvar_head) ^ "\n"

(* Note: we use def ranges. In tactics we keep the position in there, while the
 * use range is the original position of the assertion / synth / splice. *)
let ps_to_doc (msg, ps) : document =
  let p_imp imp = pp imp.imp_uvar.ctx_uvar_head in
  let n_active = List.length ps.goals in
  let n_smt    = List.length ps.smt_goals in
  let n = n_active + n_smt in
  doc_of_string (Format.fmt2 "State dump @ depth %s (%s):" (show ps.depth) msg) ^^ hardline ^^
  group (if ps.entry_range <> Range.dummyRange
   then doc_of_string "Location: " ^^ pp ps.entry_range ^^ hardline // is this def range?
   else empty) ^^
  group (if !dbg_Imp
   then doc_of_string "Imps: " ^^ (separate_map comma p_imp ps.all_implicits) ^^ hardline
   else empty) ^^
  separate hardline (
    (List.mapi (fun i g -> goal_to_doc "Goal"     (Some (1 + i, n))            ps g) ps.goals) @
    (List.mapi (fun i g -> goal_to_doc "SMT Goal" (Some (1 + n_active + i, n)) ps g) ps.smt_goals)
  )

let ps_to_string (msg, ps) =
  Pprint.render (ps_to_doc (msg, ps)) ^ "\n"

let goal_to_json g =
    let open FStarC.Json in
    let g_binders = g.goal_ctx_uvar.ctx_uvar_binders in
    let g_type = goal_type g in
    let g_binders, g_type = unshadow g_binders g_type in
    let j_binders = Print.binders_to_json (Env.dsenv (goal_env g)) g_binders in
    JsonAssoc [("hyps", j_binders);
               ("goal", JsonAssoc [("witness", JsonStr (term_to_string (goal_env g) (goal_witness g)));
                                   ("type", JsonStr (term_to_string (goal_env g) g_type));
                                   ("label", JsonStr g.label)
                                  ])]

let ps_to_json (msg, ps) =
    let open FStarC.Json in
    JsonAssoc ([("label", JsonStr msg);
                ("depth", JsonInt ps.depth);
                ("urgency", JsonInt ps.urgency);
                ("goals", JsonList (List.map goal_to_json ps.goals));
                ("smt-goals", JsonList (List.map goal_to_json ps.smt_goals))] @
                (if ps.entry_range <> Range.dummyRange
                 then [("location", Range.json_of_def_range (Range.refind_range ps.entry_range))]
                 else []))

let do_dump_proofstate ps msg =
    if not (Options.silent ()) || Options.interactive () then
        Options.with_saved_options (fun () ->
            Options.set_option "print_effect_args" (Options.Bool true);
            Format.print_generic "proof-state" ps_to_string ps_to_json (msg, ps);
            Format.flush_stdout () (* in case this is going to stdout, flush it immediately *)
        )

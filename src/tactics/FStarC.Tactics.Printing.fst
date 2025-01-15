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

open FStar open FStarC
open FStarC
open FStarC.Util
open FStarC.Effect
open FStarC.List
open FStarC.Ident
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Tactics.Types
open FStarC.Class.Show

module BU      = FStarC.Util
module Range   = FStarC.Range
module Options = FStarC.Options
module Print   = FStarC.Syntax.Print
module SS      = FStarC.Syntax.Subst
module S       = FStarC.Syntax.Syntax
module Env     = FStarC.TypeChecker.Env
module U       = FStarC.Syntax.Util
module Cfg     = FStarC.TypeChecker.Cfg
module PO      = FStarC.TypeChecker.Primops

let dbg_Imp = Debug.get_toggle "Imp"

let term_to_string (e:Env.env) (t:term) : string =
    Print.term_to_string' e.dsenv t

let goal_to_string_verbose (g:goal) : string =
    BU.format2 "%s%s\n"
        (show g.goal_ctx_uvar)
        (match check_goal_solved' g with
         | None -> ""
         | Some t -> BU.format1 "\tGOAL ALREADY SOLVED!: %s" (term_to_string (goal_env g) t))

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

let goal_to_string (kind : string) (maybe_num : option (int & int)) (ps:proofstate) (g:goal) : string =
    let w =
        if Options.print_implicits ()
        then term_to_string (goal_env g) (goal_witness g)
        else match check_goal_solved' g with
             | None -> "_"
             | Some t -> term_to_string (goal_env g) (goal_witness g) (* shouldn't really happen that we print a solved goal *)
    in
    let num = match maybe_num with
              | None -> ""
              | Some (i, n) -> BU.format2 " %s/%s" (show i) (show n)
    in
    let maybe_label =
        match g.label with
        | "" -> ""
        | l -> " (" ^ l ^ ")"
    in
    let goal_binders, goal_ty =
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
      let goal_binders = g.goal_ctx_uvar.ctx_uvar_binders in
      let goal_ty = goal_type g in
      if Options.tactic_raw_binders()
      then goal_binders, goal_ty
      else (
        let subst = PO.psc_subst ps.psc in
        let binders = rename_binders subst goal_binders in
        let ty = SS.subst subst goal_ty in
        binders, ty
      )
    in
    let goal_binders, goal_ty = unshadow goal_binders goal_ty in
    let actual_goal =
        if ps.tac_verb_dbg
        then goal_to_string_verbose g
        else BU.format3 "%s |- %s : %s\n" (String.concat ", " (map Print.binder_to_string_with_type goal_binders))
                                          w
                                          (term_to_string (goal_env g) goal_ty)
    in
    BU.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal

(* Note: we use def ranges. In tactics we keep the position in there, while the
 * use range is the original position of the assertion / synth / splice. *)
let ps_to_string (msg, ps) =
    let p_imp imp = show imp.imp_uvar.ctx_uvar_head in
    let n_active = List.length ps.goals in
    let n_smt    = List.length ps.smt_goals in
    let n = n_active + n_smt in
    String.concat ""
              ([BU.format2 "State dump @ depth %s (%s):\n" (show ps.depth) msg;
                (if ps.entry_range <> Range.dummyRange
                 then BU.format1 "Location: %s\n" (Range.string_of_def_range ps.entry_range)
                 else "");
                (if !dbg_Imp
                 then BU.format1 "Imps: %s\n" (FStarC.Common.string_of_list p_imp ps.all_implicits)
                 else "")]
                 @ (List.mapi (fun i g -> goal_to_string "Goal"     (Some (1 + i, n))            ps g) ps.goals)
                 @ (List.mapi (fun i g -> goal_to_string "SMT Goal" (Some (1 + n_active + i, n)) ps g) ps.smt_goals))

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
                 then [("location", Range.json_of_def_range ps.entry_range)]
                 else []))

let do_dump_proofstate ps msg =
    if not (Options.silent ()) || Options.interactive () then
        Options.with_saved_options (fun () ->
            Options.set_option "print_effect_args" (Options.Bool true);
            print_generic "proof-state" ps_to_string ps_to_json (msg, ps);
            BU.flush_stdout () (* in case this is going to stdout, flush it immediately *)
        )

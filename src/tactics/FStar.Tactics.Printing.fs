#light "off"
module FStar.Tactics.Printing

open FStar
open FStar.Util
open FStar.All
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Tactics.Types

module BU      = FStar.Util
module Range   = FStar.Range
module Options = FStar.Options
module Print   = FStar.Syntax.Print
module SS      = FStar.Syntax.Subst
module S       = FStar.Syntax.Syntax
module Env     = FStar.TypeChecker.Env

let term_to_string (e:Env.env) (t:term) : string =
    Print.term_to_string' e.dsenv t

let goal_to_string_verbose (g:goal) : string =
    BU.format2 "%s%s\n"
        (Print.ctx_uvar_to_string g.goal_ctx_uvar)
        (match check_goal_solved' g with
         | None -> ""
         | Some t -> BU.format1 "\tGOAL ALREADY SOLVED!: %s" (term_to_string (goal_env g) t))

let unshadow (bs : binders) (t : term) : binders * term =
    (* string name of a bv *)
    let s b = (string_of_id b.ppname) in
    let sset bv s = S.gen_bv s (Some (range_of_id bv.ppname)) bv.sort in
    let fresh_until b f =
        let rec aux i =
            let t = b ^ "'" ^ string_of_int i in
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
            let (bv0, q) = b in
            let nbs = fresh_until (s bv0) (fun s -> not (List.mem s seen)) in
            let bv = sset bv0 nbs in
            let b = (bv, q) in
            go (nbs::seen) (subst @ [NT (bv0, S.bv_to_name bv)]) bs (b :: bs') t
            end
    in
    go [] [] bs [] t

let goal_to_string (kind : string) (maybe_num : option<(int * int)>) (ps:proofstate) (g:goal) : string =
    let w =
        if Options.print_implicits ()
        then term_to_string (goal_env g) (goal_witness g)
        else match check_goal_solved' g with
             | None -> "_"
             | Some t -> term_to_string (goal_env g) (goal_witness g) (* shouldn't really happen that we print a solved goal *)
    in
    let num = match maybe_num with
              | None -> ""
              | Some (i, n) -> BU.format2 " %s/%s" (string_of_int i) (string_of_int n)
    in
    let maybe_label =
        match g.label with
        | "" -> ""
        | l -> " (" ^ l ^ ")"
    in
    let goal_binders = g.goal_ctx_uvar.ctx_uvar_binders in
    let goal_ty = g.goal_ctx_uvar.ctx_uvar_typ in
    let goal_binders, goal_ty = unshadow goal_binders goal_ty in
    let actual_goal =
        if ps.tac_verb_dbg
        then goal_to_string_verbose g
        else BU.format3 "%s |- %s : %s\n" (Print.binders_to_string ", " goal_binders)
                                          w
                                          (term_to_string (goal_env g) goal_ty)
    in
    BU.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal

(* Note: we use def ranges. In tactics we keep the position in there, while the
 * use range is the original position of the assertion / synth / splice. *)
let ps_to_string (msg, ps) =
    let p_imp imp =
        Print.uvar_to_string imp.imp_uvar.ctx_uvar_head
    in
    let n_active = List.length ps.goals in
    let n_smt    = List.length ps.smt_goals in
    let n = n_active + n_smt in
    String.concat ""
              ([BU.format2 "State dump @ depth %s (%s):\n" (string_of_int ps.depth) msg;
                (if ps.entry_range <> Range.dummyRange
                 then BU.format1 "Location: %s\n" (Range.string_of_def_range ps.entry_range)
                 else "");
                (if Env.debug ps.main_context (Options.Other "Imp")
                 then BU.format1 "Imps: %s\n" (FStar.Common.string_of_list p_imp ps.all_implicits)
                 else "")]
                 @ (List.mapi (fun i g -> goal_to_string "Goal"     (Some (1 + i, n))            ps g) ps.goals)
                 @ (List.mapi (fun i g -> goal_to_string "SMT Goal" (Some (1 + n_active + i, n)) ps g) ps.smt_goals))

let goal_to_json g =
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
    JsonAssoc ([("label", JsonStr msg);
                ("depth", JsonInt ps.depth);
                ("urgency", JsonInt ps.urgency);
                ("goals", JsonList (List.map goal_to_json ps.goals));
                ("smt-goals", JsonList (List.map goal_to_json ps.smt_goals))] @
                (if ps.entry_range <> Range.dummyRange
                 then [("location", Range.json_of_def_range ps.entry_range)]
                 else []))

let do_dump_proofstate ps msg =
    if not (Options.silent ()) then
        Options.with_saved_options (fun () ->
            Options.set_option "print_effect_args" (Options.Bool true);
            print_generic "proof-state" ps_to_string ps_to_json (msg, ps);
            BU.flush_stdout () (* in case this is going to stdout, flush it immediately *)
        )


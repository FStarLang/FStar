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
#light "off"

module FStar.SMTEncoding.ErrorReporting
open FStar
open FStar.BaseTypes
open FStar.Util
open FStar.SMTEncoding.Term
open FStar.SMTEncoding.Util
open FStar.SMTEncoding
open FStar.Range
module BU = FStar.Util

exception Not_a_wp_implication of string
type label = error_label
type labels = error_labels
let sort_labels (l:(list<(error_label * bool)>)) = List.sortWith (fun ((_, _, r1), _) ((_, _, r2), _) -> Range.compare r1 r2) l
let remove_dups (l:labels) = BU.remove_dups (fun (_, m1, r1) (_, m2, r2) -> r1=r2 && m1=m2) l
type msg = string * Range.range
type ranges = list<(option<string> * Range.range)>

//decorate a term with an error label
let fresh_label : string -> Range.range -> term -> label * term =
    let ctr = BU.mk_ref 0 in
    fun message range t ->
        let l = incr ctr; format1 "label_%s" (string_of_int !ctr) in
        let lvar = l, Bool_sort in
        let label = (lvar, message, range) in
        let lterm = mkFreeV lvar in
        let lt = Term.mkOr(lterm, t) range in
        label, lt

(*
   label_goals query : term * labels
      traverses the query, finding sub-formulas that are goals to be proven,
      and labels each such sub-goal with a distinct label variable

      Returns the labeled query and the label terms that were added
*)
let label_goals use_env_msg  //when present, provides an alternate error message,
                                  //usually "could not check implicit argument",
                                  //        "could not prove post-condition"
                                  //or something like that
                (r:Range.range)            //the source range in which this query was asked
                q            //the query
               : labels      //the labels themselves
               * term        //the query, decorated with labels
               =
    let rec is_a_post_condition post_name_opt tm =
        match post_name_opt, tm.tm with
        | None, _ -> false
        | Some nm, FreeV (nm', _) ->
          nm=nm'
        | _, App (Var "Valid", [tm])
        | _, App (Var "ApplyTT", tm::_) ->
          is_a_post_condition post_name_opt tm
        | _ ->
          false
    in
    let conjuncts t =
        match t.tm with
        | App(And, cs) -> cs
        | _ -> [t]
    in
    let is_guard_free tm =
      match tm.tm with
      | Quant(Forall, [[{tm=App(Var "Prims.guard_free", [p])}]], iopt, _, {tm=App(Iff, [l;r])}) ->
        true
      | _ -> false
    in
    let is_a_named_continuation lhs = conjuncts lhs |> BU.for_some is_guard_free in
    let flag, msg_prefix = match use_env_msg with
        | None -> false, ""
        | Some f -> true, f() in
    let fresh_label msg ropt rng t =
        let msg = if flag
                  then "Failed to verify implicit argument: " ^ msg
                  else msg in
        let rng = match ropt with
                  | None -> rng
                  | Some r -> {r with def_range=rng.def_range}
        in
        fresh_label msg rng t
    in
    let rec aux (default_msg:string) //the error message text to generate at a label
                (ropt:option<Range.range>) //an optional position, if there was an enclosing Labeled node
                (post_name_opt:option<string>) //the name of the current post-condition variable --- it is left uninstrumented
                (labels:list<label>) //the labels accumulated so far
                (q:term) //the term being instrumented
     =  match q.tm with
        | BoundV _
        | Integer _ ->
          labels, q

        | LblPos _ -> failwith "Impossible" //these get added after errorReporting instrumentation only

        | Labeled(arg, "could not prove post-condition", _) ->
//          printfn "GOT A LABELED WP IMPLICATION";
          let fallback msg =
//            printfn "FALLING BACK: %s" msg;
            aux default_msg ropt post_name_opt labels arg in
          begin try
              begin match arg.tm with
                | Quant(Forall, pats, iopt, post::sorts, {tm=App(Imp, [lhs;rhs]); rng=rng}) ->
                  let post_name = "^^post_condition_"^ (BU.string_of_int <| Syntax.Syntax.next_id ()) in
                  let names = (post_name, post)
                              ::List.mapi (fun i s -> ("^^" ^ string_of_int i, s)) sorts in
                  let instantiation = List.map mkFreeV names in
                  let lhs, rhs = Term.inst instantiation lhs, Term.inst instantiation rhs in

                  let labels, lhs = match lhs.tm with
                    | App(And, clauses_lhs) ->
                      let req, ens = BU.prefix clauses_lhs in
                      begin match ens.tm with
                        | Quant(Forall, pats_ens, iopt_ens, sorts_ens, {tm=App(Imp, [ensures_conjuncts; post]); rng=rng_ens})
                                when is_a_post_condition (Some post_name) post ->
                          let labels, ensures_conjuncts = aux "could not prove post-condition" None (Some post_name) labels ensures_conjuncts in
                          let pats_ens =
                            match pats_ens with
                            | []
                            | [[]] -> [[post]]  //make the post-condition formula the pattern, if there isn't one already (usually there isn't)
                            | _ -> pats_ens in
                          let ens = Term.mk (Quant(Forall, pats_ens, iopt_ens, sorts_ens,
                                                       Term.mk (App(Imp, [ensures_conjuncts; post])) rng_ens)) ens.rng in
                          let lhs = Term.mk (App(And, req@[ens])) lhs.rng in
                          labels, Term.abstr names lhs
                        | _ -> raise (Not_a_wp_implication ("Ensures clause doesn't match post name:  "
                                                            ^ post_name
                                                            ^ "  ... "
                                                            ^ Term.print_smt_term ens))
                      end
                    | _ -> raise (Not_a_wp_implication ("LHS not a conjunct: " ^ (Term.print_smt_term lhs))) in

                  let labels, rhs =
                    let labels, rhs = aux default_msg None (Some post_name) labels rhs in
                    labels, Term.abstr names rhs in

                  let body = Term.mkImp(lhs, rhs) rng in
                  labels, Term.mk (Quant(Forall, pats, iopt, post::sorts, body)) q.rng


                | _ -> //not in the form produced by an application of M_stronger
                  fallback ("arg not a quant: " ^ (Term.print_smt_term arg))
              end
          with Not_a_wp_implication msg -> fallback msg
          end

        | Labeled(arg, reason, r) ->
          aux reason (Some r) post_name_opt labels arg

        | Quant(Forall, [], None, [post], {tm=App(Imp, [lhs;rhs]); rng=rng})
            when is_a_named_continuation lhs ->
//          printfn "Got a named continuation";
          let post_name = "^^post_condition_"^ (BU.string_of_int <| Syntax.Syntax.next_id ()) in
          let names = (post_name, post) in
          let instantiation = [mkFreeV names] in
          let lhs, rhs = Term.inst instantiation lhs, Term.inst instantiation rhs in

          let labels, lhs_conjs =
                BU.fold_map (fun labels tm ->
                    match tm.tm with
                    | Quant(Forall, [[{tm=App(Var "Prims.guard_free", [p])}]], iopt, sorts, {tm=App(Iff, [l;r])}) ->
                        let labels, r = aux default_msg None post_name_opt labels r in
                        labels, mk (Quant(Forall, [[p]], Some 0, sorts, norng mk (App(Iff, [l;r])))) q.rng
                    | _ -> labels, tm)
                labels (conjuncts lhs) in

          let labels, rhs = aux default_msg None (Some post_name) labels rhs in
          let body = Term.mkImp(Term.mk_and_l lhs_conjs lhs.rng, rhs) rng |> Term.abstr [names] in
          let q = Term.mk (Quant(Forall, [], None, [post], body)) q.rng in
          labels, q

        | App(Imp, [lhs;rhs]) ->
          let labels, rhs = aux default_msg ropt post_name_opt labels rhs in
          labels, mkImp(lhs, rhs)

        | App(And, conjuncts) ->
          let labels, conjuncts = BU.fold_map (aux default_msg ropt post_name_opt) labels conjuncts in
          labels, Term.mk_and_l conjuncts q.rng

        | App(ITE, [hd; q1; q2]) ->
          let labels, q1 = aux default_msg ropt post_name_opt labels q1 in
          let labels, q2 = aux default_msg ropt post_name_opt labels q2 in
          labels, Term.mkITE (hd, q1, q2) q.rng

        | Quant(Exists, _, _, _, _)
        | App(Iff, _)
        | App(Or, _) -> //non-atomic, but can't case split
          let lab, q = fresh_label default_msg ropt q.rng q in
          lab::labels, q

        | App (Var _, _) when is_a_post_condition post_name_opt q ->
          //applications of the post-condition variable are never labeled
          //only specific conjuncts of an ensures clause are labeled
          labels, q

        | FreeV _
        | App(TrueOp, _)
        | App(FalseOp, _)
        | App(Not, _)
        | App(Eq, _)
        | App(LT, _)
        | App(LTE, _)
        | App(GT, _)
        | App(GTE, _)
        | App(Var _, _) -> //atomic goals
          let lab, q = fresh_label default_msg ropt q.rng q in
          lab::labels, q

        | App(Add, _)
        | App(Sub, _)
        | App(Div, _)
        | App(Mul, _)
        | App(Minus, _)
        | App(Mod, _) ->
          failwith "Impossible: non-propositional term"

        | App(ITE, _)
        | App(Imp, _) ->
          failwith "Impossible: arity mismatch"

        | Quant(Forall, pats, iopt, sorts, body) ->
          let labels, body = aux default_msg ropt post_name_opt labels body in
          labels, Term.mk (Quant(Forall, pats, iopt, sorts, body)) q.rng
    in
    aux "assertion failed" None None [] q


(*
   detail_errors all_labels potential_errors askZ3

      -- Searching through the list of errors labels to exhaustively list
         only those that are definitely not provable given the current
         solver parameters.

      -- potential_errors are the labels in the initial counterexample model
 *)
let detail_errors env
                 (all_labels:labels)
                 (askZ3:decls_t -> (either<Z3.unsat_core, (error_labels*Z3.error_kind)> * int))
    : error_labels =

    let print_banner () =
        BU.print3_error
            "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (Range.string_of_range (TypeChecker.Env.get_range env))
                (BU.string_of_int 5)
                (BU.string_of_int (List.length all_labels))
    in

    let print_result ((_, msg, r), success) =
        if success
        then BU.print1_error "OK: proof obligation at %s was proven\n" (Range.string_of_range r)
        else FStar.Errors.report r msg
    in

    let elim labs = //assumes that all the labs are true, effectively removing them from the query
        (labs |> List.map (fun (l, _, _) ->
                 Term.Assume(mkEq(mkFreeV l, mkTrue), Some "Disabling label", Some ("disable_label_"^fst l)))) in

    //check all active labels linearly and classify as eliminated/error
    let rec linear_check eliminated errors active =
        match active with
            | [] ->
              let results =
                List.map (fun x -> x, true) eliminated
                @ List.map (fun x -> x, false) errors in
              sort_labels results

            | hd::tl ->
              let result, _ = askZ3 (elim <| (eliminated @ errors @ tl)) in //hd is the only thing to prove
              if BU.is_left result //hd is provable
              then linear_check (hd::eliminated) errors tl
              else linear_check eliminated (hd::errors) tl in

    print_banner ();
    Options.set_option "z3rlimit" (Options.Int 5);
    let res = linear_check [] [] all_labels in
    res |> List.iter print_result;
    []
//    let dummy, _, _ = all_labels |> List.hd in
//    [(dummy, "Detailed errors provided", TypeChecker.Env.get_range env)]


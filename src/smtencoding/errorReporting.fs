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

exception Not_a_wp_implication
type label = error_label
type labels = error_labels
let sort_labels (l:(list<(error_label * bool)>)) = List.sortWith (fun ((_, _, r1), _) ((_, _, r2), _) -> Range.compare r1 r2) l
let remove_dups (l:labels) = Util.remove_dups (fun (_, m1, r1) (_, m2, r2) -> r1=r2 && m1=m2) l
type msg = string * Range.range
type ranges = list<(option<string> * Range.range)>

//decorate a term with an error label
let fresh_label : string -> Range.range -> term -> label * term =
    let ctr = ref 0 in 
    fun message range t -> 
        let l = incr ctr; format1 "label_%s" (string_of_int !ctr) in
        let lvar = l, Bool_sort in
        let label = (lvar, message, range) in
        let lterm = mkFreeV lvar in
        let lt = mkOr(lterm, t) in
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
                r            //the source range in which this query was asked
                q            //the query
               : labels      //the labels themselves
               * term        //the query, decorated with labels
               = 
    let is_a_post_condition tm = 
        match tm.tm with
        | App (Var "Valid", 
               [{tm=App(Var "ApplyTT", {tm=FreeV ("^^post_condition", _)}::_)}]) ->
          true
        | _ -> 
          false
    in 
    let flag, msg_prefix = match use_env_msg with 
        | None -> false, ""
        | Some f -> true, f() in
    let fresh_label msg ropt rng t = 
        let msg = if flag 
                  then "Failed to verify implicit argument: " ^ msg
                  else msg in 
        let rng = match ropt with
                  | None -> rng
                  | Some r -> r in
        fresh_label msg rng t 
    in
    let rec aux default_msg ropt labels q = 
        match q.tm with
        | BoundV _ 
        | Integer _ ->
          labels, q

        | Labeled(arg, "could not prove post-condition", _) ->
          let fallback () = aux default_msg ropt labels arg in 
          begin try 
              begin match arg.tm with 
                | Quant(Forall, pats, iopt, post::sorts, {tm=App(Imp, [lhs;rhs]); rng=rng}) -> 
                  let names = ("^^post_condition", post)
                              ::List.mapi (fun i s -> ("^^" ^ string_of_int i, s)) sorts in
                  let instantiation = List.map mkFreeV names in
                  let lhs, rhs = Term.inst instantiation lhs, Term.inst instantiation rhs in

                  let labels, lhs = match lhs.tm with 
                    | App(And, clauses_lhs) ->
                      let req, ens = Util.prefix clauses_lhs in
                      begin match ens.tm with 
                        | Quant(Forall, pats_ens, iopt_ens, sorts_ens, {tm=App(Imp, [ensures_conjuncts; post]); rng=rng_ens}) 
                                when is_a_post_condition post -> 
                          let labels, ensures_conjuncts = aux "could not prove post-condition" None labels ensures_conjuncts in 
                          let ens = Term.mk (Quant(Forall, pats_ens, iopt_ens, sorts_ens, 
                                                       Term.mk (App(Imp, [ensures_conjuncts; post])) rng_ens)) ens.rng in
                          let lhs = Term.mk (App(And, req@[ens])) lhs.rng in
                          labels, Term.abstr names lhs
                        | _ -> raise Not_a_wp_implication
                      end
                    | _ -> raise Not_a_wp_implication in
              
                  let labels, rhs = 
                    let labels, rhs = aux default_msg None labels rhs in
                    labels, Term.abstr names rhs in

                  let body = Term.mkImp(lhs, rhs) rng in
                  labels, Term.mk (Quant(Forall, pats, iopt, post::sorts, body)) q.rng
        

                | _ -> //not in the form produced by an application of M_stronger
                  fallback ()
              end
          with Not_a_wp_implication -> fallback()
          end

        | Labeled(arg, reason, r) ->
          aux reason (Some r) labels arg
//          lab::labels, arg

        | App(Imp, [lhs;rhs]) -> 
          let conjuncts t = match t.tm with 
            | App(And, cs) -> cs
            | _ -> [t]
          in
          let named_continuation_opt, other_lhs_conjuncts = 
              conjuncts lhs |> List.partition (fun tm -> 
                match tm.tm with 
                | Quant(Forall, [[{tm=App(Var "Prims.guard_free", [p])}]], iopt, sorts, {tm=App(Iff, [l;r])}) ->
                    true
                | _ -> false) 
          in
          begin match named_continuation_opt with 
                | _::_::_ -> failwith "More than one named continuation; impossible"

                | [] -> //the easy case, no continuation sharing
                  let labels, rhs = aux default_msg ropt labels rhs in
                  labels, mkImp(lhs, rhs)

                | [q] -> 
                  match q.tm with 
                  | Quant(Forall, [[{tm=App(Var "Prims.guard_free", [p])}]], iopt, sorts, {tm=App(Iff, [l;r])}) ->
                    let labels, r = aux default_msg None labels r in
                    let q = mk (Quant(Forall, [[p]], Some 0, sorts, norng mk (App(Iff, [l;r])))) q.rng in
                    let lhs = Term.mk_and_l (q::other_lhs_conjuncts) lhs.rng in
                    let rhs_p, rhs_rest = 
                        let hash_of_p = Term.hash_of_term p in
                        conjuncts rhs |> List.partition (fun t -> Term.hash_of_term t = hash_of_p) in
                    let labels, rhs_rest = aux default_msg None labels (Term.mk_and_l rhs_rest rhs.rng) in
                    let rhs = Term.mk_and_l (rhs_rest::rhs_p) rhs.rng in
                    labels, mkImp(lhs, rhs) 
                  | _ -> failwith "Impossible"
          end

        | App(And, conjuncts) ->
          let labels, conjuncts = Util.fold_map (aux default_msg ropt) labels conjuncts in
          labels, Term.mk_and_l conjuncts q.rng

        | App(ITE, [hd; q1; q2]) -> 
          let labels, q1 = aux default_msg ropt labels q1 in
          let labels, q2 = aux default_msg ropt labels q2 in
          labels, Term.mkITE (hd, q1, q2) q.rng

        | Quant(Exists, _, _, _, _)
        | App(Iff, _)
        | App(Or, _) -> //non-atomic, but can't case split 
          let lab, t = fresh_label default_msg ropt q.rng q in
          lab::labels, q

        | App (Var _, _) when is_a_post_condition q ->
          //applications of the post-condition variable are never labeled
          //only specific conjuncts of an ensures clause are labeled
          labels, q 

        | FreeV _ 
        | App(True, _)
        | App(False, _)
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
          let labels, body = aux default_msg ropt labels body in
          labels, Term.mk (Quant(Forall, pats, iopt, sorts, body)) q.rng
    in
    aux "assertion failed" None [] q


(* 
   detail_errors all_labels potential_errors askZ3
    
      -- Searching through the list of errors labels to exhaustively list 
         only those that are definitely not provable given the current 
         solver parameters.

      -- potential_errors are the labels in the initial counterexample model
 *)
let detail_errors env 
                 (all_labels:labels) 
                 (askZ3:decls_t -> (either<Z3.unsat_core, (error_labels*bool)> * int)) 
    : error_labels =

    let print_banner () = 
        Util.print3_error
            "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" 
                (Range.string_of_range (TypeChecker.Env.get_range env))
                (Util.string_of_int 5)
                (Util.string_of_int (List.length all_labels))
    in

    let print_result ((_, msg, r), success) =
        if success
        then Util.print1_error "OK: proof obligation at %s was proven\n" (Range.string_of_range r)
        else TypeChecker.Errors.report r msg
    in

    let elim labs = //assumes that all the labs are true, effectively removing them from the query
        (labs |> List.map (fun (l, _, _) -> 
                 Term.Assume(mkEq(mkFreeV l, mkTrue), Some "Disabling label", Some ("disable_label_"^fst l)))) in
    let print_labs tag l = l |> List.iter (fun (l, _, _) -> Util.print2 "%s : %s; " tag (fst l)) in

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
              if Util.is_left result //hd is provable
              then linear_check (hd::eliminated) errors tl
              else linear_check eliminated (hd::errors) tl in

    print_banner ();
    Options.set_option "z3timeout" (Options.Int 5);
    let res = linear_check [] [] all_labels in
    res |> List.iter print_result;
    let dummy, _, _ = all_labels |> List.hd in
    [(dummy, "Detailed errors provided", TypeChecker.Env.get_range env)]


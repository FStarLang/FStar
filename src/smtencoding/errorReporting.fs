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

type label = error_label
type labels = error_labels
let sort_labels (l:labels) = List.sortWith (fun (_, _, r1) (_, _, r2) -> Range.compare r1 r2) l
let remove_dups (l:labels) = Util.remove_dups (fun (_, m1, r1) (_, m2, r2) -> r1=r2 && m1=m2) l
type msg = string * Range.range
type ranges = list<(option<string> * Range.range)>

//decorate a term with an error label
let fresh_label : option<string> -> Range.range -> term -> label * term =
    let ctr = ref 0 in 
    fun msg range t -> 
        let l = incr ctr; format1 "label_%s" (string_of_int !ctr) in
        let lvar = l, Bool_sort in
        let message = match msg with 
            | Some m -> m
            | None -> "assertion failed" in
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
let label_goals use_env_msg  //when present, provides an alternate error message, usually "could not check implicit argument", or something like that
                r            //the source range in which this query was asked
                q            //the query
               : labels      //the labels themselves
               * term        //the query, decorated with labels
               = 
    let flag, msg_prefix = match use_env_msg with 
        | None -> false, ""
        | Some f -> true, f() in
    let fresh_label msg rng t = 
        let msg = if flag 
                  then match msg with 
                       | None -> Some "Failed to verify implicit argument"
                       | Some msg -> Some ("Failed to verify implicit argument: " ^ msg)
                   else msg in 
        fresh_label msg rng t 
    in
    let rec aux labels q = match q.tm with
        | BoundV _ 
        | Integer _ ->
          labels, q

        | Labeled(arg, "could not prove post-condition", _) -> 
          aux labels arg

        | Labeled(arg, reason, r) ->
          let lab, arg = fresh_label (Some reason) r arg in
          lab::labels, arg

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
                  let labels, rhs = aux labels rhs in
                  labels, mkImp(lhs, rhs)

                | [q] -> 
                  match q.tm with 
                  | Quant(Forall, [[{tm=App(Var "Prims.guard_free", [p])}]], iopt, sorts, {tm=App(Iff, [l;r])}) ->
                    let labels, r = aux labels r in
                    let q = mk (Quant(Forall, [[p]], Some 0, sorts, norng mk (App(Iff, [l;r])))) q.rng in
                    let lhs = Term.mk_and_l (q::other_lhs_conjuncts) lhs.rng in
                    let rhs_p, rhs_rest = 
                        let hash_of_p = Term.hash_of_term p in
                        conjuncts rhs |> List.partition (fun t -> Term.hash_of_term t = hash_of_p) in
                    let labels, rhs_rest = aux labels (Term.mk_and_l rhs_rest rhs.rng) in
                    let rhs = Term.mk_and_l (rhs_rest::rhs_p) rhs.rng in
                    labels, mkImp(lhs, rhs) 
                  | _ -> failwith "Impossible"
          end

        | App(And, conjuncts) ->
          let labels, conjuncts = Util.fold_map aux labels conjuncts in
          labels, Term.mk_and_l conjuncts q.rng

        | App(ITE, [hd; q1; q2]) -> 
          let labels, q1 = aux labels q1 in
          let labels, q2 = aux labels q2 in
          labels, Term.mkITE (hd, q1, q2) q.rng

        | Quant(Exists, _, _, _, _)
        | App(Iff, _)
        | App(Or, _) -> //non-atomic, but can't case split 
          let lab, t = fresh_label None q.rng q in
          lab::labels, q

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
          let lab, q = fresh_label None q.rng q in
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
          let labels, body = aux labels body in
          labels, Term.mk (Quant(Forall, pats, iopt, sorts, body)) q.rng
    in
    aux [] q


(* 
   detail_errors all_labels potential_errors askZ3
    
      -- Searching through the list of errors labels to exhaustively list 
         only those that are definitely not provable given the current 
         solver parameters.

      -- potential_errors are the labels in the initial counterexample model
 *)
let detail_errors (all_labels:labels) (potential_errors:labels) (askZ3:decls_t -> (either<Z3.unsat_core, (error_labels*bool)> * int)) : labels = 
    let ctr = Util.mk_ref 0 in
    let elim labs = //assumes that all the labs are true, effectively removing them from the query
        incr ctr;
        Term.Echo ("DETAILING ERRORS" ^ (string_of_int !ctr)) ::
        (labs |> List.map (fun (l, _, _) -> Term.Assume(mkEq(mkFreeV l, mkTrue), Some "Disabling label", Some ("disable_label_"^fst l)))) in
    let print_labs tag l = l |> List.iter (fun (l, _, _) -> Util.print2 "%s : %s; " tag (fst l)) in
    //l1 - l2: difference of label lists
    let minus l1 l2 = 
        l1 |> List.filter (fun ((x, _), _, _) ->
        not (l2 |> Util.for_some (fun ((y, _), _, _) -> x=y))) in

    //check all active labels linearly and classify as eliminated/error
    let rec linear_check eliminated errors active = 
        match active with 
            | [] -> let labs = errors |> sort_labels in
//                    print_labs "Localized errors: " labs;
                    labs
            | hd::tl -> 
              let result, _ = askZ3 (elim <| (eliminated @ errors @ tl)) in //hd is the only thing to prove
              if Util.is_left result //hd is provable
              then linear_check (hd::eliminated) errors tl
              else linear_check eliminated (hd::errors) tl in

    //bisect active labels and classify as eliminated/potential_error
    let rec bisect (eliminated:labels) (potential_errors:labels) (active:labels) =
        match active with
            | [] -> (eliminated, potential_errors)
            | _ -> 
              let pfx, sfx = match active with 
                | [_] -> active, []
                | _ -> Util.first_N (List.length active / 2) active in
              let result, _ = askZ3 (elim (eliminated @ potential_errors @ sfx)) in //focus on the goals in pfx, only
              begin match result with 
              | Inl _ -> //good; everything in the pfx is provable 
                bisect (eliminated@pfx) potential_errors sfx
              | Inr ([], timeout) ->
                //didn't prove it, but didn't get back a useful error report either
                //all of them may be errors
                bisect eliminated (potential_errors@pfx) sfx
              | Inr (pfx_subset, timeout) -> 
                //looks like something in pfx_subset may be to blame 
                let potential_errors = potential_errors@pfx_subset in
                let pfx_active = minus pfx pfx_subset in //but we can't yet eliminate pfx_active
                bisect eliminated potential_errors (pfx_active@sfx)  
              end
    in

    //bisect until fixed point; then do a linear scan on the potential errors
    let rec until_fixpoint eliminated potential_errors active = 
        let eliminated', potential_errors = bisect eliminated potential_errors active in
        if Util.physical_equality eliminated eliminated' //converged
        then linear_check eliminated [] potential_errors
        else until_fixpoint eliminated' [] potential_errors in

    let active = minus all_labels potential_errors in
    until_fixpoint [] potential_errors active
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
open FStar.Util
open FStar.SMTEncoding.Term


type label = (fv * string * Range.range)
type labels = list<label>

type msg = string * Range.range
type ranges = list<(option<string> * Range.range)>

let fresh_label : ranges -> term -> labels -> term * labels * ranges = 
    let ctr = ref 0 in 
    fun rs t labs -> 
        let l = incr ctr; format1 "label_%s" (string_of_int !ctr) in
        let lvar = l, Bool_sort in
        let message, range = match rs with 
            | [] -> t.hash, Range.dummyRange
            | (Some reason, r)::_ -> reason, r
            | (None, r)::_ -> "failed to prove a pre-condition", r in
        let label = (lvar, message, range) in
        let lterm = Term.mkFreeV lvar in
        let lt = Term.mkOr(lterm, t) in
        lt, label::labs, rs

(*
   label_goals query : term * labels
      traverses the query, finding sub-formulas that are goals to be proven, 
      and labels each such sub-goal with a distinct label variable

      Returns the labeled query and the label terms that were added
*)
let rec label_goals rs (q:term) labs : term * labels * ranges = 
    match q.tm with
        | BoundV _ 
        | Integer _ -> 
          q, labs, rs

        | Labeled(_, "push", r) -> 
//          Printf.printf "Pushing %s\n" (Range.string_of_range r);
          Term.mkTrue, labs, (None, r)::rs

        | Labeled(_, "pop", r) ->
//          Printf.printf "Popping %s\n" (Range.string_of_range r);
          Term.mkTrue, labs, List.tl rs

        | Labeled(arg, reason, r) -> 
//          Printf.printf "Pushing %s\n" (Range.string_of_range r);
          let tm, labs, rs = label_goals ((Some reason, r)::rs) arg labs in
//          Printf.printf "Popping %s\n" (Range.string_of_range r);
          tm, labs, List.tl rs

        | App(Imp, [lhs;rhs]) -> 
          let rhs, labs, rs = label_goals rs rhs labs in
          mk (App(Imp, [lhs; rhs])), labs, rs

        | App(And, conjuncts) -> 
          let rs, conjuncts, labs = List.fold_left (fun (rs, cs, labs) c -> 
            let c, labs, rs = label_goals rs c labs in
            rs, c::cs, labs) 
            (rs, [], labs)
            conjuncts in
          mk (App(And, List.rev conjuncts)), labs, rs
       
        | App(ITE, [hd; q1; q2]) -> 
          let q1, labs, _ = label_goals rs q1 labs in
          let q2, labs, _ = label_goals rs q2 labs in
          mk (App(ITE, [hd; q1; q2])), labs, rs

        | Quant(Exists, _, _, _, _)
        | App(Iff, _)
        | App(Or, _) -> //non-atomic, but can't case split 
          fresh_label rs q labs

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
          fresh_label rs q labs

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
          let body, labs, rs = label_goals rs body labs in 
          mk (Quant(Forall, pats, iopt, sorts, body)), labs, rs




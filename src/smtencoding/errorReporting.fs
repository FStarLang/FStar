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

let fresh_label : term -> labels -> term * labels = 
    let ctr = ref 0 in 
    fun t labs -> 
        let l = incr ctr; format1 "label_%s" (string_of_int !ctr) in
        let lvar = l, Bool_sort in
        let label = (lvar, t.hash, Range.dummyRange) in
        let lterm = Term.mkFreeV lvar in
        let lt = Term.mkOr(lterm, t) in
        lt, label::labs
        
(*
   label_goals query : term * labels
      traverses the query, finding sub-formulas that are goals to be proven, 
      and labels each such sub-goal with a distinct label variable

      Returns the labeled query and the label terms that were added
*)
let rec label_goals (q:term) labs : term * labels = 
    match q.tm with
        | BoundV _ 
        | Integer _ -> 
          q, labs

        | App(Imp, [lhs;rhs]) -> 
          let rhs, labs = label_goals rhs labs in
          mk (App(Imp, [lhs; rhs])), labs

        | App(And, conjuncts) -> 
          let conjuncts, labs = List.fold_right (fun c (cs, labs) -> 
            let c, labs = label_goals c labs in
            c::cs, labs) conjuncts ([], labs) in
          mk (App(And, conjuncts)), labs
       
        | App(ITE, [hd; q1; q2]) -> 
          let q1, labs = label_goals q1 labs in
          let q2, labs = label_goals q2 labs in
          mk (App(ITE, [hd; q1; q2])), labs

        | Quant(Exists, _, _, _, _)
        | App(Iff, _)
        | App(Or, _) -> //non-atomic, but can't case split 
          fresh_label q labs

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
          fresh_label q labs

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
          let body, labs = label_goals body labs in 
          mk (Quant(Forall, pats, iopt, sorts, body)), labs




(*
   Copyright 2008-2014 Aseem Rastogi and Microsoft Research

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

module FStar.SMTEncoding.SplitQueryCases

open FStar
open FStar.Util
open FStar.SMTEncoding.Term
open FStar.SMTEncoding.Util

(* return: if is ite all the way, ite for n cases, neg guards conj, rest of t *)
let rec get_next_n_ite (n:int) (t:term) (negs:term) (f:term -> term) :bool * term * term * term =
    if n <= 0 then true, f (mkTrue), negs, t
    else
        match t.tm with
            | App (ITE, g::t::e::_) ->
              get_next_n_ite (n - 1) e (mkAnd (negs, mkNot g)) (fun x -> f (mkITE (g, t, x)))

            | FreeV _ -> true, f (mkTrue), negs, t

            | _ -> false, mkFalse, mkFalse, mkFalse

(* return: if is ite all the way, list of queries, neg of all guards *)
let rec is_ite_all_the_way (n:int) (t:term) (negs:term) (l:list<term>) :bool * list<term> * term =
    if n <= 0 then raise Impos
    else
        match t.tm with
            | FreeV _ -> true, l, (mkAnd (negs, mkNot t))

            | _ ->
              let b, t, negs', rest = get_next_n_ite n t negs (fun x -> x) in
              if b then
                is_ite_all_the_way n rest negs' ((mkImp (negs, t))::l)
              else
                false, [], mkFalse

(* return: if can split, the query context, list of queries, neg of all guards *)
let rec parse_query_for_split_cases (n:int) (t:term) (f:term -> term) :bool * ((term -> term) * list<term> * term) = match t.tm with
    | Quant (Forall, l, opt, l', t) ->
      parse_query_for_split_cases n t (fun x -> f ((mkForall'' (l, opt, l', x))))

    | App (Imp, t1::t2::_) ->
      let r =
        match t2.tm with
            | Quant (Forall, _, _, _, _) ->
              parse_query_for_split_cases n t2 (fun x -> f (mkImp (t1, x)))

            | App (ITE, _) ->
              let b, l, negs = is_ite_all_the_way n t2 mkTrue [] in
              b, ((fun x -> f (mkImp (t1, x))), l, negs)

            | _ -> false, ((fun _ -> mkFalse), [], mkFalse)
      in
      r

    | App (ITE, _) ->
      let b, l, negs = is_ite_all_the_way n t mkTrue [] in
      b, (f, l, negs)

    | _ -> false, ((fun _ -> mkFalse), [], mkFalse)

let strip_not (t:term) :term = match t.tm with
    | App (Not, hd::_) -> hd
    | _                -> t

let rec check_split_cases (f:term -> term) (l:list<term>) (check:decl -> unit) :unit =
    List.iter (fun t -> check (Assume (mkNot (f t), None, None))) (List.rev l)

let check_exhaustiveness (f:term -> term) (negs:term) (check:decl -> unit) :unit =
    check (Assume (mkNot (f (mkNot negs)), None, None))

let can_handle_query (n:int) (q:decl) :bool * ((term -> term) * list<term> * term) =
    match q with
        | Assume(q', _, _) -> parse_query_for_split_cases n (strip_not q') (fun x -> x)
        | _ -> false, ((fun x -> x), [], mkFalse)

let handle_query ((f, l, negs):((term -> term) * list<term> * term)) (check:decl -> unit) :unit =
    let l = check_split_cases f l check in
    check_exhaustiveness f negs check

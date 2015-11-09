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
// (c) Microsoft Corporation. All rights reserved

module FStar.TypeChecker.Normalize
open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.TypeChecker.Env


(**********************************************************************************************
 * Reduction of types via the Krivine Abstract Machine (KN), with lazy
 * reduction and strong reduction (under binders), as described in:
 *
 * Strongly reducing variants of the Krivine abstract machine
 * Pierre Crégut
 * Higher-Order Symb Comput (2007) 20: 209–230
 **********************************************************************************************)

type step =
  | WHNF
  | Eta
  | EtaArgs
  | Delta
  | DeltaHard
  | Beta
  | DeltaComp
  | Simplify
  | SNComp
  | Unmeta
  | Unlabel
and steps = list<step>

type closure = 
  | Clos of env * term * memo<term> //memo for lazy evaluation
  | Dummy 
and env = list<closure>

type branches = list<(pat * option<term> * term)> 

type subst_t = list<subst_elt>

type stack_elt = 
 | Arg      of closure * aqual * Range.range
 | MemoLazy of memo<term>
 | Match    of env * branches
 | Abs      of env * binders * subst_t * Range.range

type stack = list<stack_elt>

let mk t r = mk t None r

let set_memo r t =
  match !r with 
    | Some _ -> failwith "Unexpected set_memo: thunk already evaluated"
    | None -> r := Some t

let rec norm : steps -> env -> stack -> term -> term = 
    fun steps env stack t -> 
        let t = compress t in 
        match t.n with 
          | Tm_delayed _ -> 
            failwith "Impossible"

          | Tm_name _ 
          | Tm_fvar _
          | Tm_uinst _
          | Tm_constant _
          | Tm_type _
          | Tm_uvar _ 
          | Tm_unknown _ ->
            rebuild steps env stack t

          | Tm_bvar x -> 
            let c = try List.nth env x.index
                    with _ -> 
                        failwith (Printf.sprintf "Failed to find %s\n" (Print.term_to_string t)) in
                begin match c with 
                    | Clos (env, t, r) ->
                          match !r with 
                            | Some t' -> norm steps env stack t'
                            | None -> norm steps env (MemoLazy r::stack) t
                end
            
          | Tm_abs(bs, body) -> 
            begin match stack with 
                | Match _::_ -> 
                  failwith "Ill-typed term: cannot pattern match an abstraction"

                | Arg(c, _, _)::stack -> 
                  let body = match bs with 
                    | [] -> failwith "Impossible"
                    | [_] -> body
                    | _::tl -> mk (Tm_abs(tl, body)) t.pos in
                  norm steps (c :: env) stack body 

                | MemoLazy r :: stack -> 
                  set_memo r t;
                  norm steps env stack t

                | Abs _::_
                | [] -> 
                  let body, closing = open_term bs body in 
                  let env' = bs |> List.fold_left (fun env _ -> Dummy::env) env in
                  norm steps env' (Abs(env, bs, closing, t.pos)::stack) body
            end

          | Tm_app(head, args) -> 
            let stack = stack |> List.fold_right (fun (a, aq) stack -> Arg (Clos(env, a, Util.mk_ref None),aq,t.pos)::stack) args in
            norm steps env stack head
                            
          | Tm_refine(x, f) -> //non tail-recursive; the alternative is to keep marks on the stack to rebuild the term ... but that's very heavy
            let t_x = norm steps env [] x.sort in 
            let f, closing = open_term [(x, None)] f in
            let f = norm steps env [] f in 
            let t = mk (Tm_refine({x with sort=t_x}, subst closing f)) t.pos in 
            rebuild steps env stack t

          | Tm_arrow(bs, c) -> 
            let c, closing = open_comp bs c in 
            let c = norm_comp steps env c in
            let c = subst_comp closing c in
            let t = mk (Tm_arrow(norm_binders steps env bs, c)) t.pos in
            rebuild steps env stack t
          
          | Tm_ascribed(t1, t2, l) -> 
            let t1 = norm steps env [] t1 in 
            let t2 = norm steps env [] t2 in
            rebuild steps env stack (mk (Tm_ascribed(t1, t2, l)) t.pos)

          | Tm_match(head, branches) -> failwith "NYI"

          | Tm_let(lbs, t) -> failwith "NYI"

          | Tm_meta (head, m) -> 
            let head = norm steps env [] head in
            let m = match m with 
                | Meta_pattern args -> 
                  let args = args |> List.map (List.map (fun (a, imp) -> norm steps env [] a, imp)) in 
                  Meta_pattern args 
                | _ -> m in
            let t = mk (Tm_meta(head, m)) t.pos in
            rebuild steps env stack t

and norm_comp : steps -> env -> comp -> comp = 
    fun steps env comp -> 
        match comp.n with 
            | Total t -> 
              {comp with n=Total (norm steps env [] t)}

            | Comp ct -> 
              let norm_args args = args |> List.map (fun (a, i) -> (norm steps env [] a, i)) in
              {comp with n=Comp {ct with result_typ=norm steps env [] ct.result_typ;
                                         effect_args=norm_args ct.effect_args}}
    
and norm_binder : steps -> env -> binder -> binder = 
    fun steps env (x, imp) -> {x with sort=norm steps env [] x.sort}, imp

and norm_binders : steps -> env -> binders -> binders = 
    fun steps env bs -> 
        let bs' = Subst.open_binders bs in
        let nbs', _ = List.fold_left (fun (nbs', env) b -> 
            let b = norm_binder steps env b in
            (b::nbs', Dummy::env) (* crossing a binder, so shift environment *)) 
            ([], env)
            bs' in
        Subst.close_binders (List.rev nbs') 

and rebuild : steps -> env -> stack -> term -> term = 
    fun steps env stack t ->
    (* Pre-condition: t is in strong normal form w.r.t env;
                      It has no free de Bruijn indices *)
        match stack with 
            | [] -> t

            | MemoLazy r::stack -> 
              set_memo r t;
              rebuild steps env stack t

            | Abs (env', bs, closing, r)::stack ->
              let t = subst closing t in 
              let bs = norm_binders steps env' bs in
              rebuild steps env stack (mk (Tm_abs(bs, t)) r)

            | Arg (Clos(env, tm, m), aq, r) :: stack ->
              let a = match !m with 
                | None -> norm steps env [MemoLazy m] tm
                | Some t -> t in 
              let t = mk (Tm_app(t, [(a,aq)])) r in 
              rebuild steps env stack t

            | Match(env, branches) :: stack -> 
              failwith "NYI"

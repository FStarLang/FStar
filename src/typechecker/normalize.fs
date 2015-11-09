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

let debug = ref false
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
  | Clos of env * term * memo<env * term> //memo for lazy evaluation
  | Dummy 
and env = list<closure>

let closure_to_string = function 
    | Clos (_, t, _) -> Print.term_to_string t
    | _ -> "dummy"

type cfg = {
    steps: steps;
    tcenv: Env.env;
    local_defs: list<(bv * env * term)>;
}

(* <Move> this out of here *)
let dummy = {
    init=(fun _ -> ());
    push=(fun _ -> ());
    pop=(fun _ -> ());
    mark=(fun _ -> ());
    reset_mark=(fun _ -> ());
    commit_mark=(fun _ -> ());
    encode_sig=(fun _ _ -> ());
    encode_modul=(fun _ _ -> ());
    solve=(fun _ _ -> ());
    is_trivial=(fun _ _ -> false);
    finish=(fun () -> ());
    refresh=(fun () -> ());
}
let empty_cfg = { 
    steps=[];
    tcenv=Env.initial_env dummy (lid_of_path ["nothing"] dummyRange);
    local_defs=[]
}
(* </Move> *)

type branches = list<(pat * option<term> * term)> 

type subst_t = list<subst_elt>

type stack_elt = 
 | Arg      of closure * aqual * Range.range
 | MemoLazy of memo<(env * term)>
 | Match    of env * branches * Range.range
 | Abs      of env * binders  * subst_t * Range.range

type stack = list<stack_elt>

let mk t r = match t with 
    | Tm_abs(bs, body) -> 
      begin match (compress body).n with 
        | Tm_abs(bs', t) -> mk (Tm_abs(bs@bs', t)) None r
        | _ -> mk t None r
      end
    | _ -> mk t None r

let set_memo r t =
  match !r with 
    | Some _ -> failwith "Unexpected set_memo: thunk already evaluated"
    | None -> r := Some t

let env_to_string env =
    List.map closure_to_string env |> String.concat "; "

let stack_elt_to_string = function 
    | Arg (c, _, _) -> closure_to_string c
    | MemoLazy _ -> "MemoLazy"
    | Abs (_, bs, _, _) -> Printf.sprintf "Abs %d" (List.length bs)
    | _ -> "Match"

let stack_to_string s = 
    List.map stack_elt_to_string s |> String.concat "; "

let log f = 
    if !debug
    then f()
    else ()

let is_empty = function
    | [] -> true
    | _ -> false

let lookup_local_def (x:bv) cfg = 
    Util.find_map cfg.local_defs (fun (y, env, tm) -> if Syntax.bv_eq x y then Some (env, tm) else None)

let rec norm : cfg -> env -> stack -> term -> term = 
    fun cfg env stack t -> 
        let t = compress t in
        log (fun () -> Printf.printf "Norm %s\n\t\tEnv=%s\n\t\tStack=%s\n" (Print.term_to_string t) (env_to_string env) (stack_to_string stack));
        match t.n with 
          | Tm_delayed _ -> 
            failwith "Impossible"

          | Tm_unknown _
          | Tm_uvar _ 
          | Tm_constant _
          | Tm_fvar(_, Some Data_ctor)
          | Tm_fvar(_, Some (Record_ctor _)) -> //these last three are just constructors; no delta steps can apply
            rebuild cfg env stack t
     
          | Tm_type u -> 
            let u = norm_universe cfg env u in
            rebuild cfg env stack (mk (Tm_type u) t.pos)
         
          | Tm_uinst _ -> failwith "NYI"
     
          | Tm_name x -> 
            begin match lookup_local_def x cfg with 
                | None -> rebuild cfg env stack t
                | Some (env, t) -> norm cfg env stack t
            end

          | Tm_fvar (f, _) -> 
            if List.contains DeltaHard cfg.steps
            || (List.contains Delta cfg.steps && not (is_empty stack)) //delta only if reduction is blocked
            then match Env.lookup_definition cfg.tcenv f.v with 
                    | None -> rebuild cfg env stack t
                    | Some t -> norm cfg env stack t 
            else rebuild cfg env stack t     

          | Tm_bvar x -> 
            let c = try List.nth env x.index
                    with _ -> 
                        failwith (Printf.sprintf "Failed to find %s\n" (Print.term_to_string t)) in
                begin match c with 
                    | Dummy -> failwith (Printf.sprintf "Bound variable was resolved to a dummy: %s\n" (Print.term_to_string t))
                    | Clos (env, t, r) -> //norm cfg env stack t
                          match !r with 
                            | Some (env, t') -> norm cfg env stack t'
                            | None -> norm cfg env (MemoLazy r::stack) t
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
                  log (fun () -> Printf.printf "\tShifted %s\n" (closure_to_string c));
                  norm cfg (c :: env) stack body 

                | MemoLazy r :: stack -> 
                  set_memo r (env, t); //TODO: fix! this doesn't always memoize the strong normal form
                  log (fun () -> Printf.printf "\tSet memo\n");
                  norm cfg env stack t

                | Abs _::_
                | [] -> 
                  let body, closing = open_term bs body in 
                  let env' = bs |> List.fold_left (fun env _ -> Dummy::env) env in
                  log (fun () -> Printf.printf "\tShifted %d dummies\n" (List.length bs));
                  norm cfg env' (Abs(env, bs, closing, t.pos)::stack) body
            end

          | Tm_app(head, args) -> 
            let stack = stack |> List.fold_right (fun (a, aq) stack -> Arg (Clos(env, a, Util.mk_ref None),aq,t.pos)::stack) args in
            log (fun () -> Printf.printf "\tPushed %d arguments\n" (List.length args));
            norm cfg env stack head
                            
          | Tm_refine(x, f) -> //non tail-recursive; the alternative is to keep marks on the stack to rebuild the term ... but that's very heavy
            let t_x = norm cfg env [] x.sort in 
            let f, closing = open_term [(x, None)] f in
            let f = norm cfg env [] f in 
            let t = mk (Tm_refine({x with sort=t_x}, subst closing f)) t.pos in 
            rebuild cfg env stack t

          | Tm_arrow(bs, c) -> 
            let c, closing = open_comp bs c in 
            let c = norm_comp cfg env c in
            let c = subst_comp closing c in
            let t = mk (Tm_arrow(norm_binders cfg env bs, c)) t.pos in
            rebuild cfg env stack t
          
          | Tm_ascribed(t1, t2, l) -> 
            let t1 = norm cfg env [] t1 in 
            let t2 = norm cfg env [] t2 in
            rebuild cfg env stack (mk (Tm_ascribed(t1, t2, l)) t.pos)

          | Tm_match(head, branches) -> 
            let stack = Match(env, branches, t.pos)::stack in 
            norm cfg env stack head

          | Tm_let((false, [lb]), body) ->
            let env = Clos(env, lb.lbdef, Util.mk_ref None)::env in 
            norm cfg env stack body

          | Tm_let((_, {lbname=Inr _}::_), _) -> //this is a top-level let binding; nothing to normalize
            rebuild cfg env stack t

          | Tm_let((_, lbs), body) -> 
            //let rec: The basic idea is to open the body with fresh names for the let bound functions; 
            //         Then, introduce definitions for those new names in cfg.local_defs
            //         Then reduce the body
            let local_defs, opening, _ = List.fold_right (fun lb (local_defs, opening, i) -> 
                match lb.lbname with 
                    | Inr _ -> failwith "Impossible" //this is a top-level let binding; excluded already
                    | Inl x -> 
                      let x = freshen_bv x in 
                      let opening = DB(i, bv_to_name x)::opening in
                      let local_defs = (x, env, lb.lbdef)::local_defs in
                      local_defs, opening, i + 1) lbs ([], [], 0) in
            let local_defs = List.map (fun (x, env, t) -> (x, env, subst opening t)) local_defs in 
            let body = subst opening body in 
            let cfg = {cfg with local_defs=local_defs@cfg.local_defs} in
            norm cfg env stack body

          | Tm_meta (head, m) -> 
            let head = norm cfg env [] head in
            let m = match m with 
                | Meta_pattern args -> 
                  let args = args |> List.map (List.map (fun (a, imp) -> norm cfg env [] a, imp)) in 
                  Meta_pattern args 
                | _ -> m in
            let t = mk (Tm_meta(head, m)) t.pos in
            rebuild cfg env stack t

and norm_comp : cfg -> env -> comp -> comp = 
    fun cfg env comp -> 
        match comp.n with 
            | Total t -> 
              {comp with n=Total (norm cfg env [] t)}

            | Comp ct -> 
              let norm_args args = args |> List.map (fun (a, i) -> (norm cfg env [] a, i)) in
              {comp with n=Comp {ct with result_typ=norm cfg env [] ct.result_typ;
                                         effect_args=norm_args ct.effect_args}}
    
and norm_binder : cfg -> env -> binder -> binder = 
    fun cfg env (x, imp) -> {x with sort=norm cfg env [] x.sort}, imp

and norm_binders : cfg -> env -> binders -> binders = 
    fun cfg env bs -> 
        let bs' = Subst.open_binders bs in
        let nbs', _ = List.fold_left (fun (nbs', env) b -> 
            let b = norm_binder cfg env b in
            (b::nbs', Dummy::env) (* crossing a binder, so shift environment *)) 
            ([], env)
            bs' in
        Subst.close_binders (List.rev nbs') 

and norm_universe cfg env u = failwith "NYI"

and rebuild : cfg -> env -> stack -> term -> term = 
    fun cfg env stack t ->
    (* Pre-condition: t is in strong normal form w.r.t env;
                      It has no free de Bruijn indices *)
        match stack with 
            | [] -> t

            | MemoLazy r::stack -> 
              set_memo r (env, t);
              rebuild cfg env stack t

            | Abs (env', bs, closing, r)::stack ->
              let t = subst closing t in 
              let bs = norm_binders cfg env' bs in
              rebuild cfg env stack (mk (Tm_abs(bs, t)) r)

            | Arg (Dummy, _, _)::_ -> failwith "Impossible"

            | Arg (Clos(env, tm, m), aq, r) :: stack ->
              let a = match !m with 
                | None -> norm cfg env [MemoLazy m] tm
                | Some (_, t) -> t in 
              let t = mk (Tm_app(t, [(a,aq)])) r in 
              rebuild cfg env stack t

            | Match(env, branches, r) :: stack -> 
              let rebuild () = rebuild cfg env stack (mk (Tm_match(t, branches)) r) in

              let guard_when_clause wopt b rest = 
                  match wopt with 
                   | None -> b
                   | Some w -> 
                     let then_branch = b in
                     let else_branch = mk (Tm_match(t, rest)) r in 
                     Util.if_then_else w then_branch else_branch in
                
              let rec matches_pat (t:term) (p:pat) :  option<list<term>> = 
                    let t = compress t in 
                    match p.v with 
                    | Pat_disj ps -> FStar.Util.find_map ps (matches_pat t)
                    | Pat_var _ -> Some [t]
                    | Pat_wild _
                    | Pat_dot_term _ -> Some []
                    | Pat_constant s -> 
                      begin match t.n with 
                        | Tm_constant s' when s=s' -> Some []
                        | _ -> None
                      end
                    | Pat_cons(fv, arg_pats) -> 
                      let head, args = Util.head_and_args t in 
                      match head.n with 
                        | Tm_fvar fv' when fv_eq fv fv' -> 
                          matches_args [] args arg_pats
                        | _ -> None

              and matches_args out (a:args) (p:list<(pat * bool)>) = match a, p with 
                | [], [] -> Some out
                | (t, _)::rest_a, (p, _)::rest_p -> 
                    begin match matches_pat t p with 
                    | None -> None
                    | Some x -> matches_args (out@x) rest_a rest_p 
                    end 
                | _ -> None in
            
              let rec matches t p = match p with 
                | [] -> rebuild ()
                | (p, wopt, b)::rest -> 
                   match matches_pat t p with
                    | None -> matches t rest 
                    | Some s ->
                      let env = List.fold_right (fun t env -> Clos([], t, Util.mk_ref (Some ([], t)))::env) s env in //the sub-terms should be fully normalized; so their environment is []
                      norm cfg env stack (guard_when_clause wopt b rest) in

              matches t branches

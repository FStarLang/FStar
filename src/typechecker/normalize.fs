(*
   Copyright 2008-2016 Nikhil Swamy and Microsoft Research

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
open FStar.TypeChecker
open FStar.TypeChecker.Env
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U  = FStar.Syntax.Util
module I  = FStar.Ident

(**********************************************************************************************
 * Reduction of types via the Krivine Abstract Machine (KN), with lazy
 * reduction and strong reduction (under binders), as described in:
 *
 * Strongly reducing variants of the Krivine abstract machine
 * Pierre Crégut
 * Higher-Order Symb Comput (2007) 20: 209–230
 **********************************************************************************************)

type step =
  | WHNF            //Only produce a weak head normal form
  | Inline
  | Unfold
  | Beta            //remove? Always do beta
  | Simplify        //Simplifies some basic log cfg ical tautolog cfg ies: not part of definitional equality!
  | EraseUniverses
  | AllowUnboundUniverses //we erase universes as we encode to SMT; so, sometimes when printing, it's ok to have some unbound universe variables
  //remove the rest?
  | DeltaComp       
  | SNComp
  | Eta             
  | EtaArgs         
  | Unmeta
  | Unlabel
and steps = list<step>


type closure = 
  | Clos of env * term * memo<(env * term)> //memo for lazy evaluation
  | Univ of universe                        //universe terms do not have free variables
  | Dummy                                   //Dummy is a placeholder for a binder when doing strong reduction
and env = list<closure>

let closure_to_string = function 
    | Clos (_, t, _) -> Print.term_to_string t
    | _ -> "dummy"

type cfg = {
    steps: steps;
    tcenv: Env.env;
    delta_level: Env.delta_level;
}

type branches = list<(pat * option<term> * term)> 

type subst_t = list<subst_elt>

type stack_elt = 
 | Arg      of closure * aqual * Range.range 
 | UnivArgs of list<universe> * Range.range
 | MemoLazy of memo<(env * term)>
 | Match    of env * branches * Range.range
 | Abs      of env * binders * env * option<lcomp> * Range.range
 | App      of term * aqual * Range.range
 | Meta     of S.metadata * Range.range

type stack = list<stack_elt>

// VALS_HACK_HERE

let mk t r = mk t None r
let set_memo r t =
  match !r with 
    | Some _ -> failwith "Unexpected set_memo: thunk already evaluated"
    | None -> r := Some t

let env_to_string env =
    List.map closure_to_string env |> String.concat "; "

let stack_elt_to_string = function 
    | Arg (c, _, _) -> closure_to_string c
    | MemoLazy _ -> "MemoLazy"
    | Abs (_, bs, _, _, _) -> Util.format1 "Abs %s" (string_of_int <| List.length bs)
    | _ -> "Match"

let stack_to_string s = 
    List.map stack_elt_to_string s |> String.concat "; "

let log cfg f = 
    if Env.debug cfg.tcenv (Options.Other "Norm")
    then f()
    else ()

let is_empty = function
    | [] -> true
    | _ -> false

let lookup_bvar env x = 
    try List.nth env x.index
    with _ -> failwith (Util.format1 "Failed to find %s\n" (Print.bv_to_string x))

(********************************************************************************************************************)
(* Normal form of a universe u is                                                                                   *)
(*  either u, where u <> U_max                                                                                      *)
(*  or     U_max [k;                        //constant                                                              *)
(*               S^n1 u1 ; ...; S^nm um;    //offsets of distinct names, in order of the names                      *)
(*               S^p1 ?v1; ...; S^pq ?vq]   //offsets of distinct unification variables, in order of the variables  *)
(*          where the size of the list is at least 2                                                                *)
(********************************************************************************************************************)
let norm_universe cfg env u =
    let norm_univs us = 
        let us = Util.sort_with U.compare_univs us in 
        (* us is in sorted order;                                                               *)
        (* so, for each sub-sequence in us with a common kernel, just retain the largest one    *)
        (* e.g., normalize [Z; S Z; S S Z; u1; S u1; u2; S u2; S S u2; ?v1; S ?v1; ?v2]         *)
        (*            to  [        S S Z;     S u1;           S S u2;      S ?v1; ?v2]          *)
        let _, u, out = 
            List.fold_left (fun (cur_kernel, cur_max, out) u -> 
                let k_u, n = U.univ_kernel u in 
                if U.eq_univs cur_kernel k_u //streak continues 
                then (cur_kernel, u, out)    //take u as the current max of the streak
                else (k_u, u, cur_max::out)) //streak ends; include cur_max in the output and start a new streak
            (U_zero, U_zero, []) us in
        List.rev (u::out) in

    (* normalize u by                                                  *)
    (*   1. flattening all max nodes                                   *)
    (*   2. pushing all S nodes under a single top-level max node      *)
    (*   3. sorting the terms in a max node, and partially evaluate it *)
    let rec aux u = 
        let u = Subst.compress_univ u in
        match u with
          | U_bvar x -> 
            begin 
                try match List.nth env x with 
                      | Univ u -> [u]
                      | _ -> failwith "Impossible: universe variable bound to a term"
                with _ -> if cfg.steps |> List.contains AllowUnboundUniverses
                          then [U_unknown]
                          else failwith "Universe variable not found"
            end
          | U_zero
          | U_unif _ 
          | U_name _ 
          | U_unknown -> [u]
          | U_max []  -> [U_zero]
          | U_max us ->  List.collect aux us |> norm_univs
          | U_succ u ->  List.map U_succ (aux u) in

    if cfg.steps |> List.contains EraseUniverses
    then U_unknown
    else match aux u with 
        | [] 
        | [U_zero] -> U_zero
        | [U_zero; u] -> u
        | U_zero::us -> U_max us
        | [u] -> u
        | us -> U_max us
           

(*******************************************************************)
(* closure_as_term env t --- t is a closure with environment env   *)
(* closure_as_term env t                                           *)
(*      is a closed term with all its free variables               *)
(*      subsituted with their closures in env (recursively closed) *)
(* This is used when computing WHNFs                               *)
(*******************************************************************)
let rec closure_as_term cfg env t =
    match env with
        | [] -> t
        | _ -> 
        let t = compress t in 
        match t.n with 
            | Tm_delayed _ -> 
              failwith "Impossible"

            | Tm_unknown
            | Tm_constant _
            | Tm_name _
            | Tm_fvar _ -> t

            | Tm_uvar(u, t') -> 
              mk (Tm_uvar(u, closure_as_term_delayed  cfg env t')) t.pos 

            | Tm_type u -> 
              mk (Tm_type (norm_universe cfg env u)) t.pos

            | Tm_uinst(t, us) -> (* head symbol must be an fvar *) 
              mk_Tm_uinst t (List.map (norm_universe cfg env) us)
         
            | Tm_bvar x -> 
              begin match lookup_bvar env x with
                    | Univ _ -> failwith "Impossible: term variable is bound to a universe"
                    | Dummy -> t
                    | Clos(env, t0, r) -> closure_as_term cfg env t0
              end

           | Tm_app(head, args) -> 
             let head = closure_as_term_delayed cfg env head in 
             let args = closures_as_args_delayed cfg env args in
             mk (Tm_app(head, args)) t.pos
        
           | Tm_abs(bs, body, lopt) -> 
             let bs, env = closures_as_binders_delayed cfg env bs in 
             let body = closure_as_term_delayed cfg env body in
             mk (Tm_abs(List.rev bs, body, close_lcomp_opt cfg env lopt)) t.pos

           | Tm_arrow(bs, c) -> 
             let bs, env = closures_as_binders_delayed cfg env bs in 
             let c = close_comp cfg env c in 
             mk (Tm_arrow(bs, c)) t.pos

           | Tm_refine(x, phi) -> 
             let x, env = closures_as_binders_delayed cfg env [mk_binder x] in 
             let phi = closure_as_term_delayed cfg env phi in 
             mk (Tm_refine(List.hd x |> fst, phi)) t.pos

           | Tm_ascribed(t1, t2, lopt) -> 
             mk (Tm_ascribed(closure_as_term_delayed cfg env t1, closure_as_term_delayed cfg env t2, lopt)) t.pos

           | Tm_meta(t', m) -> 
             mk (Tm_meta(closure_as_term_delayed cfg env t', m)) t.pos
       
           | Tm_match  _ -> failwith "NYI"
           | Tm_let _    -> failwith "NYI"
       
and closure_as_term_delayed cfg env t = 
    match env with 
        | [] -> t
        | _ -> mk_Tm_delayed (Inr (fun () -> closure_as_term cfg env t)) t.pos  
 
and closures_as_args_delayed cfg env args =
    match env with 
        | [] -> args
        | _ ->  List.map (fun (x, imp) -> closure_as_term_delayed cfg env x, imp) args 

and closures_as_binders_delayed cfg env bs = 
    let env, bs = bs |> List.fold_left (fun (env, out) (b, imp) -> 
            let b = {b with sort = closure_as_term_delayed cfg env b.sort} in
            let env = Dummy::env in
            env, ((b,imp)::out)) (env, []) in
    List.rev bs, env

and close_comp cfg env c = 
    match env with
        | [] -> c
        | _ -> 
        match c.n with 
            | Total t -> mk_Total (closure_as_term_delayed cfg env t)
            | GTotal t -> mk_GTotal (closure_as_term_delayed cfg env t)
            | Comp c -> 
              let rt = closure_as_term_delayed cfg env c.result_typ in
              let args = closures_as_args_delayed cfg env c.effect_args in 
              let flags = c.flags |> List.map (function 
                | DECREASES t -> DECREASES (closure_as_term_delayed cfg env t)
                | f -> f) in
              mk_Comp ({c with result_typ=rt;
                               effect_args=args;
                               flags=flags})  

and close_lcomp_opt cfg env = function 
    | None -> None
    | Some lc -> Some ({lc with res_typ=closure_as_term_delayed cfg env lc.res_typ;
                                comp=(fun () -> close_comp cfg env (lc.comp()))})

(*******************************************************************)
(* Simplification steps are not part of definitional equality      *)
(* simplifies True /\ t, t /\ True, t /\ False, False /\ t etc.    *)
(*******************************************************************)
let maybe_simplify steps tm =
    let w t = {t with pos=tm.pos} in
    let simp_t t = match t.n with
        | Tm_fvar (fv, _) when I.lid_equals fv.v Const.true_lid ->  Some true
        | Tm_fvar (fv, _) when I.lid_equals fv.v Const.false_lid -> Some false
        | _ -> None in
    let simplify arg = (simp_t (fst arg), arg) in
    if not <| List.contains Simplify steps
    then tm
    else match tm.n with
            | Tm_app({n=Tm_uinst({n=Tm_fvar(fv, _)}, _)}, args)
            | Tm_app({n=Tm_fvar(fv, _)}, args) -> 
              if I.lid_equals fv.v Const.and_lid
              then match args |> List.map simplify with
                     | [(Some true, _); (_, (arg, _))]
                     | [(_, (arg, _)); (Some true, _)] -> arg
                     | [(Some false, _); _]
                     | [_; (Some false, _)] -> w Util.t_false
                     | _ -> tm
              else if I.lid_equals fv.v Const.or_lid
              then match args |> List.map simplify with
                     | [(Some true, _); _]
                     | [_; (Some true, _)] -> w Util.t_true
                     | [(Some false, _); (_, (arg, _))]
                     | [(_, (arg, _)); (Some false, _)] -> arg
                     | _ -> tm
              else if I.lid_equals fv.v Const.imp_lid
              then match args |> List.map simplify with
                     | [_; (Some true, _)]
                     | [(Some false, _); _] -> w Util.t_true
                     | [(Some true, _); (_, (arg, _))] -> arg
                     | _ -> tm
              else if I.lid_equals fv.v Const.not_lid
              then match args |> List.map simplify with
                     | [(Some true, _)] ->  w Util.t_false
                     | [(Some false, _)] -> w Util.t_true
                     | _ -> tm
              else if  I.lid_equals fv.v Const.forall_lid
                    || I.lid_equals fv.v Const.exists_lid
              then match args with
                     | [(t, _)]
                     | [(_, Some Implicit); (t, _)] ->
                       begin match (SS.compress t).n with
                                | Tm_abs([_], body, _) ->
                                   (match simp_t body with
                                        | Some true ->  w Util.t_true
                                        | Some false -> w Util.t_false
                                        | _ -> tm)
                                | _ -> tm
                       end
                    | _ -> tm
              else tm
            | _ -> tm



(********************************************************************************************************************)
(* Main normalization function of the abstract machine                                                              *)
(********************************************************************************************************************)
let rec norm : cfg -> env -> stack -> term -> term = 
    fun cfg env stack t -> 
        let t = compress t in
        log cfg  (fun () -> Util.print2 ">>> %s\nNorm %s\n" (Print.tag_of_term t) (Print.term_to_string t));
        match t.n with 
          | Tm_delayed _ -> 
            failwith "Impossible"

          | Tm_unknown
          | Tm_uvar _ 
          | Tm_constant _
          | Tm_fvar(_, Some Data_ctor)
          | Tm_fvar(_, Some (Record_ctor _)) -> //these last three are just constructors; no delta steps can apply
            rebuild cfg env stack t
     
          | Tm_type u -> 
            let u = norm_universe cfg env u in
            rebuild cfg env stack (mk (Tm_type u) t.pos)
         
          | Tm_uinst(t', us) -> 
            if cfg.steps |> List.contains EraseUniverses
            then norm cfg env stack t'
            else let us = UnivArgs(List.map (norm_universe cfg env) us, t.pos) in
                 let stack = us::stack in
                 norm cfg env stack t'
     
          | Tm_name x -> 
            rebuild cfg env stack t
           
          | Tm_fvar (f, _) -> 
            if cfg.delta_level = NoDelta
            then rebuild cfg env stack t
            else begin match Env.lookup_definition cfg.delta_level cfg.tcenv f.v with 
                    | None -> rebuild cfg env stack t
                    | Some (us, t) -> 
                      let n = List.length us in 
                      if n > 0 
                      then match stack with //universe beta reduction
                             | UnivArgs(us', _)::stack -> 
                               let env = us' |> List.fold_left (fun env u -> Univ u::env) env in 
                               norm cfg env stack t 
                             | _ -> failwith (Util.format1 "Impossible: missing universe instantiation on %s" (Print.lid_to_string f.v))
                      else norm cfg env stack t             
                 end

          | Tm_bvar x -> 
            begin match lookup_bvar env x with 
                | Univ _ -> failwith "Impossible: term variable is bound to a universe"
                | Dummy -> failwith "Term variable not found"
                | Clos(env, t0, r) ->  
                   begin match !r with 
                        | Some (env, t') -> 
                            log cfg  (fun () -> Util.print2 "Lazy hit: %s cached to %s\n" (Print.term_to_string t) (Print.term_to_string t'));
                            begin match (compress t').n with
                                | Tm_abs _  ->  
                                    norm cfg env stack t'
                                | _ -> 
                                    rebuild cfg env stack t'
                            end
                        | None -> norm cfg env (MemoLazy r::stack) t0
                   end
            end
            
          | Tm_abs(bs, body, lopt) -> 
            begin match stack with 
                | Meta _ :: _ -> 
                  failwith "Labeled abstraction"

                | UnivArgs _::_ ->
                  failwith "Ill-typed term: universes cannot be applied to term abstraction"

               | Match _::_ -> 
                  failwith "Ill-typed term: cannot pattern match an abstraction"

                | Arg(c, _, _)::stack -> 
                  begin match c with 
                    | Univ _ -> //universe variables do not have explicit binders
                      norm cfg (c::env) stack t

                    | _ -> 
                      let body = match bs with 
                        | [] -> failwith "Impossible"
                        | [_] -> body
                        | _::tl -> mk (Tm_abs(tl, body, None)) t.pos in
                      log cfg  (fun () -> Util.print1 "\tShifted %s\n" (closure_to_string c));
                      norm cfg (c :: env) stack body 
                  end

                | MemoLazy r :: stack -> 
                  set_memo r (env, t); //We intentionally do not memoize the strng normal form; only the WHNF
                  log cfg  (fun () -> Util.print_string "\tSet memo\n");
                  norm cfg env stack t

                | App _ :: _ 
                | Abs _ :: _
                | [] -> 
                  if List.contains WHNF cfg.steps //don't descend beneath a lambda if we're just doing WHNF   
                  then rebuild cfg env stack (closure_as_term cfg env t) //But, if the environment is non-empty, we need to substitute within the term
                  else let bs, body = open_term bs body in 
                       let env' = bs |> List.fold_left (fun env _ -> Dummy::env) env in
                       log cfg  (fun () -> Util.print1 "\tShifted %s dummies\n" (string_of_int <| List.length bs));
                       norm cfg env' (Abs(env, bs, env', lopt, t.pos)::stack) body
            end

          | Tm_app(head, args) -> 
            let stack = stack |> List.fold_right (fun (a, aq) stack -> Arg (Clos(env, a, Util.mk_ref None),aq,t.pos)::stack) args in
            log cfg  (fun () -> Util.print1 "\tPushed %s arguments\n" (string_of_int <| List.length args));
            norm cfg env stack head
                            
          | Tm_refine(x, f) -> //non tail-recursive; the alternative is to keep marks on the stack to rebuild the term ... but that's very heavy
            if List.contains WHNF cfg.steps
            then rebuild cfg env stack (closure_as_term cfg env t)
            else let t_x = norm cfg env [] x.sort in 
                 let closing, f = open_term [(x, None)] f in
                 let f = norm cfg (Dummy::env) [] f in 
                 let t = mk (Tm_refine({x with sort=t_x}, close closing f)) t.pos in 
                 rebuild cfg env stack t 

          | Tm_arrow(bs, c) -> 
            if List.contains WHNF cfg.steps
            then rebuild cfg env stack (closure_as_term cfg env t)
            else let bs, c = open_comp bs c in 
                 let c = norm_comp cfg (bs |> List.fold_left (fun env _ -> Dummy::env) env) c in
                 let t = arrow (norm_binders cfg env bs) c in
                 rebuild cfg env stack t
          
          | Tm_ascribed(t1, t2, l) -> 
            begin match stack with 
                | Match _ :: _
                | Arg _ :: _ 
                | MemoLazy _ :: _ -> norm cfg env stack t1 //ascriptions should not block reduction                
                | _ -> 
                let t1 = norm cfg env [] t1 in 
                log cfg  (fun () -> Util.print_string "+++ Normalizing ascription \n");
                let t2 = norm cfg env [] t2 in
                rebuild cfg env stack (mk (Tm_ascribed(t1, t2, l)) t.pos)

                
            end

          | Tm_match(head, branches) -> 
            let stack = Match(env, branches, t.pos)::stack in 
            norm cfg env stack head

          | Tm_let((false, [lb]), body) ->
            let env = Clos(env, lb.lbdef, Util.mk_ref None)::env in 
            norm cfg env stack body

          | Tm_let((_, {lbname=Inr _}::_), _) -> //this is a top-level let binding; nothing to normalize
            rebuild cfg env stack t

          | Tm_let(lbs, body) -> 
            //let rec: The basic idea is to reduce the body in an environment that includes recursive bindings for the lbs
            //Consider reducing (let rec f x = f x in f 0) in initial environment env
            //We build two environments, rec_env and body_env and reduce (f 0) in body_env
            //rec_env = Clos(env, let rec f x = f x in f, memo)::env
            //body_env = Clos(rec_env, \x. f x, _)::env
            //i.e., in body, the bound variable is bound to definition, \x. f x
            //Within the definition \x.f x, f is bound to the recursive binding (let rec f x = f x in f), aka, fix f. \x. f x
            //Finally, we add one optimization for laziness by tying a knot in rec_env
            //i.e., we set memo := Some (rec_env, \x. f x)
            
            let rec_env, memos, _ = List.fold_right (fun lb (rec_env, memos, i) -> 
                    let f_i = Syntax.bv_to_tm ({left lb.lbname with index=i}) in
                    let fix_f_i = mk (Tm_let(lbs, f_i)) t.pos in 
                    let memo = Util.mk_ref None in 
                    let rec_env = Clos(env, fix_f_i, memo)::rec_env in
                    rec_env, memo::memos, i + 1) (snd lbs) (env, [], 0) in
            let _ = List.map2 (fun lb memo -> memo := Some (rec_env, lb.lbdef)) (snd lbs) memos in //tying the knot
            let body_env = List.fold_right (fun lb env -> Clos(rec_env, lb.lbdef, Util.mk_ref None)::env)
                               (snd lbs) env in
            norm cfg body_env stack body

          | Tm_meta (head, m) -> 
            begin match stack with 
                | _::_ ->
                  begin match m with 
                    | Meta_labeled(l, r, _) -> 
                      norm cfg env (Meta(m,r)::stack) head //meta doesn't block reduction, but we need to put the label back

                    | Meta_pattern args -> 
                      let args = norm_pattern_args cfg env args in
                      norm cfg env (Meta(Meta_pattern args, t.pos)::stack) head //meta doesn't block reduction, but we need to put the label back

                    | _ -> 
                      norm cfg env stack head //meta doesn't block reduction
                  end  
                | _ -> 
                let head = norm cfg env [] head in
                let m = match m with 
                    | Meta_pattern args -> 
                      Meta_pattern (norm_pattern_args cfg env args)
                    | _ -> m in
                let t = mk (Tm_meta(head, m)) t.pos in
                rebuild cfg env stack t
            end

and norm_pattern_args cfg env args = 
    args |> List.map (List.map (fun (a, imp) -> norm cfg env [] a, imp)) 
    
and norm_comp : cfg -> env -> comp -> comp = 
    fun cfg env comp -> 
        match comp.n with 
            | Total t -> 
              {comp with n=Total (norm cfg env [] t)}

            | GTotal t -> 
              {comp with n=GTotal (norm cfg env [] t)}

            | Comp ct -> 
              let norm_args args = args |> List.map (fun (a, i) -> (norm cfg env [] a, i)) in
              {comp with n=Comp ({ct with result_typ=norm cfg env [] ct.result_typ;
                                         effect_args=norm_args ct.effect_args})}
    
and norm_binder : cfg -> env -> binder -> binder = 
    fun cfg env (x, imp) -> {x with sort=norm cfg env [] x.sort}, imp

and norm_binders : cfg -> env -> binders -> binders = 
    fun cfg env bs -> 
        let nbs, _ = List.fold_left (fun (nbs', env) b -> 
            let b = norm_binder cfg env b in
            (b::nbs', Dummy::env) (* crossing a binder, so shift environment *)) 
            ([], env)
            bs in
        List.rev nbs

and rebuild : cfg -> env -> stack -> term -> term = 
    fun cfg env stack t ->
    (* Pre-condition: t is in either weak or strong normal form w.r.t env, depending on whether cfg.steps constains WHNF
                      In either case, it has no free de Bruijn indices *)
        match stack with 
            | [] -> t

            | Meta(m, r)::stack -> 
              let t = mk (Tm_meta(t, m)) r in
              rebuild cfg env stack t

            | MemoLazy r::stack -> 
              set_memo r (env, t);
              rebuild cfg env stack t

            | Abs (env', bs, env'', lopt, r)::stack ->
              let bs = norm_binders cfg env' bs in
              let lopt = close_lcomp_opt cfg env'' lopt in
              rebuild cfg env stack ({abs bs t lopt with pos=r})

            | Arg (Univ _,  _, _)::_
            | Arg (Dummy,  _, _)::_ -> failwith "Impossible"

            | UnivArgs(us, r)::stack -> 
              let t = mk_Tm_uinst t us in
              rebuild cfg env stack t

            | Arg (Clos(env, tm, m), aq, r) :: stack ->
              log cfg  (fun () -> Util.print1 "Rebuilding with arg %s\n" (Print.term_to_string tm));
              //this needs to be tail recursive for reducing large terms
              begin match !m with 
                | None -> 
                  if List.contains WHNF cfg.steps
                  then let arg = closure_as_term cfg env tm in 
                       let t = extend_app t (arg, aq) None r in 
                       rebuild cfg env stack t
                  else let stack = MemoLazy m::App(t, aq, r)::stack in 
                       norm cfg env stack tm

                | Some (_, a) -> 
                  let t = S.extend_app t (a,aq) None r in
                  rebuild cfg env stack t
              end

            | App(head, aq, r)::stack -> 
              let t = S.extend_app head (t,aq) None r in
              rebuild cfg env stack (maybe_simplify cfg.steps t)

            | Match(env, branches, r) :: stack -> 
              let norm_and_rebuild_match () =
                let whnf = List.contains WHNF cfg.steps in
                let cfg = {cfg with delta_level=glb_delta cfg.delta_level OnlyInline} in
                let norm_or_whnf env t =
                    if whnf
                    then closure_as_term cfg env t
                    else norm cfg env [] t in
                let branches = branches |> List.map (fun branch -> 
                     //Q: What about normalizing the sorts of each of bound variables in p?
                     let p, wopt, e = SS.open_branch branch in
                     let env = S.pat_bvs p |> List.fold_left (fun env x -> 
                        Dummy::env) env in
                     let wopt = match wopt with 
                        | None -> None
                        | Some w -> Some (norm_or_whnf env w) in
                     let e = norm_or_whnf env e in
                     Util.branch (p, wopt, e)) in
                rebuild cfg env stack (mk (Tm_match(t, branches)) r) in

              let rec is_cons head = match head.n with 
                | Tm_uinst(h, _) -> is_cons h
                | Tm_constant _ 
                | Tm_fvar(_, Some Data_ctor)
                | Tm_fvar(_, Some (Record_ctor _)) -> true
                | _ -> false in

              let guard_when_clause wopt b rest = 
                  match wopt with 
                   | None -> b
                   | Some w -> 
                     let then_branch = b in
                     let else_branch = mk (Tm_match(t, rest)) r in 
                     Util.if_then_else w then_branch else_branch in
                

              let rec matches_pat (t:term) (p:pat)  
                :  either<list<term>, bool> //Inl ts: p matches t and ts are bindings for the branch
                =                           //Inr false: p definitely does not match t
                                            //Inr true: p may match t, but p is an open term and we cannot decide for sure 
                    let t = compress t in 
                    let head, args = Util.head_and_args t in 
                    match p.v with 
                        | Pat_disj ps -> 
                          let mopt = Util.find_map ps (fun p -> 
                            let m = matches_pat t p in
                            match m with 
                             | Inl _ -> Some m //definite match
                             | Inr true -> Some m //maybe match; stop considering other cases
                             | Inr false -> None (*definite mismatch*)) in
                          begin match mopt with 
                            | None -> Inr false //all cases definitely do not match
                            | Some m -> m
                          end
                        | Pat_var _ 
                        | Pat_wild _ -> Inl [t]
                        | Pat_dot_term _ -> Inl []
                        | Pat_constant s -> 
                          begin match t.n with 
                            | Tm_constant s' when (s=s') -> Inl []
                            | _ -> Inr (not (is_cons head)) //if it's not a constant, it may match
                          end
                        | Pat_cons(fv, arg_pats) -> 
                          begin match head.n with 
                            | Tm_fvar fv' when fv_eq fv fv' -> 
                              matches_args [] args arg_pats
                            | _ -> Inr (not (is_cons head)) //if it's not a constant, it may match
                          end

              and matches_args out (a:args) (p:list<(pat * bool)>) : either<list<term>, bool> = match a, p with 
                | [], [] -> Inl out
                | (t, _)::rest_a, (p, _)::rest_p -> 
                    begin match matches_pat t p with 
                        | Inl s -> matches_args (out@s) rest_a rest_p 
                        | m -> m
                    end 
                | _ -> Inr false in
            
              let rec matches t p = match p with 
                | [] -> norm_and_rebuild_match ()
                | (p, wopt, b)::rest -> 
                   match matches_pat t p with
                    | Inr false -> //definite mismatch; safe to consider the remaining patterns
                      matches t rest 

                    | Inr true -> //may match this pattern but t is an open term; block reduction
                      norm_and_rebuild_match ()

                    | Inl s ->
                      //the elements of s are sub-terms of t 
                      //the have no free de Bruijn indices; so their env=[]; see pre-condition at the top of rebuild
                      let env = List.fold_right (fun t env -> Clos([], t, Util.mk_ref (Some ([], t)))::env) s env in
                      norm cfg env stack (guard_when_clause wopt b rest) in
              
              matches t branches

let config s e = 
    let d = if List.contains Unfold s 
            then Env.Unfold
            else if List.contains Inline s
            then Env.OnlyInline
            else Env.NoDelta in
    {tcenv=e; steps=s; delta_level=d}

let normalize s e t = norm (config s e) [] [] t
let normalize_comp s e t = norm_comp (config s e) [] t
let normalize_universe env u = norm_universe (config [] env) [] u

let term_to_string env t = Print.term_to_string (normalize [AllowUnboundUniverses] env t)
let comp_to_string env c = Print.comp_to_string (norm_comp (config [AllowUnboundUniverses] env) [] c)

let normalize_refinement steps env t0 =
   let t = normalize (steps@[Beta; WHNF]) env t0 in
   let rec aux t =
    let t = compress t in
    match t.n with
       | Tm_refine(x, phi) ->
         let t0 = aux x.sort in
         begin match t0.n with
            | Tm_refine(y, phi1) ->
              mk (Tm_refine(y, Util.mk_conj phi1 phi)) t0.pos
            | _ -> t
         end
       | _ -> t in
   aux t

let rec unfold_effect_abbrev env comp =
  let c = comp_to_comp_typ comp in
  match Env.lookup_effect_abbrev env (env.universe_of env c.result_typ) c.effect_name with
    | None -> c
    | Some (binders, cdef) ->
      let binders, cdef = SS.open_comp binders cdef in 
      let inst = List.map2 (fun (x, _) (t, _) -> NT(x, t)) binders (as_arg c.result_typ::c.effect_args) in
      let c1 = SS.subst_comp inst cdef in
      let c = {Util.comp_to_comp_typ c1 with flags=c.flags} |> mk_Comp in
      unfold_effect_abbrev env c

let normalize_sigelt (_:steps) (_:Env.env) (_:sigelt) : sigelt = failwith "NYI: normalize_sigelt"
let eta_expand (_:Env.env) (t:typ) : typ =
    match t.n with 
        | Tm_name x -> 
          let binders, c = Util.arrow_formals_comp x.sort in
          begin match binders with 
            | [] -> t
            | _ -> 
              let binders, args = binders |> Util.args_of_binders in
              Util.abs binders (mk_Tm_app t args None t.pos) (Util.lcomp_of_comp c |> Some)
          end
        | _ -> 
          failwith (Util.format2 "NYI: eta_expand(%s) %s" (Print.tag_of_term t) (Print.term_to_string t))
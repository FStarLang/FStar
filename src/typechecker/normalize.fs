﻿(*
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
  | Beta
  | Iota            //pattern matching
  | Zeta            //fixed points
  | Exclude of step //the first three kinds are included by default, unless Excluded explicity
  | WHNF            //Only produce a weak head normal form
  | Primops         //reduce primitive operators like +, -, *, /, etc.
  | Inline
  | NoInline
  | UnfoldUntil of S.delta_depth
  | PureSubtermsWithinComputations
  | Simplify        //Simplifies some basic logical tautologies: not part of definitional equality!
  | EraseUniverses
  | AllowUnboundUniverses //we erase universes as we encode to SMT; so, sometimes when printing, it's ok to have some unbound universe variables
  | Reify
  | CompressUvars
and steps = list<step>

type closure = 
  | Clos of env * term * memo<(env * term)> * bool //memo for lazy evaluation; bool marks whether or not this is a fixpoint 
  | Univ of universe                               //universe terms do not have free variables
  | Dummy                                          //Dummy is a placeholder for a binder when doing strong reduction
and env = list<closure>

let closure_to_string = function 
    | Clos (_, t, _, _) -> Print.term_to_string t
    | _ -> "dummy"

type cfg = {
    steps: steps;
    tcenv: Env.env;
    delta_level: Env.delta_level  // Controls how much unfolding of definitions should be performed
}

type branches = list<(pat * option<term> * term)> 

type subst_t = list<subst_elt>

type stack_elt = 
 | Arg      of closure * aqual * Range.range 
 | UnivArgs of list<universe> * Range.range
 | MemoLazy of memo<(env * term)>
 | Match    of env * branches * Range.range
 | Abs      of env * binders * env * option<either<lcomp,Ident.lident>> * Range.range //the second env is the first one extended with the binders, for reducing the option<lcomp>
 | App      of term * aqual * Range.range
 | Meta     of S.metadata * Range.range
 | Let      of env * binders * letbinding * Range.range
 | Steps    of steps * Env.delta_level

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
    with _ -> failwith (Util.format1 "Failed to find %s\n" (Print.db_to_string x))

let comp_to_comp_typ (env:Env.env) c =
    let c = match c.n with 
            | Total (t, None) -> 
              let u = env.universe_of env t in
              S.mk_Total' t (Some u)
            | GTotal (t, None) ->
              let u = env.universe_of env t in
              S.mk_GTotal' t (Some u)
            | _ -> c in
    U.comp_to_comp_typ c

let rec unfold_effect_abbrev env comp =
  let c = comp_to_comp_typ env comp in
  match Env.lookup_effect_abbrev env c.comp_univs c.effect_name with
    | None -> c
    | Some (binders, cdef) ->
      let binders, cdef = SS.open_comp binders cdef in 
      if List.length binders <> List.length c.effect_args + 1
      then raise (Error ("Effect constructor is not fully applied", comp.pos));
      let inst = List.map2 (fun (x, _) (t, _) -> NT(x, t)) binders (as_arg c.result_typ::c.effect_args) in
      let c1 = SS.subst_comp inst cdef in
      let c = {comp_to_comp_typ env c1 with flags=c.flags} |> mk_Comp in
      unfold_effect_abbrev env c

let downgrade_ghost_effect_name l = 
    if Ident.lid_equals l Const.effect_Ghost_lid
    then Some Const.effect_Pure_lid
    else if Ident.lid_equals l Const.effect_GTot_lid
    then Some Const.effect_Tot_lid
    else if Ident.lid_equals l Const.effect_GHOST_lid
    then Some Const.effect_PURE_lid
    else None

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
        (*            to   [        S S Z;     S u1;           S S u2;      S ?v1; ?v2]          *)
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
                      | Univ u -> aux u
                      | Dummy -> [u]
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
          | U_max us ->
            let us = List.collect aux us |> norm_univs in
            begin match us with
            | u_k::hd::rest ->
              let rest = hd::rest in
              begin match U.univ_kernel u_k with
                | U_zero, n -> //if the constant term n
                  if rest |> List.for_all (fun u ->
                    let _, m = U.univ_kernel u in
                    n <= m) //is smaller than or equal to all the other terms in the max
                  then rest //then just exclude it
                  else us
                | _ -> us
              end
            | _ -> us
            end
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
    log cfg  (fun () -> Util.print2 ">>> %s Closure_as_term %s\n" (Print.tag_of_term t) (Print.term_to_string t));
    match env with
        | [] when not <| List.contains CompressUvars cfg.steps -> t
        | _ -> 
        let t = compress t in 
        match t.n with 
            | Tm_delayed _ -> 
              failwith "Impossible"

            | Tm_unknown
            | Tm_constant _
            | Tm_name _
            | Tm_fvar _ -> t

            | Tm_uvar _ -> t //should be closed anyway

            | Tm_type u -> 
              mk (Tm_type (norm_universe cfg env u)) t.pos

            | Tm_uinst(t, us) -> (* head symbol must be an fvar *) 
              mk_Tm_uinst t (List.map (norm_universe cfg env) us)
         
            | Tm_bvar x -> 
              begin match lookup_bvar env x with
                    | Univ _ -> failwith "Impossible: term variable is bound to a universe"
                    | Dummy -> t
                    | Clos(env, t0, r, _) -> closure_as_term cfg env t0
              end

           | Tm_app(head, args) -> 
             let head = closure_as_term_delayed cfg env head in 
             let args = closures_as_args_delayed cfg env args in
             mk (Tm_app(head, args)) t.pos
                    
           | Tm_abs(bs, body, lopt) -> 
             let bs, env = closures_as_binders_delayed cfg env bs in 
             let body = closure_as_term_delayed cfg env body in
             mk (Tm_abs(bs, body, close_lcomp_opt cfg env lopt)) t.pos

           | Tm_arrow(bs, c) -> 
             let bs, env = closures_as_binders_delayed cfg env bs in 
             let c = close_comp cfg env c in 
             mk (Tm_arrow(bs, c)) t.pos

           | Tm_refine(x, phi) -> 
             let x, env = closures_as_binders_delayed cfg env [mk_binder x] in 
             let phi = closure_as_term_delayed cfg env phi in 
             mk (Tm_refine(List.hd x |> fst, phi)) t.pos

           | Tm_ascribed(t1, Inl t2, lopt) -> 
             mk (Tm_ascribed(closure_as_term_delayed cfg env t1, Inl <| closure_as_term_delayed cfg env t2, lopt)) t.pos

           | Tm_ascribed(t1, Inr c, lopt) -> 
             mk (Tm_ascribed(closure_as_term_delayed cfg env t1, Inr <| close_comp cfg env c, lopt)) t.pos

           | Tm_meta(t', Meta_pattern args) ->
             mk (Tm_meta(closure_as_term_delayed cfg env t',
                         Meta_pattern (args |> List.map (closures_as_args_delayed cfg env)))) t.pos

           | Tm_meta(t', Meta_monadic(m, tbody)) -> //other metadata's do not have any embedded closures
             mk (Tm_meta(closure_as_term_delayed cfg env t', Meta_monadic(m, closure_as_term_delayed cfg env tbody))) t.pos

           | Tm_meta(t', m) -> //other metadata's do not have any embedded closures
             mk (Tm_meta(closure_as_term_delayed cfg env t', m)) t.pos
       
           | Tm_let((false, [lb]), body) -> //non-recursive let 
             let env0 = env in
             let env = List.fold_left (fun env _ -> Dummy::env) env lb.lbunivs in
             let typ = closure_as_term_delayed cfg env lb.lbtyp in
             let def = closure_as_term cfg env lb.lbdef in
             let body = match lb.lbname with 
                | Inr _ -> body
                | Inl _ -> closure_as_term cfg (Dummy::env0) body in 
             let lb = {lb with lbtyp=typ; lbdef=def} in
             mk (Tm_let((false, [lb]), body)) t.pos

           | Tm_let((_,lbs), body) -> //recursive let
             let norm_one_lb env lb = 
                let env_univs = List.fold_right (fun _ env -> Dummy::env) lb.lbunivs env in
                let env = if S.is_top_level lbs
                          then env_univs
                          else List.fold_right (fun _ env -> Dummy::env) lbs env_univs in
                {lb with lbtyp=closure_as_term cfg env_univs lb.lbtyp;
                         lbdef=closure_as_term cfg env lb.lbdef} in
             let lbs = lbs |> List.map (norm_one_lb env) in
             let body = 
                let body_env = List.fold_right (fun _ env -> Dummy::env) lbs env in
                closure_as_term cfg body_env body in
             mk (Tm_let((true, lbs), body)) t.pos

           | Tm_match(head, branches) -> 
             let head = closure_as_term cfg env head in
             let norm_one_branch env (pat, w_opt, tm) = 
                let rec norm_pat env p = match p.v with 
                    | Pat_constant _ -> p, env
                    | Pat_disj [] -> failwith "Impossible"
                    | Pat_disj (hd::tl) -> 
                      let hd, env' = norm_pat env hd in 
                      let tl = tl |> List.map (fun p -> fst (norm_pat env p)) in
                      {p with v=Pat_disj(hd::tl)}, env'
                    | Pat_cons(fv, pats) -> 
                      let pats, env = pats |> List.fold_left (fun (pats, env) (p, b) -> 
                            let p, env = norm_pat env p in
                            (p,b)::pats, env) ([], env) in
                      {p with v=Pat_cons(fv, List.rev pats)}, env
                    | Pat_var x -> 
                      let x = {x with sort=closure_as_term cfg env x.sort} in
                      {p with v=Pat_var x}, Dummy::env 
                    | Pat_wild x -> 
                      let x = {x with sort=closure_as_term cfg env x.sort} in
                      {p with v=Pat_wild x}, Dummy::env 
                    | Pat_dot_term(x, t) -> 
                      let x = {x with sort=closure_as_term cfg env x.sort} in
                      let t = closure_as_term cfg env t in
                      {p with v=Pat_dot_term(x, t)}, env in
               let pat, env = norm_pat env pat in
               let w_opt = match w_opt with 
                | None -> None
                | Some w -> Some (closure_as_term cfg env w) in
               let tm = closure_as_term cfg env tm in 
               (pat, w_opt, tm) in
            mk (Tm_match(head, branches |> List.map (norm_one_branch env))) t.pos
       
and closure_as_term_delayed cfg env t = 
    match env with 
        | [] when not <| List.contains CompressUvars cfg.steps -> t
        | _ -> closure_as_term cfg env t
//            mk_Tm_delayed (Inr (fun () -> closure_as_term cfg env t)) t.pos  
 
and closures_as_args_delayed cfg env args =
    match env with 
        | [] when not <| List.contains CompressUvars cfg.steps -> args
        | _ -> List.map (fun (x, imp) -> closure_as_term_delayed cfg env x, imp) args 

and closures_as_binders_delayed cfg env bs = 
    let env, bs = bs |> List.fold_left (fun (env, out) (b, imp) -> 
            let b = {b with sort = closure_as_term_delayed cfg env b.sort} in
            let env = Dummy::env in
            env, ((b,imp)::out)) (env, []) in
    List.rev bs, env

and close_comp cfg env c = 
    match env with
        | [] when not <| List.contains CompressUvars cfg.steps -> c
        | _ -> 
        match c.n with 
            | Total (t, uopt) -> 
              mk_Total' (closure_as_term_delayed cfg env t) 
                        (Option.map (norm_universe cfg env) uopt)
            | GTotal (t, uopt) ->
              mk_GTotal' (closure_as_term_delayed cfg env t) 
                         (Option.map (norm_universe cfg env) uopt)
            | Comp c -> 
              let rt = closure_as_term_delayed cfg env c.result_typ in
              let args = closures_as_args_delayed cfg env c.effect_args in 
              let flags = c.flags |> List.map (function 
                | DECREASES t -> DECREASES (closure_as_term_delayed cfg env t)
                | f -> f) in
              mk_Comp ({c with comp_univs=List.map (norm_universe cfg env) c.comp_univs;
                               result_typ=rt;
                               effect_args=args;
                               flags=flags})  

and close_lcomp_opt cfg env lopt = match lopt with
    | Some (Inl lc) -> //NS: Too expensive to close potentially huge VCs that are hardly read
      if Util.is_total_lcomp lc
      then Some (Inr Const.effect_Tot_lid)
      else if Util.is_tot_or_gtot_lcomp lc
      then Some (Inr Const.effect_GTot_lid)
      else Some (Inr lc.eff_name) //retaining the effect name is sufficient
    | _ -> lopt

(*******************************************************************)
(* Simplification steps are not part of definitional equality      *)
(* simplifies True /\ t, t /\ True, t /\ False, False /\ t etc.    *)
(*******************************************************************)
let arith_ops =
    let int_as_const  : int -> Const.sconst = fun i -> Const.Const_int (Util.string_of_int i, None) in
    let bool_as_const : bool -> Const.sconst = fun b -> Const.Const_bool b in
    [(Const.op_Addition,    (fun x y -> int_as_const (x + y)));
     (Const.op_Subtraction, (fun x y -> int_as_const (x - y)));
     (Const.op_Multiply,    (fun x y -> int_as_const (x * y)));
     (Const.op_Division,    (fun x y -> int_as_const (x / y)));
     (Const.op_LT,          (fun x y -> bool_as_const (x < y)));
     (Const.op_LTE,         (fun x y -> bool_as_const (x <= y)));
     (Const.op_GT,          (fun x y -> bool_as_const (x > y)));
     (Const.op_GTE,         (fun x y -> bool_as_const (x >= y)));
     (Const.op_Modulus,     (fun x y -> int_as_const (x % y)))] @
     List.flatten (List.map (fun m -> [
       Const.p2l ["FStar"; m; "add"], (fun x y -> int_as_const (x + y));
       Const.p2l ["FStar"; m; "sub"], (fun x y -> int_as_const (x - y));
       Const.p2l ["FStar"; m; "mul"], (fun x y -> int_as_const (x * y))
     ]) [ "Int8"; "UInt8"; "Int16"; "UInt16"; "Int32"; "UInt32"; "Int64"; "UInt64"; "UInt128" ])

    
let reduce_primops steps tm = 
    let arith_op fv = match fv.n with 
        | Tm_fvar fv -> List.tryFind (fun (l, _) -> S.fv_eq_lid fv l) arith_ops
        | _ -> None in
    if not <| List.contains Primops steps
    then tm
    else match tm.n with
         | Tm_app(fv, [(a1, _); (a2, _)]) ->
            begin match arith_op fv with 
            | None -> tm
            | Some (_, op) -> 
              let norm i j =
                let c = op (Util.int_of_string i) (Util.int_of_string j) in
                mk (Tm_constant c) tm.pos
              in
              begin match (SS.compress a1).n, (SS.compress a2).n with
                | Tm_app (head1, [ arg1, _ ]), Tm_app (head2, [ arg2, _ ]) ->
                    begin match (SS.compress head1).n, (SS.compress head2).n, (SS.compress arg1).n, (SS.compress arg2).n with
                    | Tm_fvar fv1, Tm_fvar fv2,
                      Tm_constant (Const.Const_int (i, None)),
                      Tm_constant (Const.Const_int (j, None))
                      when Util.ends_with (Ident.text_of_lid fv1.fv_name.v) "int_to_t" &&
                      Util.ends_with (Ident.text_of_lid fv2.fv_name.v) "int_to_t" ->
                        // Machine integers are represented as applications, e.g.
                        // [FStar.UInt8.uint_to_t 0xff], so as to get proper
                        // bounds checking. Maintain that invariant.
                        mk_app (mk (Tm_fvar fv1) tm.pos) [ norm i j, None ]
                    | _ ->
                        tm
                    end
                | Tm_constant (Const.Const_int(i, None)), Tm_constant (Const.Const_int(j, None)) -> 
                    norm i j
                | _ -> tm
              end
            end
         | _ -> tm

let maybe_simplify steps tm =
    let w t = {t with pos=tm.pos} in
    let simp_t t = match t.n with
        | Tm_fvar fv when S.fv_eq_lid fv Const.true_lid ->  Some true
        | Tm_fvar fv when S.fv_eq_lid fv Const.false_lid -> Some false
        | _ -> None in
    let simplify arg = (simp_t (fst arg), arg) in
    if not <| List.contains Simplify steps
    then reduce_primops steps tm
    else match tm.n with
            | Tm_app({n=Tm_uinst({n=Tm_fvar fv}, _)}, args)
            | Tm_app({n=Tm_fvar fv}, args) -> 
              if S.fv_eq_lid fv Const.and_lid
              then match args |> List.map simplify with
                     | [(Some true, _); (_, (arg, _))]
                     | [(_, (arg, _)); (Some true, _)] -> arg
                     | [(Some false, _); _]
                     | [_; (Some false, _)] -> w Util.t_false
                     | _ -> tm
              else if S.fv_eq_lid fv Const.or_lid
              then match args |> List.map simplify with
                     | [(Some true, _); _]
                     | [_; (Some true, _)] -> w Util.t_true
                     | [(Some false, _); (_, (arg, _))]
                     | [(_, (arg, _)); (Some false, _)] -> arg
                     | _ -> tm
              else if S.fv_eq_lid fv Const.imp_lid
              then match args |> List.map simplify with
                     | [_; (Some true, _)]
                     | [(Some false, _); _] -> w Util.t_true
                     | [(Some true, _); (_, (arg, _))] -> arg
                     | _ -> tm
              else if S.fv_eq_lid fv Const.not_lid
              then match args |> List.map simplify with
                     | [(Some true, _)] ->  w Util.t_false
                     | [(Some false, _)] -> w Util.t_true
                     | _ -> tm
              else if  S.fv_eq_lid fv Const.forall_lid
                    || S.fv_eq_lid fv Const.exists_lid
              then match args with
                     | [(t, _)]
                     | [(_, Some (Implicit _)); (t, _)] ->
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
          | Tm_name _
          | Tm_fvar( {fv_delta=Delta_constant} ) 
          | Tm_fvar( {fv_qual=Some Data_ctor } ) 
          | Tm_fvar( {fv_qual=Some (Record_ctor _)} ) -> //these last three are just constructors; no delta steps can apply
            rebuild cfg env stack t
     
          | Tm_app({n=Tm_fvar fv}, [(tm, _)])   //User-requested full normalization on tm
            when S.fv_eq_lid fv Syntax.Const.normalize
              && not (Ident.lid_equals cfg.tcenv.curmodule Const.prims_lid) ->
            let s = [Beta; UnfoldUntil Delta_constant; Zeta; Iota; Primops] in
            let cfg' = {cfg with steps=s; delta_level=Unfold Delta_constant} in
            let stack' = Steps (cfg.steps, cfg.delta_level)::stack in
            norm cfg' env stack' tm

          | Tm_app({n=Tm_constant Const.Const_reify}, a1::a2::rest) ->
            let hd, _ = Util.head_and_args t in
            let t' = S.mk (Tm_app(hd, [a1])) None t.pos in
            let t = S.mk(Tm_app(t', a2::rest)) None t.pos in
            norm cfg env stack t

          | Tm_app({n=Tm_constant Const.Const_reify}, [a])
                when (cfg.steps |> List.contains Reify) ->
            let reify_head, _ = Util.head_and_args t in
            let a = SS.compress (fst a) in
            // printfn "TRYING NORMALIZATION OF REIFY: %s ... %s" (Print.tag_of_term a) (Print.term_to_string a);
            begin match a.n with 
            | Tm_meta(e, Meta_monadic (m, t_body)) ->
                begin match (SS.compress e).n with 
                | Tm_let((false, [lb]), body) ->
                    //this is M.bind
                    //reify (M.bind e1 \x.e2) ~> M.bind_repr (reify e1) (\x. (reify e2))
                    let ed = Env.get_effect_decl cfg.tcenv m in
                    let _, bind_repr = ed.bind_repr in 
                    begin match lb.lbname with 
                    | Inl x -> 
                      let head = U.mk_reify lb.lbdef in
                      let body = S.mk (Tm_abs([S.mk_binder x], U.mk_reify body, None)) None body.pos in
                      let reified = S.mk (Tm_app(bind_repr, [as_arg lb.lbtyp; as_arg t_body;  //a, b
                                                             as_arg S.tun; as_arg head;   //wp_head, head--the term shouldn't depend on wp_head
                                                             as_arg S.tun; as_arg body])) //wp_body, body--the term shouldn't depend on wp_body
                                                             None t.pos in
                      // printfn "Reified %s to %s\n" (Print.term_to_string t) (Print.term_to_string reified);
                      norm cfg env stack reified
                    | Inr _ -> failwith "Cannot reify a top-level let binding"
                    end
                | Tm_app _ ->
                  //monadic application
                  failwith "NYI: monadic application"
                | _ -> 
                  let stack = App(reify_head, None, t.pos)::stack in
                  norm cfg env stack a
                end

            | Tm_app({n=Tm_constant (Const.Const_reflect _)}, [a]) -> 
              //reify (reflect e) ~> e
              norm cfg env stack (fst a)

            | Tm_match(e, branches) -> 
              //reify (match e with p -> e') ~> match (reify e) with p -> reify e'
              let e = Util.mk_reify e in 
              let branches = branches |> List.map (fun (pat, wopt, tm) -> pat, wopt, Util.mk_reify tm) in
              let tm = mk (Tm_match(e, branches)) t.pos in
              norm cfg env stack tm

            | _ ->
              let stack = App(reify_head, None, t.pos)::stack in
              norm cfg env stack a
            end

          | Tm_type u -> 
            let u = norm_universe cfg env u in
            rebuild cfg env stack (mk (Tm_type u) t.pos)
         
          | Tm_uinst(t', us) -> 
            if cfg.steps |> List.contains EraseUniverses
            then norm cfg env stack t'
            else let us = UnivArgs(List.map (norm_universe cfg env) us, t.pos) in
                 let stack = us::stack in
                 norm cfg env stack t'
     
          | Tm_fvar f -> 
            let t0 = t in
            let should_delta = match cfg.delta_level with 
                | NoDelta -> false
                | OnlyInline -> true
                | Unfold l -> Common.delta_depth_greater_than f.fv_delta l in
                           
            if not should_delta
            then rebuild cfg env stack t
            else begin match Env.lookup_definition cfg.delta_level cfg.tcenv f.fv_name.v with 
                    | None -> rebuild cfg env stack t
                    | Some (us, t) ->
                      log cfg (fun () -> Util.print2 ">>> Unfolded %s to %s\n" 
                                    (Print.term_to_string t0) (Print.term_to_string t));
                      let n = List.length us in 
                      if n > 0 
                      then match stack with //universe beta reduction
                             | UnivArgs(us', _)::stack -> 
                               let env = us' |> List.fold_left (fun env u -> Univ u::env) env in 
                               norm cfg env stack t 
                             | _ when (cfg.steps |> List.contains EraseUniverses) -> 
                               norm cfg env stack t 
                             | _ -> failwith (Util.format1 "Impossible: missing universe instantiation on %s" (Print.lid_to_string f.fv_name.v))
                      else norm cfg env stack t             
                 end

          | Tm_bvar x -> 
            begin match lookup_bvar env x with 
                | Univ _ -> failwith "Impossible: term variable is bound to a universe"
                | Dummy -> failwith "Term variable not found"
                | Clos(env, t0, r, fix) ->
                   if not fix || not (List.contains (Exclude Zeta) cfg.steps)
                   then match !r with 
                        | Some (env, t') -> 
                            log cfg  (fun () -> Util.print2 "Lazy hit: %s cached to %s\n" (Print.term_to_string t) (Print.term_to_string t'));
                            begin match (compress t').n with
                                | Tm_abs _  ->  
                                    norm cfg env stack t'
                                | _ -> 
                                    rebuild cfg env stack t'
                            end
                        | None -> norm cfg env (MemoLazy r::stack) t0
                   else norm cfg env stack t0 //Fixpoint steps are excluded; so don't take the recursive knot
            end
            
          | Tm_abs(bs, body, lopt) -> 
            begin match stack with 
                | UnivArgs _::_ ->
                  failwith "Ill-typed term: universes cannot be applied to term abstraction"

                | Match _::_ -> 
                  failwith "Ill-typed term: cannot pattern match an abstraction"

                | Arg(c, _, _)::stack_rest -> 
                  begin match c with 
                    | Univ _ -> //universe variables do not have explicit binders
                      norm cfg (c::env) stack_rest t

                    | _ -> 
                     (* Note: we peel off one application at a time. 
                              An optimization to attempt would be to push n-args are once, 
                              and try to pop all of them at once, in the common case of a full application. 
                      *)
                      begin match bs with 
                        | [] -> failwith "Impossible"
                        | [_] -> 
                          begin match lopt with 
                            | None when (Options.__unit_tests()) -> 
                              log cfg  (fun () -> Util.print1 "\tShifted %s\n" (closure_to_string c));
                              norm cfg (c :: env) stack_rest body 

                            | Some (Inr l) 
                                when (Ident.lid_equals l Const.effect_Tot_lid
                                      || Ident.lid_equals l Const.effect_GTot_lid) ->
                              log cfg  (fun () -> Util.print1 "\tShifted %s\n" (closure_to_string c));
                              norm cfg (c :: env) stack_rest body 

                            | Some (Inl lc) when (Util.is_tot_or_gtot_lcomp lc) ->
                              log cfg  (fun () -> Util.print1 "\tShifted %s\n" (closure_to_string c));
                              norm cfg (c :: env) stack_rest body 

                            | _ when (cfg.steps |> List.contains Reify) ->
                              norm cfg (c :: env) stack_rest body 

                            | _ -> //can't reduce, as it may not terminate
//                              printfn "REFUSING TO NORMALIZE APPLICATION BECAUSE IT MAY BE IMPURE: %s" (Print.term_to_string t);
//                              printfn "Stack has %d elements" (List.length stack_rest);;
                              let cfg = {cfg with steps=WHNF::Exclude Iota::Exclude Zeta::cfg.steps} in
                              rebuild cfg env stack (closure_as_term cfg env t) //But, if the environment is non-empty, we need to substitute within the term
                          end
                        | _::tl -> 
                          log cfg  (fun () -> Util.print1 "\tShifted %s\n" (closure_to_string c));
                          let body = mk (Tm_abs(tl, body, lopt)) t.pos in
                          norm cfg (c :: env) stack_rest body 
                      end
                  end

                | Steps (s, dl) :: stack -> 
                  norm ({cfg with steps=s; delta_level=dl}) env stack t

                | MemoLazy r :: stack -> 
                  set_memo r (env, t); //We intentionally do not memoize the strong normal form; only the WHNF
                  log cfg  (fun () -> Util.print1 "\tSet memo %s\n" (Print.term_to_string t));
                  norm cfg env stack t

                | Meta _::_
                | Let _ :: _
                | App _ :: _ 
                | Abs _ :: _
                | [] -> 
                  if List.contains WHNF cfg.steps //don't descend beneath a lambda if we're just doing WHNF   
                  then rebuild cfg env stack (closure_as_term cfg env t) //But, if the environment is non-empty, we need to substitute within the term
                  else let bs, body, opening = open_term' bs body in 
                       let lopt = match lopt with 
                        | Some (Inl l) -> SS.subst_comp opening (l.comp()) |> Util.lcomp_of_comp |> Inl |> Some
                        | _ -> lopt in
                       let env' = bs |> List.fold_left (fun env _ -> Dummy::env) env in
                       log cfg  (fun () -> Util.print1 "\tShifted %s dummies\n" (string_of_int <| List.length bs));
                       norm cfg env' (Abs(env, bs, env', lopt, t.pos)::stack) body
            end

          | Tm_app(head, args) -> 
            let stack = stack |> List.fold_right (fun (a, aq) stack -> Arg (Clos(env, a, Util.mk_ref None, false),aq,t.pos)::stack) args in
            log cfg  (fun () -> Util.print1 "\tPushed %s arguments\n" (string_of_int <| List.length args));
            norm cfg env stack head
                            
          | Tm_refine(x, f) -> //non tail-recursive; the alternative is to keep marks on the stack to rebuild the term ... but that's very heavy
            if List.contains WHNF cfg.steps
            then match env, stack with 
                    | [], [] -> //TODO: Make this work in general!
                      let t_x = norm cfg env [] x.sort in 
                      let t = mk (Tm_refine({x with sort=t_x}, f)) t.pos in 
                      rebuild cfg env stack t
                    | _ -> rebuild cfg env stack (closure_as_term cfg env t)
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
          
          | Tm_ascribed(t1, tc, l) -> 
            begin match stack with 
                | Match _ :: _
                | Arg _ :: _ 
                | MemoLazy _ :: _ -> norm cfg env stack t1 //ascriptions should not block reduction                
                | _ -> 
                let t1 = norm cfg env [] t1 in 
                log cfg  (fun () -> Util.print_string "+++ Normalizing ascription \n");
                let tc = match tc with 
                    | Inl t -> Inl (norm cfg env [] t) 
                    | Inr c -> Inr (norm_comp cfg env c) in
                rebuild cfg env stack (mk (Tm_ascribed(t1, tc, l)) t.pos)
            end

          | Tm_match(head, branches) -> 
            let stack = Match(env, branches, t.pos)::stack in 
            norm cfg env stack head
 
          | Tm_let((_, {lbname=Inr _}::_), _) -> //this is a top-level let binding; nothing to normalize
            rebuild cfg env stack t

          | Tm_let((false, [lb]), body) ->
            let n = TypeChecker.Env.norm_eff_name cfg.tcenv lb.lbeff in
            if not (cfg.steps |> List.contains NoInline)
            && (Util.is_pure_effect n
            || Util.is_ghost_effect n)
            then let env = Clos(env, lb.lbdef, Util.mk_ref None, false)::env in 
                 norm cfg env stack body
            else let bs, body = Subst.open_term [lb.lbname |> Util.left |> S.mk_binder] body in
                 let lb = {lb with lbname=List.hd bs |> fst |> Inl;
                                   lbtyp=norm cfg env [] lb.lbtyp;
                                   lbdef=norm cfg env [] lb.lbdef} in
                 let env' = bs |> List.fold_left (fun env _ -> Dummy::env) env in
                 norm cfg env' (Let(env, bs, lb, t.pos)::stack) body
            
          | Tm_let(lbs, body) when List.contains (Exclude Zeta) cfg.steps -> //no fixpoint reduction allowed
            rebuild cfg env stack (closure_as_term cfg env t)

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
                    let rec_env = Clos(env, fix_f_i, memo, true)::rec_env in
                    rec_env, memo::memos, i + 1) (snd lbs) (env, [], 0) in
            let _ = List.map2 (fun lb memo -> memo := Some (rec_env, lb.lbdef)) (snd lbs) memos in //tying the knot
            let body_env = List.fold_right (fun lb env -> Clos(rec_env, lb.lbdef, Util.mk_ref None, false)::env)
                               (snd lbs) env in
            norm cfg body_env stack body

          | Tm_meta (head, m) -> 
            begin match m with 
                  | Meta_monadic (m, t) ->
                    let t = norm cfg env [] t in
                    let stack = Steps(cfg.steps, cfg.delta_level)::stack in
                    let cfg = {cfg with steps=[NoInline; Exclude Zeta]@cfg.steps; delta_level=NoDelta} in
                    norm cfg env (Meta(Meta_monadic(m, t), t.pos)::stack) head //meta doesn't block reduction, but we need to put the label back

                 | Meta_monadic_lift (m, m') ->
                    if (Util.is_pure_effect m
                    || Util.is_ghost_effect m)
                    && cfg.steps |> List.contains PureSubtermsWithinComputations
                    then let stack = Steps(cfg.steps, cfg.delta_level)::stack in
                            let cfg = {cfg with steps=[PureSubtermsWithinComputations; Primops; AllowUnboundUniverses; EraseUniverses; Exclude Zeta]; delta_level=OnlyInline} in
                            norm cfg env (Meta(Meta_monadic_lift(m, m'), head.pos)::stack) head //meta doesn't block reduction, but we need to put the label back
                    else norm cfg env (Meta(Meta_monadic_lift(m, m'), head.pos)::stack) head //meta doesn't block reduction, but we need to put the label back
            
                 | _ -> 
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
            end

and norm_pattern_args cfg env args = 
    args |> List.map (List.map (fun (a, imp) -> norm cfg env [] a, imp)) 
    
and norm_comp : cfg -> env -> comp -> comp = 
    fun cfg env comp -> 
        let comp = ghost_to_pure_aux cfg env comp in
        match comp.n with 
            | Total (t, uopt) -> 
              {comp with n=Total (norm cfg env [] t, Option.map (norm_universe cfg env) uopt)}

            | GTotal (t, uopt) -> 
              {comp with n=GTotal (norm cfg env [] t, Option.map (norm_universe cfg env) uopt)}

            | Comp ct -> 
              let norm_args args = args |> List.map (fun (a, i) -> (norm cfg env [] a, i)) in
              let flags = ct.flags |> List.map (function DECREASES t -> DECREASES (norm cfg env [] t) | f -> f) in
              {comp with n=Comp ({ct with comp_univs=List.map (norm_universe cfg env) ct.comp_univs;
                                          result_typ=norm cfg env [] ct.result_typ;
                                          effect_args=norm_args ct.effect_args;
                                          flags=flags})}

(* Promotes Ghost T, when T is not informative to Pure T
        Non-informative types T ::= unit | Type u | t -> Tot T | t -> GTot T
*)
and ghost_to_pure_aux cfg env c =
    let norm t = 
        norm ({cfg with steps=[Inline; UnfoldUntil Delta_constant; AllowUnboundUniverses]}) env [] t in
    let non_info t = non_informative (norm t) in
    match c.n with
    | Total _ -> c
    | GTotal(t,uopt) when non_info t -> {c with n=Total(t, uopt)}
    | Comp ct ->
        let l = Env.norm_eff_name cfg.tcenv ct.effect_name in
        if Util.is_ghost_effect l
        && non_info ct.result_typ
        then let ct = 
                 match downgrade_ghost_effect_name ct.effect_name with 
                 | Some pure_eff -> 
                   {ct with effect_name=pure_eff}
                 | None -> 
                    let ct = unfold_effect_abbrev cfg.tcenv c in //must be GHOST
                    {ct with effect_name=Const.effect_PURE_lid} in
             {c with n=Comp ct}
        else c
    | _ -> c

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

and norm_lcomp_opt : cfg -> env -> option<either<lcomp, Ident.lident>> -> option<either<lcomp, Ident.lident>> = 
    fun cfg env lopt -> 
        match lopt with
        | Some (Inl lc) -> 
          if Util.is_tot_or_gtot_lcomp lc
          then let t = norm cfg env [] lc.res_typ in
               if Util.is_total_lcomp lc
               then Some (Inl (Util.lcomp_of_comp (S.mk_Total t)))
               else Some (Inl (Util.lcomp_of_comp (S.mk_GTotal t)))
          else Some (Inr lc.eff_name)
       | _ -> lopt


and rebuild : cfg -> env -> stack -> term -> term = 
    fun cfg env stack t ->
    (* Pre-condition: t is in either weak or strong normal form w.r.t env, depending on whether cfg.steps constains WHNF
                      In either case, it has no free de Bruijn indices *)
        match stack with 
            | [] -> t

            | Steps (s, dl) :: stack -> 
              rebuild ({cfg with steps=s; delta_level=dl}) env stack t

            | Meta(m, r)::stack -> 
              let t = mk (Tm_meta(t, m)) r in
              rebuild cfg env stack t

            | MemoLazy r::stack -> 
              set_memo r (env, t);
              log cfg  (fun () -> Util.print1 "\tSet memo %s\n" (Print.term_to_string t));
              rebuild cfg env stack t

            | Let(env', bs, lb, r)::stack ->
              let body = SS.close bs t in
              let t = S.mk (Tm_let((false, [lb]), body)) None r in
              rebuild cfg env' stack t

            | Abs (env', bs, env'', lopt, r)::stack ->
              let bs = norm_binders cfg env' bs in
              let lopt = norm_lcomp_opt cfg env'' lopt in
              rebuild cfg env stack ({abs bs t lopt with pos=r})

            | Arg (Univ _,  _, _)::_
            | Arg (Dummy,  _, _)::_ -> failwith "Impossible"

            | UnivArgs(us, r)::stack -> 
              let t = mk_Tm_uinst t us in
              rebuild cfg env stack t

            | Arg (Clos(env, tm, m, _), aq, r) :: stack ->
              log cfg  (fun () -> Util.print1 "Rebuilding with arg %s\n" (Print.term_to_string tm));
              //this needs to be tail recursive for reducing large terms
              if List.contains (Exclude Iota) cfg.steps
              then if List.contains WHNF cfg.steps
                   then let arg = closure_as_term cfg env tm in 
                        let t = extend_app t (arg, aq) None r in 
                        rebuild cfg env stack t
                   else let stack = App(t, aq, r)::stack in 
                        norm cfg env stack tm
              else begin match !m with 
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
              log cfg  (fun () -> Util.print1 "Rebuilding with match, scrutinee is %s ...\n" (Print.term_to_string t));
              //the scrutinee is always guaranteed to be a pure or ghost term
              //see tc.fs, the case of Tm_match and the comment related to issue #594
              let scrutinee = t in
              let norm_and_rebuild_match () =
                let whnf = List.contains WHNF cfg.steps in
                let cfg = {cfg with delta_level=glb_delta cfg.delta_level OnlyInline;
                                    steps=Exclude Iota::Exclude Zeta::cfg.steps} in
                let norm_or_whnf env t =
                    if whnf
                    then closure_as_term cfg env t
                    else norm cfg env [] t in
                 let rec norm_pat env p = match p.v with 
                    | Pat_constant _ -> p, env
                    | Pat_disj [] -> failwith "Impossible"
                    | Pat_disj (hd::tl) -> 
                      let hd, env' = norm_pat env hd in 
                      let tl = tl |> List.map (fun p -> fst (norm_pat env p)) in
                      {p with v=Pat_disj(hd::tl)}, env'
                    | Pat_cons(fv, pats) -> 
                      let pats, env = pats |> List.fold_left (fun (pats, env) (p, b) -> 
                            let p, env = norm_pat env p in
                            (p,b)::pats, env) ([], env) in
                      {p with v=Pat_cons(fv, List.rev pats)}, env
                    | Pat_var x -> 
                      let x = {x with sort=norm_or_whnf env x.sort} in
                      {p with v=Pat_var x}, Dummy::env 
                    | Pat_wild x -> 
                      let x = {x with sort=norm_or_whnf env x.sort} in
                      {p with v=Pat_wild x}, Dummy::env 
                    | Pat_dot_term(x, t) -> 
                      let x = {x with sort=norm_or_whnf env x.sort} in
                      let t = norm_or_whnf env t in
                      {p with v=Pat_dot_term(x, t)}, env in
                let branches = match env with 
                    | [] when whnf -> branches //nothing to close over
                    | _ -> branches |> List.map (fun branch -> 
                     let p, wopt, e = SS.open_branch branch in
                     //It's important to normalize all the sorts within the pat!
                     let p, env = norm_pat env p in
                     let wopt = match wopt with 
                        | None -> None
                        | Some w -> Some (norm_or_whnf env w) in
                     let e = norm_or_whnf env e in
                     Util.branch (p, wopt, e)) in
                rebuild cfg env stack (mk (Tm_match(scrutinee, branches)) r) in

              let rec is_cons head = match head.n with 
                | Tm_uinst(h, _) -> is_cons h
                | Tm_constant _ 
                | Tm_fvar( {fv_qual=Some Data_ctor} )
                | Tm_fvar( {fv_qual=Some (Record_ctor _)} ) -> true
                | _ -> false in

              let guard_when_clause wopt b rest = 
                  match wopt with 
                   | None -> b
                   | Some w -> 
                     let then_branch = b in
                     let else_branch = mk (Tm_match(scrutinee, rest)) r in 
                     Util.if_then_else w then_branch else_branch in
                

              let rec matches_pat (scrutinee:term) (p:pat)  
                :  either<list<term>, bool> //Inl ts: p matches t and ts are bindings for the branch
                =                           //Inr false: p definitely does not match t
                                            //Inr true: p may match t, but p is an open term and we cannot decide for sure 
                    let scrutinee = U.unmeta scrutinee in 
                    let head, args = Util.head_and_args scrutinee in 
                    match p.v with 
                        | Pat_disj ps -> 
                          let mopt = Util.find_map ps (fun p -> 
                            let m = matches_pat scrutinee p in
                            match m with 
                             | Inl _ -> Some m //definite match
                             | Inr true -> Some m //maybe match; stop considering other cases
                             | Inr false -> None (*definite mismatch*)) in
                          begin match mopt with 
                            | None -> Inr false //all cases definitely do not match
                            | Some m -> m
                          end
                        | Pat_var _ 
                        | Pat_wild _ -> Inl [scrutinee]
                        | Pat_dot_term _ -> Inl []
                        | Pat_constant s -> 
                          begin match scrutinee.n with 
                            | Tm_constant s' when (s=s') -> Inl []
                            | _ -> Inr (not (is_cons head)) //if it's not a constant, it may match
                          end
                        | Pat_cons(fv, arg_pats) -> 
                          begin match (Util.un_uinst head).n with 
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
            
              let rec matches scrutinee p = match p with 
                | [] -> norm_and_rebuild_match ()
                | (p, wopt, b)::rest -> 
                   match matches_pat scrutinee p with
                    | Inr false -> //definite mismatch; safe to consider the remaining patterns
                      matches scrutinee rest 

                    | Inr true -> //may match this pattern but t is an open term; block reduction
                      norm_and_rebuild_match ()

                    | Inl s -> //definite match
                      log cfg (fun () -> Util.print2 "Matches pattern %s with subst = %s\n" 
                                    (Print.pat_to_string p)
                                    (List.map Print.term_to_string s |> String.concat "; "));
                      //the elements of s are sub-terms of t 
                      //the have no free de Bruijn indices; so their env=[]; see pre-condition at the top of rebuild
                      let env = List.fold_left (fun env t -> Clos([], t, Util.mk_ref (Some ([], t)), false)::env) env s in
                      norm cfg env stack (guard_when_clause wopt b rest) in
              
              if cfg.steps |> List.contains (Exclude Iota)
              then norm_and_rebuild_match ()
              else matches scrutinee branches

let config s e = 
    let d = match Util.find_map s (function UnfoldUntil k -> Some k | _ -> None) with
                | Some k -> Env.Unfold k
                | None -> if List.contains Inline s
                          then Env.OnlyInline
                          else Env.NoDelta in
    {tcenv=e; steps=s; delta_level=d}

let normalize s e t = norm (config s e) [] [] t
let normalize_comp s e t = norm_comp (config s e) [] t
let normalize_universe env u = norm_universe (config [] env) [] u
let ghost_to_pure env c = ghost_to_pure_aux (config [] env) [] c

let ghost_to_pure_lcomp env (lc:lcomp) = 
    let cfg = config [Inline; UnfoldUntil Delta_constant; EraseUniverses; AllowUnboundUniverses] env in
    let non_info t = non_informative (norm cfg [] [] t) in
    if Util.is_ghost_effect lc.eff_name
    && non_info lc.res_typ
    then match downgrade_ghost_effect_name lc.eff_name with 
         | Some pure_eff -> 
           {lc with eff_name=pure_eff;
                    comp=(fun () -> ghost_to_pure env (lc.comp()))}
         | None -> //can't downgrade, don't know the particular incarnation of PURE to use
           lc
    else lc
     
let term_to_string env t = Print.term_to_string (normalize [AllowUnboundUniverses] env t)
let comp_to_string env c = Print.comp_to_string (norm_comp (config [AllowUnboundUniverses] env) [] c)

let normalize_refinement steps env t0 =
   let t = normalize (steps@[Beta]) env t0 in
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

let eta_expand (env:Env.env) (t:typ) : typ =
  let expand sort =
    let binders, c = Util.arrow_formals_comp sort in
    begin match binders with
    | [] -> t
    | _ ->
        let binders, args = binders |> Util.args_of_binders in
        Util.abs binders (mk_Tm_app t args None t.pos) (Util.lcomp_of_comp c |> Inl |> Some)
    end
  in
  match !t.tk, t.n with
  | Some sort, _ ->
      expand (mk sort t.pos)
  | _, Tm_name x ->
      expand x.sort
  | _ ->
      let head, args = Util.head_and_args t in
      begin match (SS.compress head).n with 
      | Tm_uvar(_, thead) -> 
        let formals, tres = Util.arrow_formals thead in
        if List.length formals = List.length args
        then t 
        else let _, ty, _ = env.type_of ({env with lax=true; use_bv_sorts=true; expected_typ=None}) t in
             expand ty
      | _ ->
        let _, ty, _ = env.type_of ({env with lax=true; use_bv_sorts=true; expected_typ=None}) t in
        expand ty
      end

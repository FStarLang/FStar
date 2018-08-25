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
open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.String
open FStar.Const
open FStar.Char
open FStar.Errors
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.TypeChecker.Cfg

module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
//basic util
module BU = FStar.Util
module FC = FStar.Const
module PC = FStar.Parser.Const
module U  = FStar.Syntax.Util
module I  = FStar.Ident
module EMB = FStar.Syntax.Embeddings
module Z = FStar.BigInt

(**********************************************************************************************
 * Reduction of types via the Krivine Abstract Machine (KN), with lazy
 * reduction and strong reduction (under binders), as described in:
 *
 * Strongly reducing variants of the Krivine abstract machine
 * Pierre Crégut
 * Higher-Order Symb Comput (2007) 20: 209–230
 **********************************************************************************************)

let cases f d = function
  | Some x -> f x
  | None -> d

type closure =
  | Clos of env * term * memo<(env * term)> * bool //memo for lazy evaluation; bool marks whether or not this is a fixpoint
  | Univ of universe                               //universe terms do not have free variables
  | Dummy                                          //Dummy is a placeholder for a binder when doing strong reduction
and env = list<(option<binder>*closure)>

let dummy : option<binder> * closure = None,Dummy

type branches = list<(pat * option<term> * term)>

type stack_elt =
 | Arg      of closure * aqual * Range.range
 | UnivArgs of list<universe> * Range.range
 | MemoLazy of memo<(env * term)>
 | Match    of env * branches * cfg * Range.range
 | Abs      of env * binders * env * option<residual_comp> * Range.range //the second env is the first one extended with the binders, for reducing the option<lcomp>
 | App      of env * term * aqual * Range.range
 | Meta     of env * S.metadata * Range.range
 | Let      of env * binders * letbinding * Range.range
 | Cfg      of cfg
 | Debug    of term * BU.time
type stack = list<stack_elt>

let head_of t = let hd, _ = U.head_and_args' t in hd

let mk t r = mk t None r
let set_memo cfg (r:memo<'a>) (t:'a) =
  if cfg.memoize_lazy then
    match !r with
    | Some _ -> failwith "Unexpected set_memo: thunk already evaluated"
    | None -> r := Some t

let rec env_to_string env = //BU.format1 "(%s elements)" (string_of_int <| List.length env)
    List.map (fun (bopt, c) ->
                BU.format2 "(%s, %s)"
                   (match bopt with None -> "." | Some x -> FStar.Syntax.Print.binder_to_string x)
                   (closure_to_string c))
             env
            |> String.concat "; "
and closure_to_string = function
    | Clos (env, t, _, _) -> BU.format2 "(env=%s elts; %s)" (List.length env |> string_of_int) (Print.term_to_string t)
    | Univ _ -> "Univ"
    | Dummy -> "dummy"

let stack_elt_to_string = function
    | Arg (c, _, _) -> BU.format1 "Closure %s" (closure_to_string c)
    | MemoLazy _ -> "MemoLazy"
    | Abs (_, bs, _, _, _) -> BU.format1 "Abs %s" (string_of_int <| List.length bs)
    | UnivArgs _ -> "UnivArgs"
    | Match   _ -> "Match"
    | App (_, t,_,_) -> BU.format1 "App %s" (Print.term_to_string t)
    | Meta (_, m,_) -> "Meta"
    | Let  _ -> "Let"
    | Cfg _ -> "Cfg"
    | Debug (t, _) -> BU.format1 "Debug %s" (Print.term_to_string t)
    // | _ -> "Match"

let stack_to_string s =
    List.map stack_elt_to_string s |> String.concat "; "

let is_empty = function
    | [] -> true
    | _ -> false

let lookup_bvar env x =
    try snd (List.nth env x.index)
    with _ -> failwith (BU.format2 "Failed to find %s\nEnv is %s\n" (Print.db_to_string x) (env_to_string env))

let downgrade_ghost_effect_name l =
    if Ident.lid_equals l PC.effect_Ghost_lid
    then Some PC.effect_Pure_lid
    else if Ident.lid_equals l PC.effect_GTot_lid
    then Some PC.effect_Tot_lid
    else if Ident.lid_equals l PC.effect_GHOST_lid
    then Some PC.effect_PURE_lid
    else None

(********************************************************************************************************************)
(* Normal form of a universe u is                                                                                   *)
(*  either u, where u <> U_max                                                                                      *)
(*  or     U_max [k;                        --constant                                                              *)
(*               S^n1 u1 ; ...; S^nm um;    --offsets of distinct names, in order of the names                      *)
(*               S^p1 ?v1; ...; S^pq ?vq]   --offsets of distinct unification variables, in order of the variables  *)
(*          where the size of the list is at least 2                                                                *)
(********************************************************************************************************************)
let norm_universe cfg (env:env) u =
    let norm_univs us =
        let us = BU.sort_with U.compare_univs us in
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
                try match snd (List.nth env x) with
                      | Univ u ->
                           if Env.debug cfg.tcenv <| Options.Other "univ_norm" then
                               BU.print1 "Univ (in norm_universe): %s\n" (Print.univ_to_string u)
                           else ();  aux u
                      | Dummy -> [u]
                      | _ -> failwith (BU.format1 "Impossible: universe variable u@%s bound to a term"
                                                   (string_of_int x))
                with _ -> if cfg.steps.allow_unbound_universes
                          then [U_unknown]
                          else failwith ("Universe variable not found: u@" ^ string_of_int x)
            end
          | U_unif _ when cfg.steps.check_no_uvars ->
            [U_zero]
//            failwith (BU.format2 "(%s) CheckNoUvars: unexpected universes variable remains: %s"
//                                       (Range.string_of_range (Env.get_range cfg.tcenv))
//                                       (Print.univ_to_string u))

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

    if cfg.steps.erase_universes
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
let rec inline_closure_env cfg (env:env) stack t =
    log cfg (fun () -> BU.print3 "\n>>> %s (env=%s) Closure_as_term %s\n" (Print.tag_of_term t) (env_to_string env) (Print.term_to_string t));
    match env with
    | [] when not <| cfg.steps.compress_uvars ->
      rebuild_closure cfg env stack t

    | _ ->
      match t.n with
      | Tm_delayed _ ->
        inline_closure_env cfg env stack (compress t)

      | Tm_unknown
      | Tm_constant _
      | Tm_name _
      | Tm_lazy _
      | Tm_fvar _ ->
        rebuild_closure cfg env stack t

      | Tm_uvar (uv, s) ->
        if cfg.steps.check_no_uvars
        then let t = compress t in
             match t.n with
             | Tm_uvar _ ->
               failwith (BU.format2 "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        (Range.string_of_range t.pos)
                        (Print.term_to_string t))
             | _ ->
              inline_closure_env cfg env stack t
        else
            let s' = fst s |> List.map (fun s ->
                    s |> List.map (function
                | NT(x, t) ->
                  NT(x, inline_closure_env cfg env [] t)
                | NM(x, i) ->
                  let x_i = S.bv_to_tm ({x with index=i}) in
                  let t = inline_closure_env cfg env [] x_i in
                  (match t.n with
                   | Tm_bvar x_j -> NM(x, x_j.index)
                   | _ -> NT(x, t))
                | _ -> failwith "Impossible: subst invariant of uvar nodes"))
             in
             //let _ = match s with
             //        | [], _
             //        | [[]], _ -> ()
             //        | _::_, _ -> BU.print2 "inline_closure_env\n\tBefore %s\n\t After %s"
             //                               (List.map Print.subst_to_string (fst s) |> String.concat "@")
             //                               (List.map Print.subst_to_string s' |> String.concat "@")
             //        | _ -> () in
             let t = {t with n=Tm_uvar(uv, (s', snd s))} in
             rebuild_closure cfg env stack t

      | Tm_type u ->
        let t = mk (Tm_type (norm_universe cfg env u)) t.pos in
        rebuild_closure cfg env stack t

      | Tm_uinst(t', us) -> (* head symbol must be an fvar *)
        let t = mk_Tm_uinst t' (List.map (norm_universe cfg env) us) in
        rebuild_closure cfg env stack t

      | Tm_bvar x ->
        begin
            match lookup_bvar env x with
            | Univ _ -> failwith "Impossible: term variable is bound to a universe"
            | Dummy ->
              let x = {x with sort = S.tun} in
              let t = mk (Tm_bvar x) t.pos in
              rebuild_closure cfg env stack t
            | Clos(env, t0, _, _) ->
              inline_closure_env cfg env stack t0
        end

      | Tm_app(head, args) ->
        let stack =
            stack |> List.fold_right
            (fun (a, aq) stack -> Arg (Clos(env, a, BU.mk_ref None, false),aq,t.pos)::stack)
            args
        in
        inline_closure_env cfg env stack head

      | Tm_abs(bs, body, lopt) ->
        let env' =
            env |> List.fold_right
            (fun _b env -> (None, Dummy)::env)
            bs
        in
        let stack = (Abs(env, bs, env', lopt, t.pos)::stack) in
        inline_closure_env cfg env' stack body

      | Tm_arrow(bs, c) ->
        let bs, env' = close_binders cfg env bs in
        let c = close_comp cfg env' c in
        let t = mk (Tm_arrow(bs, c)) t.pos in
        rebuild_closure cfg env stack t

      | Tm_refine(x, phi) ->
        let x, env = close_binders cfg env [mk_binder x] in
        let phi = non_tail_inline_closure_env cfg env phi in
        let t = mk (Tm_refine(List.hd x |> fst, phi)) t.pos in
        rebuild_closure cfg env stack t

      | Tm_ascribed(t1, (annot,tacopt), lopt) ->
        let annot =
            match annot with
            | Inl t -> Inl (non_tail_inline_closure_env cfg env t)
            | Inr c -> Inr (close_comp cfg env c) in
        let tacopt = BU.map_opt tacopt (non_tail_inline_closure_env cfg env) in
        let t =
            mk (Tm_ascribed(non_tail_inline_closure_env cfg env t1,
                            (annot, tacopt),
                            lopt)) t.pos
        in
        rebuild_closure cfg env stack t

      | Tm_quoted (t', qi) ->
        let t =
            match qi.qkind with
            | Quote_dynamic ->
              mk (Tm_quoted(non_tail_inline_closure_env cfg env t', qi)) t.pos
            | Quote_static  ->
              let qi = S.on_antiquoted (non_tail_inline_closure_env cfg env) qi in
              mk (Tm_quoted(t', qi)) t.pos
        in
        rebuild_closure cfg env stack t

      | Tm_meta(t', m) ->
        let stack = Meta(env, m, t.pos)::stack in
        inline_closure_env cfg env stack t'

      | Tm_let((false, [lb]), body) -> //non-recursive let
        let env0 = env in
        let env = List.fold_left (fun env _ -> dummy::env) env lb.lbunivs in
        let typ = non_tail_inline_closure_env cfg env lb.lbtyp in
        let def = non_tail_inline_closure_env cfg env lb.lbdef in
        let nm, body =
            if S.is_top_level [lb]
            then lb.lbname, body
            else let x = BU.left lb.lbname in
                 Inl ({x with sort=typ}),
                 non_tail_inline_closure_env cfg (dummy::env0) body
        in
        let lb = {lb with lbname=nm; lbtyp=typ; lbdef=def} in
        let t = mk (Tm_let((false, [lb]), body)) t.pos in
        rebuild_closure cfg env0 stack t

      | Tm_let((_,lbs), body) -> //recursive let
        let norm_one_lb env lb =
            let env_univs = List.fold_right (fun _ env -> dummy::env) lb.lbunivs env in
            let env =
                if S.is_top_level lbs
                then env_univs
                else List.fold_right (fun _ env -> dummy::env) lbs env_univs in
            let ty = non_tail_inline_closure_env cfg env_univs lb.lbtyp in
            let nm =
                if S.is_top_level lbs
                then lb.lbname
                else let x = BU.left lb.lbname in
                     Inl ({x with sort=ty})
            in
            {lb with lbname=nm;
                     lbtyp=ty;
                     lbdef=non_tail_inline_closure_env cfg env lb.lbdef}
        in
        let lbs = lbs |> List.map (norm_one_lb env) in
        let body =
            let body_env = List.fold_right (fun _ env -> dummy::env) lbs env in
            non_tail_inline_closure_env cfg body_env body in
        let t = mk (Tm_let((true, lbs), body)) t.pos in
        rebuild_closure cfg env stack t

      | Tm_match(head, branches) ->
        let stack = Match(env, branches, cfg, t.pos)::stack in
        inline_closure_env cfg env stack head

and non_tail_inline_closure_env cfg env t =
    inline_closure_env cfg env [] t

and rebuild_closure cfg env stack t =
    log cfg (fun () -> BU.print4 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n" (Print.tag_of_term t) (env_to_string env) (stack_to_string stack) (Print.term_to_string t));
    match stack with
    | [] -> t

    | Arg (Clos(env_arg, tm, _, _), aq, r) :: stack ->
      let stack = App(env, t, aq, r)::stack in
      inline_closure_env cfg env_arg stack tm

    | App(env, head, aq, r)::stack ->
      let t = S.extend_app head (t,aq) None r in
      rebuild_closure cfg env stack t

    | Abs (env', bs, env'', lopt, r)::stack ->
      let bs, _ = close_binders cfg env' bs in
      let lopt = close_lcomp_opt cfg env'' lopt in
      rebuild_closure cfg env stack ({abs bs t lopt with pos=r})

    | Match(env, branches, cfg, r)::stack ->
      let close_one_branch env (pat, w_opt, tm) =
          let rec norm_pat env p =
            match p.v with
            | Pat_constant _ ->
              p, env
            | Pat_cons(fv, pats) ->
              let pats, env =
                  pats |> List.fold_left
                  (fun (pats, env) (p, b) ->
                    let p, env = norm_pat env p in (p,b)::pats, env)
                  ([], env)
              in
              {p with v=Pat_cons(fv, List.rev pats)}, env
            | Pat_var x ->
              let x = {x with sort=non_tail_inline_closure_env cfg env x.sort} in
              {p with v=Pat_var x}, dummy::env
            | Pat_wild x ->
              let x = {x with sort=non_tail_inline_closure_env cfg env x.sort} in
              {p with v=Pat_wild x}, dummy::env
            | Pat_dot_term(x, t) ->
              let x = {x with sort=non_tail_inline_closure_env cfg env x.sort} in
              let t = non_tail_inline_closure_env cfg env t in
              {p with v=Pat_dot_term(x, t)}, env
          in
          let pat, env = norm_pat env pat in
          let w_opt =
              match w_opt with
              | None -> None
              | Some w -> Some (non_tail_inline_closure_env cfg env w) in
          let tm = non_tail_inline_closure_env cfg env tm in
          (pat, w_opt, tm)
      in
      let t =
          mk (Tm_match(t, branches |> List.map (close_one_branch env))) t.pos
      in
      rebuild_closure cfg env stack t

    | Meta(env_m, m, r)::stack ->
      let m =
          match m with
          | Meta_pattern args ->
            Meta_pattern (args |> List.map (fun args ->
                                            args |> List.map (fun (a, q) ->
                                            non_tail_inline_closure_env cfg env_m a, q)))

          | Meta_monadic(m, tbody) ->
            Meta_monadic(m, non_tail_inline_closure_env cfg env_m tbody)

          | Meta_monadic_lift(m1, m2, tbody) ->
            Meta_monadic_lift(m1, m2, non_tail_inline_closure_env cfg env_m tbody)

          | _ -> //other metadata's do not have any embedded closures
            m
      in
      let t = mk (Tm_meta(t, m)) r in
      rebuild_closure cfg env stack t

    | _ -> failwith "Impossible: unexpected stack element"

and close_imp cfg env imp =
    match imp with
    | Some (S.Meta t) -> Some (S.Meta (inline_closure_env cfg env [] t))
    | i -> i

and close_binders cfg env bs =
    let env, bs = bs |> List.fold_left (fun (env, out) (b, imp) ->
            let b = {b with sort = inline_closure_env cfg env [] b.sort} in
            let imp = close_imp cfg env imp in
            let env = dummy::env in
            env, ((b,imp)::out)) (env, []) in
    List.rev bs, env

and close_comp cfg env c =
    match env with
    | [] when not <| cfg.steps.compress_uvars -> c
    | _ ->
      match c.n with
      | Total (t, uopt) ->
        mk_Total' (inline_closure_env cfg env [] t)
                  (Option.map (norm_universe cfg env) uopt)

      | GTotal (t, uopt) ->
        mk_GTotal' (inline_closure_env cfg env [] t)
                   (Option.map (norm_universe cfg env) uopt)

      | Comp c ->
        let rt = inline_closure_env cfg env [] c.result_typ in
        let args =
            c.effect_args |>
            List.map (fun (a, q) -> inline_closure_env cfg env [] a, q)
        in
        let flags =
            c.flags |>
            List.map (function
                | DECREASES t -> DECREASES (inline_closure_env cfg env [] t)
                | f -> f)
        in
        mk_Comp ({c with comp_univs=List.map (norm_universe cfg env) c.comp_univs;
                result_typ=rt;
                effect_args=args;
                flags=flags})

and filter_out_lcomp_cflags flags =
    (* TODO : lc.comp might have more cflags than lcomp.cflags *)
    flags |> List.filter (function DECREASES _ -> false | _ -> true)

and close_lcomp_opt cfg env lopt = match lopt with
    | Some rc ->
      let flags =
          rc.residual_flags |>
          List.filter (function DECREASES _ -> false | _ -> true) in
      let rc = {rc with residual_flags=flags; residual_typ=BU.map_opt rc.residual_typ (inline_closure_env cfg env [])} in
      Some rc
    | _ -> lopt

let closure_as_term cfg env t = non_tail_inline_closure_env cfg env t

(* A hacky knot, set by FStar.Main *)
let unembed_binder_knot : ref<option<EMB.embedding<binder>>> = BU.mk_ref None
let unembed_binder (t : term) : option<S.binder> =
    match !unembed_binder_knot with
    | Some e -> EMB.unembed e t true EMB.id_norm_cb
    | None ->
        Errors.log_issue t.pos (Errors.Warning_UnembedBinderKnot, "unembed_binder_knot is unset!");
        None

let mk_psc_subst cfg env =
    List.fold_right
        (fun (binder_opt, closure) subst ->
            match binder_opt, closure with
            | Some b, Clos(env, term, _, _) ->
                // BU.print1 "++++++++++++Name in environment is %s" (Print.binder_to_string b);
                let bv,_ = b in
                if not (U.is_constructed_typ bv.sort PC.binder_lid)
                then subst
                else let term = closure_as_term cfg env term in
                     begin match unembed_binder term with
                     | None -> subst
                     | Some x ->
                         let b = S.freshen_bv ({bv with sort=SS.subst subst (fst x).sort}) in
                         let b_for_x = S.NT(fst x, S.bv_to_name b) in
                         //remove names shadowed by b
                         let subst = List.filter (function NT(_, {n=Tm_name b'}) ->
                                                                  not (Ident.ident_equals b.ppname b'.ppname)
                                                          | _ -> true) subst in
                         b_for_x :: subst
                     end
            | _ -> subst)
        env []

let reduce_primops norm_cb cfg env tm =
    if not cfg.steps.primops
    then tm
    else begin
         let head, args = U.head_and_args tm in
         match (U.un_uinst head).n with
         | Tm_fvar fv -> begin
           match find_prim_step cfg fv with
           | Some prim_step when prim_step.strong_reduction_ok || not cfg.strong ->
             let l = List.length args in
             if l < prim_step.arity
             then begin log_primops cfg (fun () -> BU.print3 "primop: found partially applied %s (%s/%s args)\n"
                                                     (Print.lid_to_string prim_step.name)
                                                     (string_of_int l)
                                                     (string_of_int prim_step.arity));
                        tm //partial application; can't step
                  end
             else begin
                  let args_1, args_2 = if l = prim_step.arity
                                       then args, []
                                       else List.splitAt prim_step.arity args
                  in
                  log_primops cfg (fun () -> BU.print1 "primop: trying to reduce <%s>\n" (Print.term_to_string tm));
                  let psc = {
                      psc_range = head.pos;
                      psc_subst = fun () -> if prim_step.requires_binder_substitution
                                            then mk_psc_subst cfg env
                                            else []
                  } in
                  let r =
                      if false
                      then begin let (r, ms) = BU.record_time (fun () -> prim_step.interpretation psc norm_cb args_1) in
                                 primop_time_count (Ident.string_of_lid fv.fv_name.v) ms;
                                 r
                           end
                      else prim_step.interpretation psc norm_cb args_1
                  in
                  match r with
                  | None ->
                      log_primops cfg (fun () -> BU.print1 "primop: <%s> did not reduce\n" (Print.term_to_string tm));
                      tm
                  | Some reduced ->
                      log_primops cfg (fun () -> BU.print2 "primop: <%s> reduced to <%s>\n"
                                              (Print.term_to_string tm)
                                              (Print.term_to_string reduced));
                      U.mk_app reduced args_2
                 end
           | Some _ ->
               log_primops cfg (fun () -> BU.print1 "primop: not reducing <%s> since we're doing strong reduction\n"
                                            (Print.term_to_string tm));
               tm
           | None -> tm
           end

         | Tm_constant Const_range_of when not cfg.strong ->
           log_primops cfg (fun () -> BU.print1 "primop: reducing <%s>\n"
                                        (Print.term_to_string tm));
           begin match args with
           | [(a1, _)] -> embed_simple EMB.e_range a1.pos tm.pos
           | _ -> tm
           end

         | Tm_constant Const_set_range_of when not cfg.strong ->
           log_primops cfg (fun () -> BU.print1 "primop: reducing <%s>\n"
                                        (Print.term_to_string tm));
           begin match args with
           | [(t, _); (r, _)] ->
                begin match try_unembed_simple EMB.e_range r with
                | Some rng -> Subst.set_use_range rng t
                | None -> tm
                end
           | _ -> tm
           end

         | _ -> tm
   end

let reduce_equality norm_cb cfg tm =
    reduce_primops norm_cb ({cfg with steps = { default_steps with primops = true };
                              primitive_steps=equality_ops}) tm

(********************************************************************************************************************)
(* Main normalization function of the abstract machine                                                              *)
(********************************************************************************************************************)
let is_norm_request hd args =
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_; _] ->
      S.fv_eq_lid fv PC.normalize_term

    | Tm_fvar fv, [_] ->
      S.fv_eq_lid fv PC.normalize

    | Tm_fvar fv, [steps; _; _] ->
      S.fv_eq_lid fv PC.norm

    | _ -> false

let is_nbe_request s = BU.for_some (eq_step NBE) s

let tr_norm_step = function
    | EMB.Zeta ->    [Zeta]
    | EMB.Iota ->    [Iota]
    | EMB.Delta ->   [UnfoldUntil delta_constant]
    | EMB.Simpl ->   [Simplify]
    | EMB.Weak ->    [Weak]
    | EMB.HNF  ->    [HNF]
    | EMB.Primops -> [Primops]
    | EMB.Reify ->   [Reify]
    | EMB.UnfoldOnly names ->
        [UnfoldUntil delta_constant; UnfoldOnly (List.map I.lid_of_str names)]
    | EMB.UnfoldFully names ->
        [UnfoldUntil delta_constant; UnfoldFully (List.map I.lid_of_str names)]
    | EMB.UnfoldAttr names ->
        [UnfoldUntil delta_constant; UnfoldAttr (List.map I.lid_of_str names)]
    | EMB.NBE -> [NBE]

let tr_norm_steps s =
    List.concatMap tr_norm_step s

let get_norm_request cfg (full_norm:term -> term) args =
    let parse_steps s =
      match try_unembed_simple (EMB.e_list EMB.e_norm_step) s with
      | Some steps -> Some (tr_norm_steps steps)
      | None -> None
    in
    let inherited_steps =
        (if cfg.steps.erase_universes then [EraseUniverses] else [])
      @ (if cfg.steps.allow_unbound_universes then [AllowUnboundUniverses] else [])
    in
    match args with
    | [_; (tm, _)]
    | [(tm, _)] ->
      let s = [Beta; Zeta; Iota; Primops; UnfoldUntil delta_constant; Reify] in
      Some (inherited_steps @ s, tm)
    | [(steps, _); _; (tm, _)] ->
      let add_exclude s z = if BU.for_some (eq_step z) s then s else Exclude z :: s in
      begin
      match parse_steps (full_norm steps) with
      | None -> None
      | Some s ->
        let s = Beta::s in
        let s = add_exclude s Zeta in
        let s = add_exclude s Iota in
        Some (inherited_steps @ s, tm)
      end
    | _ ->
      None

let nbe_eval (cfg:cfg) (s:steps) (tm:term) : term =
    let delta_level =
      if s |> BU.for_some (function UnfoldUntil _ | UnfoldOnly _ | UnfoldFully _ -> true | _ -> false)
      then [Unfold delta_constant]
      else [NoDelta] in
    log_nbe cfg (fun () -> BU.print1 "Invoking NBE with  %s\n" (Print.term_to_string tm));
    let tm_norm = (cfg_env cfg).nbe s cfg.tcenv tm in
    log_nbe cfg (fun () -> BU.print1 "Result of NBE is  %s\n" (Print.term_to_string tm_norm));
    tm_norm

let is_reify_head = function
    | App(_, {n=Tm_constant FC.Const_reify}, _, _)::_ ->
      true
    | _ ->
      false

let firstn k l = if List.length l < k then l,[] else first_N k l
let should_reify cfg stack =
    let rec drop_irrel = function
        | MemoLazy _ :: s -> drop_irrel s
        | s -> s
    in
    match drop_irrel stack with
    | App (_, {n=Tm_constant FC.Const_reify}, _, _) :: _ ->
        // BU.print1 "Found a reify on the stack. %s" "" ;
        cfg.steps.reify_
    | _ -> false

let rec maybe_weakly_reduced tm :  bool =
    let aux_comp c =
        match c.n with
        | GTotal (t, _)
        | Total (t, _) ->
          maybe_weakly_reduced t

        | Comp ct ->
          maybe_weakly_reduced ct.result_typ
          || BU.for_some (fun (a, _) -> maybe_weakly_reduced a) ct.effect_args
    in
    let t = Subst.compress tm in
    match t.n with
      | Tm_delayed _ -> failwith "Impossible"

      | Tm_name _
      | Tm_uvar _
      | Tm_type _
      | Tm_bvar _
      | Tm_fvar _
      | Tm_constant _
      | Tm_lazy _
      | Tm_unknown
      | Tm_uinst _
      | Tm_quoted _ -> false

      | Tm_let _
      | Tm_abs _
      | Tm_arrow _
      | Tm_refine _
      | Tm_match _ ->
        true

      | Tm_app(t, args) ->
        maybe_weakly_reduced t
        || (args |> BU.for_some (fun (a, _) -> maybe_weakly_reduced a))

      | Tm_ascribed(t1, asc, _) ->
        maybe_weakly_reduced t1
        || (match fst asc with
            | Inl t2 -> maybe_weakly_reduced t2
            | Inr c2 -> aux_comp c2)
        || (match snd asc with
           | None -> false
           | Some tac -> maybe_weakly_reduced tac)

      | Tm_meta(t, m) ->
        maybe_weakly_reduced t
        || (match m with
           | Meta_pattern args ->
             BU.for_some (BU.for_some (fun (a, _) -> maybe_weakly_reduced a)) args

           | Meta_monadic_lift(_, _, t')
           | Meta_monadic(_, t') ->
             maybe_weakly_reduced t'

           | Meta_labeled _
           | Meta_desugared _
           | Meta_named _ -> false)

type should_unfold_res =
    | Should_unfold_no
    | Should_unfold_yes
    | Should_unfold_fully
    | Should_unfold_reify

let should_unfold cfg should_reify fv qninfo : should_unfold_res =
    let attrs = match Env.attrs_of_qninfo qninfo with
            | None -> []
            | Some ats -> ats
    in
    (* unfold or not, fully or not, reified or not *)
    let yes   = true  , false , false in
    let no    = false , false , false in
    let fully = true  , true  , false in
    let reif  = true  , false , true in

    let yesno b = if b then yes else no in
    let fullyno b = if b then fully else no in
    let comb_or l = List.fold_right (fun (a,b,c) (x,y,z) -> (a||x, b||y, c||z)) l (false, false, false) in
    let string_of_res (x,y,z) = BU.format3 "(%s,%s,%s)" (string_of_bool x) (string_of_bool y) (string_of_bool z) in

    let res = match qninfo, cfg.steps.unfold_only, cfg.steps.unfold_fully, cfg.steps.unfold_attr with
    // We unfold dm4f actions if and only if we are reifying
    | _ when Env.qninfo_is_action qninfo ->
        let b = should_reify cfg in
        log_unfolding cfg (fun () -> BU.print2 "should_unfold: For DM4F action %s, should_reify = %s\n"
                                               (Print.fv_to_string fv)
                                               (string_of_bool b));
        if b then reif else no

    // If it is handled primitively, then don't unfold
    | _ when Option.isSome (find_prim_step cfg fv) ->
        log_unfolding cfg (fun () -> BU.print_string " >> It's a primop, not unfolding\n");
        no

    // Don't unfold HasMaskedEffect
    | Some (Inr ({sigquals=qs; sigel=Sig_let((is_rec, _), _)}, _), _), _, _, _ when
            List.contains HasMaskedEffect qs ->
        log_unfolding cfg (fun () -> BU.print_string " >> HasMaskedEffect, not unfolding\n");
        no

    // UnfoldTac means never unfold FVs marked [@"tac_opaque"]
    | _, _, _, _ when cfg.steps.unfold_tac && BU.for_some (U.attr_eq U.tac_opaque_attr) attrs ->
        log_unfolding cfg (fun () -> BU.print_string " >> tac_opaque, not unfolding\n");
        no

    // Recursive lets may only be unfolded when Zeta is on
    | Some (Inr ({sigquals=qs; sigel=Sig_let((is_rec, _), _)}, _), _), _, _, _ when
            is_rec && not cfg.steps.zeta ->
        log_unfolding cfg (fun () -> BU.print_string " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
        no

    // We're doing selectively unfolding, assume it to not unfold unless it meets the criteria
    | _, Some _, _, _
    | _, _, Some _, _
    | _, _, _, Some _ ->
        log_unfolding cfg (fun () -> BU.print1 "should_unfold: Reached a %s with selective unfolding\n"
                                               (Print.fv_to_string fv));
        // How does the following code work?
        // We are doing selective unfolding so, by default, we assume everything
        // should *not* be unfolded unless it meets *at least one* of the criteria.
        // So we check exactly that, that this `fv` meets some criteria that is presently
        // being used. Note that in `None`, we default to `no`, otherwise everything would
        // unfold (unless we had all criteria present at once, which is unlikely)

        comb_or [
         (match cfg.steps.unfold_only with
          | None -> no
          | Some lids -> yesno <| BU.for_some (fv_eq_lid fv) lids)
        ;(match cfg.steps.unfold_attr with
          | None -> no
          | Some lids -> yesno <| BU.for_some (fun at -> BU.for_some (fun lid -> U.is_fvar lid at) lids) attrs)
        ;(match cfg.steps.unfold_fully with
          | None -> no
          | Some lids -> fullyno <| BU.for_some (fv_eq_lid fv) lids)
        ]

    // Nothing special, just check the depth
    | _ ->
        log_unfolding cfg (fun () -> BU.print3 "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                                               (Print.fv_to_string fv)
                                               (Print.delta_depth_to_string fv.fv_delta)
                                               (FStar.Common.string_of_list Env.string_of_delta_level cfg.delta_level));
        yesno <| (cfg.delta_level |> BU.for_some (function
             | NoDelta -> false
             | InliningDelta
             | Eager_unfolding_only -> true
             | Unfold l -> Common.delta_depth_greater_than (Env.delta_depth_of_fv cfg.tcenv fv) l))
    in
    log_unfolding cfg (fun () -> BU.print3 "should_unfold: For %s (%s), unfolding res = %s\n"
                    (Print.fv_to_string fv)
                    (Range.string_of_range (S.range_of_fv fv))
                    (string_of_res res)
                    );
    match res with
    | false, _, _ -> Should_unfold_no
    | true, false, false -> Should_unfold_yes
    | true, true, false -> Should_unfold_fully
    | true, false, true -> Should_unfold_reify
    | _ ->
      failwith <| BU.format1 "Unexpected unfolding result: %s" (string_of_res res)

let decide_unfolding cfg env stack rng fv qninfo (* : option<(cfg * stack)> *) =
    let res =
        should_unfold cfg (fun cfg -> should_reify cfg stack) fv qninfo
    in
    match res with
    | Should_unfold_no ->
        // No unfolding
        None
    | Should_unfold_yes ->
        // Usual unfolding, no change to cfg or stack
        Some (cfg, stack)
    | Should_unfold_fully ->
        // Unfolding fully, use new cfg with more steps and keep old one in stack
        let cfg' =
            { cfg with steps = { cfg.steps with
                       unfold_only  = None
                     ; unfold_fully = None
                     ; unfold_attr  = None
                     ; unfold_until = Some delta_constant } } in

        (* Take care to not change the stack's head if there's a universe
         * instantiation, but we do need to keep the old cfg. *)
        (* This is ugly, and a recurring problem, but I'm working around it for now *)
        let stack' = match stack with
                     | UnivArgs (us, r) :: stack' -> UnivArgs (us, r) :: Cfg cfg :: stack'
                     | stack' -> Cfg cfg :: stack'
        in
        Some (cfg', stack')

    | Should_unfold_reify ->
        // Reifying, adding a reflect on the stack to cancel the reify
        // NB: The fv in the Const_reflect is bogus, it'll be ignored anyway
        let ref = S.mk (Tm_constant (Const_reflect (S.lid_of_fv fv)))
                       None Range.dummyRange in
        Some (cfg, App (env, ref, None, Range.dummyRange) :: stack)

let rec norm : cfg -> env -> stack -> term -> term =
    fun cfg env stack t ->
        let t =
            if cfg.debug.norm_delayed
            then (match t.n with
                  | Tm_delayed _ ->
                    BU.print1 "NORM delayed: %s\n" (Print.term_to_string t)
                  | _ -> ());
            compress t
        in
        log cfg (fun () ->
          BU.print5 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                                        (Print.tag_of_term t)
                                        (BU.string_of_bool (cfg.steps.no_full_norm))
                                        (Print.term_to_string t)
                                        (BU.string_of_int (List.length env))
                                        (stack_to_string (fst <| firstn 4 stack)));
        log_cfg cfg (fun () -> BU.print1 ">>> cfg = %s\n" (cfg_to_string cfg));
        match t.n with
          | Tm_unknown
          | Tm_constant _
          | Tm_name _

          | Tm_lazy _

          //these three are just constructors; no delta steps can apply
          | Tm_fvar({ fv_qual = Some Data_ctor })
          | Tm_fvar({ fv_qual = Some (Record_ctor _) }) ->
            log_unfolding cfg (fun () -> BU.print1 ">>> Tm_fvar case 0 for %s\n" (Print.term_to_string t));
            rebuild cfg env stack t

          | Tm_fvar fv ->
            let lid = S.lid_of_fv fv in
            let qninfo = Env.lookup_qname cfg.tcenv lid in
            begin
            match Env.delta_depth_of_qninfo fv qninfo with
            | Some (Delta_constant_at_level 0) ->
              log_unfolding cfg (fun () -> BU.print1 ">>> Tm_fvar case 0 for %s\n" (Print.term_to_string t));
              rebuild cfg env stack t
            | _ ->
              match decide_unfolding cfg env stack t.pos fv qninfo with
              | Some (cfg, stack) -> do_unfold_fv cfg env stack t qninfo fv
              | None -> rebuild cfg env stack t
            end

          | Tm_quoted _ ->
            rebuild cfg env stack (closure_as_term cfg env t)

          | Tm_app(hd, args)
            when not (cfg.steps.no_full_norm)
              && is_norm_request hd args
              && not (Ident.lid_equals cfg.tcenv.curmodule PC.prims_lid) ->
            if cfg.debug.print_normalized
            then BU.print_string "Potential norm request ... \n";
            let cfg' = { cfg with steps = { cfg.steps with unfold_only = None
                                                         ; unfold_fully = None
                                                         ; do_not_unfold_pure_lets = false };
                                  delta_level=[Unfold delta_constant];
                                  normalize_pure_lets=true} in
            begin
            match get_norm_request cfg (norm cfg' env []) args with
            | None -> //just normalize it as a normal application
              if cfg.debug.print_normalized
              then BU.print_string "Norm request None ... \n";
              let stack =
                stack |>
                List.fold_right
                  (fun (a, aq) stack -> Arg (Clos(env, a, BU.mk_ref None, false),aq,t.pos)::stack)
                  args
              in
              log cfg  (fun () -> BU.print1 "\tPushed %s arguments\n" (string_of_int <| List.length args));
              norm cfg env stack hd

            | Some (s, tm) when is_nbe_request s ->
              if cfg.debug.print_normalized
              then BU.print1 "Starting NBE request on %s ... \n" (Print.term_to_string tm);
              let tm' = closure_as_term cfg env tm in
              let start = BU.now() in
              let tm_norm = nbe_eval cfg s tm' in
              let fin = BU.now () in
              if cfg.debug.print_normalized
              then BU.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                   (BU.string_of_int (snd (BU.time_diff start fin)))
                   (Print.term_to_string tm')
                   (Print.term_to_string tm_norm);

              norm cfg env stack tm_norm
              (* Zoe, NS:
                 This call to norm is needed to evaluate the continuation with the fully evaluated tm_norm
                 But, it's potentially wasteful, since norm will attempt to normalize tm_norm again.
                 In cases where tm_norm is small (e.g., 2), this is not a big deal;
                 but in general, this may incur a large unnecessary traversal
               *)
            | Some (s, tm) ->
              if cfg.debug.print_normalized
              then BU.print1 "Starting norm request on %s ... \n" (Print.term_to_string tm);
              let delta_level =
                if s |> BU.for_some (function UnfoldUntil _ | UnfoldOnly _ | UnfoldFully _ -> true | _ -> false)
                then [Unfold delta_constant]
                else [NoDelta] in
              let cfg' = {cfg with steps = ({ to_fsteps s with in_full_norm_request=true})
                               ; delta_level = delta_level
                               ; normalize_pure_lets = true } in
              let stack' =
                let tail = (Cfg cfg)::stack in
                if cfg.debug.print_normalized
                then (Debug(t, BU.now())::tail)
                else tail in
              norm cfg' env stack' tm
            end

          | Tm_type u ->
            let u = norm_universe cfg env u in
            rebuild cfg env stack (mk (Tm_type u) t.pos)

          | Tm_uinst(t', us) ->
            if cfg.steps.erase_universes
            then norm cfg env stack t'
            else let us = UnivArgs(List.map (norm_universe cfg env) us, t.pos) in
                 let stack = us::stack in
                 norm cfg env stack t'

          | Tm_bvar x ->
            begin match lookup_bvar env x with
                | Univ _ -> failwith "Impossible: term variable is bound to a universe"
                | Dummy -> failwith "Term variable not found"
                | Clos(env, t0, r, fix) ->
                   if not fix || cfg.steps.zeta
                   then match !r with
                        | Some (env, t') ->
                            log cfg  (fun () -> BU.print2 "Lazy hit: %s cached to %s\n" (Print.term_to_string t) (Print.term_to_string t'));
                            if maybe_weakly_reduced t'
                            then match stack with
                                 | [] when cfg.steps.weak || cfg.steps.compress_uvars ->
                                   rebuild cfg env stack t'
                                 | _ -> norm cfg env stack t'
                            else rebuild cfg env stack t'
                        | None -> norm cfg env (MemoLazy r::stack) t0
                   else norm cfg env stack t0 //Fixpoint steps are excluded; so don't take the recursive knot
            end

          | Tm_abs(bs, body, lopt) ->
            begin match stack with
                | UnivArgs _::_ ->
                  failwith "Ill-typed term: universes cannot be applied to term abstraction"

                | Arg(c, _, _)::stack_rest ->
                  begin match c with
                    | Univ _ -> //universe variables do not have explicit binders
                      norm cfg ((None,c)::env) stack_rest t

                    | _ ->
                     (* Note: we peel off one application at a time.
                              An optimization to attempt would be to push n-args are once,
                              and try to pop all of them at once, in the common case of a full application.
                      *)
                      begin match bs with
                        | [] -> failwith "Impossible"
                        | [b] ->
                          log cfg  (fun () -> BU.print1 "\tShifted %s\n" (closure_to_string c));
                          norm cfg ((Some b, c) :: env) stack_rest body
                        | b::tl ->
                          log cfg  (fun () -> BU.print1 "\tShifted %s\n" (closure_to_string c));
                          let body = mk (Tm_abs(tl, body, lopt)) t.pos in
                          norm cfg ((Some b, c) :: env) stack_rest body
                      end
                  end

                // TODO: GM: This bit is shady, and it breaks unfold_fully across lambdas
                | Cfg cfg :: stack ->
                  norm cfg env stack t

                | MemoLazy r :: stack ->
                  set_memo cfg r (env, t); //We intentionally do not memoize the strong normal form; only the WHNF
                  log cfg  (fun () -> BU.print1 "\tSet memo %s\n" (Print.term_to_string t));
                  norm cfg env stack t

                | Match _::_
                | Debug _::_
                | Meta _::_
                | Let _ :: _
                | App _ :: _
                | Abs _ :: _
                | [] ->
                  if cfg.steps.weak
                  then let t = closure_as_term cfg env t in
                       rebuild cfg env stack t
                  else let bs, body, opening = open_term' bs body in
                       let env' = bs |> List.fold_left (fun env _ -> dummy::env) env in
                       let lopt = match lopt with
                        | Some rc ->
                          let rct =
                            if cfg.steps.check_no_uvars
                            then BU.map_opt rc.residual_typ (fun t -> norm cfg env' [] (SS.subst opening t))
                            else BU.map_opt rc.residual_typ (SS.subst opening) in
                          Some ({rc with residual_typ=rct})
                        | _ -> lopt in
                       log cfg  (fun () -> BU.print1 "\tShifted %s dummies\n" (string_of_int <| List.length bs));
                       let stack = (Cfg cfg)::stack in
                       let cfg = { cfg with strong = true } in
                       norm cfg env' (Abs(env, bs, env', lopt, t.pos)::stack) body
            end

          | Tm_app(head, args) ->
            let stack = stack |> List.fold_right (fun (a, aq) stack -> Arg (Clos(env, a, BU.mk_ref None, false),aq,t.pos)::stack) args in
            log cfg  (fun () -> BU.print1 "\tPushed %s arguments\n" (string_of_int <| List.length args));
            norm cfg env stack head

          | Tm_refine(x, f) -> //non tail-recursive; the alternative is to keep marks on the stack to rebuild the term ... but that's very heavy
            if cfg.steps.weak
            then match env, stack with
                    | [], [] -> //TODO: Make this work in general!
                      let t_x = norm cfg env [] x.sort in
                      let t = mk (Tm_refine({x with sort=t_x}, f)) t.pos in
                      rebuild cfg env stack t
                    | _ -> rebuild cfg env stack (closure_as_term cfg env t)
            else let t_x = norm cfg env [] x.sort in
                 let closing, f = open_term [(x, None)] f in
                 let f = norm cfg (dummy::env) [] f in
                 let t = mk (Tm_refine({x with sort=t_x}, close closing f)) t.pos in
                 rebuild cfg env stack t

          | Tm_arrow(bs, c) ->
            if cfg.steps.weak
            then rebuild cfg env stack (closure_as_term cfg env t)
            else let bs, c = open_comp bs c in
                 let c = norm_comp cfg (bs |> List.fold_left (fun env _ -> dummy::env) env) c in
                 let t = arrow (norm_binders cfg env bs) c in
                 rebuild cfg env stack t

          | Tm_ascribed(t1, (tc, tacopt), l) when cfg.steps.unascribe ->
            norm cfg env stack t1

          | Tm_ascribed(t1, (tc, tacopt), l) ->
            begin match stack with
              | Match _ :: _
              | Arg _ :: _
              | App (_, {n=Tm_constant FC.Const_reify}, _, _) :: _
              | MemoLazy _ :: _ when cfg.steps.beta ->
                log cfg  (fun () -> BU.print_string "+++ Dropping ascription \n");
                norm cfg env stack t1 //ascriptions should not block reduction
              | _ ->
                (* Drops stack *)
                log cfg  (fun () -> BU.print_string "+++ Keeping ascription \n");
                let t1 = norm cfg env [] t1 in
                log cfg  (fun () -> BU.print_string "+++ Normalizing ascription \n");
                let tc = match tc with
                    | Inl t -> Inl (norm cfg env [] t)
                    | Inr c -> Inr (norm_comp cfg env c) in
                let tacopt = BU.map_opt tacopt (norm cfg env []) in
                match stack with
                | Cfg cfg :: stack ->
                  let t = mk (Tm_ascribed(U.unascribe t1, (tc, tacopt), l)) t.pos in
                  norm cfg env stack t
                | _ ->
                  rebuild cfg env stack (mk (Tm_ascribed(U.unascribe t1, (tc, tacopt), l)) t.pos)
            end

          | Tm_match(head, branches) ->
            let stack = Match(env, branches, cfg, t.pos)::stack in
            if cfg.steps.iota
                && cfg.steps.weakly_reduce_scrutinee
                && not cfg.steps.weak
            then let cfg' = { cfg with steps= { cfg.steps with weak = true } } in
                 norm cfg' env (Cfg cfg :: stack) head
            else norm cfg env stack head

          | Tm_let((b, lbs), lbody) when is_top_level lbs && cfg.steps.compress_uvars ->
            let lbs = lbs |> List.map (fun lb ->
              let openings, lbunivs = Subst.univ_var_opening lb.lbunivs in
              let cfg = { cfg with tcenv = Env.push_univ_vars cfg.tcenv lbunivs } in
              let norm t = Subst.close_univ_vars lbunivs (norm cfg env [] (Subst.subst openings t)) in
              let lbtyp = norm lb.lbtyp in
              let lbdef = norm lb.lbdef in
              { lb with lbunivs = lbunivs; lbtyp = lbtyp; lbdef = lbdef }
            ) in

            rebuild cfg env stack (mk (Tm_let ((b, lbs), lbody)) t.pos)

          | Tm_let((_, {lbname=Inr _}::_), _) -> //this is a top-level let binding; nothing to normalize
            rebuild cfg env stack t

          | Tm_let((false, [lb]), body) ->
            let n = TypeChecker.Env.norm_eff_name cfg.tcenv lb.lbeff in
            if not (cfg.steps.do_not_unfold_pure_lets) //we're allowed to do some delta steps, and ..
            && ((cfg.steps.pure_subterms_within_computations &&
                 U.has_attribute lb.lbattrs PC.inline_let_attr)        //1. we're extracting, and it's marked @inline_let
             || (U.is_pure_effect n && (cfg.normalize_pure_lets        //Or, 2. it's pure and we either not extracting, or
                                        || U.has_attribute lb.lbattrs PC.inline_let_attr)) //it's marked @inline_let
             || (U.is_ghost_effect n &&                                //Or, 3. it's ghost and we're not extracting
                    not (cfg.steps.pure_subterms_within_computations)))
            then let binder = S.mk_binder (BU.left lb.lbname) in
                 let env = (Some binder, Clos(env, lb.lbdef, BU.mk_ref None, false))::env in
                 log cfg (fun () -> BU.print_string "+++ Reducing Tm_let\n");
                 norm cfg env stack body
            else if cfg.steps.weak
            then (log cfg (fun () -> BU.print_string "+++ Not touching Tm_let\n");
                  rebuild cfg env stack (closure_as_term cfg env t))
            else let bs, body = Subst.open_term [lb.lbname |> BU.left |> S.mk_binder] body in
                 log cfg (fun () -> BU.print_string "+++ Normalizing Tm_let -- type");
                 let ty = norm cfg env [] lb.lbtyp in
                 let lbname =
                    let x = fst (List.hd bs) in
                    Inl ({x with sort=ty}) in
                 log cfg (fun () -> BU.print_string "+++ Normalizing Tm_let -- definiens\n");
                 let lb = {lb with lbname=lbname;
                                   lbtyp=ty;
                                   lbdef=norm cfg env [] lb.lbdef} in
                 let env' = bs |> List.fold_left (fun env _ -> dummy::env) env in
                 let stack = (Cfg cfg)::stack in
                 let cfg = { cfg with strong = true } in
                 log cfg (fun () -> BU.print_string "+++ Normalizing Tm_let -- body\n");
                 norm cfg env' (Let(env, bs, lb, t.pos)::stack) body

          | Tm_let((true, lbs), body)
                when cfg.steps.compress_uvars
                  || ((not cfg.steps.zeta) &&
                      cfg.steps.pure_subterms_within_computations) -> //no fixpoint reduction allowed
            let lbs, body = Subst.open_let_rec lbs body in
            let lbs = List.map (fun lb ->
                let ty = norm cfg env [] lb.lbtyp in
                let lbname = Inl ({BU.left lb.lbname with sort=ty}) in
                let xs, def_body, lopt = U.abs_formals lb.lbdef in
                let xs = norm_binders cfg env xs in
                let env = List.map (fun _ -> dummy) lbs
                        @ List.map (fun _ -> dummy) xs
                        @ env in
                let def_body = norm cfg env [] def_body in
                let lopt =
                  match lopt with
                  | Some rc -> Some ({rc with residual_typ=BU.map_opt rc.residual_typ (norm cfg env [])})
                  | _ -> lopt in
                let def = U.abs xs def_body lopt in
                { lb with lbname = lbname;
                          lbtyp = ty;
                          lbdef = def}) lbs in
            let env' = List.map (fun _ -> dummy) lbs @ env in
            let body = norm cfg env' [] body in
            let lbs, body = Subst.close_let_rec lbs body in
            let t = {t with n=Tm_let((true, lbs), body)} in
            rebuild cfg env stack t

          | Tm_let(lbs, body) when not cfg.steps.zeta -> //no fixpoint reduction allowed
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
                    let bv = {left lb.lbname with index=i} in
                    let f_i = Syntax.bv_to_tm bv in
                    let fix_f_i = mk (Tm_let(lbs, f_i)) t.pos in
                    let memo = BU.mk_ref None in
                    let rec_env = (None, Clos(env, fix_f_i, memo, true))::rec_env in
                    rec_env, memo::memos, i + 1) (snd lbs) (env, [], 0) in
            let _ = List.map2 (fun lb memo -> memo := Some (rec_env, lb.lbdef)) (snd lbs) memos in //tying the knot
            let body_env = List.fold_right (fun lb env -> (None, Clos(rec_env, lb.lbdef, BU.mk_ref None, false))::env)
                               (snd lbs) env in
            norm cfg body_env stack body

          | Tm_meta (head, m) ->
            log cfg (fun () -> BU.print1 ">> metadata = %s\n" (Print.metadata_to_string m));
            begin match m with
              | Meta_monadic (m, t) ->
                reduce_impure_comp cfg env stack head (Inl m) t

              | Meta_monadic_lift (m, m', t) ->
                reduce_impure_comp cfg env stack head (Inr (m, m')) t

              | _ ->
                if cfg.steps.unmeta
                then norm cfg env stack head
                else begin match stack with
                  | _::_ ->
                    begin match m with
                      | Meta_labeled(l, r, _) ->
                        (* meta doesn't block reduction, but we need to put the label back *)
                        norm cfg env (Meta(env,m,r)::stack) head

                      | Meta_pattern args ->
                          let args = norm_pattern_args cfg env args in
                          norm cfg env (Meta(env,Meta_pattern args, t.pos)::stack) head //meta doesn't block reduction, but we need to put the label back

                      | _ ->
                          norm cfg env stack head //meta doesn't block reduction
                    end
                  | [] ->
                    let head = norm cfg env [] head in
                    let m = match m with
                        | Meta_pattern args ->
                            Meta_pattern (norm_pattern_args cfg env args)
                        | _ -> m in
                    let t = mk (Tm_meta(head, m)) t.pos in
                    rebuild cfg env stack t
                end
        end //Tm_meta

        | Tm_delayed _ ->
          let t = SS.compress t in
          norm cfg env stack t

        | Tm_uvar _ ->
          let t = SS.compress t in
          match t.n with
          | Tm_uvar _ ->
            if cfg.steps.check_no_uvars
            then failwith (BU.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                                    (Range.string_of_range t.pos)
                                    (Print.term_to_string t))
            else rebuild cfg env stack (inline_closure_env cfg env [] t)

          | _ ->
            norm cfg env stack t

and do_unfold_fv cfg env stack (t0:term) (qninfo : qninfo) (f:fv) : term =
    match Env.lookup_definition_qninfo cfg.delta_level f.fv_name.v qninfo with
       | None ->
         log_unfolding cfg (fun () -> // printfn "delta_level = %A, qninfo=%A" cfg.delta_level qninfo;
                                      BU.print1 " >> Tm_fvar case 2 for %s\n" (Print.fv_to_string f));
         rebuild cfg env stack t0

       | Some (us, t) ->
         begin
         log_unfolding cfg (fun () -> BU.print2 " >> Unfolded %s to %s\n"
                       (Print.term_to_string t0) (Print.term_to_string t));
         // preserve the range info on the returned term
         let t =
           if cfg.steps.unfold_until = Some delta_constant
           //we're really trying to compute here; no point propagating range information
           //which can be expensive
           then t
           else Subst.set_use_range t0.pos t
         in
         let n = List.length us in
         if n > 0
         then match stack with //universe beta reduction
                | UnivArgs(us', _)::stack ->
                  if Env.debug cfg.tcenv <| Options.Other "univ_norm" then
                      List.iter (fun x -> BU.print1 "Univ (normalizer) %s\n" (Print.univ_to_string x)) us'
                  else ();
                  let env = us' |> List.fold_left (fun env u -> (None, Univ u)::env) env in
                  norm cfg env stack t
                | _ when cfg.steps.erase_universes || cfg.steps.allow_unbound_universes ->
                  norm cfg env stack t
                | _ -> failwith (BU.format1 "Impossible: missing universe instantiation on %s" (Print.lid_to_string f.fv_name.v))
         else norm cfg env stack t
         end

and reduce_impure_comp cfg env stack (head : term) // monadic term
                                     (m : either<monad_name,(monad_name * monad_name)>)
                                        // relevant monads.
                                        // Inl m - this is a Meta_monadic with monad m
                                        // Inr (m, m') - this is a Meta_monadic_lift with monad m
                                     (t : typ) // annotated type in the Meta
                                     : term =
    (* We have an impure computation, and we aim to perform any pure      *)
    (* steps within that computation.                                     *)

    (* This scenario arises primarily as we extract (impure) programs and *)
    (* partially evaluate them before extraction, as an optimization.     *)

    (* First, we reduce **the type annotation** t with an empty stack (as *)
    (* it's not applied to anything)                                      *)

    (* Then, we reduce the monadic computation `head`, in a stack marked  *)
    (* with a Meta_monadic, indicating that this reduction should         *)
    (* not consume any arguments on the stack. `rebuild` will notice      *)
    (* the Meta_monadic marker and reconstruct the computation after      *)
    (* normalization.                                                     *)
    let t = norm cfg env [] t in
    let stack = (Cfg cfg)::stack in
    let cfg =
      if cfg.steps.pure_subterms_within_computations
      then
        let new_steps = [PureSubtermsWithinComputations;
                         Primops;
                         AllowUnboundUniverses;
                         EraseUniverses;
                         Exclude Zeta;
                         Inlining]
        in { cfg with
               steps = List.fold_right fstep_add_one new_steps cfg.steps;
               delta_level = [Env.InliningDelta; Env.Eager_unfolding_only]
           }
      else cfg
    in
    (* monadic annotations don't block reduction, but we need to put the label back *)
    let metadata = match m with
                   | Inl m -> Meta_monadic (m, t)
                   | Inr (m, m') -> Meta_monadic_lift (m, m', t)
    in
    norm cfg env (Meta(env,metadata, head.pos)::stack) head

and do_reify_monadic fallback cfg env stack (head : term) (m : monad_name) (t : typ) : term =
    (* Precondition: the stack head is an App (reify, ...) *)
    begin match stack with
    | App (_, {n=Tm_constant FC.Const_reify}, _, _) :: _ -> ()
    | _ -> failwith (BU.format1 "INTERNAL ERROR: do_reify_monadic: bad stack: %s" (stack_to_string stack))
    end;
    let head0 = head in
    let head = U.unascribe head in
    log cfg (fun () -> BU.print2 "Reifying: (%s) %s\n" (Print.tag_of_term head) (Print.term_to_string head));
    let head = U.unmeta_safe head in
    match (SS.compress head).n with
    | Tm_let ((false, [lb]), body) ->
      (* ****************************************************************************)
      (* Monadic binding                                                            *)
      (*                                                                            *)
      (* This is reify (M.bind e1 (fun x -> e2)) which is elaborated to             *)
      (*                                                                            *)
      (*        M.bind_repr (reify e1) (fun x -> reify e2)                          *)
      (*                                                                            *)
      (* ****************************************************************************)
      let ed = Env.get_effect_decl cfg.tcenv (Env.norm_eff_name cfg.tcenv m) in
      let _, bind_repr = ed.bind_repr in
      begin match lb.lbname with
        | Inr _ -> failwith "Cannot reify a top-level let binding"
        | Inl x ->

          (* [is_return e] returns [Some e'] if [e] is a lift from Pure of [e'], [None] otherwise *)
          let is_return e =
            match (SS.compress e).n with
            | Tm_meta(e, Meta_monadic(_, _)) ->
              begin match (SS.compress e).n with
                | Tm_meta(e, Meta_monadic_lift(_, msrc, _)) when U.is_pure_effect msrc ->
                    Some (SS.compress e)
                | _ -> None
              end
           | _ -> None
          in

          match is_return lb.lbdef with
          (* We are in the case where [head] = [bind (return e) (fun x -> body)] *)
          (* which can be optimised to a non-monadic let-binding [let x = e in body] *)
          | Some e ->
            let lb = {lb with lbeff=PC.effect_PURE_lid; lbdef=e} in
            norm cfg env (List.tl stack) (S.mk (Tm_let((false, [lb]), U.mk_reify body)) None head.pos)
          | None ->
            if (match is_return body with Some ({n=Tm_bvar y}) -> S.bv_eq x y | _ -> false)
            then
              (* We are in the case where [head] = [bind e (fun x -> return x)] *)
              (* which can be optimised to just keeping normalizing [e] with a reify on the stack *)
              norm cfg env stack lb.lbdef
            else (
              (* TODO : optimize [bind (bind e1 e2) e3] into [bind e1 (bind e2 e3)] *)
              (* Rewriting binds in that direction would be better for exception-like monad *)
              (* since we wouldn't rematch on an already raised exception *)
              let rng = head.pos in

              let head = U.mk_reify <| lb.lbdef in
              let body = U.mk_reify <| body in
              (* TODO : Check that there is no sensible cflags to pass in the residual_comp *)
              let body_rc = {
                residual_effect=m;
                residual_flags=[];
                residual_typ=Some t
              } in
              let body = S.mk (Tm_abs([S.mk_binder x], body, Some body_rc)) None body.pos in
              let close = closure_as_term cfg env in
              let bind_inst = match (SS.compress bind_repr).n with
                | Tm_uinst (bind, [_ ; _]) ->
                    S.mk (Tm_uinst (bind, [ cfg.tcenv.universe_of cfg.tcenv (close lb.lbtyp)
                                          ; cfg.tcenv.universe_of cfg.tcenv (close t)]))
                    None rng
                | _ -> failwith "NIY : Reification of indexed effects"
              in
              let maybe_range_arg =
                if BU.for_some (U.attr_eq U.dm4f_bind_range_attr) ed.eff_attrs
                then [as_arg (embed_simple EMB.e_range lb.lbpos lb.lbpos);
                      as_arg (embed_simple EMB.e_range body.pos body.pos)]
                else []
              in
              let reified = S.mk (Tm_app(bind_inst, [
                  (* a, b *)
                  as_arg lb.lbtyp; as_arg t] @
                  maybe_range_arg @ [
                  (* wp_head, head--the term shouldn't depend on wp_head *)
                  as_arg S.tun; as_arg head;
                  (* wp_body, body--the term shouldn't depend on wp_body *)
                  as_arg S.tun; as_arg body]))
                None rng
              in
              log cfg (fun () -> BU.print2 "Reified (1) <%s> to %s\n" (Print.term_to_string head0) (Print.term_to_string reified));
              norm cfg env (List.tl stack) reified
            )
      end
    | Tm_app (head_app, args) ->
        (* ****************************************************************************)
        (* Monadic application                                                        *)
        (*                                                                            *)
        (* The typechecker should have turned any monadic application into a serie of *)
        (* let-bindings (binding explicitly any monadic term)                         *)
        (*    let x0 = head in let x1 = arg0 in ... let xn = argn in x0 x1 ... xn     *)
        (*                                                                            *)
        (* which wil be ultimately reified to                                         *)
        (*     bind (reify head) (fun x0 ->                                           *)
        (*            bind (reify arg0) (fun x1 -> ... (fun xn -> x0 x1 .. xn) ))     *)
        (*                                                                            *)
        (* If head is an action then it is unfolded otherwise the                     *)
        (* resulting application is reified again                                     *)
        (* ****************************************************************************)

        (* Checking that the typechecker did its job correctly and hoisted all impure *)
        (* terms to explicit let-bindings (see TcTerm, monadic_application) *)
        (* GM: Now only when --defensive is on, so we don't waste cycles otherwise *)
        if Options.defensive () then begin
          let is_arg_impure (e,q) =
            match (SS.compress e).n with
            | Tm_meta (e0, Meta_monadic_lift(m1, m2, t')) -> not (U.is_pure_effect m1)
            | _ -> false
          in
          if BU.for_some is_arg_impure ((as_arg head_app)::args) then
            Errors.log_issue head.pos
                             (Errors.Warning_Defensive,
                              BU.format1 "Incompatibility between typechecker and normalizer; \
                                          this monadic application contains impure terms %s\n"
                                          (Print.term_to_string head))
        end;

        (* GM: I'm really suspicious of this code, I tried to change it the least
         * when trying to fixing it but these two seem super weird. Why 2 of them?
         * Why is it not calling rebuild? I'm gonna keep it for now. *)
        let fallback1 () =
            log cfg (fun () -> BU.print2 "Reified (2) <%s> to %s\n" (Print.term_to_string head0) "");
            norm cfg env (List.tl stack) (U.mk_reify head)
        in
        let fallback2 () =
            log cfg (fun () -> BU.print2 "Reified (3) <%s> to %s\n" (Print.term_to_string head0) "");
            norm cfg env (List.tl stack) (mk (Tm_meta (head, Meta_monadic(m, t))) head0.pos)
        in

        (* This application case is only interesting for fully-applied dm4f actions. Otherwise,
         * we just continue rebuilding. *)
        begin match (U.un_uinst head_app).n with
        | Tm_fvar fv ->
            let lid = S.lid_of_fv fv in
            let qninfo = Env.lookup_qname cfg.tcenv lid in
            if not (Env.is_action cfg.tcenv lid) then fallback1 () else

            (* GM: I think the action *must* be fully applied at this stage
             * since we were triggered into this function by a Meta_monadic
             * annotation. So we don't check anything. *)

            (* Fallback if it does not have a definition. This happens,
             * but I'm not sure why. *)
            if Option.isNone (Env.lookup_definition_qninfo cfg.delta_level fv.fv_name.v qninfo)
            then fallback2 ()
            else

            (* Turn it info (reify head) args, then do_unfold_fv will kick in on the head *)
            let t = S.mk_Tm_app (U.mk_reify head_app) args None t.pos in
            norm cfg env (List.tl stack) t

        | _ ->
            fallback1 ()
        end

    // Doubly-annotated effect.. just take the outmost one. (unsure..)
    | Tm_meta(e, Meta_monadic _) ->
        do_reify_monadic fallback cfg env stack e m t

    | Tm_meta(e, Meta_monadic_lift (msrc, mtgt, t')) ->
        let lifted = reify_lift cfg e msrc mtgt (closure_as_term cfg env t') in
        log cfg (fun () -> BU.print1 "Reified lift to (2): %s\n" (Print.term_to_string lifted));
        norm cfg env (List.tl stack) lifted

    | Tm_match(e, branches) ->
      (* Commutation of reify with match, note that the scrutinee should never be effectful    *)
      (* (should be checked at typechecking and elaborated with an explicit binding if needed) *)
      (* reify (match e with p -> e') ~> match e with p -> reify e' *)
      let branches = branches |> List.map (fun (pat, wopt, tm) -> pat, wopt, U.mk_reify tm) in
      let tm = mk (Tm_match(e, branches)) head.pos in
      norm cfg env (List.tl stack) tm

    | _ ->
      fallback ()

(* Reifies the lifting of the term [e] of type [t] from computational  *)
(* effect [m] to computational effect [m'] using lifting data in [env] *)
and reify_lift cfg e msrc mtgt t : term =
  let env = cfg.tcenv in
  log cfg (fun () -> BU.print3 "Reifying lift %s -> %s: %s\n"
        (Ident.string_of_lid msrc) (Ident.string_of_lid mtgt) (Print.term_to_string e));
  (* check if the lift is concrete, if so replace by its definition on terms *)
  (* if msrc is PURE or Tot we can use mtgt.return *)
  if U.is_pure_effect msrc || U.is_div_effect msrc
  then
    let ed = Env.get_effect_decl env (Env.norm_eff_name cfg.tcenv mtgt) in
    let _, return_repr = ed.return_repr in
    let return_inst = match (SS.compress return_repr).n with
        | Tm_uinst(return_tm, [_]) ->
            S.mk (Tm_uinst (return_tm, [env.universe_of env t])) None e.pos
        | _ -> failwith "NIY : Reification of indexed effects"
    in
    S.mk (Tm_app(return_inst, [as_arg t ; as_arg e])) None e.pos
  else
    match Env.monad_leq env msrc mtgt with
    | None ->
      failwith (BU.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                            (Ident.text_of_lid msrc)
                            (Ident.text_of_lid mtgt))
    | Some {mlift={mlift_term=None}} ->
      failwith (BU.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                            (Ident.text_of_lid msrc)
                            (Ident.text_of_lid mtgt))
    | Some {mlift={mlift_term=Some lift}} ->
      (* We don't have any reasonable wp to provide so we just pass unknow *)
      (* Usually the wp is only necessary to typecheck, so this should not *)
      (* create a big issue. *)
      lift (env.universe_of env t) t S.tun (U.mk_reify e)
      (* We still eagerly unfold the lift to make sure that the Unknown is not kept stuck on a folded application *)
      (* let cfg = *)
      (*   { steps=[Exclude Iota ; Exclude Zeta; Inlining ; Eager_unfolding ; UnfoldUntil Delta_constant]; *)
      (*     tcenv=env; *)
      (*     delta_level=[Env.Unfold Delta_constant ; Env.Eager_unfolding_only ; Env.Inlining ] } *)
      (* in *)
      (* norm cfg [] [] (lift t S.tun (U.mk_reify e)) *)

and norm_pattern_args cfg env args =
    (* Drops stack *)
    args |> List.map (List.map (fun (a, imp) -> norm cfg env [] a, imp))

and norm_comp : cfg -> env -> comp -> comp =
    fun cfg env comp ->
        log cfg (fun () -> BU.print2 ">>> %s\nNormComp with with %s env elements"
                                        (Print.comp_to_string comp)
                                        (BU.string_of_int (List.length env)));
        match comp.n with
            | Total (t, uopt) ->
              let t = norm cfg env [] t in
              let uopt = match uopt with
                         | Some u -> Some <| norm_universe cfg env u
                         | None -> None
              in
              { comp with n = Total (t, uopt) }

            | GTotal (t, uopt) ->
              let t = norm cfg env [] t in
              let uopt = match uopt with
                         | Some u -> Some <| norm_universe cfg env u
                         | None -> None
              in
              { comp with n = GTotal (t, uopt) }

            | Comp ct ->
              let norm_args = List.mapi (fun idx (a, i) -> (norm cfg env [] a, i)) in
              let effect_args = norm_args ct.effect_args in
              let flags = ct.flags |> List.map (function DECREASES t -> DECREASES (norm cfg env [] t) | f -> f) in
              let comp_univs = List.map (norm_universe cfg env) ct.comp_univs in
              let result_typ = norm cfg env [] ct.result_typ in
              { comp with n = Comp ({ct with comp_univs  = comp_univs;
                                             result_typ  = result_typ;
                                             effect_args = effect_args;
                                             flags       = flags}) }

and norm_binder (cfg:Cfg.cfg) (env:env) (b:binder) : binder =
    let (x, imp) = b in
    let x = { x with sort = norm cfg env [] x.sort } in
    let imp = match imp with
              | Some (S.Meta t) -> Some (S.Meta (closure_as_term cfg env t))
              | i -> i
    in
    (x, imp)

and norm_binders : cfg -> env -> binders -> binders =
    fun cfg env bs ->
        let nbs, _ = List.fold_left (fun (nbs', env) b ->
            let b = norm_binder cfg env b in
            (b::nbs', dummy::env) (* crossing a binder, so shift environment *))
            ([], env)
            bs in
        List.rev nbs

and norm_lcomp_opt : cfg -> env -> option<residual_comp> -> option<residual_comp> =
    fun cfg env lopt ->
        match lopt with
        | Some rc ->
          let flags = filter_out_lcomp_cflags rc.residual_flags in
          Some ({rc with residual_typ=BU.map_opt rc.residual_typ (norm cfg env [])})
       | _ -> lopt

and maybe_simplify cfg env stack tm =
    let tm' = maybe_simplify_aux cfg env stack tm in
    if cfg.debug.b380
    then BU.print3 "%sSimplified\n\t%s to\n\t%s\n"
                   (if cfg.steps.simplify then "" else "NOT ")
                   (Print.term_to_string tm) (Print.term_to_string tm');
    tm'

and norm_cb cfg : EMB.norm_cb = function
    | Inr x -> norm cfg [] [] x
    | Inl l ->
        //FStar.Syntax.DsEnv.try_lookup_lid cfg.tcenv.dsenv l |> fst
        match
            FStar.Syntax.DsEnv.try_lookup_lid cfg.tcenv.dsenv l
        with
        | Some(t, _) -> t
        | None -> S.fv_to_tm (S.lid_as_fv l delta_constant None)


(*******************************************************************)
(* Simplification steps are not part of definitional equality      *)
(* simplifies True /\ t, t /\ True, t /\ False, False /\ t etc.    *)
(*******************************************************************)
and maybe_simplify_aux (cfg:cfg) (env:env) (stack:stack) (tm:term) : term =
    let tm = reduce_primops (norm_cb cfg) cfg env tm in
    if not <| cfg.steps.simplify then tm
    else
    let w t = {t with pos=tm.pos} in
    let simp_t t =
        // catch annotated subformulae too
        match (U.unmeta t).n with
        | Tm_fvar fv when S.fv_eq_lid fv PC.true_lid ->  Some true
        | Tm_fvar fv when S.fv_eq_lid fv PC.false_lid -> Some false
        | _ -> None
    in
    let rec args_are_binders args bs =
        match args, bs with
        | (t, _)::args, (bv, _)::bs ->
            begin match (SS.compress t).n with
            | Tm_name bv' -> S.bv_eq bv bv' && args_are_binders args bs
            | _ -> false
            end
        | [], [] -> true
        | _, _ -> false
    in
    let is_applied (bs:binders) (t : term) : option<bv> =
        if cfg.debug.wpe then
            BU.print2 "WPE> is_applied %s -- %s\n"  (Print.term_to_string t) (Print.tag_of_term t);
        let hd, args = U.head_and_args' t in
        match (SS.compress hd).n with
        | Tm_name bv when args_are_binders args bs ->
            if cfg.debug.wpe then
                BU.print3 "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                            (Print.term_to_string t)
                            (Print.bv_to_string bv)
                            (Print.term_to_string hd);
            Some bv
        | _ -> None
    in
    let is_applied_maybe_squashed (bs : binders) (t : term) : option<bv> =
        if cfg.debug.wpe then
            BU.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"  (Print.term_to_string t) (Print.tag_of_term t);
        match is_squash t with
        | Some (_, t') -> is_applied bs t'
        | _ -> begin match is_auto_squash t with
               | Some (_, t') -> is_applied bs t'
               | _ -> is_applied bs t
               end
    in
    // A very F*-specific optimization:
    //  1)  forall p.                       (p ==> E[p])     ~>     E[True]
    //  2)  forall p.                      (~p ==> E[p])     ~>     E[False]
    //  3)  forall p. (forall j1 j2 ... jn. p j1 j2 ... jn)    ==> E[p]    ~>    E[(fun j1 j2 ... jn -> True)]
    //  4)  forall p. (forall j1 j2 ... jn. ~(p j1 j2 ... jn)) ==> E[p]    ~>    E[(fun j1 j2 ... jn -> False)]
    let is_quantified_const (bv:bv) (phi : term) : option<term> =
        match U.destruct_typ_as_formula phi with
        | Some (BaseConn (lid, [(p, _); (q, _)])) when Ident.lid_equals lid PC.imp_lid ->
            if cfg.debug.wpe then
                BU.print2 "WPE> p = (%s); q = (%s)\n"
                        (Print.term_to_string p)
                        (Print.term_to_string q);
            begin match U.destruct_typ_as_formula p with
            // Case 1)
            | None -> begin match (SS.compress p).n with
                      | Tm_bvar bv' when S.bv_eq bv bv' ->
                            if cfg.debug.wpe then
                                BU.print_string "WPE> Case 1\n";
                            Some (SS.subst [NT (bv, U.t_true)] q)
                      | _ -> None
                      end

            // Case 2)
            | Some (BaseConn (lid, [(p, _)])) when Ident.lid_equals lid PC.not_lid ->
                begin match (SS.compress p).n with
                | Tm_bvar bv' when S.bv_eq bv bv' ->
                        if cfg.debug.wpe then
                            BU.print_string "WPE> Case 2\n";
                        Some (SS.subst [NT (bv, U.t_false)] q)
                | _ -> None
                end

            | Some (QAll (bs, pats, phi)) ->
                begin match U.destruct_typ_as_formula phi with
                | None ->
                    begin match is_applied_maybe_squashed bs phi with
                    // Case 3)
                    | Some bv' when S.bv_eq bv bv' ->
                        if cfg.debug.wpe then
                            BU.print_string "WPE> Case 3\n";
                        let ftrue = U.abs bs U.t_true (Some (U.residual_tot U.ktype0)) in
                        Some (SS.subst [NT (bv, ftrue)] q)
                    | _ ->
                        None
                    end
                | Some (BaseConn (lid, [(p, _)])) when Ident.lid_equals lid PC.not_lid ->
                    begin match is_applied_maybe_squashed bs p with
                    // Case 4)
                    | Some bv' when S.bv_eq bv bv' ->
                        if cfg.debug.wpe then
                            BU.print_string "WPE> Case 4\n";
                        let ffalse = U.abs bs U.t_false (Some (U.residual_tot U.ktype0)) in
                        Some (SS.subst [NT (bv, ffalse)] q)
                    | _ ->
                        None
                    end
                | _ ->
                    None
                end

            | _ -> None
            end
        | _ -> None
    in
    let is_forall_const (phi : term) : option<term> =
        match U.destruct_typ_as_formula phi with
        | Some (QAll ([(bv, _)], _, phi')) ->
            if cfg.debug.wpe then
                BU.print2 "WPE> QAll [%s] %s\n" (Print.bv_to_string bv) (Print.term_to_string phi');
            is_quantified_const bv phi'
        | _ -> None
    in
    let is_const_match (phi : term) : option<bool> =
        match (SS.compress phi).n with
        (* Trying to be efficient, but just checking if they all agree *)
        (* Note, if we wanted to do this for any term instead of just True/False
         * we need to open the terms *)
        | Tm_match (_, br::brs) ->
            let (_, _, e) = br in
            let r = begin match simp_t e with
            | None -> None
            | Some b -> if List.for_all (fun (_, _, e') -> simp_t e' = Some b) brs
                        then Some b
                        else None
            end
            in
            r
        | _ -> None
    in
    let maybe_auto_squash t =
        if U.is_sub_singleton t
        then t
        else U.mk_auto_squash U_zero t
    in
    let squashed_head_un_auto_squash_args t =
        //The head of t is already a squashed operator, e.g. /\ etc.
        //no point also squashing its arguments if they're already in U_zero
        let maybe_un_auto_squash_arg (t,q) =
            match U.is_auto_squash t with
            | Some (U_zero, t) ->
             //if we're squashing from U_zero to U_zero
             // then just remove it
              t, q
            | _ ->
              t,q
        in
        let head, args = U.head_and_args t in
        let args = List.map maybe_un_auto_squash_arg args in
        S.mk_Tm_app head args None t.pos
    in
    let rec clearly_inhabited (ty : typ) : bool =
        match (U.unmeta ty).n with
        | Tm_uinst (t, _) -> clearly_inhabited t
        | Tm_arrow (_, c) -> clearly_inhabited (U.comp_result c)
        | Tm_fvar fv ->
            let l = S.lid_of_fv fv in
               (Ident.lid_equals l PC.int_lid)
            || (Ident.lid_equals l PC.bool_lid)
            || (Ident.lid_equals l PC.string_lid)
            || (Ident.lid_equals l PC.exn_lid)
        | _ -> false
    in
    let simplify arg = (simp_t (fst arg), arg) in
    match is_forall_const tm with
    (* We need to recurse, and maybe reduce further! *)
    | Some tm' ->
        if cfg.debug.wpe then
            BU.print2 "WPE> %s ~> %s\n" (Print.term_to_string tm) (Print.term_to_string tm');
        maybe_simplify_aux cfg env stack (norm cfg env [] tm')
    (* Otherwise try to simplify this point *)
    | None ->
    match (SS.compress tm).n with
    | Tm_app({n=Tm_uinst({n=Tm_fvar fv}, _)}, args)
    | Tm_app({n=Tm_fvar fv}, args) ->
      if S.fv_eq_lid fv PC.and_lid
      then match args |> List.map simplify with
           | [(Some true, _); (_, (arg, _))]
           | [(_, (arg, _)); (Some true, _)] -> maybe_auto_squash arg
           | [(Some false, _); _]
           | [_; (Some false, _)] -> w U.t_false
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.or_lid
      then match args |> List.map simplify with
           | [(Some true, _); _]
           | [_; (Some true, _)] -> w U.t_true
           | [(Some false, _); (_, (arg, _))]
           | [(_, (arg, _)); (Some false, _)] -> maybe_auto_squash arg
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.imp_lid
      then match args |> List.map simplify with
           | [_; (Some true, _)]
           | [(Some false, _); _] -> w U.t_true
           | [(Some true, _); (_, (arg, _))] -> maybe_auto_squash arg
           | [(_, (p, _)); (_, (q, _))] ->
             if U.term_eq p q
             then w U.t_true
             else squashed_head_un_auto_squash_args tm
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.iff_lid
      then match args |> List.map simplify with
           | [(Some true, _)  ; (Some true, _)]
           | [(Some false, _) ; (Some false, _)] -> w U.t_true
           | [(Some true, _)  ; (Some false, _)]
           | [(Some false, _) ; (Some true, _)]  -> w U.t_false
           | [(_, (arg, _))   ; (Some true, _)]
           | [(Some true, _)  ; (_, (arg, _))]   -> maybe_auto_squash arg
           | [(_, (arg, _))   ; (Some false, _)]
           | [(Some false, _) ; (_, (arg, _))]   -> maybe_auto_squash (U.mk_neg arg)
           | [(_, (p, _)); (_, (q, _))] ->
             if U.term_eq p q
             then w U.t_true
             else squashed_head_un_auto_squash_args tm
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.not_lid
      then match args |> List.map simplify with
           | [(Some true, _)] ->  w U.t_false
           | [(Some false, _)] -> w U.t_true
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.forall_lid
      then match args with
           (* Simplify ∀x. True to True *)
           | [(t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs([_], body, _) ->
                     (match simp_t body with
                     | Some true -> w U.t_true
                     | _ -> tm)
                   | _ -> tm
             end
           (* Simplify ∀x. True to True, and ∀x. False to False, if the domain is not empty *)
           | [(ty, Some (Implicit _)); (t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs([_], body, _) ->
                     (match simp_t body with
                     | Some true -> w U.t_true
                     | Some false when clearly_inhabited ty -> w U.t_false
                     | _ -> tm)
                   | _ -> tm
             end
           | _ -> tm
      else if S.fv_eq_lid fv PC.exists_lid
      then match args with
           (* Simplify ∃x. False to False *)
           | [(t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs([_], body, _) ->
                     (match simp_t body with
                     | Some false -> w U.t_false
                     | _ -> tm)
                   | _ -> tm
             end
           (* Simplify ∃x. False to False and ∃x. True to True, if the domain is not empty *)
           | [(ty, Some (Implicit _)); (t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs([_], body, _) ->
                     (match simp_t body with
                     | Some false -> w U.t_false
                     | Some true when clearly_inhabited ty -> w U.t_true
                     | _ -> tm)
                   | _ -> tm
             end
           | _ -> tm
      else if S.fv_eq_lid fv PC.b2t_lid
      then match args with
           | [{n=Tm_constant (Const_bool true)}, _] -> w U.t_true
           | [{n=Tm_constant (Const_bool false)}, _] -> w U.t_false
           | _ -> tm //its arg is a bool, can't unsquash
      else begin
           match U.is_auto_squash tm with
           | Some (U_zero, t)
             when U.is_sub_singleton t ->
             //remove redundant auto_squashes
             t
           | _ ->
             reduce_equality (norm_cb cfg) cfg env tm
      end
    | Tm_refine (bv, t) ->
        begin match simp_t t with
        | Some true -> bv.sort
        | Some false -> tm
        | None -> tm
        end
    | Tm_match _ ->
        begin match is_const_match tm with
        | Some true -> w U.t_true
        | Some false -> w U.t_false
        | None -> tm
        end
    | _ -> tm


and rebuild (cfg:cfg) (env:env) (stack:stack) (t:term) : term =
  (* Pre-condition: t is in either weak or strong normal form w.r.t env, depending on *)
  (* whether cfg.steps constains WHNF In either case, it has no free de Bruijn *)
  (* indices *)
  log cfg (fun () ->
    BU.print4 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                                        (Print.tag_of_term t)
                                        (Print.term_to_string t)
                                        (BU.string_of_int (List.length env))
                                        (stack_to_string (fst <| firstn 4 stack));
    if Env.debug cfg.tcenv (Options.Other "NormRebuild")
    then match FStar.Syntax.Util.unbound_variables t with
         | [] -> ()
         | bvs ->
           BU.print3 "!!! Rebuild (%s) %s, free vars=%s\n"
                               (Print.tag_of_term t)
                               (Print.term_to_string t)
                               (bvs |> List.map Print.bv_to_string |> String.concat ", ");
           failwith "DIE!");
  let t = maybe_simplify cfg env stack t in
  match stack with
  | [] -> t

  | Debug (tm, time_then) :: stack ->
    if cfg.debug.print_normalized
    then begin
      let time_now = BU.now () in
      BU.print3 "Normalized (%s ms) %s\n\tto %s\n"
                   (BU.string_of_int (snd (BU.time_diff time_then time_now)))
                   (Print.term_to_string tm)
                   (Print.term_to_string t)
    end;
    rebuild cfg env stack t

  | Cfg cfg :: stack ->
    rebuild cfg env stack t

  | Meta(_, m, r)::stack ->
    let t = mk (Tm_meta(t, m)) r in
    rebuild cfg env stack t

  | MemoLazy r::stack ->
    set_memo cfg r (env, t);
    log cfg  (fun () -> BU.print1 "\tSet memo %s\n" (Print.term_to_string t));
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

  | Arg (Clos(env_arg, tm, _, _), aq, r) :: stack
        when U.is_fstar_tactics_by_tactic (head_of t) ->
    let t = S.extend_app t (closure_as_term cfg env_arg tm, aq) None r in
    rebuild cfg env stack t

  | Arg (Clos(env_arg, tm, m, _), aq, r) :: stack ->
    log cfg (fun () -> BU.print1 "Rebuilding with arg %s\n" (Print.term_to_string tm));
    // this needs to be tail recursive for reducing large terms

    // GM: This is basically saying "if exclude iota, don't memoize".
    // what's up with that?
    // GM: I actually get a regression if I just keep the second branch.
    if not cfg.steps.iota
    then if cfg.steps.hnf
         then let arg = closure_as_term cfg env_arg tm in
              let t = extend_app t (arg, aq) None r in
              rebuild cfg env_arg stack t
         else let stack = App(env, t, aq, r)::stack in
              norm cfg env_arg stack tm
    else begin match !m with
      | None ->
        if cfg.steps.hnf
        then let arg = closure_as_term cfg env_arg tm in
             let t = extend_app t (arg, aq) None r in
             rebuild cfg env_arg stack t
        else let stack = MemoLazy m::App(env, t, aq, r)::stack in
             norm cfg env_arg stack tm

      | Some (_, a) ->
        let t = S.extend_app t (a,aq) None r in
        rebuild cfg env_arg stack t
    end

  | App(env, head, aq, r)::stack' when should_reify cfg stack ->
    let t0 = t in
    let fallback msg () =
       log cfg (fun () -> BU.print2 "Not reifying%s: %s\n" msg (Print.term_to_string t));
       let t = S.extend_app head (t, aq) None r in
       rebuild cfg env stack' t
    in
    begin match (SS.compress t).n with
    | Tm_meta (t, Meta_monadic (m, ty)) ->
       do_reify_monadic (fallback " (1)") cfg env stack t m ty

    | Tm_meta (t, Meta_monadic_lift (msrc, mtgt, ty)) ->
       let lifted = reify_lift cfg t msrc mtgt (closure_as_term cfg env ty) in
       log cfg (fun () -> BU.print1 "Reified lift to (1): %s\n" (Print.term_to_string lifted));
       norm cfg env (List.tl stack) lifted

    | Tm_app ({n = Tm_constant (FC.Const_reflect _)}, [(e, _)]) ->
       // reify (reflect e) ~> e
       // Although shouldn't `e` ALWAYS be marked with a Meta_monadic?
       norm cfg env stack' e

    | Tm_app _ when cfg.steps.primops ->
      let hd, args = U.head_and_args t in
      (match (U.un_uinst hd).n with
       | Tm_fvar fv ->
           begin
           match find_prim_step cfg fv with
           | Some ({auto_reflect=Some n})
             when List.length args = n ->
             norm cfg env stack' t
           | _ -> fallback " (3)" ()
           end
       | _ -> fallback " (4)" ())

    | _ ->
        fallback " (2)" ()
    end

  | App(env, head, aq, r)::stack ->
    let t = S.extend_app head (t,aq) None r in
    rebuild cfg env stack t

  | Match(env', branches, cfg, r) :: stack ->
    log cfg  (fun () -> BU.print1 "Rebuilding with match, scrutinee is %s ...\n" (Print.term_to_string t));
    //the scrutinee is always guaranteed to be a pure or ghost term
    //see tc.fs, the case of Tm_match and the comment related to issue #594
    let scrutinee_env = env in
    let env = env' in
    let scrutinee = t in
    let norm_and_rebuild_match () =
      log cfg (fun () ->
          BU.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n"
                (Print.term_to_string scrutinee)
                (branches |> List.map (fun (p, _, _) -> Print.pat_to_string p) |> String.concat "\n\t"));
      // If either Weak or HNF, then don't descend into branch
      let whnf = cfg.steps.weak || cfg.steps.hnf in
      let cfg_exclude_zeta =
         let new_delta =
           cfg.delta_level |> List.filter (function
             | Env.InliningDelta
             | Env.Eager_unfolding_only -> true
             | _ -> false)
         in
         let steps = {
                cfg.steps with
                zeta = false;
                unfold_until = None;
                unfold_only = None;
                unfold_attr = None;
                unfold_tac = false
         }
         in
        ({cfg with delta_level=new_delta; steps=steps; strong=true})
      in
      let norm_or_whnf env t =
        if whnf
        then closure_as_term cfg_exclude_zeta env t
        else norm cfg_exclude_zeta env [] t
      in
      let rec norm_pat env p = match p.v with
        | Pat_constant _ -> p, env
        | Pat_cons(fv, pats) ->
          let pats, env = pats |> List.fold_left (fun (pats, env) (p, b) ->
                let p, env = norm_pat env p in
                (p,b)::pats, env) ([], env) in
          {p with v=Pat_cons(fv, List.rev pats)}, env
        | Pat_var x ->
          let x = {x with sort=norm_or_whnf env x.sort} in
          {p with v=Pat_var x}, dummy::env
        | Pat_wild x ->
          let x = {x with sort=norm_or_whnf env x.sort} in
          {p with v=Pat_wild x}, dummy::env
        | Pat_dot_term(x, t) ->
          let x = {x with sort=norm_or_whnf env x.sort} in
          let t = norm_or_whnf env t in
          {p with v=Pat_dot_term(x, t)}, env
      in
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
          U.branch (p, wopt, e))
      in
      let scrutinee =
        if cfg.steps.iota
        && (not cfg.steps.weak)
        && (not cfg.steps.compress_uvars)
        && cfg.steps.weakly_reduce_scrutinee
        && maybe_weakly_reduced scrutinee
        then norm ({cfg with steps={cfg.steps with weakly_reduce_scrutinee=false}})
                  scrutinee_env
                  []
                  scrutinee //scrutinee was only reduced to wnf; reduce it fully
        else scrutinee
      in
      rebuild cfg env stack (mk (Tm_match(scrutinee, branches)) r)
    in

    let rec is_cons head = match (SS.compress head).n with
      | Tm_uinst(h, _) -> is_cons h
      | Tm_constant _
      | Tm_fvar( {fv_qual=Some Data_ctor} )
      | Tm_fvar( {fv_qual=Some (Record_ctor _)} ) -> true
      | _ -> false
    in

    let guard_when_clause wopt b rest =
      match wopt with
      | None -> b
      | Some w ->
        let then_branch = b in
        let else_branch = mk (Tm_match(scrutinee, rest)) r in
        U.if_then_else w then_branch else_branch
    in


    let rec matches_pat (scrutinee_orig:term) (p:pat)
      : either<list<(bv * term)>, bool>
        (* Inl ts: p matches t and ts are bindings for the branch *)
        (* Inr false: p definitely does not match t *)
        (* Inr true: p may match t, but p is an open term and we cannot decide for sure *)
      = let scrutinee = U.unmeta scrutinee_orig in
        let scrutinee = U.unlazy scrutinee in
        let head, args = U.head_and_args scrutinee in
        match p.v with
        | Pat_var bv
        | Pat_wild bv -> Inl [(bv, scrutinee_orig)]
        | Pat_dot_term _ -> Inl []
        | Pat_constant s -> begin
          match scrutinee.n with
            | Tm_constant s'
              when FStar.Const.eq_const s s' ->
              Inl []
            | _ -> Inr (not (is_cons head)) //if it's not a constant, it may match
          end
        | Pat_cons(fv, arg_pats) -> begin
          match (U.un_uinst head).n with
            | Tm_fvar fv' when fv_eq fv fv' ->
              matches_args [] args arg_pats
            | _ -> Inr (not (is_cons head)) //if it's not a constant, it may match
          end

    and matches_args out (a:args) (p:list<(pat * bool)>) : either<list<(bv * term)>, bool> = match a, p with
      | [], [] -> Inl out
      | (t, _)::rest_a, (p, _)::rest_p ->
          begin match matches_pat t p with
              | Inl s -> matches_args (out@s) rest_a rest_p
              | m -> m
          end
      | _ -> Inr false
    in

    let rec matches scrutinee p = match p with
      | [] -> norm_and_rebuild_match ()
      | (p, wopt, b)::rest ->
          match matches_pat scrutinee p with
          | Inr false -> //definite mismatch; safe to consider the remaining patterns
            matches scrutinee rest

          | Inr true -> //may match this pattern but t is an open term; block reduction
            norm_and_rebuild_match ()

          | Inl s -> //definite match
            log cfg (fun () -> BU.print2 "Matches pattern %s with subst = %s\n"
                          (Print.pat_to_string p)
                          (List.map (fun (_, t) -> Print.term_to_string t) s |> String.concat "; "));
            //the elements of s are sub-terms of t
            //the have no free de Bruijn indices; so their env=[]; see pre-condition at the top of rebuild
            let env0 = env in
            let env = List.fold_left
                  (fun env (bv, t) -> (Some (S.mk_binder bv),
                                       Clos([], t, BU.mk_ref (Some ([], t)), false))::env)
                  env s in
            norm cfg env stack (guard_when_clause wopt b rest)
    in

    if cfg.steps.iota
    then matches scrutinee branches
    else norm_and_rebuild_match ()

let normalize_with_primitive_steps ps s e t =
    let c = config' ps s e in
    log_cfg c (fun () -> BU.print1 "Cfg = %s\n" (cfg_to_string c));
    if is_nbe_request s then begin
      log_top c (fun () -> BU.print1 "Starting NBE for (%s) {\n" (Print.term_to_string t));
      log_top c (fun () -> BU.print1 ">>> cfg = %s\n" (cfg_to_string c));
      let r = nbe_eval c s t in
      log_top c (fun () -> BU.print1 "}\nNormalization result = (%s)\n" (Print.term_to_string r));
      r
    end else begin
      log_top c (fun () -> BU.print1 "Starting normalizer for (%s) {\n" (Print.term_to_string t));
      log_top c (fun () -> BU.print1 ">>> cfg = %s\n" (cfg_to_string c));
      let r = norm c [] [] t in
      log_top c (fun () -> BU.print1 "}\nNormalization result = (%s)\n" (Print.term_to_string r));
      r
    end

let normalize s e t = normalize_with_primitive_steps [] s e t
let normalize_comp s e t = norm_comp (config s e) [] t
let normalize_universe env u = norm_universe (config [] env) [] u

(* Promotes Ghost T, when T is not informative to Pure T
        Non-informative types T ::= unit | Type u | t -> Tot T | t -> GTot T
*)
let ghost_to_pure env c =
    let cfg = config [UnfoldUntil delta_constant; AllowUnboundUniverses; EraseUniverses] env in
    let non_info t = non_informative (norm cfg [] [] t) in
    match c.n with
    | Total _ -> c
    | GTotal (t, uopt) when non_info t -> {c with n = Total (t, uopt)}
    | Comp ct ->
        let l = Env.norm_eff_name cfg.tcenv ct.effect_name in
        if U.is_ghost_effect l
        && non_info ct.result_typ
        then let ct =
                 match downgrade_ghost_effect_name ct.effect_name with
                 | Some pure_eff ->
                   let flags = if Ident.lid_equals pure_eff PC.effect_Tot_lid then TOTAL::ct.flags else ct.flags in
                   {ct with effect_name=pure_eff; flags=flags}
                 | None ->
                    let ct = unfold_effect_abbrev cfg.tcenv c in //must be GHOST
                    {ct with effect_name=PC.effect_PURE_lid} in
             {c with n=Comp ct}
        else c
    | _ -> c

let ghost_to_pure_lcomp env (lc:lcomp) =
    let cfg = config [Eager_unfolding; UnfoldUntil delta_constant; EraseUniverses; AllowUnboundUniverses] env in
    let non_info t = non_informative (norm cfg [] [] t) in
    if U.is_ghost_effect lc.eff_name
    && non_info lc.res_typ
    then match downgrade_ghost_effect_name lc.eff_name with
         | Some pure_eff ->
           S.mk_lcomp pure_eff lc.res_typ lc.cflags
                      (fun () -> ghost_to_pure env (lcomp_comp lc))
         | None -> //can't downgrade, don't know the particular incarnation of PURE to use
           lc
    else lc

let term_to_string env t =
  let t =
    try normalize [AllowUnboundUniverses] env t
    with e -> Errors.log_issue t.pos (Errors.Warning_NormalizationFailure, (BU.format1 "Normalization failed with error %s\n" (BU.message_of_exn e))) ; t
  in
  Print.term_to_string' env.dsenv t

let comp_to_string env c =
  let c =
    try norm_comp (config [AllowUnboundUniverses] env) [] c
    with e -> Errors.log_issue c.pos (Errors.Warning_NormalizationFailure, (BU.format1 "Normalization failed with error %s\n" (BU.message_of_exn e))) ; c
  in
  Print.comp_to_string' env.dsenv c

let normalize_refinement steps env t0 =
   let t = normalize (steps@[Beta]) env t0 in
   let rec aux t =
    let t = compress t in
    match t.n with
       | Tm_refine(x, phi) ->
         let t0 = aux x.sort in
         begin match t0.n with
            | Tm_refine(y, phi1) ->
              //NB: this is working on de Bruijn
              //    representations; so no need
              //    to substitute y/x in phi
              mk (Tm_refine(y, U.mk_conj_simp phi1 phi)) t0.pos
            | _ -> t
         end
       | _ -> t in
   aux t

let whnf_steps = [Primops; Weak; HNF; UnfoldUntil delta_constant; Beta]
let unfold_whnf' steps env t = normalize (steps@whnf_steps) env t
let unfold_whnf  env t = unfold_whnf' [] env t

let reduce_or_remove_uvar_solutions remove env t =
    normalize ((if remove then [CheckNoUvars] else [])
              @[Beta; DoNotUnfoldPureLets; CompressUvars; Exclude Zeta; Exclude Iota; NoFullNorm;])
              env
              t
let reduce_uvar_solutions env t = reduce_or_remove_uvar_solutions false env t
let remove_uvar_solutions env t = reduce_or_remove_uvar_solutions true env t

let eta_expand_with_type (env:Env.env) (e:term) (t_e:typ) =
  //unfold_whnf env t_e in
  //It would be nice to eta_expand based on the WHNF of t_e
  //except that this triggers a brittleness in the unification algorithm and its interaction with SMT encoding
  //in particular, see Rel.u_abs (roughly line 520)
  let formals, c = U.arrow_formals_comp t_e in
  match formals with
  | [] -> e
  | _ ->
    let actuals, _, _ = U.abs_formals e in
    if List.length actuals = List.length formals
    then e
    else let binders, args = formals |> U.args_of_binders in
         U.abs binders (mk_Tm_app e args None e.pos)
                       (Some (U.residual_comp_of_comp c))

let eta_expand (env:Env.env) (t:term) : term =
  match t.n with
  | Tm_name x ->
      eta_expand_with_type env t x.sort
  | _ ->
      let head, args = U.head_and_args t in
      begin match (SS.compress head).n with
      | Tm_uvar (u,s) ->
        let formals, _tres = U.arrow_formals (SS.subst' s u.ctx_uvar_typ) in
        if List.length formals = List.length args
        then t
        else let _, ty, _ = env.type_of ({env with lax=true; use_bv_sorts=true; expected_typ=None}) t in
             eta_expand_with_type env t ty
      | _ ->
        let _, ty, _ = env.type_of ({env with lax=true; use_bv_sorts=true; expected_typ=None}) t in
        eta_expand_with_type env t ty
      end

//////////////////////////////////////////////////////////////////
//Eliminating all unification variables and delayed substitutions in a sigelt
//////////////////////////////////////////////////////////////////

let rec elim_delayed_subst_term (t:term) : term =
    let mk x = S.mk x None t.pos in
    let t = SS.compress t in
    let elim_bv x = {x with sort=elim_delayed_subst_term x.sort} in
    match t.n with
    | Tm_delayed _ -> failwith "Impossible"
    | Tm_bvar _
    | Tm_name _
    | Tm_fvar _
    | Tm_uinst _
    | Tm_constant _
    | Tm_type _
    | Tm_lazy _
    | Tm_unknown -> t

    | Tm_abs(bs, t, rc_opt) ->
      let elim_rc rc =
        {rc with
            residual_typ=BU.map_opt rc.residual_typ elim_delayed_subst_term;
            residual_flags=elim_delayed_subst_cflags rc.residual_flags}
      in
      mk (Tm_abs(elim_delayed_subst_binders bs,
                 elim_delayed_subst_term t,
                 BU.map_opt rc_opt elim_rc))

    | Tm_arrow(bs, c) ->
      mk (Tm_arrow(elim_delayed_subst_binders bs, elim_delayed_subst_comp c))

    | Tm_refine(bv, phi) ->
      mk (Tm_refine(elim_bv bv, elim_delayed_subst_term phi))

    | Tm_app(t, args) ->
      mk (Tm_app(elim_delayed_subst_term t, elim_delayed_subst_args args))

    | Tm_match(t, branches) ->
      let rec elim_pat (p:pat) =
        match p.v with
        | Pat_var x ->
          {p with v=Pat_var (elim_bv x)}
        | Pat_wild x ->
          {p with v=Pat_wild (elim_bv x)}
        | Pat_dot_term(x, t0) ->
          {p with v=Pat_dot_term(elim_bv x, elim_delayed_subst_term t0)}
        | Pat_cons (fv, pats) ->
          {p with v=Pat_cons(fv, List.map (fun (x, b) -> elim_pat x, b) pats)}
        | _ -> p
      in
      let elim_branch (pat, wopt, t) =
          (elim_pat pat,
           BU.map_opt wopt elim_delayed_subst_term,
           elim_delayed_subst_term t)
      in
      mk (Tm_match(elim_delayed_subst_term t, List.map elim_branch branches))

    | Tm_ascribed(t, a, lopt) ->
      let elim_ascription (tc, topt) =
        (match tc with
         | Inl t -> Inl (elim_delayed_subst_term t)
         | Inr c -> Inr (elim_delayed_subst_comp c)),
        BU.map_opt topt elim_delayed_subst_term
      in
      mk (Tm_ascribed(elim_delayed_subst_term t, elim_ascription a, lopt))

    | Tm_let(lbs, t) ->
      let elim_lb lb =
         {lb with
             lbtyp = elim_delayed_subst_term lb.lbtyp;
             lbdef = elim_delayed_subst_term lb.lbdef }
      in
      mk (Tm_let((fst lbs, List.map elim_lb (snd lbs)),
                  elim_delayed_subst_term t))

    | Tm_uvar(u,s) ->
      mk (Tm_uvar(u,s)) //explicitly don't descend into (bs,t) to not break sharing there

    | Tm_quoted (tm, qi) ->
      let qi = S.on_antiquoted elim_delayed_subst_term qi in
      mk (Tm_quoted (elim_delayed_subst_term tm, qi))

    | Tm_meta(t, md) ->
      mk (Tm_meta(elim_delayed_subst_term t, elim_delayed_subst_meta md))

and elim_delayed_subst_cflags flags =
    List.map
        (function
        | DECREASES t -> DECREASES (elim_delayed_subst_term t)
        | f -> f)
        flags

and elim_delayed_subst_comp (c:comp) : comp =
    let mk x = S.mk x None c.pos in
    match c.n with
    | Total(t, uopt) ->
      mk (Total(elim_delayed_subst_term t, uopt))
    | GTotal(t, uopt) ->
      mk (GTotal(elim_delayed_subst_term t, uopt))
    | Comp ct ->
      let ct =
        {ct with
            result_typ=elim_delayed_subst_term ct.result_typ;
            effect_args=elim_delayed_subst_args ct.effect_args;
            flags=elim_delayed_subst_cflags ct.flags} in
      mk (Comp ct)

and elim_delayed_subst_meta = function
  | Meta_pattern args -> Meta_pattern(List.map elim_delayed_subst_args args)
  | Meta_monadic(m, t) -> Meta_monadic(m, elim_delayed_subst_term t)
  | Meta_monadic_lift(m1, m2, t) -> Meta_monadic_lift(m1, m2, elim_delayed_subst_term t)
  | m -> m

and elim_delayed_subst_args args =
    List.map (fun (t, q) -> elim_delayed_subst_term t, q) args

and elim_delayed_subst_binders bs =
    List.map (fun (x, q) -> {x with sort=elim_delayed_subst_term x.sort}, q) bs

let elim_uvars_aux_tc (env:Env.env) (univ_names:univ_names) (binders:binders) (tc:either<typ, comp>) =
    let t =
      match binders, tc with
      | [], Inl t -> t
      | [], Inr c -> failwith "Impossible: empty bindes with a comp"
      | _ , Inr c -> S.mk (Tm_arrow(binders, c)) None c.pos
      | _ , Inl t -> S.mk (Tm_arrow(binders, S.mk_Total t)) None t.pos
    in
    let univ_names, t = Subst.open_univ_vars univ_names t in
    let t = remove_uvar_solutions env t in
    let t = Subst.close_univ_vars univ_names t in
    let t = elim_delayed_subst_term t in
    let binders, tc =
        match binders with
        | [] -> [], Inl t
        | _ -> begin
          match (SS.compress t).n, tc with
          | Tm_arrow(binders, c), Inr _ -> binders, Inr c
          | Tm_arrow(binders, c), Inl _ -> binders, Inl (U.comp_result c)
          | _,                    Inl _ -> [], Inl t
          | _ -> failwith "Impossible"
          end
    in
    univ_names, binders, tc

let elim_uvars_aux_t env univ_names binders t =
   let univ_names, binders, tc = elim_uvars_aux_tc env univ_names binders (Inl t) in
   univ_names, binders, BU.left tc

let elim_uvars_aux_c env univ_names binders c =
   let univ_names, binders, tc = elim_uvars_aux_tc env univ_names binders (Inr c) in
   univ_names, binders, BU.right tc

let rec elim_uvars (env:Env.env) (s:sigelt) =
    match s.sigel with
    | Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') ->
      let univ_names, binders, typ = elim_uvars_aux_t env univ_names binders typ in
      {s with sigel = Sig_inductive_typ(lid, univ_names, binders, typ, lids, lids')}

    | Sig_bundle (sigs, lids) ->
      {s with sigel = Sig_bundle(List.map (elim_uvars env) sigs, lids)}

    | Sig_datacon (lid, univ_names, typ, lident, i, lids) ->
      let univ_names, _, typ = elim_uvars_aux_t env univ_names [] typ in
      {s with sigel = Sig_datacon(lid, univ_names, typ, lident, i, lids)}

    | Sig_declare_typ (lid, univ_names, typ) ->
      let univ_names, _, typ = elim_uvars_aux_t env univ_names [] typ in
      {s with sigel = Sig_declare_typ(lid, univ_names, typ)}

    | Sig_let((b, lbs), lids) ->
      let lbs = lbs |> List.map (fun lb ->
        let opening, lbunivs = Subst.univ_var_opening lb.lbunivs in
        let elim t = elim_delayed_subst_term (Subst.close_univ_vars lbunivs (remove_uvar_solutions env (Subst.subst opening t))) in
        let lbtyp = elim lb.lbtyp in
        let lbdef = elim lb.lbdef in
        {lb with lbunivs = lbunivs;
                 lbtyp   = lbtyp;
                 lbdef   = lbdef})
      in
      {s with sigel = Sig_let((b, lbs), lids)}

    | Sig_main t ->
      {s with sigel = Sig_main (remove_uvar_solutions env t)}

    | Sig_assume (l, us, t) ->
      let us, _, t = elim_uvars_aux_t env us [] t in
      {s with sigel = Sig_assume (l, us, t)}

    | Sig_new_effect_for_free _ -> failwith "Impossible: should have been desugared already"

    | Sig_new_effect ed ->
      let univs, binders, signature = elim_uvars_aux_t env ed.univs ed.binders ed.signature in
      let univs_opening, univs_closing =
        let univs_opening, univs = SS.univ_var_opening univs in
        univs_opening, SS.univ_var_closing univs
      in
      let b_opening, b_closing =
        let binders = SS.open_binders binders in
        SS.opening_of_binders binders,
        SS.closing_of_binders binders
      in
      let n = List.length univs in
      let n_binders = List.length binders in
      let elim_tscheme (us, t) =
        let n_us = List.length us in
        let us, t = SS.open_univ_vars us t in
        let b_opening, b_closing =
            b_opening |> SS.shift_subst n_us,
            b_closing |> SS.shift_subst n_us in
        let univs_opening, univs_closing =
            univs_opening |> SS.shift_subst n_us,
            univs_closing |> SS.shift_subst n_us in
        let t = SS.subst univs_opening (SS.subst b_opening t) in
        let _, _, t = elim_uvars_aux_t env [] [] t in
        let t = SS.subst univs_closing (SS.subst b_closing (SS.close_univ_vars us t)) in
        us, t
      in
      let elim_term t =
        let _, _, t = elim_uvars_aux_t env univs binders t in
        t
      in
      let elim_action a =
        let action_typ_templ =
            let body = S.mk (Tm_ascribed(a.action_defn, (Inl a.action_typ, None), None)) None a.action_defn.pos in
            match a.action_params with
            | [] -> body
            | _ -> S.mk (Tm_abs(a.action_params, body, None)) None a.action_defn.pos in
        let destruct_action_body body =
            match (SS.compress body).n with
            | Tm_ascribed(defn, (Inl typ, None), None) -> defn, typ
            | _ -> failwith "Impossible"
        in
        let destruct_action_typ_templ t =
            match (SS.compress t).n with
            | Tm_abs(pars, body, _) ->
              let defn, typ = destruct_action_body body in
              pars, defn, typ
            | _ ->
              let defn, typ = destruct_action_body t in
              [], defn, typ
        in
        let action_univs, t = elim_tscheme (a.action_univs, action_typ_templ) in
        let action_params, action_defn, action_typ = destruct_action_typ_templ t in
        let a' =
            {a with action_univs = action_univs;
                    action_params = action_params;
                    action_defn = action_defn;
                    action_typ = action_typ} in
        a'
      in
      let ed = { ed with
               univs        = univs;
               binders      = binders;
               signature    = signature;
               ret_wp       = elim_tscheme ed.ret_wp;
               bind_wp      = elim_tscheme ed.bind_wp;
               if_then_else = elim_tscheme ed.if_then_else;
               ite_wp       = elim_tscheme ed.ite_wp;
               stronger     = elim_tscheme ed.stronger;
               close_wp     = elim_tscheme ed.close_wp;
               assert_p     = elim_tscheme ed.assert_p;
               assume_p     = elim_tscheme ed.assume_p;
               null_wp      = elim_tscheme ed.null_wp;
               trivial      = elim_tscheme ed.trivial;
               repr         = elim_term    ed.repr;
               return_repr  = elim_tscheme ed.return_repr;
               bind_repr    = elim_tscheme ed.bind_repr;
               actions      = List.map elim_action ed.actions } in
      {s with sigel=Sig_new_effect ed}

    | Sig_sub_effect sub_eff ->
      let elim_tscheme_opt = function
        | None -> None
        | Some (us, t) -> let us, _, t = elim_uvars_aux_t env us [] t in Some (us, t)
      in
      let sub_eff = {sub_eff with lift    = elim_tscheme_opt sub_eff.lift;
                                  lift_wp = elim_tscheme_opt sub_eff.lift_wp} in
      {s with sigel=Sig_sub_effect sub_eff}

    | Sig_effect_abbrev(lid, univ_names, binders, comp, flags) ->
      let univ_names, binders, comp = elim_uvars_aux_c env univ_names binders comp in
      {s with sigel = Sig_effect_abbrev (lid, univ_names, binders, comp, flags)}

    | Sig_pragma _ ->
      s

    (* This should never happen, it should have been run by now *)
    | Sig_splice _ ->
      s

let erase_universes env t =
    normalize [EraseUniverses; AllowUnboundUniverses] env t

let unfold_head_once env t =
  let aux f us args =
      match Env.lookup_nonrec_definition [Env.Unfold delta_constant] env f.fv_name.v with
      | None -> None
      | Some head_def_ts ->
        let _, head_def = Env.inst_tscheme_with head_def_ts us in
        let t' = S.mk_Tm_app head_def args None t.pos in
        let t' = normalize [Env.Beta; Env.Iota] env t' in
        Some t'
  in
  let head, args = U.head_and_args t in
  match (SS.compress head).n with
  | Tm_fvar fv -> aux fv [] args
  | Tm_uinst({n=Tm_fvar fv}, us) -> aux fv us args
  | _ -> None

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
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
//basic util
module BU = FStar.Util
module FC = FStar.Const
module SC = FStar.Syntax.Const
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
  | Eager_unfolding
  | Inlining
  | NoDeltaSteps
  | UnfoldUntil of S.delta_depth
  | PureSubtermsWithinComputations
  | Simplify        //Simplifies some basic logical tautologies: not part of definitional equality!
  | EraseUniverses
  | AllowUnboundUniverses //we erase universes as we encode to SMT; so, sometimes when printing, it's ok to have some unbound universe variables
  | Reify
  | CompressUvars
  | NoFullNorm
and steps = list<step>

type primitive_step = {
    name:Ident.lid;
    arity:int;
    strong_reduction_ok:bool;
    interpretation:(Range.range -> args -> option<term>)
}

type closure =
  | Clos of env * term * memo<(env * term)> * bool //memo for lazy evaluation; bool marks whether or not this is a fixpoint
  | Univ of universe                               //universe terms do not have free variables
  | Dummy                                          //Dummy is a placeholder for a binder when doing strong reduction
and env = list<closure>

let closure_to_string = function
    | Clos (_, t, _, _) -> Print.term_to_string t
    | Univ _ -> "Univ"
    | Dummy -> "dummy"

type cfg = {
    steps: steps;
    tcenv: Env.env;
    delta_level: list<Env.delta_level>;  // Controls how much unfolding of definitions should be performed
    primitive_steps:list<primitive_step>
}

type branches = list<(pat * option<term> * term)>

type subst_t = list<subst_elt>

type stack_elt =
 | Arg      of closure * aqual * Range.range
 | UnivArgs of list<universe> * Range.range
 | MemoLazy of memo<(env * term)>
 | Match    of env * branches * Range.range
 | Abs      of env * binders * env * option<either<lcomp,residual_comp>> * Range.range //the second env is the first one extended with the binders, for reducing the option<lcomp>
 | App      of term * aqual * Range.range
 | Meta     of S.metadata * Range.range
 | Let      of env * binders * letbinding * Range.range
 | Steps    of steps * list<primitive_step> * list<Env.delta_level>
 | Debug    of term

type stack = list<stack_elt>



let mk t r = mk t None r
let set_memo r t =
  match !r with
    | Some _ -> failwith "Unexpected set_memo: thunk already evaluated"
    | None -> r := Some t

let env_to_string env =
    List.map closure_to_string env |> String.concat "; "

let stack_elt_to_string = function
    | Arg (c, _, _) -> BU.format1 "Closure %s" (closure_to_string c)
    | MemoLazy _ -> "MemoLazy"
    | Abs (_, bs, _, _, _) -> BU.format1 "Abs %s" (string_of_int <| List.length bs)
    | UnivArgs _ -> "UnivArgs"
    | Match   _ -> "Match"
    | App (t,_,_) -> BU.format1 "App %s" (Print.term_to_string t)
    | Meta (m,_) -> "Meta"
    | Let  _ -> "Let"
    | Steps (_, _, _) -> "Steps"
    | Debug t -> BU.format1 "Debug %s" (Print.term_to_string t)
    // | _ -> "Match"

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
    with _ -> failwith (BU.format1 "Failed to find %s\n" (Print.db_to_string x))

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
(*  or     U_max [k;                        --constant                                                              *)
(*               S^n1 u1 ; ...; S^nm um;    --offsets of distinct names, in order of the names                      *)
(*               S^p1 ?v1; ...; S^pq ?vq]   --offsets of distinct unification variables, in order of the variables  *)
(*          where the size of the list is at least 2                                                                *)
(********************************************************************************************************************)
let norm_universe cfg env u =
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
    log cfg  (fun () -> BU.print2 ">>> %s Closure_as_term %s\n" (Print.tag_of_term t) (Print.term_to_string t));
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

           | Tm_ascribed(t1, (annot,tacopt), lopt) ->
             let annot = match annot with
                | Inl t -> Inl (closure_as_term_delayed cfg env t)
                | Inr c -> Inr (close_comp cfg env c) in
             let tacopt = BU.map_opt tacopt (closure_as_term_delayed cfg env) in
             mk (Tm_ascribed(closure_as_term_delayed cfg env t1,
                             (annot, tacopt),
                             lopt)) t.pos

           | Tm_meta(t', Meta_pattern args) ->
             mk (Tm_meta(closure_as_term_delayed cfg env t',
                         Meta_pattern (args |> List.map (closures_as_args_delayed cfg env)))) t.pos

           | Tm_meta(t', Meta_monadic(m, tbody)) -> //other metadata's do not have any embedded closures
             mk (Tm_meta(closure_as_term_delayed cfg env t', Meta_monadic(m, closure_as_term_delayed cfg env tbody))) t.pos
           | Tm_meta(t', Meta_monadic_lift(m1, m2, tbody)) ->
                 mk (Tm_meta(closure_as_term_delayed cfg env t', Meta_monadic_lift(m1, m2, closure_as_term_delayed cfg env tbody))) t.pos

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
and filter_out_lcomp_cflags lc =
    (* TODO : lc.comp might have more cflags than lcomp.cflags *)
    lc.cflags |> List.filter (function DECREASES _ -> false | _ -> true)

and close_lcomp_opt cfg env lopt = match lopt with
    | Some (Inl lc) -> //NS: Too expensive to close potentially huge VCs that are hardly read
      let flags = filter_out_lcomp_cflags lc in
      if U.is_total_lcomp lc
      then Some (Inr (Const.effect_Tot_lid, flags))
      else if U.is_tot_or_gtot_lcomp lc
      then Some (Inr (Const.effect_GTot_lid, flags))
      else Some (Inr (lc.eff_name, flags)) //retaining the effect name and flags is sufficient
    | _ -> lopt

(*******************************************************************)
(* Semantics for primitive operators (+, -, >, &&, ...)            *)
(*******************************************************************)
let built_in_primitive_steps : list<primitive_step> =
    let const_as_tm c p = mk (Tm_constant c) p in
    let int_as_const  : Range.range -> int  -> term =
        fun p i -> const_as_tm (FC.Const_int (BU.string_of_int i, None)) p
    in
    let bool_as_const : Range.range -> bool -> term =
        fun p b -> const_as_tm (FC.Const_bool b) p
    in
    let string_as_const : Range.range -> string -> term =
        fun p b -> const_as_tm (FC.Const_string (BU.bytes_of_string b, p)) p
    in
    let arg_as_int (a, _) : option<int> =
        match (SS.compress a).n with
        | Tm_constant (FC.Const_int(i, None)) ->
          Some (BU.int_of_string i)
        | _ ->
          None
    in
    let arg_as_bounded_int (a, _) : option<(fv * int)> =
        match (SS.compress a).n with
        | Tm_app ({n=Tm_fvar fv1}, [({n=Tm_constant (FC.Const_int (i, None))}, _)])
            when BU.ends_with (Ident.text_of_lid fv1.fv_name.v) "int_to_t" ->
          Some (fv1, BU.int_of_string i)
        | _ -> None
    in
    let arg_as_bool (a, _) : option<bool> =
        match (SS.compress a).n with
        | Tm_constant (FC.Const_bool b) ->
          Some b
        | _ ->
          None
    in
    let arg_as_char (a, _) : option<char> =
        match (SS.compress a).n with
        | Tm_constant (Const_char c) ->
          Some c
        | _ ->
          None
    in
    let arg_as_string (a, _) : option<string> =
        match (SS.compress a).n with
        | Tm_constant (FC.Const_string(bytes, _)) ->
          Some (BU.string_of_bytes bytes)
        | _ ->
          None
    in
    let arg_as_list (f : arg -> option<'a>) (a, _) : option<list<'a>> =
        let rec sequence (l:list<option<'a>>) : option<list<'a>> =
            match l with
            | [] -> Some []
            | None::_ -> None
            | Some x::xs -> begin match sequence xs with
                            | None -> None
                            | Some xs' -> Some (x::xs')
                            end
        in
        match U.list_elements a with
        | None -> None
        | Some elts -> sequence (List.map (fun x -> f (as_arg x)) elts)
    in
    let lift_unary
        : ('a -> 'b) -> list<option<'a>> ->option<'b>
        = fun f aopts ->
            match aopts with
            | [Some a] -> Some (f a)
            | _ -> None
    in
    let lift_binary
        : ('a -> 'a -> 'b) -> list<option<'a>> -> option<'b>
        = fun f aopts ->
            match aopts with
            | [Some a0; Some a1] -> Some (f a0 a1)
            | _ -> None
    in
    let unary_op
        :  (arg -> option<'a>)
        -> (Range.range -> 'a -> term)
        -> Range.range
        -> args
        -> option<term>
        = fun as_a f r args -> lift_unary (f r) (List.map as_a args)
    in
    let binary_op
        :  (arg -> option<'a>)
        -> (Range.range -> 'a -> 'a -> term)
        -> Range.range
        -> args
        -> option<term>
        = fun as_a f r args -> lift_binary (f r) (List.map as_a args)
    in
    let as_primitive_step (l, arity, f) = {
        name=l;
        arity=arity;
        strong_reduction_ok=true;
        interpretation=f
    } in
    let unary_int_op (f:int -> int) =
        unary_op arg_as_int (fun r x -> int_as_const r (f x))
    in
    let binary_int_op (f:int -> int -> int) =
        binary_op arg_as_int (fun r x y -> int_as_const r (f x y))
    in
    let unary_bool_op (f:bool -> bool) =
        unary_op arg_as_bool (fun r x -> bool_as_const r (f x))
    in
    let binary_bool_op (f:bool -> bool -> bool) =
        binary_op arg_as_bool (fun r x y -> bool_as_const r (f x y))
    in
    let binary_string_op (f : string -> string -> string) =
        binary_op arg_as_string (fun r x y -> string_as_const r (f x y))
    in
    let list_of_string' rng (s:string) : term =
        let name l = mk (Tm_fvar (lid_as_fv l Delta_constant None)) rng in
        let char_t = name SC.char_lid in
        let charterm c = mk (Tm_constant (Const_char c)) rng in
        U.mk_list char_t rng <| List.map charterm (list_of_string s)
    in
    let string_of_list' rng (l:list<char>) : term =
        let s = string_of_list l in
        SC.exp_string s
    in
    let string_of_int rng (i:int) : term =
        string_as_const rng (BU.string_of_int i)
    in
    let string_of_bool rng (b:bool) : term =
        string_as_const rng (if b then "true" else "false")
    in
    let string_of_int rng (i:int) : term =
        string_as_const rng (BU.string_of_int i)
    in
    let string_of_bool rng (b:bool) : term =
        string_as_const rng (if b then "true" else "false")
    in
    let basic_ops : list<(Ident.lid * int * (Range.range -> args -> option<term>))> =
            [(Const.op_Minus,       1, unary_int_op (fun x -> - x));
             (Const.op_Addition,    2, binary_int_op (fun x y -> (x + y)));
             (Const.op_Subtraction, 2, binary_int_op (fun x y -> (x - y)));
             (Const.op_Multiply,    2, binary_int_op (fun x y -> (Prims.op_Multiply x y)));
             (Const.op_Division,    2, binary_int_op (fun x y -> (x / y)));
             (Const.op_LT,          2, binary_op arg_as_int (fun r x y -> bool_as_const r (x < y)));
             (Const.op_LTE,         2, binary_op arg_as_int (fun r x y -> bool_as_const r (x <= y)));
             (Const.op_GT,          2, binary_op arg_as_int (fun r x y -> bool_as_const r (x > y)));
             (Const.op_GTE,         2, binary_op arg_as_int (fun r x y -> bool_as_const r (x >= y)));
             (Const.op_Modulus,     2, binary_int_op (fun x y -> (x % y)));
             (Const.op_Negation,    1, unary_bool_op (fun x -> not x));
             (Const.op_And,         2, binary_bool_op (fun x y -> x && y));
             (Const.op_Or,          2, binary_bool_op (fun x y -> x || y));
             (Const.strcat_lid,     2, binary_string_op (fun x y -> x ^ y));
             (Const.string_of_int_lid, 1, unary_op arg_as_int string_of_int);
             (Const.string_of_bool_lid, 1, unary_op arg_as_bool string_of_bool);
             (Const.p2l ["FStar"; "String"; "list_of_string"],
                                    1, unary_op arg_as_string list_of_string');
             (Const.p2l ["FStar"; "String"; "string_of_list"],
                                    1, unary_op (arg_as_list arg_as_char) string_of_list')]
    in
    let bounded_arith_ops =
        let bounded_int_types =
           [ "Int8"; "UInt8"; "Int16"; "UInt16"; "Int32"; "UInt32"; "Int64"; "UInt64"; "UInt128"]
        in
        let int_as_bounded r int_to_t n =
            let c = int_as_const r n in
            let int_to_t = S.fv_to_tm int_to_t in
            S.mk_Tm_app int_to_t [S.as_arg c] None r
        in
        bounded_int_types |> List.collect (fun m ->
        [(Const.p2l ["FStar"; m; "add"], 2, binary_op arg_as_bounded_int (fun r (int_to_t, x) (_, y) -> int_as_bounded r int_to_t (x + y)));
         (Const.p2l ["FStar"; m; "sub"], 2, binary_op arg_as_bounded_int (fun r (int_to_t, x) (_, y) -> int_as_bounded r int_to_t (x - y)));
         (Const.p2l ["FStar"; m; "mul"], 2, binary_op arg_as_bounded_int (fun r (int_to_t, x) (_, y) -> int_as_bounded r int_to_t (Prims.op_Multiply x y)))])
    in
    List.map as_primitive_step (basic_ops@bounded_arith_ops)

let equality_ops : list<primitive_step> =
    let interp_bool rng (args:args) : option<term> =
        match args with
        | [(_typ, _); (a1, _); (a2, _)] ->
            (match U.eq_tm a1 a2 with
            | U.Equal -> Some (mk (Tm_constant (FC.Const_bool true)) rng)
            | U.NotEqual -> Some (mk (Tm_constant (FC.Const_bool false)) rng)
            | _ -> None)
        | _ ->
            failwith "Unexpected number of arguments"
    in
    let interp_prop (r:Range.range) (args:args) : option<term> =
        match args with
        | [(_typ, _); (a1, _); (a2, _)]    //eq2
        | [(_typ, _); _; (a1, _); (a2, _)] ->    //eq3
            (match U.eq_tm a1 a2 with
            | U.Equal -> Some ({U.t_true with pos=r})
            | U.NotEqual -> Some ({U.t_false with pos=r})
            | _ -> None)
        | _ ->
            failwith "Unexpected number of arguments"
    in
    let decidable_equality =
        {name = Const.op_Eq;
         arity = 3;
         strong_reduction_ok=true;
         interpretation=interp_bool}
    in
    let propositional_equality =
        {name = Const.eq2_lid;
         arity = 3;
         strong_reduction_ok=true;
         interpretation = interp_prop}
    in
    let hetero_propositional_equality =
        {name = Const.eq3_lid;
         arity = 4;
         strong_reduction_ok=true;
         interpretation = interp_prop}
    in

    [decidable_equality;propositional_equality; hetero_propositional_equality]

let reduce_primops cfg tm =
    if not <| List.contains Primops cfg.steps
    then tm
    else begin
         let head, args = U.head_and_args tm in
         match (U.un_uinst head).n with
         | Tm_fvar fv -> begin
           match List.tryFind (fun ps -> S.fv_eq_lid fv ps.name) cfg.primitive_steps with
           | None -> tm
           | Some prim_step ->
             if List.length args < prim_step.arity
             then tm //partial application; can't step
             else match prim_step.interpretation head.pos args with
                  | None -> tm
                  | Some reduced -> reduced
           end
         | _ -> tm
   end

let reduce_equality cfg tm =
    reduce_primops ({cfg with steps=[Primops]; primitive_steps=equality_ops}) tm

(*******************************************************************)
(* Simplification steps are not part of definitional equality      *)
(* simplifies True /\ t, t /\ True, t /\ False, False /\ t etc.    *)
(*******************************************************************)
let maybe_simplify cfg tm =
    let steps = cfg.steps in
    let w t = {t with pos=tm.pos} in
    let simp_t t = match t.n with
        | Tm_fvar fv when S.fv_eq_lid fv Const.true_lid ->  Some true
        | Tm_fvar fv when S.fv_eq_lid fv Const.false_lid -> Some false
        | _ -> None in
    let simplify arg = (simp_t (fst arg), arg) in
    if not <| List.contains Simplify steps
    then reduce_primops cfg tm
    else match tm.n with
            | Tm_app({n=Tm_uinst({n=Tm_fvar fv}, _)}, args)
            | Tm_app({n=Tm_fvar fv}, args) ->
              if S.fv_eq_lid fv Const.and_lid
              then match args |> List.map simplify with
                     | [(Some true, _); (_, (arg, _))]
                     | [(_, (arg, _)); (Some true, _)] -> arg
                     | [(Some false, _); _]
                     | [_; (Some false, _)] -> w U.t_false
                     | _ -> tm
              else if S.fv_eq_lid fv Const.or_lid
              then match args |> List.map simplify with
                     | [(Some true, _); _]
                     | [_; (Some true, _)] -> w U.t_true
                     | [(Some false, _); (_, (arg, _))]
                     | [(_, (arg, _)); (Some false, _)] -> arg
                     | _ -> tm
              else if S.fv_eq_lid fv Const.imp_lid
              then match args |> List.map simplify with
                     | [_; (Some true, _)]
                     | [(Some false, _); _] -> w U.t_true
                     | [(Some true, _); (_, (arg, _))] -> arg
                     | _ -> tm
              else if S.fv_eq_lid fv Const.not_lid
              then match args |> List.map simplify with
                     | [(Some true, _)] ->  w U.t_false
                     | [(Some false, _)] -> w U.t_true
                     | _ -> tm
              else if S.fv_eq_lid fv Const.forall_lid
              then match args with
                     | [(t, _)]
                     | [(_, Some (Implicit _)); (t, _)] ->
                       begin match (SS.compress t).n with
                                | Tm_abs([_], body, _) ->
                                   (match simp_t body with
                                        | Some true ->  w U.t_true
                                        | _ -> tm)
                                | _ -> tm
                       end
                    | _ -> tm
              else if S.fv_eq_lid fv Const.exists_lid
              then match args with
                     | [(t, _)]
                     | [(_, Some (Implicit _)); (t, _)] ->
                       begin match (SS.compress t).n with
                                | Tm_abs([_], body, _) ->
                                   (match simp_t body with
                                        | Some false -> w U.t_false
                                        | _ -> tm)
                                | _ -> tm
                       end
                    | _ -> tm
              else reduce_equality cfg tm
            | _ -> tm

(********************************************************************************************************************)
(* Main normalization function of the abstract machine                                                              *)
(********************************************************************************************************************)
let is_norm_request hd args =
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_; _] ->
      S.fv_eq_lid fv Const.normalize_term

    | Tm_fvar fv, [_] ->
      S.fv_eq_lid fv Const.normalize

    | _ -> false

let get_norm_request args =
    match args with
    | [_; (tm, _)]
    | [(tm, _)] -> tm
    | _ -> failwith "Impossible"

let is_reify_head = function
    | App({n=Tm_constant FC.Const_reify}, _, _)::_ ->
      true
    | _ ->
      false

let is_fstar_tactics_embed t =
    match (U.un_uinst t).n with
    | Tm_fvar fv -> S.fv_eq_lid fv FStar.Syntax.Const.fstar_tactics_embed_lid
    | _ -> false

let rec norm : cfg -> env -> stack -> term -> term =
    fun cfg env stack t ->
        let t = compress t in
        let firstn k l = if List.length l < k then l,[] else first_N k l in
        log cfg  (fun () -> BU.print3 ">>> %s\nNorm %s with top of the stack %s \n"
                                        (Print.tag_of_term t)
                                        (Print.term_to_string t)
                                        (stack_to_string (fst <| firstn 4 stack)));
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
            //log cfg (fun () -> BU.print "Tm_fvar case 0\n" []) ;
            rebuild cfg env stack t

          | Tm_app({n=Tm_fvar fv}, _)
            when S.fv_eq_lid fv FStar.Syntax.Const.fstar_tactics_embed_lid ->
            rebuild cfg env stack t //embedded terms should not be normalized

          | Tm_app(hd, args)
            when is_fstar_tactics_embed hd ->
            let args = closures_as_args_delayed cfg env args in
            let t = {t with n=Tm_app(hd, args)} in
            let t = reduce_primops cfg t in
            rebuild cfg env stack t //embedded terms should not be normalized, but they may have free variables

          | Tm_app(hd, args)
            when not (cfg.steps |> List.contains NoFullNorm)
              && is_norm_request hd args
              && not (Ident.lid_equals cfg.tcenv.curmodule Const.prims_lid) ->
            let tm = get_norm_request args in
            let s = [Reify; UnfoldUntil Delta_constant; Primops] in
            let cfg' = {cfg with steps=s; delta_level=[Unfold Delta_constant]} in
            let stack' = Debug t :: Steps (cfg.steps, cfg.primitive_steps, cfg.delta_level)::stack in
            norm cfg' env stack' tm

          | Tm_app({n=Tm_constant FC.Const_reify}, a1::a2::rest) ->
            let hd, _ = U.head_and_args t in
            let t' = S.mk (Tm_app(hd, [a1])) None t.pos in
            let t = S.mk(Tm_app(t', a2::rest)) None t.pos in
            norm cfg env stack t

          | Tm_app({n=Tm_constant (FC.Const_reflect _)}, [a])
                when (cfg.steps |> List.contains Reify &&
                      is_reify_head stack) ->
            norm cfg env (List.tl stack) (fst a)

          | Tm_app({n=Tm_constant FC.Const_reify}, [a])
                when (cfg.steps |> List.contains Reify) ->
            let reify_head, _ = U.head_and_args t in
            let a = SS.compress (U.unascribe <| fst a) in
            //BU.print2_warning "TRYING NORMALIZATION OF REIFY: %s ... %s\n" (Print.tag_of_term a) (Print.term_to_string a);
            begin match a.n with
              (* KM : This assumes that reflect is never tagged by a Meta_monadic flag *)
              (* Is that really the case ? *)
              | Tm_app({n=Tm_constant (FC.Const_reflect _)}, [a]) ->
                //reify (reflect e) ~> e
                norm cfg env stack (fst a)

              (* KM : This case reall y does not make any sense to me *)
              // | Tm_match(e, branches) ->
              //   //reify (match e with p -> e') ~> match (reify e) with p -> reify e'
              //   let e = BU.mk_reify e in
              //   let branches = branches |> List.map (fun (pat, wopt, tm) -> pat, wopt, BU.mk_reify tm) in
              //   let tm = mk (Tm_match(e, branches)) t.pos in
              //   norm cfg env stack tm

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
            let should_delta =
                cfg.delta_level |> BU.for_some (function
                    | NoDelta -> false
                    | Env.Inlining
                    | Eager_unfolding_only -> true
                    | Unfold l -> Common.delta_depth_greater_than f.fv_delta l) in

            if not should_delta
            then rebuild cfg env stack t
            else let r_env = Env.set_range cfg.tcenv (S.range_of_fv f) in //preserve the range info on the returned def
                 begin match Env.lookup_definition cfg.delta_level r_env f.fv_name.v with
                    | None ->
                      log cfg (fun () -> BU.print "Tm_fvar case 2\n" []) ;
                      rebuild cfg env stack t

                    | Some (us, t) ->
                      log cfg (fun () -> BU.print2 ">>> Unfolded %s to %s\n"
                                    (Print.term_to_string t0) (Print.term_to_string t));
                      let t =
                        if cfg.steps |> List.contains (UnfoldUntil Delta_constant)
                        //we're really trying to compute here; no point propagating range information
                        //which can be expensive
                        then t
                        else Subst.set_use_range (Ident.range_of_lid f.fv_name.v) t
                      in
                      let n = List.length us in
                      if n > 0
                      then match stack with //universe beta reduction
                             | UnivArgs(us', _)::stack ->
                               let env = us' |> List.fold_left (fun env u -> Univ u::env) env in
                               norm cfg env stack t
                             | _ when (cfg.steps |> List.contains EraseUniverses) ->
                               norm cfg env stack t
                             | _ -> failwith (BU.format1 "Impossible: missing universe instantiation on %s" (Print.lid_to_string f.fv_name.v))
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
                            log cfg  (fun () -> BU.print2 "Lazy hit: %s cached to %s\n" (Print.term_to_string t) (Print.term_to_string t'));
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
                          (* TODO : what happens if the argument is implicit ? is it already elaborated on the stack ? *)
                          begin match lopt with
                            | None when (Options.__unit_tests()) ->
                              log cfg  (fun () -> BU.print1 "\tShifted %s\n" (closure_to_string c));
                              norm cfg (c :: env) stack_rest body

                            | Some (Inr (l, cflags))
                            (* TODO (KM) : wouldn't it be better to check the TOTAL cflag ? *)
                                when (Ident.lid_equals l Const.effect_Tot_lid
                                      || Ident.lid_equals l Const.effect_GTot_lid
                                      || cflags |> BU.for_some (function TOTAL -> true | _ -> false)) ->
                              log cfg  (fun () -> BU.print1 "\tShifted %s\n" (closure_to_string c));
                              norm cfg (c :: env) stack_rest body

                            | Some (Inl lc) when (U.is_tot_or_gtot_lcomp lc) ->
                              log cfg  (fun () -> BU.print1 "\tShifted %s\n" (closure_to_string c));
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
                          log cfg  (fun () -> BU.print1 "\tShifted %s\n" (closure_to_string c));
                          let body = mk (Tm_abs(tl, body, lopt)) t.pos in
                          norm cfg (c :: env) stack_rest body
                      end
                  end

                | Steps (s, ps, dl) :: stack ->
                  norm ({cfg with steps=s; primitive_steps=ps; delta_level=dl}) env stack t

                | MemoLazy r :: stack ->
                  set_memo r (env, t); //We intentionally do not memoize the strong normal form; only the WHNF
                  log cfg  (fun () -> BU.print1 "\tSet memo %s\n" (Print.term_to_string t));
                  norm cfg env stack t

                | Debug _::_
                | Meta _::_
                | Let _ :: _
                | App _ :: _
                | Abs _ :: _
                | [] ->
                  if List.contains WHNF cfg.steps //don't descend beneath a lambda if we're just doing WHNF
                  then rebuild cfg env stack (closure_as_term cfg env t) //But, if the environment is non-empty, we need to substitute within the term
                  else let bs, body, opening = open_term' bs body in
                       let lopt = match lopt with
                        | Some (Inl l) -> SS.subst_comp opening (l.comp()) |> U.lcomp_of_comp |> Inl |> Some
                        | _ -> lopt in
                       let env' = bs |> List.fold_left (fun env _ -> Dummy::env) env in
                       log cfg  (fun () -> BU.print1 "\tShifted %s dummies\n" (string_of_int <| List.length bs));
                       let stack = Steps(cfg.steps, cfg.primitive_steps, cfg.delta_level)::stack in
                       let cfg = {cfg with primitive_steps=List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps} in
                       norm cfg env' (Abs(env, bs, env', lopt, t.pos)::stack) body
            end

          | Tm_app(head, args) ->
            let stack = stack |> List.fold_right (fun (a, aq) stack -> Arg (Clos(env, a, BU.mk_ref None, false),aq,t.pos)::stack) args in
            log cfg  (fun () -> BU.print1 "\tPushed %s arguments\n" (string_of_int <| List.length args));
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

          | Tm_ascribed(t1, (tc, tacopt), l) ->
            begin match stack with
              | Match _ :: _
              | Arg _ :: _
              | App ({n=Tm_constant FC.Const_reify}, _, _) :: _
              | MemoLazy _ :: _ -> norm cfg env stack t1 //ascriptions should not block reduction
              | _ ->
                (* Drops stack *)
                let t1 = norm cfg env [] t1 in
                log cfg  (fun () -> BU.print_string "+++ Normalizing ascription \n");
                let tc = match tc with
                    | Inl t -> Inl (norm cfg env [] t)
                    | Inr c -> Inr (norm_comp cfg env c) in
                let tacopt = BU.map_opt tacopt (norm cfg env []) in
                rebuild cfg env stack (mk (Tm_ascribed(t1, (tc, tacopt), l)) t.pos)
            end

          | Tm_match(head, branches) ->
            let stack = Match(env, branches, t.pos)::stack in
            norm cfg env stack head

          | Tm_let((_, {lbname=Inr _}::_), _) -> //this is a top-level let binding; nothing to normalize
            rebuild cfg env stack t

          | Tm_let((false, [lb]), body) ->
            let n = TypeChecker.Env.norm_eff_name cfg.tcenv lb.lbeff in
            if not (cfg.steps |> List.contains NoDeltaSteps)
            && (U.is_pure_effect n
            || (U.is_ghost_effect n && not (cfg.steps |> List.contains PureSubtermsWithinComputations)))
            then let env = Clos(env, lb.lbdef, BU.mk_ref None, false)::env in
                 norm cfg env stack body
            else let bs, body = Subst.open_term [lb.lbname |> BU.left |> S.mk_binder] body in
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
                    let memo = BU.mk_ref None in
                    let rec_env = Clos(env, fix_f_i, memo, true)::rec_env in
                    rec_env, memo::memos, i + 1) (snd lbs) (env, [], 0) in
            let _ = List.map2 (fun lb memo -> memo := Some (rec_env, lb.lbdef)) (snd lbs) memos in //tying the knot
            let body_env = List.fold_right (fun lb env -> Clos(rec_env, lb.lbdef, BU.mk_ref None, false)::env)
                               (snd lbs) env in
            norm cfg body_env stack body

          | Tm_meta (head, m) ->
            begin match m with
              | Meta_monadic (m, t) ->

                let should_reify = match stack with
                    | App ({n=Tm_constant FC.Const_reify}, _, _) :: _ ->
                        // BU.print1 "Found a reify on the stack. %s" "" ;
                        cfg.steps |> List.contains Reify
                    | _ -> false
                in

                // BU.print2 "Will %sreify : %s \n" (if should_reify then "" else "not ") (stack_to_string stack);

                if not should_reify
                then
                 (*  We have an impure computation, and we aim to perform any pure steps within that computation.   *
                  *                                                                                                 *
                  *  This scenario arises primarily as we extract (impure) programs and partially evaluate them     *
                  *  before extraction, as an optimization.                                                         *
                  *                                                                                                 *
                  *  First, we reduce **the type annotation** t with an empty stack                                 *
                  *                                                                                                 *
                  *  Then, we reduce the monadic computation `head`, in a stack marked with a Meta_monadic,         *
                  *  indicating that this reduction should not consume any arguments on the stack. `rebuild`        *
                  *  will notice the Meta_monadic marker and reconstruct the computation after normalization.       *)

                  let t = norm cfg env [] t in
                  let stack = Steps(cfg.steps, cfg.primitive_steps, cfg.delta_level)::stack in
                  let cfg =
                    if cfg.steps |> List.contains PureSubtermsWithinComputations
                    then
                      (* KM : This case should be tailored for extraction but I'm not exactly sure that the logic here is correct *)
                      (* Why are we dropping previous steps arbitrarily ? This will silently break any extension of the steps *)
                      { cfg with
                        steps=[PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta;
                               NoDeltaSteps];
                        delta_level=[Env.Inlining; Env.Eager_unfolding_only]
                      }
                    else
                      { cfg with
                        steps=[NoDeltaSteps; Exclude Zeta]@cfg.steps;
                        delta_level=[NoDelta]}
                  in
                  (* meta doesn't block reduction, but we need to put the label back *)
                  norm cfg env (Meta(Meta_monadic(m, t), t.pos)::stack) head
                else
                  begin match (SS.compress head).n with
                    | Tm_let((false, [lb]), body) ->
                      (* ****************************************************************************)
                      (* Monadic binding                                                            *)
                      (*                                                                            *)
                      (* This is reify (M.bind e1 (fun x -> e2)) which is elaborated to             *)
                      (*                                                                            *)
                      (*        M.bind_repr (reify e1) (fun x -> reify e2)                          *)
                      (*                                                                            *)
                      (* ****************************************************************************)
                      let ed = Env.get_effect_decl cfg.tcenv m in
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
                            let lb = {lb with lbeff=Const.effect_PURE_lid; lbdef=e} in
                            norm cfg env (List.tl stack) (S.mk (Tm_let((false, [lb]), U.mk_reify body)) None head.pos)
                          | None ->
                            if (match is_return body with Some ({n=Tm_bvar y}) -> S.bv_eq x y | _ -> false)
                            then
                              (* We are in the case where [head] = [bind e (fun x -> return x)] *)
                              (* which can be optimised to just keeping normalizing [e] with a reify on the stack *)
                              norm cfg env stack lb.lbdef
                            else
                              (* TODO : optimize [bind (bind e1 e2) e3] into [bind e1 (bind e2 e3)] *)
                              (* Rewriting binds in that direction would be better for exception-like monad *)
                              (* since we wouldn't rematch on an already raised exception *)
                              let head = U.mk_reify <| lb.lbdef in
                              let body = U.mk_reify <| body in
                              (* TODO : Check that there is no sensible cflags to pass in the residual_comp *)
                              let body = S.mk (Tm_abs([S.mk_binder x], body, Some (Inr (m, [])))) None body.pos in
                              let close = closure_as_term cfg env in
                              let bind_inst = match (SS.compress bind_repr).n with
                                | Tm_uinst (bind, [_ ; _]) ->
                                    S.mk (Tm_uinst (bind, [ cfg.tcenv.universe_of cfg.tcenv (close lb.lbtyp)
                                                          ; cfg.tcenv.universe_of cfg.tcenv (close t)]))
                                    None t.pos
                                | _ -> failwith "NIY : Reification of indexed effects"
                              in
                              let reified = S.mk (Tm_app(bind_inst, [
                                  (* a, b *)
                                  as_arg lb.lbtyp; as_arg t;
                                  (* wp_head, head--the term shouldn't depend on wp_head *)
                                  as_arg S.tun; as_arg head;
                                  (* wp_body, body--the term shouldn't depend on wp_body *)
                                  as_arg S.tun; as_arg body]))
                                None t.pos
                              in
                              norm cfg env (List.tl stack) reified
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


                        let ed = Env.get_effect_decl cfg.tcenv m in
                        let _, bind_repr = ed.bind_repr in

                        (* [maybe_unfold_action head] test whether [head] is an action and tries to unfold it if it is *)
                        let maybe_unfold_action head =
                          let maybe_extract_fv t =
                            let t = match (SS.compress t).n with
                              | Tm_uinst (t, _) -> t
                              | _ -> head
                            in match (SS.compress t).n with
                              | Tm_fvar x -> Some x
                              | _ -> None
                          in
                          match maybe_extract_fv head with
                          | Some x when Env.is_action cfg.tcenv (S.lid_of_fv x) ->
                            (* Note that this is not a tail call, but it's a bounded (small) number of recursive steps *)
                            let head = norm cfg env [] head in
                            let action_unfolded = match maybe_extract_fv head with | Some _ -> Some true | _ -> Some false in
                            head, action_unfolded
                          | _ ->
                            head, None
                        in

                        (* Checking that the typechecker did its job correctly and hoisted all impure *)
                        (* terms to explicit let-bindings (see TcTerm, monadic_application) *)
                        let _ =
                          let is_arg_impure (e,q) =
                            match (SS.compress e).n with
                            | Tm_meta (e0, Meta_monadic_lift(m1, m2, t')) -> not (U.is_pure_effect m1)
                            | _ -> false
                          in
                          if BU.for_some is_arg_impure ((as_arg head_app)::args)
                          then failwith (BU.format1 "Incompability between typechecker and normalizer; \
                                                     this monadic application contains impure terms %s\n"
                                                    (Print.term_to_string head))
                        in

                        let head_app, found_action = maybe_unfold_action head_app in
                        let mk tm = S.mk tm None t.pos in
                        let body = mk (Tm_app(head_app, args)) in
                        let body = match found_action with
                          (* This is not an action let's just reify it *)
                          | None -> U.mk_reify body

                          (* The action was found but not unfolded (maybe abstract ?) *)
                          | Some false -> mk (Tm_meta (body, Meta_monadic(m, t)))

                          (* An action was found and successfully unfolded *)
                          | Some true -> body
                        in

                        norm cfg env (List.tl stack) body
                    | Tm_meta(e, Meta_monadic_lift (msrc, mtgt, t')) ->
                        let lifted = reify_lift cfg.tcenv e msrc mtgt (closure_as_term cfg env t') in
                        norm cfg env (List.tl stack) lifted
                    | Tm_match(e, branches) ->
                      (* Commutation of reify with match, note that the scrutinee should never be effectful    *)
                      (* (should be checked at typechecking and elaborated with an explicit binding if needed) *)
                      (* reify (match e with p -> e') ~> match e with p -> reify e' *)
                      let branches = branches |> List.map (fun (pat, wopt, tm) -> pat, wopt, U.mk_reify tm) in
                      let tm = mk (Tm_match(e, branches)) t.pos in
                      norm cfg env (List.tl stack) tm
                    | _ ->
                        (* TODO : that seems a little fishy *)
                        norm cfg env stack head
                end


              | Meta_monadic_lift (m, m', t) ->
                (* KM : This code is a partial duplicate of what can be found in Meta_monadic *)
                (* KM : Not exactly sure which case should be eliminated *)
                let should_reify = match stack with
                    | App ({n=Tm_constant FC.Const_reify}, _, _) :: _ ->
                        // BU.print1 "Found a reify on the stack. %s" "" ;
                        cfg.steps |> List.contains Reify
                    | _ -> false
                in

                if should_reify
                then
                    norm cfg env (List.tl stack) (reify_lift cfg.tcenv head m m' (closure_as_term cfg env t))
                else
                (* KM: We need to normalize at least to erase universes when extracting *)
                let t = norm cfg env [] t in
                if (U.is_pure_effect m
                    || U.is_ghost_effect m)
                && cfg.steps |> List.contains PureSubtermsWithinComputations
                then
                  let stack = Steps(cfg.steps, cfg.primitive_steps, cfg.delta_level)::stack in
                  let cfg =
                    { cfg with
                      steps=[PureSubtermsWithinComputations;
                             Primops;
                             AllowUnboundUniverses;
                             EraseUniverses;
                             Exclude Zeta];
                      delta_level=[Env.Inlining; Env.Eager_unfolding_only]
                    }
                  in
                  (* meta doesn't block reduction, but we need to put the label back *)
                  norm cfg env (Meta(Meta_monadic_lift(m, m', t), head.pos)::stack) head
                else
                  (* meta doesn't block reduction, but we need to put the label back *)
                  norm cfg env (Meta(Meta_monadic_lift(m, m', t), head.pos)::stack) head

              | _ ->
                begin match stack with
                  | _::_ ->
                    begin match m with
                      | Meta_labeled(l, r, _) ->
                        (* meta doesn't block reduction, but we need to put the label back *)
                        norm cfg env (Meta(m,r)::stack) head

                      | Meta_pattern args ->
                          let args = norm_pattern_args cfg env args in
                          norm cfg env (Meta(Meta_pattern args, t.pos)::stack) head //meta doesn't block reduction, but we need to put the label back

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
        end

(* Reifies the lifting of the term [e] of type [t] from computational  *)
(* effect [m] to computational effect [m'] using lifting data in [env] *)
and reify_lift (env : Env.env) e msrc mtgt t =
  (* check if the lift is concrete, if so replace by its definition on terms *)
  (* if msrc is PURE or Tot we can use mtgt.return *)
  if U.is_pure_effect msrc
  then
    let ed = Env.get_effect_decl env mtgt in
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
      failwith "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
    | Some {mlift={mlift_term=Some lift}} ->
      (* We don't have any reasonable wp to provide so we just pass unknow *)
      (* Usually the wp is only necessary to typecheck, so this should not *)
      (* create a big issue. *)
      lift t S.tun (U.mk_reify e)
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
        norm ({cfg with steps=[Eager_unfolding; UnfoldUntil Delta_constant; AllowUnboundUniverses]}) env [] t in
    let non_info t = non_informative (norm t) in
    match c.n with
    | Total _ -> c
    | GTotal(t,uopt) when non_info t -> {c with n=Total(t, uopt)}
    | Comp ct ->
        let l = Env.norm_eff_name cfg.tcenv ct.effect_name in
        if U.is_ghost_effect l
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

and norm_lcomp_opt : cfg -> env -> option<either<lcomp, residual_comp>> -> option<either<lcomp, residual_comp>> =
    fun cfg env lopt ->
        match lopt with
        | Some (Inl lc) ->
          let flags = filter_out_lcomp_cflags lc in
          if U.is_tot_or_gtot_lcomp lc
          then let t = norm cfg env [] lc.res_typ in
               if U.is_total_lcomp lc
               then Some (Inl (U.lcomp_of_comp (comp_set_flags (S.mk_Total t) flags)))
               else Some (Inl (U.lcomp_of_comp (comp_set_flags (S.mk_GTotal t) flags)))
          else Some (Inr (lc.eff_name, flags))
       | _ -> lopt


and rebuild (cfg:cfg) (env:env) (stack:stack) (t:term) : term =
  (* Pre-condition: t is in either weak or strong normal form w.r.t env, depending on *)
  (* whether cfg.steps constains WHNF In either case, it has no free de Bruijn *)
  (* indices *)
  match stack with
  | [] -> t

  | Debug tm :: stack ->
    if Env.debug cfg.tcenv <| Options.Other "print_normalized_terms"
    then BU.print2 "Normalized %s to %s\n" (Print.term_to_string tm) (Print.term_to_string t);
    rebuild cfg env stack t

  | Steps (s, ps, dl) :: stack ->
    rebuild ({cfg with steps=s; primitive_steps=ps; delta_level=dl}) env stack t

  | Meta(m, r)::stack ->
    let t = mk (Tm_meta(t, m)) r in
    rebuild cfg env stack t

  | MemoLazy r::stack ->
    set_memo r (env, t);
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

  | Arg (Clos(env, tm, m, _), aq, r) :: stack ->
    log cfg  (fun () -> BU.print1 "Rebuilding with arg %s\n" (Print.term_to_string tm));
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
    rebuild cfg env stack (maybe_simplify cfg t)

  | Match(env, branches, r) :: stack ->
    log cfg  (fun () -> BU.print1 "Rebuilding with match, scrutinee is %s ...\n" (Print.term_to_string t));
    //the scrutinee is always guaranteed to be a pure or ghost term
    //see tc.fs, the case of Tm_match and the comment related to issue #594
    let scrutinee = t in
    let norm_and_rebuild_match () =
      log cfg (fun () ->
          BU.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n"
                (Print.term_to_string scrutinee)
                (branches |> List.map (fun (p, _, _) -> Print.pat_to_string p) |> String.concat "\n\t"));
      let whnf = List.contains WHNF cfg.steps in
      let cfg_exclude_iota_zeta =
        let new_delta =
          cfg.delta_level |> List.filter (function
            | Env.Inlining
            | Env.Eager_unfolding_only -> true
            | _ -> false)
        in
        let steps' =
          if cfg.steps |> List.contains PureSubtermsWithinComputations
          then [Exclude Zeta]
          (* KM : Why are we excluding Iota (pattern matching) here ? *)
          else [Exclude Iota; Exclude Zeta]
        in
        {cfg with delta_level=new_delta;
                        steps=steps'@cfg.steps}
      in
      let norm_or_whnf env t =
        if whnf
        then closure_as_term cfg_exclude_iota_zeta env t
        else norm cfg_exclude_iota_zeta env [] t
      in
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
      rebuild cfg env stack (mk (Tm_match(scrutinee, branches)) r)
    in

    let rec is_cons head = match head.n with
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


    let rec matches_pat (scrutinee:term) (p:pat)
      : either<list<term>, bool>
        (* Inl ts: p matches t and ts are bindings for the branch *)
        (* Inr false: p definitely does not match t *)
        (* Inr true: p may match t, but p is an open term and we cannot decide for sure *)
      = let scrutinee = U.unmeta scrutinee in
        let head, args = U.head_and_args scrutinee in
        match p.v with
        | Pat_disj ps ->
          let mopt = BU.find_map ps (fun p ->
            let m = matches_pat scrutinee p in
            match m with
              | Inl _ -> Some m //definite match
              | Inr true -> Some m //maybe match; stop considering other cases
              | Inr false -> None (*definite mismatch*))
          in
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
          begin match (U.un_uinst head).n with
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
                          (List.map Print.term_to_string s |> String.concat "; "));
            //the elements of s are sub-terms of t
            //the have no free de Bruijn indices; so their env=[]; see pre-condition at the top of rebuild
            let env = List.fold_left (fun env t -> Clos([], t, BU.mk_ref (Some ([], t)), false)::env) env s in
            norm cfg env stack (guard_when_clause wopt b rest)
    in

    if cfg.steps |> List.contains (Exclude Iota)
    then norm_and_rebuild_match ()
    else matches scrutinee branches

let config s e =
    let d = s |> List.collect (function
        | UnfoldUntil k -> [Env.Unfold k]
        | Eager_unfolding -> [Env.Eager_unfolding_only]
        | Inlining -> [Env.Inlining]
        | _ -> []) in
    let d = match d with
        | [] -> [Env.NoDelta]
        | _ -> d in
    {tcenv=e; steps=s; delta_level=d; primitive_steps=built_in_primitive_steps@equality_ops}

let normalize_with_primitive_steps ps s e t =
    let c = config s e in
    let c = {config s e with primitive_steps=c.primitive_steps@ps} in
    norm c [] [] t
let normalize s e t = normalize_with_primitive_steps [] s e t
let normalize_comp s e t = norm_comp (config s e) [] t
let normalize_universe env u = norm_universe (config [] env) [] u
let ghost_to_pure env c = ghost_to_pure_aux (config [] env) [] c

let ghost_to_pure_lcomp env (lc:lcomp) =
    let cfg = config [Eager_unfolding; UnfoldUntil Delta_constant; EraseUniverses; AllowUnboundUniverses] env in
    let non_info t = non_informative (norm cfg [] [] t) in
    if U.is_ghost_effect lc.eff_name
    && non_info lc.res_typ
    then match downgrade_ghost_effect_name lc.eff_name with
         | Some pure_eff ->
           {lc with eff_name=pure_eff;
                    comp=(fun () -> ghost_to_pure env (lc.comp()))}
         | None -> //can't downgrade, don't know the particular incarnation of PURE to use
           lc
    else lc

let term_to_string env t =
  let t =
    try normalize [AllowUnboundUniverses] env t
    with e -> BU.print1_warning "Normalization failed with error %s" (BU.message_of_exn e) ; t
  in
  Print.term_to_string t

let comp_to_string env c =
  let c =
    try norm_comp (config [AllowUnboundUniverses] env) [] c
    with e -> BU.print1_warning "Normalization failed with error %s" (BU.message_of_exn e) ; c
  in
  Print.comp_to_string c

let normalize_refinement steps env t0 =
   let t = normalize (steps@[Beta]) env t0 in
   let rec aux t =
    let t = compress t in
    match t.n with
       | Tm_refine(x, phi) ->
         let t0 = aux x.sort in
         begin match t0.n with
            | Tm_refine(y, phi1) ->
              mk (Tm_refine(y, U.mk_conj phi1 phi)) t0.pos
            | _ -> t
         end
       | _ -> t in
   aux t

let unfold_whnf env t = normalize [WHNF; UnfoldUntil Delta_constant; Beta] env t
let reduce_uvar_solutions env t =
    normalize [Beta; NoDeltaSteps; CompressUvars; Exclude Zeta; Exclude Iota; NoFullNorm]
              env
              t

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
                       (U.lcomp_of_comp c |> Inl |> Some)

let eta_expand (env:Env.env) (t:term) : term =
  match !t.tk, t.n with
  | Some sort, _ ->
      eta_expand_with_type env t (mk sort t.pos)
  | _, Tm_name x ->
      eta_expand_with_type env t x.sort
  | _ ->
      let head, args = U.head_and_args t in
      begin match (SS.compress head).n with
      | Tm_uvar(_, thead) ->
        let formals, tres = U.arrow_formals thead in
        if List.length formals = List.length args
        then t
        else let _, ty, _ = env.type_of ({env with lax=true; use_bv_sorts=true; expected_typ=None}) t in
             eta_expand_with_type env t ty
      | _ ->
        let _, ty, _ = env.type_of ({env with lax=true; use_bv_sorts=true; expected_typ=None}) t in
        eta_expand_with_type env t ty
      end

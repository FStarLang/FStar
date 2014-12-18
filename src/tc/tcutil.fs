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

module Microsoft.FStar.Tc.Util

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Tc.Normalize
open Microsoft.FStar.Tc.Rel
open Microsoft.FStar.Absyn.Syntax

let t_unit   = syn dummyRange ktype <| mk_Typ_const (Util.withsort Const.unit_lid   ktype)
let t_bool   = syn dummyRange ktype <| mk_Typ_const (Util.withsort Const.bool_lid   ktype)
let t_uint8  = syn dummyRange ktype <| mk_Typ_const (Util.withsort Const.uint8_lid  ktype)
let t_int    = syn dummyRange ktype <| mk_Typ_const (Util.withsort Const.int_lid    ktype)
let t_int64  = syn dummyRange ktype <| mk_Typ_const (Util.withsort Const.int64_lid  ktype)
let t_string = syn dummyRange ktype <| mk_Typ_const (Util.withsort Const.string_lid ktype)
let t_float  = syn dummyRange ktype <| mk_Typ_const (Util.withsort Const.float_lid  ktype)
let t_char   = syn dummyRange ktype <| mk_Typ_const (Util.withsort Const.char_lid   ktype)

let syn' env k = syn (Tc.Env.get_range env) k

let typing_const env (s:sconst) = match s with 
  | Const_unit -> t_unit 
  | Const_bool _ -> t_bool
  | Const_int32 _ -> t_int
  | Const_string _ -> t_string
  | Const_float _ -> t_float
  | Const_char _ -> t_char
  | Const_int64 _ -> t_int64
  | Const_uint8 _ -> t_uint8
  | _ -> raise (Error("Unsupported constant", Tc.Env.get_range env))

let is_xvar_free (x:bvvdef) t = 
  let f = Util.freevars_typ t in
  Util.set_mem (bvd_to_bvar_s x tun) f.fxvs

let is_tvar_free (a:btvdef) t = 
  let f = Util.freevars_typ t in
  Util.set_mem (bvd_to_bvar_s a kun) f.ftvs

let check_and_ascribe env (e:exp) (t1:typ) (t2:typ) : exp * guard_t =
  let env = Env.set_range env e.pos in
  match try_subtype env t1 t2 with
    | None -> 
        if env.is_pattern
        then raise (Error(Tc.Errors.expected_pattern_of_type env t2 e t1, Tc.Env.get_range env))
        else raise (Error(Tc.Errors.expected_expression_of_type env t2 e t1, Tc.Env.get_range env))
    | Some f -> 
        let g = apply_guard f e in
        if debug env <| Options.Other "Rel"
        then Util.fprint1 "Applied guard is %s\n" <| guard_to_string env g;
        let e = Util.compress_exp e in
        let e = match e.n with 
            | Exp_bvar x -> mk_Exp_bvar (Util.bvd_to_bvar_s x.v t2) t2 e.pos 
            | _ -> {e with tk=t2} in
        e, g

let env_binders env = 
    if !Options.full_context_dependency 
    then let binders = Env.binders env in
         if !Options.verify
         then binders
         else binders |> List.filter (function 
                | Inl _, _ -> true
                | Inr x, _ -> begin match x.sort.n with 
                                 | Typ_fun _ -> false
                                 | _ -> true
                              end)
         else Env.t_binders env
let new_kvar env   = Rel.new_kvar (Env.get_range env) (env_binders env)   |> fst
let new_tvar env t = Rel.new_tvar (Env.get_range env) (env_binders env) t |> fst
let new_evar env t = Rel.new_evar (Env.get_range env) (env_binders env) t |> fst

let force_trivial env g = 
    if Rel.is_trivial g 
    then ()
    else raise (Error("Unexpected non-trivial guard", Env.get_range env))
    
let destruct_arrow_kind env tt k args : (Syntax.args * binders * knd) = 
    let ktop = compress_kind k |> Normalize.norm_kind [WHNF; Beta; Eta] env in 
    let r = Env.get_range env in
    let rec aux k = match k.n with 
        | Kind_arrow(bs, k') -> 
          let imp_follows = match args with 
            | (_, imp)::_ -> imp
            | _ -> false in
          let rec mk_implicits vars subst bs = match bs with 
            | b::brest -> 
              if snd b 
              then let imp_arg = match fst b with 
                    | Inl a -> Tc.Rel.new_tvar r vars (Util.subst_kind subst a.sort) |> fst |> (fun x -> Inl x, true) //set the implicit flag
                    | Inr x -> Tc.Rel.new_evar r vars (Util.subst_typ subst x.sort) |> fst |>  (fun x -> Inr x, true) in
                   let subst = if is_null_binder b then subst else  (subst_formal b imp_arg)::subst in
                   let imp_args, bs = mk_implicits vars subst brest in
                   imp_arg::imp_args, bs
              else [], subst_binders subst bs
            | _ -> [], subst_binders subst bs in
          if imp_follows 
          then [], bs, k' 
          else let imps, bs = mk_implicits (Tc.Env.binders env) [] bs in  
               imps, bs, k'

       | Kind_abbrev(_, k) -> aux k

       | Kind_uvar _ -> 
         let fvs = Util.freevars_kind k in
         let binders = Util.binders_of_freevars fvs in 
         let kres = Tc.Rel.new_kvar r binders |> fst in
         let bs = null_binders_of_args args in
         let kar = mk_Kind_arrow(bs, kres) r in
         force_trivial env <| keq env None k kar;
         [], bs, kres

       | _ -> raise (Error(Tc.Errors.expected_tcon_kind env tt ktop, r)) in

    aux ktop

(*
    Turns a disjunctive pattern p into a quadruple:
 *)
let pat_as_exps env p : (list<binding>     (* pattern-bound variables (which may appear in the branch of match) *)
                         * list<binding>   (* pattern-bound wild-card variables (may not appear in the branch, but do appear in expresions corresponding to the pattern) *)
                         * list<exp>       (* expressions corresponding to each arm of the disjunct *)
                         * pat) =          (* decorated pattern, with all the missing implicit args in p filled in *)
     let pvar_eq x y = match x, y with 
          | Env.Binding_var(x, _), Env.Binding_var(y, _) -> bvd_eq x y
          | Env.Binding_typ(x, _), Env.Binding_typ(y, _) -> bvd_eq x y
          | _ -> false in
  
     let vars_of_bindings bs =
        bs |> List.map (function 
           | Env.Binding_var(x, _) -> Inr x
           | Env.Binding_typ(x, _) -> Inl x
           | _ -> failwith "impos") in
  
     let rec pat_env env (p:pat) : list<Env.binding> * list<Env.binding> * Env.env = 
        match p.v with 
           | Pat_dot_term _
           | Pat_dot_typ _ 
           | Pat_constant _ -> [], [], env
           | Pat_wild x -> 
                let w = Env.Binding_var(x.v, new_tvar env ktype) in
                let env = Env.push_local_binding env w in
                [], [w], env
           | Pat_var (x, _) ->
                let b = Env.Binding_var(x.v, new_tvar env ktype) in
                let env = Env.push_local_binding env b in
                [b], [], env
           | Pat_twild a -> 
                let w = Env.Binding_typ(a.v, new_kvar env) in
                let env = Env.push_local_binding env w in
                [], [w], env
           | Pat_tvar a ->      
                let b = Env.Binding_typ(a.v, new_kvar env) in
                let env = Env.push_local_binding env b in 
                [b], [], env
           | Pat_cons(fv, pats) -> 
               let b, w, env = pats |> List.fold_left (fun (b, w, env) p -> 
                    let b', w', env = pat_env env p in
                    b'::b, w'::w, env)  ([], [], env) in
               List.rev b |> List.flatten, 
               List.rev w |> List.flatten, 
               env
           | Pat_disj _ -> failwith "impossible" in

     let rec pat_as_arg env (p:pat) : arg * pat = match p.v with
           | Pat_dot_term (x, _) -> 
                let t = new_tvar env ktype in
                let e = fst <| Rel.new_evar p.p [] t in //TODO: why empty vars?
                let p = {p with v=Pat_dot_term(x, e)} in
                varg e, p

           | Pat_dot_typ (a, _) -> 
                let k = new_kvar env in
                let t = new_tvar env k in
                let p = {p with v=Pat_dot_typ(a, t)} in
                (Inl t, true), p

           | Pat_constant c -> 
                let e = mk_Exp_constant c tun p.p in
                varg e, p

           | Pat_wild x -> 
                let e = mk_Exp_bvar x tun p.p in
                varg e, p

           | Pat_var (x, imp) -> 
                let e = mk_Exp_bvar x tun p.p in
                (Inr e, imp), p
 
           | Pat_twild a -> 
                let t = mk_Typ_btvar a kun p.p in
                targ t, p

           | Pat_tvar a ->      
                let t = mk_Typ_btvar a kun p.p in
                targ t, p

           | Pat_cons(fv, pats) -> 
               let args, pats = pats |> List.map (pat_as_arg env) |> List.unzip in
               let e = mk_Exp_meta(Meta_desugared(mk_Exp_app'(Util.fvar true fv.v fv.p, args) tun p.p, Data_app)) in
               varg e,
               {p with v=Pat_cons(fv, pats)}

           | Pat_disj _ -> failwith "impossible: nested disjunctive pattern" in

    let rec elaborate_pat env p = //Adds missing implicit patterns to constructor patterns
        match p.v with 
           | Pat_cons(fv, pats) -> 
               let pats = List.map (elaborate_pat env) pats in
               let t = Tc.Env.lookup_datacon env fv.v in
               let pats = match Util.function_formals t with 
                    | None -> []
                    | Some(f, _) -> 
                      let rec aux formals pats = match formals, pats with 
                        | [], [] -> []
                        | [], _::_ -> raise (Error("Too many pattern arguments", range_of_lid fv.v))
                        | _::_, [] -> 
                          formals |> List.map (fun f -> match f with 
                            | Inl t, _ -> 
                              let a = Util.bvd_to_bvar_s (Util.new_bvd None) kun in
                              withinfo (Pat_dot_typ (a, tun)) (Inl kun) (Syntax.range_of_lid fv.v)

                            | Inr _, true ->
                              let a = Util.gen_bvar tun in
                              withinfo (Pat_var(a, true)) (Inr tun) (Syntax.range_of_lid fv.v)

                            | _ -> raise (Error("Insufficient pattern arguments", range_of_lid fv.v)))

                        | f::formals', p::pats' -> 
                            begin match f, p.v with 
                                | (Inl _, _), Pat_tvar _ -> p::aux formals' pats'
                                | (Inl _, _), _ -> 
                                    let a = Util.bvd_to_bvar_s (Util.new_bvd None) kun in
                                    let p = withinfo (Pat_dot_typ (a, tun)) (Inl kun) (Syntax.range_of_lid fv.v) in
                                    p::aux formals' pats
                                | (Inr _, true), Pat_var(_, true) -> 
                                    p::aux formals' pats'
                                | (Inr _, true), _ ->
                                    let a = Util.gen_bvar tun in
                                    let p = withinfo (Pat_var(a, true)) (Inr tun) (Syntax.range_of_lid fv.v) in
                                    p::aux formals' pats
                                | (Inr _, false), _ ->
                                  p::aux formals' pats' 
                            end in
                      aux f pats in
               {p with v=Pat_cons(fv, pats)} 

        | _ -> p in

    let one_pat env p = 
        let p = elaborate_pat env p in
        let b, w, env = pat_env env p in
        let arg, p = pat_as_arg env p in
        match b |> Util.find_dup pvar_eq with 
            | Some (Env.Binding_var(x, _)) -> raise (Error(Tc.Errors.nonlinear_pattern_variable (Inr x), p.p))
            | Some (Env.Binding_typ(x, _)) -> raise (Error(Tc.Errors.nonlinear_pattern_variable (Inl x), p.p))
            | _ -> b, w, arg, p in


   let top_level_pat_as_args env (p:pat) : (list<Env.binding>                    (* pattern bound variables *)
                                            * list<Env.binding>                  (* pattern-bound wild variables *)
                                            * list<arg>                          (* pattern sub-terms *)
                                            * pat) =                             (* decorated pattern *)
        match p.v with 
           | Pat_disj [] -> failwith "impossible"

           | Pat_disj (q::pats) -> 
              let b, w, arg, q = one_pat env q in
              let w, args, pats = List.fold_right (fun p (w, args, pats) -> 
                  let b', w', arg, p = one_pat env p in
                  if not (Util.multiset_equiv pvar_eq b b')
                  then raise (Error(Tc.Errors.disjunctive_pattern_vars (vars_of_bindings b) (vars_of_bindings b'), Tc.Env.get_range env))
                  else (w'@w, arg::args, p::pats)) 
                  pats (w, [], []) in
              b, w, arg::args, {p with v=Pat_disj(q::pats)}

           | _ -> 
             let b, w, arg, p = one_pat env p in 
             b, w, [arg], p in

    let b, w, args, p = top_level_pat_as_args env p in
    let exps = args |> List.map (function 
        | Inl _, _ -> failwith "Impossible: top-level pattern must be an expression"
        | Inr e, _ -> e) in
    b, w, exps, p 

let decorate_pattern env p exps = 
    let rec aux p e = 
        let pkg q t = withinfo q (Inr t) p.p in
        let e = Util.unmeta_exp e in
        match p.v, e.n with 
            | Pat_constant _, Exp_constant _ -> pkg p.v e.tk

            | Pat_var (x,imp), Exp_bvar y -> 
              if Util.bvar_eq x y |> not
              then failwith (Util.format2 "Expected pattern variable %s; got %s" (Print.strBvd x.v) (Print.strBvd y.v));
              if Env.debug env <| Options.Other "Pat"
              then Util.fprint2 "Pattern variable %s introduced at type %s\n" (Print.strBvd x.v) (Normalize.typ_norm_to_string env y.sort);
              let s = Normalize.norm_typ [Normalize.Beta] env y.sort in
              let x = {x with sort=s} in
              pkg (Pat_var (x, imp)) e.tk

            | Pat_wild x, Exp_bvar y -> 
              if Util.bvar_eq x y |> not
              then failwith (Util.format2 "Expected pattern variable %s; got %s" (Print.strBvd x.v) (Print.strBvd y.v));
              let x = {x with sort=e.tk} in
              pkg (Pat_wild x) e.tk
            
            | Pat_dot_term(x, _), _ -> 
              let x = {x with sort=e.tk} in
              pkg (Pat_dot_term(x, e)) e.tk 

            | Pat_cons(fv, []), Exp_fvar (fv',_) -> 
              if Util.fvar_eq fv fv' |> not
              then failwith (Util.format2 "Expected pattern constructor %s; got %s" fv.v.str fv'.v.str);
              let fv = {fv with sort=e.tk} in
              pkg (Pat_cons(fv, [])) e.tk

            | Pat_cons(fv, argpats), Exp_app({n=Exp_fvar(fv', _);tk=t}, args) -> 
              if Util.fvar_eq fv fv' |> not
              then failwith (Util.format2 "Expected pattern constructor %s; got %s" fv.v.str fv'.v.str);
              let fv = {fv with sort=t} in

              let rec match_args matched_pats args argpats = match args, argpats with 
                | [], [] -> pkg (Pat_cons(fv, List.rev matched_pats)) e.tk
                | (Inl t, true)::args, _ -> (* implicit type argument *)
                  let x = Util.gen_bvar_p p.p t.tk in
                  let q = withinfo (Pat_dot_typ(x, t)) (Inl t.tk) p.p in
                  match_args (q::matched_pats) args argpats
                 
                | (Inr e, true)::args, _ -> (* implicit value argument *)  
                  let x = Util.gen_bvar_p p.p e.tk in
                  let q = withinfo (Pat_dot_term(x, e)) (Inr e.tk) p.p in
                  match_args (q::matched_pats) args argpats
                  
                | (Inl t, _)::args, pat::argpats -> 
                  let pat = aux_t pat t in
                  match_args (pat::matched_pats) args argpats

                | (Inr e, _)::args, pat::argpats -> 
                  let pat = aux pat e in
                  match_args (pat::matched_pats) args argpats

                | _ -> failwith "Unexpected number of pattern arguments" in

              match_args [] args argpats

           | _ -> failwith (Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" (Range.string_of_range p.p) (Print.pat_to_string p) (Print.exp_to_string e))
        
    and aux_t p t =
       let pkg q k = withinfo q (Inl k) p.p in
       let t = Util.compress_typ t in
       match p.v, t.n with
         | Pat_twild a, Typ_btvar b -> 
            if Util.bvar_eq a b |> not
            then failwith (Util.format2 "Expected pattern variable %s; got %s" (Print.strBvd a.v) (Print.strBvd b.v));
            let a = {a with sort=t.tk} in
            pkg (Pat_twild a) t.tk

         | Pat_tvar a, Typ_btvar b -> 
            if Util.bvar_eq a b |> not
            then failwith (Util.format2 "Expected pattern variable %s; got %s" (Print.strBvd a.v) (Print.strBvd b.v));
            let a = {a with sort=t.tk} in
            pkg (Pat_tvar a) t.tk

         | Pat_dot_typ(a, _), _ -> 
            let a = {a with sort=t.tk} in
            pkg (Pat_dot_typ(a, t)) t.tk
            
         | _ -> failwith (Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" (Range.string_of_range p.p) (Print.pat_to_string p) (Print.typ_to_string t)) in

    match p.v, exps with 
        | Pat_disj ps, _ when (List.length ps = List.length exps) -> 
          let ps = List.map2 aux ps exps in
          withinfo (Pat_disj ps) (Inr tun) p.p

        | _, [e] ->
          aux p e
          
        | _ -> failwith "Unexpected number of patterns"
 
 let rec decorated_pattern_as_exp (pat:pat) : list<either_var> * exp = 
    let t = match pat.sort with 
        | Inr t -> t 
        | Inl _ -> failwith "top-level pattern should be decorated with a type" in
    let pkg f = f t pat.p in

    let pat_as_arg p = 
        let vars, te = decorated_pattern_as_either p in 
        vars, (te, true) in
    
    match pat.v with 
        | Pat_disj _ -> failwith "Impossible" (* these are only on top-level patterns *)
    
        | Pat_constant c -> 
            [], mk_Exp_constant c |> pkg

        | Pat_wild x
        | Pat_var (x, _)  ->
            [Inr x], mk_Exp_bvar x |> pkg

        | Pat_cons(fv, pats) -> 
            let vars, args = pats |> List.map pat_as_arg |> List.unzip in
            let vars = List.flatten vars in
            vars,  mk_Exp_app'(mk_Exp_fvar(fv, true) fv.sort fv.p, args) |> pkg

        | Pat_dot_term(x, e) -> 
            [], e

        | Pat_twild _
        | Pat_tvar _
        | Pat_dot_typ _ -> failwith "Impossible: expected a term pattern" 

and decorated_pattern_as_typ (p:pat) : list<either_var> * typ = match p.v with 
    | Pat_twild a
    | Pat_tvar a -> 
        [Inl a], mk_Typ_btvar a a.sort p.p

    | Pat_dot_typ(a, t) ->
        [], t 
            
    | _ -> failwith "Expected a type pattern" 

and decorated_pattern_as_either (p:pat) =
    match p.v with 
        | Pat_twild _
        | Pat_tvar _
        | Pat_dot_typ _ -> 
            let vars, t = decorated_pattern_as_typ p in
            vars, Inl t

        | _ -> 
            let vars, e = decorated_pattern_as_exp p in
            vars, Inr e 


//DTuple u1 (\_:u1. u2) (\_:u1 u2. u3) ...
// where ui:Type
let mk_basic_dtuple_type env n = 
  let r = Tc.Env.get_range env in
  let l = Util.mk_dtuple_lid n r in
  let k = Tc.Env.lookup_typ_lid env l in
  let t = Util.ftv l k in
  let vars = Env.binders env in
  match k.n with 
    | Kind_arrow(bs, {n=Kind_type}) ->
      let args, _ = bs |> List.fold_left (fun (out, subst) (b, _) -> match b with 
        | Inr _ -> failwith "impossible"
        | Inl a -> 
          let k = Util.subst_kind subst a.sort in 
          let arg = match k.n with 
            | Kind_type -> 
              Rel.new_tvar r vars ktype |> fst 
            | Kind_arrow(bs, k) -> 
              mk_Typ_lam(bs, Rel.new_tvar r vars ktype |> fst) k r
            | _ -> failwith "Impossible" in
          let subst = (Inl(a.v, arg))::subst in 
          (targ arg::out, subst)) ([], []) in
      mk_Typ_app(t, List.rev args) ktype r

    | _ -> failwith "Impossible" 

let extract_lb_annotation (is_rec:bool) env t e = match t.n with 
  | Typ_unknown -> 
    let r = Env.get_range env in
    let mk_t_binder scope a = match a.sort.n with 
        | Kind_unknown ->
          let k =  Rel.new_kvar e.pos scope |> fst in
          {a with sort=k}
        | _ -> a in

    let mk_v_binder scope x = match x.sort.n with 
        | Typ_unknown -> 
          let t = Rel.new_tvar e.pos scope ktype |> fst in
          {x with sort=t}
        | _ -> x in 

    let rec aux vars e = match e.n with 
      | Exp_meta(Meta_desugared(e, _)) -> aux vars e 
      | Exp_ascribed(_, t) -> e, t

      | Exp_abs(bs, e) -> 
        let scope, bs = bs |> List.fold_left (fun (scope, bs) b -> match fst b with 
            | Inl a -> 
              let b = (Inl (mk_t_binder scope a), snd b) in
              let bs = bs@[b] in
              let scope = scope@[b] in
              scope, bs
            | Inr x -> 
              let b = (Inr (mk_v_binder scope x), snd b) in
              let scope = if !Options.full_context_dependency then scope@[b] else scope in//don't introduce dependent types, if there's no annotation, by default
              scope, bs@[b]) (vars,[]) in

        let e, res = aux scope e in 
        let c = Util.ml_comp res r in
        let t = mk_Typ_fun(bs, c) ktype e.pos in
        if debug env Options.High then Util.fprint2 "(%s) Using type %s\n" (Range.string_of_range r) (Print.typ_to_string t);
        mk_Exp_abs(bs, e) e.tk e.pos, t

      | _ -> e, Rel.new_tvar r vars ktype |> fst in

     aux (Env.t_binders env)  e       

  | _ -> e, t

(*********************************************************************************************)
(* Utils related to monadic computations *)
(*********************************************************************************************)
type comp_with_binder = option<Env.binding> * comp

let destruct_comp c : (typ * typ * typ) = 
  let wp, wlp = match c.effect_args with 
    | [(Inl wp, _); (Inl wlp, _)] -> wp, wlp
    | _ -> failwith (Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.effect_name.str 
      (List.map Print.arg_to_string c.effect_args |> String.concat ", ")) in
  c.result_typ, wp, wlp

let lift_comp c m lift =
  let _, wp, wlp = destruct_comp c in
  {effect_name=m;
   result_typ=c.result_typ;
   effect_args=[targ (lift c.result_typ wp); targ (lift c.result_typ wlp)]; 
   flags=[]}

let lift_and_destruct env c1 c2 = 
  let c1 = Tc.Normalize.weak_norm_comp env c1 in
  let c2 = Tc.Normalize.weak_norm_comp env c2 in 
  let m, lift1, lift2 = Tc.Env.join env c1.effect_name c2.effect_name in
  let m1 = lift_comp c1 m lift1 in
  let m2 = lift_comp c2 m lift2 in
  let md = Tc.Env.get_monad_decl env m in
  let a, kwp = Tc.Env.wp_signature env md.mname in
  (md, a, kwp), (destruct_comp m1), destruct_comp m2

let is_pure env c = 
  let c = Tc.Normalize.weak_norm_comp env c in
  lid_equals c.effect_name Const.pure_effect_lid

let mk_comp md result wp wlp flags = 
  mk_Comp ({effect_name=md.mname;
         result_typ=result;
         effect_args=[targ wp; targ wlp];
         flags=flags})

//let return_value env t v = Util.total_comp t (range_of_exp v (Env.get_range env))
let is_function t = match (compress_typ t).n with
    | Typ_fun _ -> true
    | _ -> false
  
let return_value env t v = 
  if is_function t then failwith (Util.format1 "(%s): Returning a function!" (Range.string_of_range (Env.get_range env)));
  let c = match Tc.Env.monad_decl_opt env Const.pure_effect_lid with 
    | None -> mk_Total t 
    | Some m -> 
       let a, kwp = Env.wp_signature env Const.pure_effect_lid in
       let k = Util.subst_kind [Inl(a.v, t)] kwp in
       let wp = Tc.Normalize.norm_typ [Beta] env <| mk_Typ_app(m.ret, [targ t; varg v]) k v.pos in
       let wlp = wp in
       mk_comp m t wp wlp [RETURN] in
  if debug env Options.High
  then Util.fprint2 "(%s) returning at comp type %s\n" (Range.string_of_range v.pos) (Normalize.comp_typ_norm_to_string env c);
  c

let bind env e1opt (c1:comp) ((b, c2):comp_with_binder) : comp = 
  if debug env Options.Extreme
  then 
    (let bstr = match b with 
      | None -> "none"
      | Some (Env.Binding_var(x, _)) -> Print.strBvd x
      | _ -> "??" in
    Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" (Print.comp_typ_to_string c1) bstr (Print.comp_typ_to_string c2));
  let try_simplify () = 
    let aux () = 
        if Util.is_trivial_wp c1
        then match b with 
                | None -> Some c2 
                | Some (Env.Binding_lid _) -> Some c2
                | Some (Env.Binding_var _) -> 
                    if Util.is_ml_comp c2 //|| not (Util.is_free [Inr x] (Util.freevars_comp c2))
                    then Some c2
                    else None
                | _ -> None
        else if Util.is_ml_comp c1 && Util.is_ml_comp c2 then Some c2
        else None in
    match e1opt, b with 
        | Some e, Some (Env.Binding_var(x,_)) -> 
            if Util.is_total_comp c1 && not (Syntax.is_null_bvd x)
            then Some <| Util.subst_comp [Inr(x, e)] c2
            else aux ()
        | _ -> aux () in
  match try_simplify () with 
    | Some c -> c
    | None -> 
      let (md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2) = lift_and_destruct env c1 c2 in 
      let bs = match b with 
        | None -> [null_v_binder t1]
        | Some (Env.Binding_var(x, t1)) -> [v_binder (bvd_to_bvar_s x t1)]
        | Some (Env.Binding_lid(l, t1)) -> [null_v_binder t1]
        | _ -> failwith "Unexpected type-variable binding" in
      let mk_lam wp = mk_Typ_lam(bs, wp) (mk_Kind_arrow(bs, wp.tk) wp.pos) wp.pos in
      let wp_args = [targ t1; targ t2; targ wp1; targ wlp1; targ (mk_lam wp2); targ (mk_lam wlp2)] in
      let wlp_args = [targ t1; targ t2; targ wlp1; targ (mk_lam wlp2)] in
//      if debug env
//      then printfn "Making bind c1=%s\nc2=%s\nlifted to %s\n" (Print.comp_typ_to_string c1) (Print.comp_typ_to_string c2) (md.mname.str);
      let k = Util.subst_kind [Inl(a.v, t2)] kwp in
      let wp = mk_Typ_app(md.bind_wp, wp_args) k t2.pos in
      let wlp = mk_Typ_app(md.bind_wlp, wlp_args) k t2.pos in
      let c = mk_comp md t2 wp wlp [] in
//      if debug env then printfn "Result comp type is %s\n" (Print.comp_typ_to_string c);
//      if debug env then printfn "Normalized comp type is %s\n" (Print.comp_typ_to_string (Comp <| Normalize.normalize_comp env c));
      c
     
let lift_formula env t mk_wp mk_wlp f = 
  let md_pure = Tc.Env.get_monad_decl env Const.pure_effect_lid in
  let a, kwp = Tc.Env.wp_signature env md_pure.mname in 
  let k = Util.subst_kind [Inl(a.v, t)] kwp in
  let wp = mk_Typ_app(mk_wp, [targ t; targ f]) k f.pos in
  let wlp = mk_Typ_app(mk_wlp, [targ t; targ f]) k f.pos in
  mk_comp md_pure t_unit wp wlp []

let lift_assertion env f =
  let assert_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assert_pure_lid in
  let assume_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assume_pure_lid in
  lift_formula env t_unit assert_pure assume_pure f

let lift_assumption env f =
  let assume_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assume_pure_lid in
  lift_formula env t_unit assume_pure assume_pure f

let lift_pure env t f = 
  let md = Tc.Env.get_monad_decl env Const.pure_effect_lid in
  let a, kwp = Tc.Env.wp_signature env md.mname in 
  let k = Util.subst_kind [Inl(a.v, t)] kwp in
  let trivial = mk_Typ_app(md.trivial, [targ t]) k f.pos in
  let wp = mk_Typ_app(md.assert_p, [targ t; targ f; targ trivial]) k f.pos in
  let wlp = mk_Typ_app(md.assume_p, [targ t; targ f; targ trivial]) k f.pos in
  mk_comp md t wp wlp []

let unlabel t = mk_Typ_meta(Meta_refresh_label(t, None, t.pos))

let refresh_comp_label env b c = 
    if Util.is_ml_comp c then c
    else match c.n with 
    | Total _ -> c
    | Comp ct -> 
      if Tc.Env.debug env Options.Low
      then (Util.fprint1 "Refreshing label at %s\n" (Range.string_of_range <| Env.get_range env));
      let c' = Tc.Normalize.weak_norm_comp env c in
      if not <| lid_equals ct.effect_name c'.effect_name && Tc.Env.debug env Options.Low
      then Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" (Print.comp_typ_to_string c) (Print.comp_typ_to_string <| mk_Comp c');
      let t, wp, wlp = destruct_comp c' in 
      let wp = mk_Typ_meta(Meta_refresh_label(wp, Some b, Env.get_range env)) in
      let wlp = mk_Typ_meta(Meta_refresh_label(wlp, Some b, Env.get_range env)) in
      Syntax.mk_Comp ({c' with effect_args=[targ wp; targ wlp]; flags=c'.flags})

let label reason r f = 
    let label = Util.format2 "%s (%s)" reason (Range.string_of_range r) in
    Syntax.mk_Typ_meta(Meta_labeled(f, label, true))
let label_opt reason r f = match reason with 
    | None -> f
    | Some reason -> 
        if not <| !Options.verify
        then f
        else label (reason()) r f

let label_guard reason r g = match g with 
    | Trivial -> g
    | NonTrivial f -> NonTrivial (label reason r f)

let weaken_guard g1 g2 = match g1, g2 with 
    | NonTrivial f1, NonTrivial f2 ->
      let g = (Util.mk_imp f1 f2) in
      NonTrivial g
    | _ -> g2

let weaken_precondition env c f = match f with 
  | Trivial -> c
  | NonTrivial f -> 
    if Util.is_ml_comp c then c
    else
      let c = Tc.Normalize.weak_norm_comp env c in
      let res_t, wp, wlp = destruct_comp c in
      let md = Tc.Env.get_monad_decl env c.effect_name in 
      let wp = mk_Typ_app(md.assume_p, [targ res_t; targ f; targ wp]) wp.tk wp.pos in
      let wlp = mk_Typ_app(md.assume_p, [targ res_t; targ f; targ wlp]) wlp.tk wlp.pos in
      mk_comp md res_t wp wlp c.flags

let strengthen_precondition (reason:option<(unit -> string)>) env (e:exp) (c:comp) f = match f with 
  | Trivial -> c
  | NonTrivial f -> 
    if debug env Options.High then Util.fprint2 "\tStrengthening precondition %s with %s\n" (Normalize.comp_typ_norm_to_string env c) (Normalize.typ_norm_to_string env f);
    let c = 
        if Util.is_pure_comp c && not (is_function (Util.comp_result c))
        then let x = Util.gen_bvar (Util.comp_result c) in
             let xexp = Util.bvar_to_exp x in
             let xret = return_value env x.sort (Util.bvar_to_exp x) in
             let xbinding = Env.Binding_var(x.v, x.sort) in
             bind env (Some e) c (Some xbinding, xret)
        else c in
    let c = Tc.Normalize.weak_norm_comp env c in
    let res_t, wp, wlp = destruct_comp c in
    //if debug env then Util.fprint1 "\tWp is %s" (Print.typ_to_string wp);
    let md = Tc.Env.get_monad_decl env c.effect_name in 
    let wp = mk_Typ_app(md.assert_p, [targ res_t; targ <| label_opt reason (Env.get_range env) f; targ wp]) wp.tk wp.pos in
    let wlp = mk_Typ_app(md.assume_p, [targ res_t; targ f; targ wlp]) wlp.tk wlp.pos in
    let c2 = mk_comp md res_t wp wlp [] in
   // if debug env then Util.fprint1 "\tStrengthened precondition is %s" (Print.comp_typ_to_string c2);
    c2
let bind_cases env (res_t:typ) (cases:list<(formula * comp)>) : comp =
    if List.length cases = 0 then failwith "Empty cases!"; (* TODO: Fix precedence of semi colon *)
    if debug env Options.Extreme then Util.fprint1 "bind_cases, res_t is %s\n" (Print.typ_to_string res_t);
    let ifthenelse md res_t g wp_t wp_e = mk_Typ_app(md.if_then_else, [targ res_t; targ g; targ wp_t; targ wp_e]) wp_t.tk (Range.union_ranges wp_t.pos wp_e.pos) in
    let default_case = 
        let post_k = mk_Kind_arrow([null_v_binder res_t], ktype) res_t.pos in
        let kwp = mk_Kind_arrow([null_t_binder post_k], ktype) res_t.pos in
        let post = Util.bvd_to_bvar_s (Util.new_bvd None) post_k in
        let wp = mk_Typ_lam([t_binder post], label Errors.exhaustiveness_check (Env.get_range env) <| Util.ftv Const.false_lid ktype) kwp res_t.pos in
        let wlp = mk_Typ_lam([t_binder post], Util.ftv Const.true_lid ktype) kwp res_t.pos in
        let md = Tc.Env.get_monad_decl env Const.pure_effect_lid in
        mk_comp md res_t wp wlp [] in 
    let comp = List.fold_right (fun (g, cthen) celse ->
        let (md, a, kwp), (res_t, wp_then, wlp_then), (_, wp_else, wlp_else) = lift_and_destruct env cthen celse in
        mk_comp md res_t (ifthenelse md res_t g wp_then wp_else) (ifthenelse md res_t g wlp_then wlp_else) []) cases default_case in
    let comp = comp_to_comp_typ comp in
    let md = Tc.Env.get_monad_decl env comp.effect_name in
    let res_t, wp, wlp = destruct_comp comp in
    let wp = mk_Typ_app(md.ite_wp, [targ res_t; targ wlp; targ wp]) wp.tk wp.pos in
    let wlp = mk_Typ_app(md.ite_wlp, [targ res_t; targ wlp]) wlp.tk wlp.pos in
    mk_comp md res_t wp wlp []
 
let close_comp env bindings (c:comp) = 
  if Util.is_ml_comp c then c
  else
    let close_wp md res_t bindings wp0 =  
      List.fold_right (fun b wp -> match b with 
        | Env.Binding_var(x, t) -> 
          let bs = [v_binder <| bvd_to_bvar_s x t] in
          let wp = mk_Typ_lam(bs, wp) (mk_Kind_arrow(bs, wp0.tk) wp0.pos) wp.pos in
          mk_Typ_app(md.close_wp, [targ res_t; targ t; targ wp]) wp0.tk wp0.pos

        | Env.Binding_typ(a, k) -> //A bit sloppy here: close_wp_t is only for Type; overloading it here for all kinds
          let bs = [t_binder <| bvd_to_bvar_s a k] in
          let wp = mk_Typ_lam(bs, wp) (mk_Kind_arrow(bs, wp0.tk) wp0.pos) wp.pos in
          mk_Typ_app(md.close_wp_t, [targ res_t; targ wp]) wp0.tk wp0.pos 

        | Env.Binding_lid(l, t) -> 
          (* TODO: replace every occurrence of l in wp with a fresh bound var, abstract over the bound var and then close it.
                   Except that it is highly unlikely for the wp to actually contain such a free occurrence of l *)
          wp
        | Env.Binding_sig s -> failwith "impos") bindings wp0 in //(Printf.sprintf "NYI close_comp_typ with binding %A" b)) 
    let c = Tc.Normalize.weak_norm_comp env c in
    let t, wp, wlp = destruct_comp c in
    let md = Tc.Env.get_monad_decl env c.effect_name in
    let wp = close_wp md c.result_typ bindings wp in
    let wlp = close_wp md c.result_typ bindings wlp in
    mk_comp md c.result_typ wp wlp c.flags

let check_comp env (e:exp) (c:comp) (c':comp) : exp * comp * guard_t = 
  //printfn "Checking sub_comp:\n%s has type %s\n\t<:\n%s\n" (Print.exp_to_string e) (Print.comp_typ_to_string c) (Print.comp_typ_to_string c');
  match Tc.Rel.sub_comp env c c' with 
    | None -> raise (Error(Tc.Errors.computed_computation_type_does_not_match_annotation env e c c', Tc.Env.get_range env))
    | Some g -> e, c', g

let maybe_assume_result_eq_pure_term env (e:exp) (c:comp) : comp = 
  if not (is_pure env c) then c
  else match (compress_typ (Util.comp_result c)).n with 
    | Typ_fun _ -> c (* no need to include equalities for functions *)
    | _ -> 
       let c = Tc.Normalize.weak_norm_comp env c in
       let t = c.result_typ in
       let c = mk_Comp c in 
       let x = Util.new_bvd None in
       let xexp = Util.bvd_to_exp x t in
       let ret = return_value env t xexp in
       let eq_ret = weaken_precondition env ret (NonTrivial (Util.mk_eq xexp e)) in
       comp_set_flags (bind env None c (Some (Env.Binding_var(x, t)), eq_ret)) (comp_flags c)

let maybe_instantiate env e t = 
  let t = compress_typ t in 
  if not (env.instantiate_targs && env.instantiate_vargs) then e, t else
  match t.n with 
    | Typ_fun(bs, c) -> 
      let rec aux subst = function 
        | (Inl a, _)::rest -> 
          let k = Util.subst_kind subst a.sort in
          let t = new_tvar env k in
          let subst = (Inl(a.v, t))::subst in 
          let args, bs, subst = aux subst rest in 
          (Inl t, true)::args, bs, subst  

        | (Inr x, true)::rest -> 
          let t = Util.subst_typ subst x.sort in 
          let v = new_evar env t in
          let subst = (Inr(x.v, v))::subst in 
          let args, bs, subst = aux subst rest in 
          (Inr v, true)::args, bs, subst

        | bs -> [], bs, subst in 
     let args, bs, subst = aux [] bs in
     let mk_exp_app e args t = match args with 
        | [] -> e 
        | _ -> mk_Exp_app(e, args) t e.pos in
     begin match bs with 
        | [] -> 
            if Util.is_total_comp c
            then let t = Util.subst_typ subst (Util.comp_result c) in
                 mk_exp_app e args t, t
            else e, t //don't instantiate implicitly, if it has an effect
        | _ -> 
            let t = mk_Typ_fun(bs, c) ktype e.pos |> Util.subst_typ subst in 
            mk_exp_app e args t, t
     end

  | _ -> e, t


(**************************************************************************************)
(* Calling the solver *)
(**************************************************************************************)
let try_solve env f = env.solver.solve env f 
let report env errs = 
    Tc.Errors.report (Tc.Env.get_range env)
                     (Tc.Errors.failed_to_prove_specification errs)

let discharge_guard env (g:guard_t) = 
    let ok, errs = Rel.try_discharge_guard env g in
    if not ok then report env errs

(**************************************************************************************)
(* Generalizing types *)
(**************************************************************************************)
let check_uvars r t = 
  let uvt = Util.uvars_in_typ t in
  if Util.set_count uvt.uvars_e + 
     Util.set_count uvt.uvars_t + 
     Util.set_count uvt.uvars_k > 0
  then
    let ue = List.map Print.uvar_e_to_string (Util.set_elements uvt.uvars_e) in
    let ut = List.map Print.uvar_t_to_string (Util.set_elements uvt.uvars_t) in
    let uk = List.map Print.uvar_k_to_string (Util.set_elements uvt.uvars_k) in
    let union = String.concat ","  (ue @ ut @ uk) in
    (* ignoring the hide_uvar_nums and print_implicits flags here *)
    let hide_uvar_nums_saved = !Options.hide_uvar_nums in
    let print_implicits_saved = !Options.print_implicits in
    Options.hide_uvar_nums := false;
    Options.print_implicits := true;
    Tc.Errors.report r
      (format2 "Unconstrained unification variables %s in type signature %s; \
       please add an annotation" union (Print.typ_to_string t));
    Options.hide_uvar_nums := hide_uvar_nums_saved;
    Options.print_implicits := print_implicits_saved

let gen env (ecs:list<(exp * comp)>) : option<list<(exp * comp)>> =
  if not <| (Util.for_all (fun (_, c) -> Util.is_pure_comp c) ecs) //No value restriction in F*---generalize the types of pure computations
  then None
  else
     let norm c =
        if debug env Options.Medium then Util.fprint1 "Normalizing before generalizing:\n\t %s" (Print.comp_typ_to_string c);    
         let steps = [Eta;Delta;Beta;SNComp] in
         let c = if !Options.verify then 
                 Normalize.norm_comp steps env c
                 else Normalize.norm_comp [Beta; Delta] env c
         in
        if debug env Options.Medium then Util.fprint1 "Normalized to:\n\t %s" (Print.comp_typ_to_string c);
        c in
     let env_uvars = Env.uvars_in_env env in
     let gen_uvars uvs = Util.set_difference uvs env_uvars.uvars_t |> Util.set_elements in
     let should_gen t = match t.n with 
        | Typ_fun(bs, _) -> 
            if bs |> Util.for_some (function (Inl _, _) -> true | _ -> false)
            then false (* contains an explicit type abstraction; don't generalize further *)
            else true
        | _ -> true in

     let uvars = ecs |> List.map (fun (e, c) -> 
          let t = Util.comp_result c |> Util.compress_typ in 
          if not <| should_gen t
          then ([], e, c)
          else let c = norm c in 
               let ct = comp_to_comp_typ c in
               let t = ct.result_typ in
               let uvt = Util.uvars_in_typ t in
               let uvs = gen_uvars uvt.uvars_t in 
               if !Options.verify && not <| Util.is_total_comp c
               then begin
                  let _, wp, _ = destruct_comp ct in 
                  let binder = [null_v_binder t] in
                  let post = mk_Typ_lam(binder, Util.ftv Const.true_lid ktype) (mk_Kind_arrow(binder, ktype) t.pos) t.pos in
                  let vc = Normalize.norm_typ [Delta; Beta] env (syn wp.pos ktype <| mk_Typ_app(wp, [targ post])) in
                  discharge_guard env (Rel.guard_of_guard_formula <| NonTrivial vc)
               end;
               uvs, e, c) in 

     let ecs = uvars |> List.map (fun (uvs, e, c) -> 
          let tvars = uvs |> List.map (fun (u, k) -> 
            let a = match Unionfind.find u with 
              | Fixed ({n=Typ_btvar a})
              | Fixed ({n=Typ_lam(_, {n=Typ_btvar a})}) -> Util.bvd_to_bvar_s a.v k
              | Fixed _ -> failwith "Unexpected instantiation of mutually recursive uvar"
              | _ -> 
                  let a = Util.new_bvd (Some <| Tc.Env.get_range env) in
                  let t = Util.close_for_kind (Util.bvd_to_typ a ktype) k in
                  //let t = Util.bvd_to_typ a k in
                  unchecked_unify u t; 
                  Util.bvd_to_bvar_s a ktype in
            t_binder a) in
    
          let t = match Util.comp_result c |> Util.function_formals with 
            | Some (bs, cod) -> mk_Typ_fun(tvars@bs, cod) ktype c.pos 
            | None -> match tvars with [] -> Util.comp_result c | _ -> mk_Typ_fun(tvars, c) ktype c.pos in
     
          let e = match tvars with
            | [] -> e
            | _ -> mk_Exp_abs'(tvars, e) t e.pos in
          e, mk_Total t) in
     Some ecs 


let generalize env (lecs:list<(lbname*exp*comp)>) : (list<(lbname*exp*comp)>) = 
  if debug env Options.Low then Util.fprint1 "Generalizing: %s" (List.map (fun (lb, _, _) -> Print.lbname_to_string lb) lecs |> String.concat ", ");
  match gen env (lecs |> List.map (fun (_, e, c) -> (e, c))) with 
    | None -> lecs
    | Some ecs -> 
      List.map2 (fun (l, _, _) (e, c) -> 
         if debug env Options.Medium then Util.fprint3 "(%s) Generalized %s to %s" (Range.string_of_range e.pos) (Print.lbname_to_string l) (Print.typ_to_string (Util.comp_result c));
      (l, e, c)) lecs ecs

 
let weaken_result_typ env (e:exp) (c:comp) (t:typ) : exp * comp * guard_t = 
  let aux e c = 
      let ct = Tc.Normalize.weak_norm_comp env c in
      let tc, _, _ = destruct_comp ct in
      match Tc.Rel.try_subtype env tc t with
        | None -> None
        | Some g -> 
           begin match g.guard_f with 
               | Trivial -> Some (e, mk_Comp ct, g)
               | NonTrivial f -> 
                  let g = {g with guard_f=Trivial} in
                  let a, kwp = Env.wp_signature env Const.pure_effect_lid in
                  let k = Util.subst_kind [Inl(a.v, t)] kwp in
                  let md = Tc.Env.get_monad_decl env ct.effect_name in
                  let x = new_bvd None in
                  let xexp = Util.bvd_to_exp x t in
                  let wp = mk_Typ_app(md.ret, [targ t; varg xexp]) k xexp.pos  in
                  let cret = mk_comp md t wp wp ct.flags in
                  let eq_ret = strengthen_precondition (Some <| Errors.subtyping_failed env tc t) (Env.set_range env e.pos) e cret (NonTrivial (mk_Typ_app(f, [varg xexp]) ktype f.pos)) in
                  let eq_ret = 
                    if Util.is_pure_comp c 
                    then weaken_precondition env eq_ret (NonTrivial (Util.mk_eq xexp e))
                    else eq_ret in 
                  let c = bind env (Some e) (mk_Comp ct) (Some(Env.Binding_var(x, tc)), eq_ret) in
                  Some(e, c, g)
            end in
  let must = function 
    | Some ec -> ec
    | None -> subtype_fail env (Util.comp_result c) t in
  match aux e c with
    | None -> (* before giving up, try again after generalizing the type of e, if possible *)
      begin match gen env [e,c] with 
        | Some ([(e,c)]) -> aux e c |> must
        | _ -> Rel.subtype_fail env (Util.comp_result c) t
      end
    | Some ecg -> ecg

let check_total env c : bool * list<string> = 
  if Util.is_total_comp c 
  then true, []
  else
      let steps = [Normalize.Beta; Normalize.SNComp] in
      let c = Tc.Normalize.norm_comp steps env c in
      match Tc.Rel.sub_comp env c (Util.total_comp (Util.comp_result c) (Env.get_range env)) with 
        | Some g -> try_discharge_guard env g 
        | _ -> false, []

let refine_data_type env l (formals:binders) (result_t:typ) = 
    match formals with 
        | [] -> result_t
        | _ -> 
            let r = range_of_lid l in 
            let formals, args = Util.args_of_binders formals in
            let basic_t = mk_Typ_fun(formals, mk_Total result_t) ktype r in
            let v = mk_Exp_app({Util.fvar true l r with tk=basic_t}, args) result_t r in
            mk_Typ_fun(formals, return_value env result_t v) ktype r


(* Having already seen_args to head (from right to left), 
   compute the guard, if any, for the next argument, 
   if head is a short-circuiting operator *)
let short_circuit_guard (head:either<typ, exp>) (seen_args:args) : guard_t = 
    let short_bin_op_e f : args -> guard_formula = function
        | [] -> (* no args seen yet *) Trivial
        | [(Inr fst, _)] -> f fst
        | _ -> failwith "Unexpexted args to binary operator" in
    let short_bin_op_t f : args -> guard_formula = function
        | [] -> (* no args seen yet *) Trivial
        | [(Inl fst, _)] -> f fst
        | _ -> failwith "Unexpexted args to binary operator" in
    
    let op_and_e e =  Util.b2t e |> NonTrivial in
    let op_or_e e = Util.mk_neg (Util.b2t e) |> NonTrivial in
    let op_and_t t = unlabel t |> NonTrivial in
    let op_or_t t =  unlabel t |> Util.mk_neg |> NonTrivial in
    let op_imp_t t = unlabel t |> NonTrivial in
    let short_op_ite : args -> guard_formula = function 
        | [] -> Trivial
        | [(Inl guard, _)] -> NonTrivial guard
        | [_then;(Inl guard, _)] -> Util.mk_neg guard |> NonTrivial 
        | _ -> failwith "Unexpected args to ITE" in 
    let table = 
        [(Const.op_And,  short_bin_op_e op_and_e);
         (Const.op_Or,   short_bin_op_e op_or_e);
         (Const.and_lid, short_bin_op_t op_and_t);
         (Const.or_lid,  short_bin_op_t op_or_t);
         (Const.imp_lid, short_bin_op_t op_imp_t);
         (Const.ite_lid, short_op_ite);] in

    let head_lid = match head with 
        | Inr ({n=Exp_fvar(fv, _)}) -> Some fv.v
        | Inl ({n=Typ_const fv}) -> Some fv.v 
        | _ -> None in
    match head_lid with 
        | None -> Rel.guard_of_guard_formula Trivial
        | Some lid -> 
          begin match Util.find_map table (fun (x, mk) -> if lid_equals x lid then Some (mk seen_args) else None) with 
            | None -> Rel.guard_of_guard_formula Trivial
            | Some g -> Rel.guard_of_guard_formula g
          end
        
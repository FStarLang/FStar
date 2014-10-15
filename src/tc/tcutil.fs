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
  | Const_uint8 _ -> t_char
  | _ -> raise (Error("Unsupported constant", Tc.Env.get_range env))

let is_xvar_free (x:bvvdef) t = 
  let f = Util.freevars_typ t in
  Util.set_mem (bvd_to_bvar_s x tun) f.fxvs

let is_tvar_free (a:btvdef) t = 
  let f = Util.freevars_typ t in
  Util.set_mem (bvd_to_bvar_s a kun) f.ftvs

let close_guard (b:binders) (g:guard_t) : guard_t = match g with 
  | Trivial -> g
  | NonTrivial f -> NonTrivial <|
   List.fold_right (fun b f -> match b with 
      | Inr x, _ -> Util.mk_forall x f
      | Inl a, _ -> Util.mk_forallT a f) b f

let apply_guard g e = match g with 
    | Trivial -> g
    | NonTrivial f -> NonTrivial (syn f.pos ktype <| mk_Typ_app(f, [varg e]))

let check_and_ascribe env (e:exp) (t1:typ) (t2:typ) : exp * guard_t =
  let env = Env.set_range env e.pos in
  match try_subtype env t1 t2 with
    | None -> 
        if env.is_pattern
        then raise (Error(Tc.Errors.expected_pattern_of_type t2 e t1, Tc.Env.get_range env))
        else raise (Error(Tc.Errors.expected_expression_of_type t2 e t1, Tc.Env.get_range env))
    | Some f -> 
        {e with tk=t2}, apply_guard f e

let new_kvar env   = Rel.new_kvar (Env.get_range env) (Env.binders env)   |> fst
let new_tvar env t = Rel.new_tvar (Env.get_range env) (Env.binders env) t |> fst

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
                   let subst = if is_null_binder b then subst else extend_subst (subst_formal b imp_arg) subst in
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
//         printfn "(%s) instantiating %s to %s" (Range.string_of_range r) (Print.kind_to_string k) (Print.kind_to_string kar);
         trivial <| keq env None k kar;
//         printfn "(%s) got  %s" (Range.string_of_range r) (Print.kind_to_string k);
         [], bs, kres

       | _ -> raise (Error(Tc.Errors.expected_tcon_kind tt ktop, r)) in

    aux ktop

let pat_as_exps env p : list<exp> = 
  let single = function 
    | [te] -> te
    | _ -> failwith "impossible" in
  let r = Env.get_range env in
  let rec aux p = match p with
    | Pat_wild ->  [Inr (fst <| Rel.new_evar r [] (new_tvar env ktype))] //TODO: why empty vars?
    | Pat_twild  -> [Inl (fst <| Rel.new_tvar r (Tc.Env.t_binders env) (new_kvar env))] 
    | Pat_var x -> [Inr (Util.bvd_to_exp x (new_tvar env ktype))]
    | Pat_tvar a -> [Inl (Util.bvd_to_typ a (new_kvar env))]
    | Pat_constant c -> [Inr (syn' env tun <| mk_Exp_constant c)]
    | Pat_cons(l, pats) -> 
      let args = List.map (fun p -> List.hd (aux p), false) pats in 
      [Inr (Util.mk_data l args)]
    | Pat_disj pats -> 
      pats |> List.map (fun p -> single <| aux p)
    | Pat_withinfo(p, r) -> 
      aux p |> List.map (function 
        | Inr (e) -> Inr ({e with pos=r})
        | Inl t -> Inl ({t with pos=r})) in
  List.map (function 
    | Inl _ -> failwith "Impossible"
    | Inr (e) -> e) (aux p)    

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
          let subst = extend_subst (Inl(a.v, arg)) subst in 
          (targ arg::out, subst)) ([], []) in
      mk_Typ_app(t, List.rev args) ktype r

    | _ -> failwith "Impossible" 

let extract_lb_annotation is_rec env t e = match t.n with 
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
            | Inr x -> //don't introduce dependent types, if there's no annotation
              let b = (Inr (mk_v_binder scope x), snd b) in
              scope, bs@[b]) (vars,[]) in

        let e, res = aux scope e in 
        let c = 
            if is_rec then Util.ml_comp res r 
            else (failwith "Building a cvar needlessly!") in//; Rel.new_cvar r (vars@bs) res |> fst) in
        let t = mk_Typ_fun(bs, c) ktype e.pos in
        if debug env Options.High then Util.fprint2 "(%s) Using type %s" (Range.string_of_range r) (Print.typ_to_string t);
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
    | _ -> failwith (Util.format2 "Impossible: Got a computation %s with effect args %s" c.effect_name.str 
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

let return_value env t v = 
  (match (compress_typ t).n with
    | Typ_fun _ -> failwith (Util.format1 "(%s): Returning a function!" (Range.string_of_range (Env.get_range env)))
    | _ -> ());
  let c = match Tc.Env.monad_decl_opt env Const.pure_effect_lid with 
    | None -> mk_Total t 
    | Some m -> 
       let a, kwp = Env.wp_signature env Const.pure_effect_lid in
       let k = Util.subst_kind [Inl(a.v, t)] kwp in
       let wp = Tc.Normalize.norm_typ [Beta] env <| mk_Typ_app(m.ret, [targ t; varg v]) k v.pos in
       let wlp = wp in
       mk_comp m t wp wlp [RETURN] in
  if debug env Options.High
  then Util.fprint2 "(%s) returning at comp type %s" (Range.string_of_range v.pos) (Print.comp_typ_to_string c);
  c


let bind env e1opt (c1:comp) ((b, c2):comp_with_binder) : comp = 
  if debug env Options.Extreme
  then 
    (let bstr = match b with 
      | None -> "none"
      | Some (Env.Binding_var(x, _)) -> Print.strBvd x
      | _ -> "??" in
    Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s" (Print.comp_typ_to_string c1) bstr (Print.comp_typ_to_string c2));
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
            if Util.is_total_comp c1 
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
      let k = Util.subst_kind' [Inl(a.v, t2)] kwp in
      let wp = mk_Typ_app(md.bind_wp, wp_args) k t2.pos in
      let wlp = mk_Typ_app(md.bind_wlp, wlp_args) k t2.pos in
      let c = mk_comp md t2 wp wlp [] in
//      if debug env then printfn "Result comp type is %s\n" (Print.comp_typ_to_string c);
//      if debug env then printfn "Normalized comp type is %s\n" (Print.comp_typ_to_string (Comp <| Normalize.normalize_comp env c));
      c
     
let lift_formula env t mk_wp mk_wlp f = 
  let md_pure = Tc.Env.get_monad_decl env Const.pure_effect_lid in
  let a, kwp = Tc.Env.wp_signature env md_pure.mname in 
  let k = Util.subst_kind' [Inl(a.v, t)] kwp in
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
  let assert_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assert_pure_lid in
  let assume_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assume_pure_lid in
  lift_formula env t assert_pure assume_pure f

let strengthen_precondition env (c:comp) f = match f with 
  | Trivial -> c
  | NonTrivial f -> 
    if debug env Options.High then Util.fprint2 "\tStrengthening precondition %s with %s" (Print.comp_typ_to_string c) (Print.typ_to_string f);
    let c = Tc.Normalize.weak_norm_comp env c in
    let res_t, wp, wlp = destruct_comp c in
    //if debug env then Util.fprint1 "\tWp is %s" (Print.typ_to_string wp);
    let md = Tc.Env.get_monad_decl env c.effect_name in 
    let wp = mk_Typ_app(md.assert_p, [targ res_t; targ f; targ wp]) wp.tk wp.pos in
    let wlp = mk_Typ_app(md.assume_p, [targ res_t; targ f; targ wlp]) wlp.tk wlp.pos in
    let c2 = mk_comp md res_t wp wlp [] in
   // if debug env then Util.fprint1 "\tStrengthened precondition is %s" (Print.comp_typ_to_string c2);
    c2

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

let bind_cases env (res_t:typ) (cases:list<(option<formula> * comp)>) : comp =
  (if List.length cases = 0 then failwith "Empty cases!"); (* TODO: Fix precedence of semi colon *)
  match cases with 
    | [(None, c)] -> c
    | [(Some f, c)] -> strengthen_precondition env c (NonTrivial f)
    | _ -> 
      let caccum, some_pat_matched = cases |> List.fold_left (fun (caccum, prior_pat_matched) (gopt, c) -> 
        let prior_or_c_matched, cguard = match prior_pat_matched, gopt with 
          | None, Some g -> Some g, Some g
          | Some g, None -> prior_pat_matched, Some <| Util.mk_neg g
          | Some g, Some g' -> Some (Util.mk_disj g g'), Some <| Util.mk_conj (Util.mk_neg g) g'
          | None, None -> None, None in
        let c = match cguard with 
          | None -> c
          | Some g -> weaken_precondition env c (NonTrivial g) in 
        match caccum with 
          | None -> (Some c, prior_or_c_matched)
          | Some caccum -> 
            let (md, a, kwp), (t, wp1, wlp1), (_, wp2, wlp2) = lift_and_destruct env caccum c in 
            let k = Util.subst_kind' [Inl(a.v, t)] kwp in
            let wp_conj wp1 wp2 = 
              mk_Typ_app(md.wp_binop, [targ t; targ wp1; targ (Util.ftv Const.and_lid (Const.kbin ktype ktype ktype)); targ wp2]) k wp2.pos in
            let wp = wp_conj wp1 wp2 in
            let wlp = wp_conj wlp1 wlp2 in 
            (Some <| mk_comp md t wp wlp [], prior_or_c_matched)) (None, None) in
      let caccum = comp_to_comp_typ <| flex_to_ml env (must <| caccum) in
      let md = Tc.Env.get_monad_decl env caccum.effect_name in
      let res_t, wp, wlp = destruct_comp caccum in
      let wp = match some_pat_matched with 
        | None -> wp 
        | Some guard -> mk_Typ_app(md.assert_p, [targ res_t; targ guard; targ wp]) wp.tk wp.pos in
      let a, kwp = Tc.Env.wp_signature env caccum.effect_name in
      let k = Util.subst_kind' [Inl(a.v, res_t)] kwp in
      let wp = mk_Typ_app(md.ite_wp, [targ res_t; targ wlp; targ wp]) k wp.pos in
      let wlp = mk_Typ_app(md.ite_wlp, [targ res_t; targ wlp]) k wlp.pos in
      //Comp <| Normalize.normalize_comp env (
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

let weaken_result_typ env (e:exp) (c:comp) (t:typ) : exp * comp = 
  let c = Tc.Normalize.weak_norm_comp env c in
  let tc, _, _ = destruct_comp c in
  let g = Tc.Rel.subtype env tc t in
  match g with 
    | Trivial -> e, mk_Comp c
    | NonTrivial f -> 
      let md = Tc.Env.get_monad_decl env c.effect_name in
      let x = new_bvd None in
      let xexp = Util.bvd_to_exp x t in
      let a, kwp = Env.wp_signature env Const.pure_effect_lid in
      let k = Util.subst_kind [Inl(a.v, t)] kwp in
      let wp = mk_Typ_app(md.ret, [targ t; varg xexp]) k xexp.pos  in
      let cret = mk_comp md t wp wp c.flags in
      let eq_ret = strengthen_precondition env cret (NonTrivial (mk_Typ_app(f, [varg xexp]) ktype f.pos)) in
      let c = bind env (Some e) (mk_Comp c) (Some(Env.Binding_var(x, tc)), eq_ret) in
      e, c

let check_comp env (e:exp) (c:comp) (c':comp) : exp * comp * guard_t = 
  //printfn "Checking sub_comp:\n%s has type %s\n\t<:\n%s\n" (Print.exp_to_string e) (Print.comp_typ_to_string c) (Print.comp_typ_to_string c');
  match Tc.Rel.sub_comp env c c' with 
    | None -> raise (Error(Tc.Errors.computed_computation_type_does_not_match_annotation e c c', Tc.Env.get_range env))
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

let refine_data_type env l (formals:binders) (result_t:typ) = 
   match formals with 
    | [] -> result_t
    | _ -> 
       let r = range_of_lid l in 
       let formals, args = Util.args_of_binders formals in
       let basic_t = mk_Typ_fun(formals, mk_Total result_t) ktype r in
       let v = mk_Exp_app({Util.fvar l r with tk=basic_t}, args) result_t r in
       mk_Typ_fun(formals, return_value env result_t v) ktype r
       
let maybe_instantiate env e t = 
  let t = compress_typ t in 
  if not (env.instantiate_targs && env.instantiate_vargs) then e, t else
  match t.n with 
    | Typ_fun(bs, c) -> 
      let vars = Env.binders env in 
      let tvars = vars |> List.filter (function Inl _, _ -> true | _ -> false) in
      let rec aux subst = function 
        | (Inl a, _)::rest -> 
          let k = Util.subst_kind subst a.sort in
          let t = Rel.new_tvar e.pos tvars k |> fst in
          let subst = extend_subst (Inl(a.v, t)) subst in 
          let args, bs, subst = aux subst rest in 
          (Inl t, true)::args, bs, subst  

        | (Inr x, true)::rest -> 
          let t = Util.subst_typ subst x.sort in 
          let v = Rel.new_evar e.pos vars t |> fst in
          let subst = extend_subst (Inr(x.v, v)) subst in 
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
let discharge_guard env g = 
    if not (!Options.verify) then ()
    else match g with 
        | Trivial -> ()
        | NonTrivial vc -> 
            let vc = Normalize.norm_typ [Delta; Beta; Eta] env vc in
            if Tc.Env.debug env Options.High then Tc.Errors.diag (Tc.Env.get_range env) (Util.format1 "Checking VC=\n%s\n" (Print.formula_to_string vc));
            if not <| env.solver.solve env vc
            then Tc.Errors.report (Tc.Env.get_range env) (Tc.Errors.failed_to_prove_specification [])

(**************************************************************************************)
(* Generalizing types *)
(**************************************************************************************)
let check_uvars r t = 
  let uvt = Util.uvars_in_typ t in
  if Util.set_count uvt.uvars_e + 
     Util.set_count uvt.uvars_t + 
     Util.set_count uvt.uvars_k > 0
  then Tc.Errors.report r "Unconstrained unification variables; please add an annotation"

   
let generalize env (ecs:list<(lbname*exp*comp)>) : (list<(lbname*exp*comp)>) = 
 if debug env Options.Low then Util.fprint1 "Generalizing: %s" (List.map (fun (lb, _, _) -> Print.lbname_to_string lb) ecs |> String.concat ", ");
 //  let _ = printfn "Generalizing %s\n" (Print.typ_to_string (Util.comp_result c)) in
//  let _ = printfn "In normal form %s\n" (Print.typ_to_string (Normalize.norm_typ  [Normalize.Beta; Normalize.Delta; Normalize.SNComp; Normalize.DeltaComp] env (Util.comp_result c))) in 
//     let print_uvars uvs =
//       uvs |> List.iter (fun (uv, _) -> printfn "\t%d" (Unionfind.uvar_id uv)) in
  if not <| (Util.for_all (fun (_, _, c) -> Util.is_pure_comp c) ecs)
  then ecs
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

     let uvars = ecs |> List.map (fun (x, e, c) -> 
          let t = Util.comp_result c |> Util.compress_typ in 
          if not <| should_gen t
          then (x, [], e, flex_to_total env c)
          else let c = norm c in 
               let ct = comp_to_comp_typ c in
               let t = ct.result_typ in
               let uvt = Util.uvars_in_typ t in
               let uvs = gen_uvars <| uvt.uvars_t in 
               if !Options.verify && not <| Util.is_total_comp c
               then begin
                  let _, wp, _ = destruct_comp ct in 
                  let binder = [null_v_binder t] in
                  let post = mk_Typ_lam(binder, Util.ftv Const.true_lid ktype) (mk_Kind_arrow(binder, ktype) t.pos) t.pos in
                  let vc = Normalize.norm_typ [Delta; Beta] env (syn wp.pos ktype <| mk_Typ_app(wp, [targ post])) in
                  if Tc.Env.debug env Options.Medium then Tc.Errors.diag (range_of_lbname x) (Util.format2  "Checking %s with VC=\n%s\n" (Print.lbname_to_string x) (Print.formula_to_string vc));
                  if not <| env.solver.solve env vc
                  then Tc.Errors.report (range_of_lbname x) (Tc.Errors.failed_to_prove_specification_of x [])
               end;
               x, uvs, e, c) in //return_value env t e) in

     let ecs = uvars |> List.map (fun (x, uvs, e, c) -> 
          let tvars = uvs |> List.map (fun (u, k) -> 
            let a = match Unionfind.find u with 
              | Fixed ({n=Typ_btvar a}) -> a.v 
              | _ -> 
                  let a = Util.new_bvd (Some <| Tc.Env.get_range env) in
                  let t = Util.bvd_to_typ a k in
    //              let _ = printfn "Unifying %d with %s\n" (Unionfind.uvar_id u) (Print.typ_to_string t) in
                  unchecked_unify u t; a in
            t_binder <| Util.bvd_to_bvar_s a k) in
    
          let t = match Util.comp_result c |> Util.function_formals with 
            | Some (bs, cod) -> mk_Typ_fun(tvars@bs, cod) ktype c.pos 
            | None -> match tvars with [] -> Util.comp_result c | _ -> mk_Typ_fun(tvars, c) ktype c.pos in
          let e = match e.n with 
            | Exp_abs(bs, body) -> mk_Exp_abs(tvars@bs, body) t e.pos 
            | _ -> mk_Exp_abs(tvars, e) t e.pos in
          if debug env Options.Medium then Util.fprint3 "(%s) Generalized %s to %s" (Range.string_of_range e.pos) (Print.lbname_to_string x) (Print.typ_to_string t);
          x, e, mk_Total t) in
     ecs 

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
 
module Microsoft.FStar.ToSMT.Encode

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Tc
open Microsoft.FStar.ToSMT.Term


let withenv c (a, b) = (a,b,c)

(* ------------------------------------ *)
(* Some operations on constants *)
let escape (s:string) = Util.replace_char s '\'' '_'
let mk_typ_projector_name lid (a:btvdef) = escape <| format2 "%s_%s" lid.str a.ppname.idText
let mk_term_projector_name lid (a:bvvdef) = escape <| format2 "%s_%s" lid.str (Util.unmangle_field_name a.ppname).idText
let mk_term_projector_name_by_pos lid (i:int) = escape <| format2 "%s_%s" lid.str (string_of_int i)
let mk_typ_projector (lid:lident) (a:btvdef)  : term = 
    mkFreeV(mk_typ_projector_name lid a, Arrow(Term_sort, Type_sort))
let mk_term_projector (lid:lident) (a:bvvdef) : term = 
    mkFreeV(mk_term_projector_name lid a, Arrow(Term_sort, Term_sort))
let mk_term_projector_by_pos (lid:lident) (i:int) : term = 
    mkFreeV(mk_term_projector_name_by_pos lid i, Arrow(Term_sort, Term_sort))
let mk_data_tester env l x = Term.mk_tester l.str x
(* ------------------------------------ *)
(* New name generation *)
type ex_vars = list<(var * term)> (* existentially bound variables and their guards *)
type varops_t = {
    push: unit -> unit;
    pop: unit -> unit;
    new_var:ident -> ident -> string; (* each name is distinct and has a prefix corresponding to the name used in the program text *)
    new_fvar:lident -> string;
    fresh:string -> string;
    string_const:string -> term;
    next_id: unit -> int;
}
let varops = 
    let initial_ctr = 10 in
    let ctr = Util.mk_ref initial_ctr in
    let new_scope () = (Util.smap_create 100, Util.smap_create 100) in (* a scope records all the names and string constants used in that scope *)
    let scopes = Util.mk_ref [new_scope ()] in 
    let mk_unique y = 
        let y = escape y in
        let y = match Util.find_map (!scopes) (fun (names, _) -> Util.smap_try_find names y) with 
                  | None -> y 
                  | Some _ -> incr ctr; y ^ "__" ^ (string_of_int !ctr) in
        let top_scope = fst <| List.hd !scopes in
        Util.smap_add top_scope y true; y in
    let new_var pp rn = mk_unique <| pp.idText ^ "__" ^ rn.idText in
    let new_fvar lid = mk_unique lid.str in
    let next_id () = incr ctr; !ctr in
    let fresh sfx = format2 "%s_%s" sfx (string_of_int <| next_id()) in
    let string_const s = match Util.find_map !scopes (fun (_, strings) -> Util.smap_try_find strings s) with
        | Some f -> f
        | None -> 
            let id = next_id () in
            let f = Term.boxString <| mk_String_const id in
            let top_scope = snd <| List.hd !scopes in
            Util.smap_add top_scope s f;
            f in
    let push () = scopes := new_scope()::!scopes in
    let pop () = scopes := List.tl !scopes in
    {push=push;
     pop=pop;
     new_var=new_var;
     new_fvar=new_fvar;
     fresh=fresh;
     string_const=string_const;
     next_id=next_id}

 let unmangle (x:bvdef<'a>) = Util.mkbvd (Util.unmangle_field_name x.ppname, Util.unmangle_field_name x.realname)
(* ---------------------------------------------------- *)
(* <Environment> *)
(* Each entry maps a Syntax variable to its encoding as a SMT2 term *)
type binding = 
    | Binding_var   of bvvdef * term
    | Binding_tvar  of btvdef * term
    | Binding_fvar  of lident * string * term (* free variables, depending on whether or not they are fully applied ...  *)
    | Binding_ftvar of lident * string * term (* ... are mapped either to SMT2 functions, or to nullary term/type tokens *)
   
type env_t = {bindings:list<binding>;
              tcenv:Env.env}

let lookup_binding env f = Util.find_map env.bindings f 
              
let caption_t env t = 
    if Tc.Env.debug env.tcenv Options.Low
    then Some (Print.typ_to_string t)
    else None


let fresh_bvar x s = let xsym = varops.fresh x in xsym, mkBoundV(xsym, s)
let fresh_fvar x s = let xsym = varops.fresh x in xsym, mkFreeV(xsym, s)
(* generate terms corresponding to a variable and record the mapping in the environment *)

(* Bound term variables *)
let gen_term_var (env:env_t) (x:bvvdef) = 
    let ysym = varops.new_var x.ppname x.realname in 
    let y = mkBoundV(ysym, Term_sort) in 
    ysym, y, {env with bindings=Binding_var(x,y)::env.bindings}
let gen_free_term_var (env:env_t) (x:bvvdef) = 
    let ysym = varops.new_var x.ppname x.realname in 
    let y = mkFreeV(ysym, Term_sort) in 
    ysym, y, {env with bindings=Binding_var(x,y)::env.bindings}
let push_term_var (env:env_t) (x:bvvdef) (t:term) = 
    {env with bindings=Binding_var(x,t)::env.bindings}
let lookup_term_var env a = 
    match lookup_binding env (function Binding_var(b, t) when Util.bvd_eq b a.v -> Some t | _ -> None) with
    | None -> failwith (format1 "Bound term variable not found: %s" (Print.strBvd a.v))
    | Some s -> s

(* Bound type variables *)
let gen_typ_var (env:env_t) (x:btvdef) = 
    let ysym = varops.new_var x.ppname x.realname in 
    let y = mkBoundV(ysym, Type_sort) in
    ysym, y, {env with bindings=Binding_tvar(x,y)::env.bindings}
let gen_free_typ_var (env:env_t) (x:btvdef) = 
    let ysym = varops.new_var x.ppname x.realname in 
    let y = mkFreeV(ysym, Type_sort) in
    ysym, y, {env with bindings=Binding_tvar(x,y)::env.bindings}
let push_typ_var (env:env_t) (x:btvdef) (t:term) = 
    {env with bindings=Binding_tvar(x,t)::env.bindings}
 let lookup_typ_var env a = 
   match lookup_binding env (function Binding_tvar(b, t) when Util.bvd_eq b a.v -> Some t | _ -> None) with 
    | None -> failwith (format1 "Bound type variable not found: %s" (Print.strBvd a.v))
    | Some s -> s

(* Qualified term names *)
let gen_free_var (env:env_t) (x:lident) =
    let fname = varops.new_fvar x in
    let ftok = mkFreeV(varops.new_fvar x , Term_sort) in
    fname, ftok, {env with bindings=Binding_fvar(x, fname, ftok)::env.bindings}
let try_lookup_lid env a = 
    lookup_binding env (function Binding_fvar(b, t1, t2) when lid_equals b a -> Some (t1, t2) | _ -> None) 
let lookup_lid env a = 
    match lookup_binding env (function Binding_fvar(b, t1, t2) when lid_equals b a -> Some (t1, t2) | _ -> None) with
    | None -> failwith (format1 "Name not found: %s" (Print.sli a))
    | Some s -> s
let push_free_var env (x:lident) fname ftok = 
    {env with bindings=Binding_fvar(x, fname, ftok)::env.bindings}
let lookup_free_var env a = lookup_lid env a.v |> snd
let lookup_free_var_name env a = lookup_lid env a.v |> fst

(* Qualified type names *)
let gen_free_tvar (env:env_t) (x:lident) =
    let fname = varops.new_fvar x in
    let ftok = mkFreeV(varops.new_fvar x, Type_sort) in 
    fname, ftok, {env with bindings=Binding_ftvar(x, fname, ftok)::env.bindings}
let lookup_tlid env a = 
    match lookup_binding env (function Binding_ftvar(b, t1, t2) when lid_equals b a -> Some (t1, t2) | _ -> None) with
    | None -> failwith (format1 "Type name not found: %s" (Print.sli a))
    | Some s -> s
let push_free_tvar env (x:lident) fname ftok = 
    {env with bindings=Binding_ftvar(x, fname, ftok)::env.bindings}
let lookup_free_tvar env a = lookup_tlid env a.v |> snd
let lookup_free_tvar_name env a = lookup_tlid env a.v |> fst

(* </Environment> *)
(*---------------------------------------------------------------------------------*)

(* <Utilities> *)
let norm_t env t = Tc.Normalize.norm_typ [Tc.Normalize.Delta;Tc.Normalize.Beta] env.tcenv t
let norm_k env k = Tc.Normalize.normalize_kind env.tcenv k
let trivial_post t : typ = mk_Typ_lam([null_v_binder t], Util.ftv Const.true_lid ktype) 
                                     (mk_Kind_arrow([null_v_binder t], ktype) t.pos) t.pos

let mk_ApplyE e vars =  
    vars |> List.fold_left (fun out var -> match snd var with 
            | Type_sort -> mk_ApplyET out (Term.mkBoundV var)
            | _ -> mk_ApplyEE out (Term.mkBoundV var)) e
let mk_ApplyE_args e args = 
    args |> List.fold_left (fun out arg -> match arg with 
            | Inl t -> mk_ApplyET out t
            | Inr e -> mk_ApplyEE out e) e

let mk_ApplyT t vars = 
    vars |> List.fold_left (fun out var -> match snd var with 
            | Type_sort -> mk_ApplyTT out (Term.mkBoundV var)
            | _ -> mk_ApplyTE out (Term.mkBoundV var)) t
let mk_ApplyT_args t args = 
    args |> List.fold_left (fun out arg -> match arg with 
            | Inl t -> mk_ApplyTT out t
            | Inr e -> mk_ApplyTE out e) t

let close_ex vars pred = match vars with 
    | [] -> pred
    | _ -> 
        let vars, guards = List.unzip vars in 
        Term.mkExists([], vars, mk_and_l (pred::guards))
(* </Utilities> *)

(**********************************************************************************)
(* The main encoding of kinds/types/expressions/formulae: all mutually recursive  *)
(* see fstar-priv/papers/mm/encoding.txt for a semi-formal sketch of the encoding *)
(**********************************************************************************)

(* Abstractly:

      ctx = (bvvdef -> term(Term_sort)) U (btvdef -> term(Type_sort)

    [[k]] : ctx -> term(Type_sort) -> term(Bool)
    [[t]] : ctx -> term(Term_sort) -> term(Bool)
    [[e]] : ctx -> term(Term_sort)
    [[f]] : ctx -> term(Bool)
   [[bs]] : ctx -> (vars
                    * term(Bool)  <-- guard on bound vars
                    * ctx)   <-- context extended with bound vars
                    
    Concretely, [[*]] are the encode_* functions, for knd, typ, exp, formula, binders
    ctx is implemented using env_t
    and term(*) is just term
 *)

let encode_const = function 
    | Const_unit -> mk_Term_unit
    | Const_bool true -> boxBool mkTrue
    | Const_bool false -> boxBool mkFalse
    | Const_int32 i -> boxInt (mkInteger i)
    | Const_string(bytes, _) -> varops.string_const (Util.string_of_bytes <| bytes)
    | c -> failwith (Util.format1 "Unhandled constant: %s\n" (Print.const_to_string c))
 
let rec encode_knd (k:knd) (env:env_t) (t:term) : term = 
    match (Util.compress_kind k).n with 
        | Kind_type -> 
            mk_HasKind t (Term.mk_Kind_type)

        | Kind_abbrev(_, k) -> 
            encode_knd k env t

        | Kind_uvar (uv, _) -> (* REVIEW: warn? *)
            Term.mkTrue 

        | Kind_arrow(bs, k) -> 
            let vars, guards, env', _ = encode_binders bs env in 
            let prekind = mk_tester "Kind_arrow" (mk_PreKind t) in
            let app = mk_ApplyT t vars in
            Term.mkAnd(prekind,
                       Term.mkForall(app::guards, vars, mkImp(mk_and_l guards, encode_knd k env' app)))

        | _ -> failwith (Util.format1 "Unknown kind: %s" (Print.kind_to_string k))

and encode_binders (bs:Syntax.binders) (env:env_t) : (list<var>       (* translated bound variables *)
                                                      * list<term>    (* guards *)
                                                      * env_t         (* extended context *)
                                                      * list<either<btvdef, bvvdef>>) (* unmangled names *) =
    let vars, guards, env, names = bs |> List.fold_left (fun (vars, guards, env, names) b -> 
        let v, g, env, n = match fst b with 
            | Inl {v=a; sort=k} -> 
                let a = unmangle a in
                let aasym, aa, env' = 
                    if is_null_binder b 
                    then withenv env <| fresh_bvar "a" Type_sort
                    else gen_typ_var env a in 
                let guard_a_k = encode_knd k env aa in
                (aasym, Type_sort), 
                guard_a_k,
                env', 
                Inl a  

            | Inr {v=x; sort=t} -> 
                let x = unmangle x in
                let xxsym, xx, env' = 
                    if is_null_binder b   
                    then withenv env <| fresh_bvar "x" Term_sort
                    else gen_term_var env (unmangle x) in
                let guard_x_t = encode_typ_pred t env xx in
                (xxsym, Term_sort), 
                guard_x_t,
                env', 
                Inr x in
        v::vars, g::guards, env, n::names) ([], [], env, []) in
    List.rev vars,
    List.rev guards,
    env, 
    List.rev names

and encode_typ_pred (t:typ) (env:env_t) (e:term) : term = (* expects t to be in normal form already *)
    let t0 = Util.compress_typ t in
    match t0.n with 
      | Typ_btvar a -> 
        mk_HasType e (lookup_typ_var env a)

      | Typ_const fv -> 
        mk_HasType e (lookup_free_tvar env fv)

      | Typ_refine(x, f) ->
        let base_pred = encode_typ_pred x.sort env e in 
        let env' = push_term_var env x.v e in
        let refinement = encode_formula f env' in
        Term.mkAnd(base_pred, refinement)

      | Typ_fun(binders, res) -> 
        let pretype = mk_tester "Typ_fun" (mk_PreType e) in
        if not <| Util.is_pure env.tcenv res 
        then pretype 
        else let vars, guards, env', _ = encode_binders binders env in 
             let app = mk_ApplyE e vars in
             if Util.is_total_comp res
             then let app_pred = mkForall(app::guards, vars, mkImp(mk_and_l guards, encode_typ_pred (Util.comp_result res) env' app)) in
                  mkAnd(pretype, app_pred)
             else let t2, wp2, _ = Tc.Util.destruct_comp (Util.comp_to_comp_typ <| Normalize.normalize_comp env.tcenv res) in
                  let pre = Syntax.mk_Typ_app(wp2, [targ <| trivial_post t2]) ktype t2.pos in
                  let app_pred = mkForall(app::guards, vars, mkImp(Term.mkAnd(mk_and_l guards, encode_formula pre env'), 
                                                                   encode_typ_pred t2 env' app)) in
                  mkAnd(pretype, app_pred)

      | Typ_app _ ->
        let t, vars = encode_typ_term t env in 
        let pred = mk_HasType e t in
        close_ex vars pred

      | Typ_lam _ -> failwith "Impossible: type-lambdas cannot be encoded as predicates"
        
      | Typ_ascribed(t, _) -> 
        encode_typ_pred t env e

      | Typ_uvar _ -> 
        Term.mkTrue (* REVIEW: warn? *)

      | Typ_meta _
      | Typ_delayed  _ 
      | Typ_unknown    -> failwith (format2 "(%s) Impossible: %s" (Range.string_of_range <| t.pos) (Print.tag_of_typ t))                 

and encode_typ_term (t:typ) (env:env_t) : (term       (* encoding of t *)
                                           * ex_vars) (* new names and guards generated for this type, which must be bound in the caller's scope *) = 
    let t0 = Util.compress_typ t in
    match t0.n with 
      | Typ_btvar a -> 
        lookup_typ_var env a, []

      | Typ_const fv -> 
        lookup_free_tvar env fv, []

      | Typ_refine _
      | Typ_fun _ 
      | Typ_uvar _ ->
        let name = varops.fresh (Print.tag_of_typ t0), Type_sort in
        let sym = mkBoundV name in
        let xvar = varops.fresh "x", Term_sort in
        let x = mkBoundV xvar in
        let ty_pred = mk_HasType x sym in 
        let guard = mkForall([ty_pred], [xvar], mkImp(ty_pred,  encode_typ_pred t0 env x)) in
        sym, [(name, guard)]

      | Typ_app(head, args) -> (* this is in head normal form; so t must be a type variable or a constant *)
        let is_full_app () = match (Util.compress_kind head.tk).n with
            | Kind_arrow(formals, _) -> List.length formals = List.length args
            | _ -> false in
        let head = Util.compress_typ head in
        begin match head.n with
            | Typ_btvar a -> 
              let head = lookup_typ_var env a in
              let args, vars = encode_args args env in
              let t = mk_ApplyT_args head args in
              t, vars
                
            | Typ_const fv -> 
              let args, vars = encode_args args env in
              if is_full_app () && !Options.z3_optimize_full_applications
              then let head = lookup_free_tvar_name env fv in
                   let t = Term.mkApp(head, List.map (function Inl t | Inr t -> t) args) in
                   t, vars
              else let head = lookup_free_tvar env fv in
                   let t = mk_ApplyT_args head args in
                   t, vars

            | _ -> 
              let t = norm_t env t in
              encode_typ_term t env
        end

      | Typ_lam(bs, t) ->
        let vars, guards, env, _ = encode_binders bs env in
        let name = varops.fresh (Print.tag_of_typ t0), Type_sort in 
        let tag = mkBoundV name in 
        let app = mk_ApplyT tag vars in
        let body, vars_body = encode_typ_term t env in
        let eq = close_ex vars_body (mkEq(app, body)) in
        let guard = mkForall(app::guards, vars, mkImp(mk_and_l guards, eq)) in
        tag, [(name, guard)]

      | Typ_ascribed(t, _) -> 
        encode_typ_term t env

      | Typ_meta _
      | Typ_delayed  _ 
      | Typ_unknown    -> failwith (format2 "(%s) Impossible: %s" (Range.string_of_range <| t.pos) (Print.tag_of_typ t))                 

and encode_exp (e:exp) (env:env_t) : (term * ex_vars) = 
    let e = Visit.compress_exp_uvars e in 
    let e0 = e in
    match e.n with 
      | Exp_delayed _ -> (* REVIEW: dead code? *)
        encode_exp (Util.compress_exp e) env

      | Exp_bvar x -> 
        lookup_term_var env x, []

      | Exp_fvar(v, _) -> 
        lookup_free_var env v, []

      | Exp_constant c -> 
        encode_const c, []
      
      | Exp_ascribed(e, _)
      | Exp_meta(Meta_desugared(e, _)) -> 
        encode_exp e env

      | Exp_uvar(uv, _) ->
        let fsym = varops.fresh "Exp_uvar", Term_sort in
        mkBoundV fsym, [(fsym, Term.mkTrue)]
 
      | Exp_abs(bs, body) -> 
        begin match (Util.compress_typ e.tk).n with 
            | Typ_fun(_, c) -> 
                let esym, lam = fresh_fvar "lambda" Term_sort in
                if not <| Util.is_pure env.tcenv c
                then lam, [(esym, Term_sort), Term.mkTrue]
                else let vars, guards, env, _ = encode_binders bs env in 
                     let app = mk_ApplyE lam vars in
                     let body, body_vars = encode_exp body env in
                     let eq = close_ex body_vars (mkEq(app, body)) in
                     let tguard = encode_typ_pred (Util.comp_result c) env app in
                     let pre = if Util.is_total_comp c 
                               then mk_and_l guards
                               else let tres, wp, _ =  Tc.Util.destruct_comp (Util.comp_to_comp_typ c) in   
                                    let pre = encode_formula (Syntax.mk_Typ_app(wp, [targ <| trivial_post tres]) ktype e.pos) env in
                                    mk_and_l (pre::guards) in
                     let appAx = Term.mkForall(app::guards, vars, mkImp(mk_and_l guards, mkAnd(eq, tguard))) in
                     lam, [(esym, Term_sort), appAx]

            | _ -> failwith "Impossible"
        end

      | Exp_app(head, args) -> 
        let args, vars = encode_args args env in
    
        let encode_partial_app () = 
            let head, vars' = encode_exp head env in
            mk_ApplyE_args head args, vars'@vars in

        let encode_full_app fv = 
            let fname = lookup_free_var_name env fv in
            let tm = Term.mkApp(fname, List.map (function Inl t | Inr t -> t) args) in
            tm, vars in
        
        let head = Util.compress_exp head in
        begin match head.n with 
            | Exp_fvar(fv, _) -> 
                if not <| !Options.z3_optimize_full_applications
                then encode_partial_app()
                else
                    (match Util.function_formals head.tk with 
                        | None -> failwith (Util.format3 "(%s) term is %s; head type is %s\n" 
                                           (Range.string_of_range e0.pos) (Print.exp_to_string e0) (Print.typ_to_string e.tk))
                        | Some (formals, _) -> 
                          if List.length formals = List.length args
                          then encode_full_app fv
                          else (Util.fprint1 "%s is not a full application!\n" (Print.exp_to_string e0);
                                encode_partial_app ()))
            | _ ->
                Util.fprint1 "%s is not a full application!\n" (Print.exp_to_string e0); encode_partial_app ()
        end

      | Exp_let((false, [(Inr _, _, _)]), _) -> failwith "Impossible: already handled by encoding of Sig_let" 

      | Exp_let((false, [(Inl x, t1, e1)]), e2) ->
        let xvar, x, env' = gen_term_var env x in 
        let guard = encode_typ_pred t1 env x in
        let ee1, vars1 = encode_exp e1 env in
        let ee2, vars2 = encode_exp e2 env' in
        ee2, vars1@[(xvar, Term_sort), mkAnd(guard, mkEq(x, ee1))]@vars2 
  
      | Exp_let _
      | Exp_match _ -> 
        let name = varops.fresh "Expression", Term_sort in
        let sym = mkBoundV name in
        sym, [(name, Term.mkTrue)]


//        
//      | Exp_let((true, _), _) -> failwith "Nested let recs not yet supported in SMT encoding" 
//      | Exp_let((_, (Inr l, _, _)::_), _) -> failwith "Unexpected top-level binding"

//      | Exp_let((false, [(Inl x, t1, e1)]), e2) ->
//        let ee1, g1 = encode_exp env e1 in
//        let tt1, g2 = encode_typ env t1 in 
//        let env' = push_term_var env x ee1 in
//        let ee2, g3 = encode_exp env' e2 in
//        let g = [Term.Assume(mk_HasType ee1 tt1, None)] in
//        ee2, g1@g2@g@g3
//      
//      | Exp_let _ -> failwith "Impossible"
//
//        
//      | Exp_match(e, pats) -> 
//        let encode_pat env ee pat wopt b = 
//            let rec top_level_pats x = match x with
//                | Pat_withinfo(p, _) -> top_level_pats p 
//                | Pat_disj pats -> pats
//                | p -> [p] in
//            let rec mk_guard_env env d pat = match pat with 
//                | Pat_disj _ -> failwith "Impossible"
//                | Pat_withinfo(p, _) -> mk_guard_env env d p
//                | Pat_var x -> mkTrue, push_term_var env x d, []     
//                | Pat_tvar a -> mkTrue, push_typ_var env a d, [] 
//                | Pat_wild
//                | Pat_twild -> mkTrue, env, []
//                | Pat_constant c -> 
//                  let c, g = encode_const c in
//                  mkEq(d, c), env, g 
//                | Pat_cons(lid, pats) -> 
//                  let guard = mk_data_tester env lid d in
//                  let formals =  match Util.function_formals <| Tc.Env.lookup_datacon env.tcenv lid with 
//                    | Some (args, _) -> args
//                    | _ -> [] in  
//                  let guards, env, g, _ = List.fold_left2 (fun (guards, env, g, i) formal pat -> match fst formal with 
//                    | Inl {v=a; sort=k} -> 
//                      let t = mk_typ_projector lid a in
//                      let aa = Term.mk_ApplyTE t d in 
//                      let guard, env, g' = mk_guard_env env aa pat in
//                      (guard::guards, env, g@g', i+1)
//                    | Inr {v=x; sort=t} -> 
//                      let t = if is_null_binder formal
//                              then mk_term_projector_by_pos lid i
//                              else mk_term_projector lid x in
//                      let xx = Term.mk_ApplyTE t d in 
//                      let guard, env, g' = mk_guard_env env xx pat in
//                      (guard::guards, env, g@g', i+1))
//                      ([], env, [], 0) formals pats in
//                  let guard = Term.mk_and_l (guard::guards) in 
//                  guard, env, g in
//            top_level_pats pat |> 
//            List.map (mk_guard_env env ee) |>
//            List.map (fun (guard, env, g) -> 
//                let bb, g1 = encode_exp env b in
//                let guard, g2 = match wopt with 
//                    | None -> guard, []
//                    | Some e -> 
//                        let w, g = encode_exp env e in  
//                        mkAnd(guard, mkEq(w, boxBool mkTrue)), g in
//                guard, bb, g@g1@g2) in
//
//        let ee, g1 = encode_exp env e in 
//        let branches, g = List.fold_right (fun (pat, wopt, b) (def, g) -> 
//            let gbgs = encode_pat env ee pat wopt b in 
//            List.fold_right (fun (guard, branch, g') (def, g) -> 
//               mkITE(guard, branch, def), g@g') gbgs (def, g))
//            pats (Term.boxBool mkFalse, []) in
//        branches, g@g1
//      
//      
      | Exp_meta _ -> failwith (Util.format2 "(%s): Impossible: encode_exp got %s" (Range.string_of_range e.pos) (Print.exp_to_string e))

and encode_fe l env = 
    let tms, ex_vars = l |> List.fold_left (fun (tms, ex_vars) x -> match x with 
        | Inl t, _ -> encode_formula t env::tms, ex_vars
        | Inr e, _ -> let e, vars = encode_exp e env in e::tms, vars@ex_vars) ([], []) in
    List.rev tms, ex_vars

and encode_args l env =
    let l, vars = l |> List.fold_left (fun (tms, ex_vars) x -> match x with
        | Inl t, _ -> let t, vs = encode_typ_term t env in Inl t::tms, vs@ex_vars
        | Inr e, _ -> let t, vs = encode_exp e env in Inr t::tms, vs@ex_vars) ([], []) in
    List.rev l, vars

and encode_formula  (phi:typ) (env:env_t) : term = (* expects phi to be normalized *)
    let enc : (list<term> -> term) -> args -> term = fun f l -> let l, ex_vars = encode_fe l env in close_ex ex_vars (f l) in
    let const_op f _ = f in
    let un_op f l = f <| List.hd l in
    let bin_op : ((term * term) -> term) -> list<term> -> term = fun f -> function 
        | [t1;t2] -> f(t1,t2)
        | _ -> failwith "Impossible" in
    let tri_op : ((term * term * term) -> term) -> list<term> -> term = fun f -> function
        | [t1;t2;t3] -> f(t1,t2,t3)
        | _ -> failwith "Impossible" in
    let eq_op : ((term * term) -> term) -> list<term> -> term = fun f -> function 
        | [_;_;e1;e2] -> bin_op f [e1;e2]
        | l -> bin_op f l in
    let unboxInt_l : (list<term> -> term) -> list<term> -> term = fun f l -> f (List.map Term.unboxInt l) in
    let connectives = [ 
                        (Const.and_lid, enc <| bin_op mkAnd);
                        (Const.or_lid,  enc <| bin_op mkOr);
                        (Const.imp_lid, enc <| bin_op mkImp);
                        (Const.iff_lid, enc <| bin_op mkIff);
                        (Const.ite_lid, enc <| tri_op mkITE);
                        (Const.not_lid, enc <| un_op mkNot);
                        (Const.lt_lid,  enc (unboxInt_l <| bin_op mkLT));
                        (Const.gt_lid,  enc (unboxInt_l <| bin_op mkGT));
                        (Const.gte_lid, enc (unboxInt_l <| bin_op mkGTE));
                        (Const.lte_lid, enc (unboxInt_l <| bin_op mkLTE));
                        (Const.eqT_lid, enc <| bin_op mkEq);
                        (Const.eq2_lid, enc <| eq_op mkEq);
                        (Const.true_lid, const_op mkTrue);
                        (Const.false_lid, const_op mkFalse);
                    ] in

    let fallback phi =  
     //   let t, args = Util.head_and_args phi in
//        let _ = printfn "Falling back on %s\n" (Print.typ_to_string phi) in
//        let _ = printfn "Failed to destruct %s (%s) (%s)\n" (Print.typ_to_string t) (Print.tag_of_typ t) (args |> List.map (function Inl t -> Print.tag_of_typ t | Inr e -> Print.exp_to_string e) |> String.concat ", ") in
        let tt, ex_vars = encode_typ_term phi env in
        close_ex ex_vars <| Term.mk_Valid tt in

    let encode_q_body env (bs:Syntax.binders) (ps:args) body = 
        let vars, guards, env, _ = encode_binders bs env in 
        let pats, ex_vars = encode_fe ps env in
        match ex_vars with 
            | _::_ -> failwith (Util.format1 "Unexpected patterns %s\n" (Print.args_to_string ps))
            | [] -> 
             let body = encode_formula body env in
             vars, pats, mk_and_l guards, body in

    if Tc.Env.debug env.tcenv Options.Low
    then Util.fprint1 ">>>> Destructing as formula ... %s\n" (Print.typ_to_string phi);
         
    match Util.destruct_typ_as_formula phi with
        | None -> 
          if Tc.Env.debug env.tcenv Options.Low
          then Util.print_string ">>>> Not a formula ... falling back\n";
          fallback phi
        
        | Some (Util.BaseConn(op, arms)) -> 
          (match connectives |> List.tryFind (fun (l, _) -> lid_equals op l) with 
             | None -> fallback phi
             | Some (_, f) -> f arms)

        | Some (Util.QAll(vars, pats, body)) -> 
          if Tc.Env.debug env.tcenv Options.Low
          then Util.fprint1 ">>>> Got QALL [%s]\n" (vars |> Print.binders_to_string "; ");

          let vars, pats, guard, body = encode_q_body env vars pats body in
          mkForall(pats, vars, mkImp(guard, body))

        | Some (Util.QEx(vars, pats, body)) -> 
          let vars, pats, guard, body = encode_q_body env vars pats body in
          mkExists(pats, vars, mkAnd(guard, body))

(***************************************************************************************************)
(* end main encoding of kinds/types/exps/formulae *)
(***************************************************************************************************)

(* ----------------------------------------------------------------------------------------------- *)

let mk_prim =
    let asym, a = fresh_bvar "a" Type_sort in 
    let bsym, b = fresh_bvar "b" Type_sort in 
    let xsym, x = fresh_bvar "x" Term_sort in 
    let ysym, y = fresh_bvar "y" Term_sort in 
    let eq_assumption vars t1 t2 = Term.Assume(mkForall([t1], vars, mkEq(t1,t2)), None) in
    let mk_tm v args = match v with 
        | Inl vname -> Term.mkApp(vname, List.map Term.mkBoundV args)
        | Inr vtok -> mk_ApplyE vtok args in
    let abxy_t : term -> either<string, term> -> decl = fun tm v -> 
        let vars = [(asym, Type_sort); (bsym, Type_sort); (xsym, Term_sort); (ysym, Term_sort)] in 
        eq_assumption vars (mk_tm v vars) tm in 
    let xy_t : term -> either<string,term> -> decl = fun tm v -> 
        let vars = [(xsym, Term_sort); (ysym, Term_sort)] in 
        eq_assumption vars (mk_tm v vars) tm in 
    let x_t : term -> either<string, term> -> decl = fun tm v -> 
        let vars = [(xsym, Term_sort)] in
        eq_assumption vars (mk_tm v vars) tm in 
    let prims = [
        (Const.op_Eq,          (abxy_t (boxBool <| mkEq(x,y))));
        (Const.op_notEq,       (abxy_t (boxBool <| mkNot(mkEq(x,y)))));
        (Const.op_LT,          (xy_t  (boxBool <| mkLT(unboxInt x, unboxInt y))));
        (Const.op_LTE,         (xy_t  (boxBool <| mkLTE(unboxInt x, unboxInt y))));
        (Const.op_GT,          (xy_t  (boxBool <| mkGT(unboxInt x, unboxInt y))));
        (Const.op_GTE,         (xy_t  (boxBool <| mkGTE(unboxInt x, unboxInt y))));
        (Const.op_Subtraction, (xy_t  (boxInt  <| mkSub(unboxInt x, unboxInt y))));
        (Const.op_Minus,       (x_t   (boxInt  <| mkMinus(unboxInt x))));
        (Const.op_Addition,    (xy_t  (boxInt  <| mkAdd(unboxInt x, unboxInt y))));
        (Const.op_Multiply,    (xy_t  (boxInt  <| mkMul(unboxInt x, unboxInt y))));
        (Const.op_Division,    (xy_t  (boxInt  <| mkDiv(unboxInt x, unboxInt y))));
        (Const.op_Modulus,     (xy_t  (boxInt  <| mkMod(unboxInt x, unboxInt y))));
        (Const.op_And,         (xy_t  (boxBool <| mkAnd(unboxBool x, unboxBool y))));
        (Const.op_Or,          (xy_t  (boxBool <| mkOr(unboxBool x, unboxBool y))));
        (Const.op_Negation,    (x_t   (boxBool <| mkNot(unboxBool x))));
        ] in
    (fun l v -> prims |> List.filter (fun (l', _) -> lid_equals l l') |> List.map (fun (_, b) -> b v))

let primitive_type_axioms : lident -> term -> list<decl> = 
    let xx = ("x", Term_sort) in
    let x = mkBoundV xx in
    let mk_unit : term -> decl = fun tt -> Term.Assume(mkForall([], [xx], mkIff(Term.mk_HasType x tt, mkEq(x, Term.mk_Term_unit))),    Some "unit inversion") in
    let mk_bool : term -> decl = fun tt -> Term.Assume(mkForall([], [xx], mkIff(Term.mk_tester "BoxBool" x, Term.mk_HasType x tt)),    Some "bool inversion") in
    let mk_int : term -> decl  = fun tt -> Term.Assume(mkForall([], [xx], mkIff(Term.mk_tester "BoxInt" x, Term.mk_HasType x tt)),     Some "int inversion") in
    let mk_str : term -> decl  = fun tt -> Term.Assume(mkForall([], [xx], mkIff(Term.mk_tester "BoxString" x, Term.mk_HasType x tt)),  Some "string inversion") in
    let prims = [(Const.unit_lid,   mk_unit);
                 (Const.bool_lid,   mk_bool);
                 (Const.int_lid,    mk_int);
                 (Const.string_lid, mk_str);
                ] in
    (fun (t:lident) (tt:term) -> 
        match Util.find_opt (fun (l, _) -> lid_equals l t) prims with 
            | None -> []
            | Some(_, f) -> [f tt])

let rec encode_sigelt (env:env_t) (se:sigelt) : (decls * env_t) = 
    if Tc.Env.debug env.tcenv Options.Low
    then Util.fprint1 ">>>>Encoding [%s]\n" 
         <| (Print.sigelt_to_string_short se);//Util.lids_of_sigelt se |> List.map Print.sli |> String.concat ", ");
    let nm = match Util.lid_of_sigelt se with 
        | None -> ""
        | Some l -> l.str in
    let g, e = encode_sigelt' env se in 
    match g with 
     | [] -> [Caption (format1 "<Skipped %s/>" nm)], e
     | _ -> Caption (format1 "<Start encoding %s>" nm)::g@[Caption (format1 "</end encoding %s>" nm)], e
    
and encode_sigelt' (env:env_t) (se:sigelt) : (decls * env_t) = 
    match se with
     | Sig_typ_abbrev(_, _, _, _, [Effect], _) -> [], env

     | Sig_typ_abbrev(lid, tps, _, t, tags, _) -> 
        let tname, ttok, env = gen_free_tvar env lid in 
        let tps, t = match t.n with 
            | Typ_lam(tps', body) -> tps@tps', body
            | _ -> tps, t in 
        let vars, guards, env', _ = encode_binders tps env in
        let tok_app = mk_ApplyT ttok vars in
        let tok_decl = Term.DeclFun(Term.freeV_sym ttok, [], Type_sort, None) in
        let app, decls = 
            if !Options.z3_optimize_full_applications 
            then let app = mkApp(tname, List.map mkBoundV vars) in
                 let decls = [Term.DeclFun(tname, List.map snd vars, Type_sort, None);
                              tok_decl;
                              Term.Assume(mkForall([tok_app], vars, mkEq(tok_app, app)), Some "name-token correspondence")] in
                 app, decls 
            else tok_app, [tok_decl] in
        let def, (body, ex_vars) = 
            if tags |> Util.for_some (function Logic -> true | _ -> false) (* REVIEW: This code is dead, given the previous pattern *)
            then mk_Valid app, (encode_formula t env', [])
            else app, encode_typ_term t env' in 
        let g = decls@[Term.Assume(mkForall([def], vars, mkImp(mk_and_l guards, close_ex ex_vars <| mkEq(def, body))), None)] in 
        g, env

     | Sig_val_decl(lid, t, quals, _) -> 
        encode_free_var env lid t quals

     | Sig_assume(l, f, _, _) -> 
        let g = [Term.Assume(encode_formula f env, Some (format1 "Assumption: %s" (Print.sli l)))] in 
        g, env
               
     | Sig_tycon(t, tps, k, _, datas, quals, _) -> 
        let constructor_or_logic_type_decl c = 
            if quals |> Util.for_some (function Logic -> true | _ -> false) 
            then let name, args, _, _ = c in 
                if !Options.z3_optimize_full_applications
                then [Term.DeclFun(name, args |> List.map snd, Type_sort, None)]
                else [Term.DeclFun(name, [], Type_sort, None)]
            else constructor_to_decl c in
 
        let inversion_axioms tapp vars = 
            if List.length datas = 0
            then []
            else let xxsym, xx = fresh_bvar "x" Term_sort in
                    let data_ax = datas |> List.fold_left (fun out l -> mkOr(out, mk_data_tester env l xx)) mkFalse in
                    [Term.Assume(mkForall([mk_HasType xx tapp], (xxsym, Term_sort)::vars,
                                        mkImp(mk_HasType xx tapp, data_ax)), Some "inversion axiom")] in

        let projection_axioms tapp vars = 
            match quals |> Util.find_opt (function Projector _ -> true | _ -> false) with
            | Some (Projector(d, Inl a)) -> 
                let _, xx = Util.prefix vars in
                let dproj_app = Term.mkApp(mk_typ_projector_name d a, [mkBoundV xx]) in
                [Term.Assume(mkForall([tapp], vars, mkEq(tapp, dproj_app)), Some "projector axiom")]
            | _ -> [] in

        let tname, ttok, env = gen_free_tvar env t in
        let k = Util.close_kind tps k in 
        let formals, res = match (Util.compress_kind k).n with 
            | Kind_arrow(bs, res) -> bs, res
            | _ -> [], k in
        let vars, guards, env', _ = encode_binders formals env in
        let guard = mk_and_l guards in
        let decls, tapp, env =
            if !Options.z3_optimize_full_applications
            then let tname_decl = constructor_or_logic_type_decl(tname, vars, Type_sort, varops.next_id()) in
                 let tapp = Term.mkApp(tname, List.map mkBoundV vars) in
                 let tok_decls, env = match vars with 
                    | [] -> [], push_free_tvar env t tname (mkFreeV(tname, Type_sort)) 
                    | _ -> 
                         let ttok_decl = Term.DeclFun(Term.freeV_sym ttok, [], Type_sort, Some "token") in
                         let ttok_app = mk_ApplyT ttok vars in 
                         let name_tok_corr = Term.Assume(mkForall([ttok_app], vars, mkEq(ttok_app, tapp)), Some "name-token correspondence") in
                         [ttok_decl;name_tok_corr], env in
                 tname_decl@tok_decls, tapp, env 
            else let ttok_decl = constructor_or_logic_type_decl (Term.freeV_sym ttok, [], Type_sort, varops.next_id()) in
                 let ttok_app = mk_ApplyT ttok vars in 
                 ttok_decl, ttok_app, env in
        let kindingAx = Term.Assume(mkForall([tapp], vars, mkImp(guard, encode_knd res env' tapp)), Some "kinding") in
        let g = decls
                @[kindingAx]
                @(primitive_type_axioms t tapp)
                @(inversion_axioms tapp vars)
                @(projection_axioms tapp vars) in
        g, env

    | Sig_datacon(d, t, _, quals, _) -> 
        let ddconstrsym, ddtok, env = gen_free_var env d in //Print.sli d in
        let formals, t_res = match Util.function_formals t with 
            | Some (f, c) -> f, Util.comp_result c
            | None -> [], t in
        let vars, guards, env', names = encode_binders formals env in 
        let projectors = names |> List.map (function 
            | Inl a -> mk_typ_projector_name d a, Type_sort
            | Inr x -> mk_term_projector_name d x, Term_sort) in
        let datacons = (ddconstrsym, projectors, Term_sort, varops.next_id()) |> Term.constructor_to_decl in
        let app = mk_ApplyE ddtok vars in
        let guard = Term.mk_and_l guards in 
        let dapp =  mkApp(ddconstrsym, List.map mkBoundV vars) in
        let ty_pred = encode_typ_pred t_res env' dapp in
        let g = [Term.DeclFun(Term.freeV_sym ddtok, [], Term_sort, Some (format1 "data constructor proxy: %s" (Print.sli d)));
                 Term.Assume(mkForall([app], vars, 
                                       mkEq(app, dapp)), Some "equality for proxy");
                Term.Assume(mkForall([ty_pred], vars, mkImp(guard, ty_pred)), Some "data constructor typing")] in
        datacons@g, env

    | Sig_bundle(ses, _, _) -> 
      let g, env = encode_signature env ses in
      let g', inversions = g |> List.partition (function
        | Term.Assume(_, Some "inversion axiom") -> false
        | _ -> true) in
      g'@inversions, env

    | Sig_let((is_rec, [(Inr f, t1, e)]), _, _) when not is_rec -> 
        if not (Util.is_pure_function t1) then [], env  else
        let (f, ftok), decls, env = declare_top_level_let env f t1 in
        let e = Util.compress_exp e in
        let binders, body = match e.n with
            | Exp_abs(binders, body) -> binders, body 
            | _ -> [], e in
        let vars, guards, env', _ = encode_binders binders env in
        let app = if !Options.z3_optimize_full_applications 
                  then Term.mkApp(f, List.map mkBoundV vars)
                  else mk_ApplyE ftok vars in
        let body, ex_vars = encode_exp body env' in
        let eqn = Term.Assume(mkForall([app], vars, mkImp(mk_and_l guards, close_ex ex_vars <| mkEq(app, body))), None) in
        decls@[eqn], env
     

    | Sig_let((is_rec, [(Inr f, t, e)]), _, _) ->
      (* only encoding recursive pure functions defined immediately by cases on some subset of the arguments 
         The case where the subset of arguments is just xi looks like this:
        
                 let rec f x1 .. xi .. xn = match xi with
                   | P1 y1..ym1 -> e1 
                   | P2 y1..ym2 -> e2
                   | ... 
                  ~>
                  forall x1...xn. f x1...(Pj y1..ymj)..xn = [[ej]]

        The extension to a tuple of the arguments in place of xi is tedious but straightforward.
      *)

      if not (Util.is_pure_function t) then [], env else
      let _ = if Env.debug env.tcenv Options.Low then Util.fprint1 "Encoding let rec %s\n" (Print.sli f) in
      let (f, ftok), decls, env = declare_top_level_let env f t in
  
      let binders_until bs x = match x.n with 
        | Exp_bvar xi -> 
          let rec aux prefix bs = match bs with
            | [] -> None
            | (Inl _, _)::tl -> aux (List.hd bs::prefix) tl
            | (Inr xi', _)::tl -> 
              if Util.bvar_eq xi xi'
              then Some (List.rev prefix, xi, tl)
              else aux (List.hd bs::prefix) tl in
          aux [] bs
        | _ -> None in
        
      let encode_pat p env : list<var> * term * exp * env_t = 
        let _, tun = Tc.Rel.new_tvar Syntax.dummyRange [] ktype in
        let kun, _ = Tc.Rel.new_kvar Syntax.dummyRange [] in
        let rec aux (vars, env) p = match p with 
            | Pat_disj _ -> failwith "Impossible: nested disjunctive pattern"
            | Pat_var x -> 
               let x, _, env = gen_term_var env x in
               let vars = (x,Term_sort)::vars in
               vars,  env
    
            | Pat_tvar a -> 
               let a, _, env = gen_typ_var env a in
               let vars = (a, Type_sort)::vars in
               vars, env
    
            | Pat_wild
            | Pat_twild
            | Pat_constant _ -> vars, env

            | Pat_cons(l, pats) -> 
               let vars, env = pats |> List.fold_left aux (vars, env) in
               vars, env
        
            | Pat_meta(Meta_pat_exp(p, _)) 
            | Pat_meta(Meta_pat_pos(p, _)) -> 
                aux (vars, env) p in
        
        let vars, env = aux ([], env) p in 

        let pat_tm, pat_exp, wildcards = match p with 
            | Pat_meta(Meta_pat_exp(_, e))
            | Pat_meta(Meta_pat_pos(Pat_meta(Meta_pat_exp(_,e)), _)) -> 
              let pat_tm, ex_vars = encode_exp e env in
              pat_tm, e, ex_vars
            | _ -> failwith "Impossible" in

        vars@List.map fst wildcards, pat_tm, pat_exp, env in

      let encode_equation (xs:Syntax.binders) (scrutinee:exp) (p, w, br) (env:env_t) : option<decl> = 
        let arg_pats = match scrutinee.n, p with
            | Exp_bvar x, _ -> [varg <| scrutinee, p] 
           
            | Exp_app({n=Exp_fvar(fv, _)}, args), Pat_cons(l, pats) 
                when (Util.is_tuple_data_lid fv.v (List.length args)
                      && Util.is_tuple_data_lid l (List.length pats)) ->
              List.zip args pats 
              
            | _ -> [] in

        let rec encode_pat_binders binders arg_pats (env, vars, args, guards) = match arg_pats with 
            | [] -> 
              let vars', guards', env, _ = encode_binders binders env in 
              Some (env, vars@vars', args@List.map mkBoundV vars', guards@guards')

            | ((Inr a, _), p)::arg_pats -> 
              begin match binders_until binders a with 
                | None -> None
                | Some(prefix, xi, suffix) -> 
                  let prefix, guards', env, _ = encode_binders prefix env in 
                  let pat_vars, pat_tm, pat_exp, env = encode_pat p env in
                  let pat_guard = encode_typ_pred xi.sort env pat_tm in
                  let suffix = Util.subst_binders ([Inr(xi.v, pat_exp)]) suffix in
                  encode_pat_binders suffix arg_pats (env, vars@prefix@pat_vars, args@List.map mkBoundV prefix@[pat_tm], guards@[pat_guard]@guards')
              end

            | _ -> None  in

        match encode_pat_binders xs arg_pats (env, [], [], []) with 
            | None -> None
            | Some (env, vars, args, guards) -> 
                let f_app = 
                    if !Options.z3_optimize_full_applications
                    then Term.mkApp(f, args)
                    else let args = args |> List.map (fun a -> match a.tm with 
                                | BoundV(_, Type_sort) -> Inl a
                                | BoundV(_, Term_sort) -> Inr a 
                                | _ -> Inr a) in
                         mk_ApplyE_args ftok args in
                let w = match w with 
                    | None -> Term.mkTrue
                    | Some w -> let w, wvars = encode_exp w env in close_ex wvars (mkEq(w, Term.boxBool(Term.mkTrue))) in
                let br, br_vars = encode_exp br env in
                Some <| Term.Assume(mkForall([f_app], vars, mkImp(mk_and_l (w::guards), close_ex br_vars <| mkEq(f_app, br))), Some (Util.format1 "Equation: %s" f)) in
        
        let equations = match e.n with 
            | Exp_abs(xs, {n=Exp_match(scrutinee, cases)}) -> 
                let rec aux out = function 
                    | [] -> List.rev out
                    | case::cases -> 
                      match encode_equation xs scrutinee case env with 
                        | None -> 
                          if Env.debug env.tcenv Options.Low then Util.fprint1 "No equations; failed to encode case %s\n" (Print.pat_to_string (let p, _, _ = case in p));
                          []
                        | Some d -> aux (d::out) cases in

                aux [] cases

            | _ -> 
              if Env.debug env.tcenv Options.Low then Util.print_string "No equations, because top-level term is not a match\n";
              [] in
        decls@equations, env


    | Sig_let((_,lbs), _, _) -> //TODO: mutual recursion
        let msg = lbs |> List.map (fun (lb, _, _) -> Print.lbname_to_string lb) |> String.concat " and " in
        [], env

    | Sig_main _
    | Sig_monads _ -> [], env

and declare_top_level_let env x t =
    match try_lookup_lid env x with 
        | None -> (* Need to introduce a new name decl *)
            let decls, env = encode_free_var env x t [] in
            lookup_lid env x, decls, env 
        | Some (n, x) -> (* already declared, only need an equation *)
            (n, x), [], env

and encode_free_var env lid t quals = 
    if not <| Util.is_pure_function t 
    then [], env
    else let formals, res = match Util.function_formals t with 
            | Some (args, comp) -> args, Util.comp_result comp 
            | None -> [], t in

         let mk_disc_proj_axioms vapp vars = quals |> List.collect (function 
            | Discriminator d -> 
                let _, (xxsym, _) = Util.prefix vars in
                let xx = mkBoundV(xxsym, Term_sort) in
                [Term.Assume(mkForall([vapp], vars,
                                        mkEq(vapp, Term.boxBool <| Term.mk_tester d.str xx)), None)]

            | Projector(d, Inr f) -> 
                let _, (xxsym, _) = Util.prefix vars in
                let xx = mkBoundV(xxsym, Term_sort) in
                [Term.Assume(mkForall([vapp], vars,
                                        mkEq(vapp, Term.mkApp(mk_term_projector_name d f, [xx]))), None)]
            | _ -> []) in
        
        let vname, vtok, env = gen_free_var env lid in 

        let vars, guards, env', _ = encode_binders formals env in
        let guard = mk_and_l guards in
        let vtok_app = mk_ApplyE vtok vars in
        
        let vapp, prim, decls, env =    
            if !Options.z3_optimize_full_applications
            then (* Generate a token and a function symbol; equate the two, and use the function symbol for full applications *)
                let vapp = Term.mkApp(vname, List.map Term.mkBoundV vars) in
                let vname_decl = Term.DeclFun(vname, formals |> List.map (function Inl _, _ -> Type_sort | _ -> Term_sort), Term_sort, None) in
                let tok_decl, env = match formals with 
                    | [] -> [], push_free_var env lid vname (mkFreeV(vname, Term_sort))
                    | _ -> 
                        let vtok_decl = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, None) in
                        let name_tok_corr = Term.Assume(mkForall([vtok_app], vars, mkEq(vtok_app, vapp)), None) in
                        [vtok_decl;name_tok_corr], env in
                vapp, Inl vname, vname_decl::tok_decl, env
            else     
                let tok_decl = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, None) in
                vtok_app, Inr vtok, [tok_decl], env in

        let ty_pred = encode_typ_pred res env' vapp in
        let typingAx = Term.Assume(mkForall([vapp], vars, mkImp(guard, ty_pred)), None) in
        let g = decls@typingAx::mk_disc_proj_axioms vapp vars@mk_prim lid prim in
        g, env
       

and encode_signature env ses = 
    ses |> List.fold_left (fun (g, env) se ->            
      let g', env = encode_sigelt env se in 
      g@g', env) ([], env) 

let encode_env_bindings (env:env_t) (bindings:list<Tc.Env.binding>) : (decls * env_t) = 
    let encode_binding b (decls, env) = match b with
        | Env.Binding_var(x, t) -> 
            let xxsym, xx, env' = gen_free_term_var env x in 
            let g = [Term.DeclFun(xxsym, [], Term_sort, Some (Print.strBvd x));
                     Term.Assume(encode_typ_pred (norm_t env t) env xx, None)] in
            decls@g, env'
        | Env.Binding_typ(a, k) -> 
            let aasym, aa, env' = gen_free_typ_var env a in 
            let g = [Term.DeclFun(aasym, [], Type_sort, Some (Print.strBvd a));
                     Term.Assume(encode_knd k env aa, None)] in
            decls@g, env'
        | Env.Binding_lid(x, t) -> 
            let g, env' = encode_free_var env x t [] in
            decls@g, env'
        | Env.Binding_sig se -> 
            let g, env' = encode_sigelt env se in 
            decls@g, env' in
    List.fold_right encode_binding bindings ([], env)

(* caching encodings of the environment and the top-level API to the encoding *)
open Microsoft.FStar.Tc.Env
let last_env : ref<list<env_t>> = Util.mk_ref []
let init_env tcenv = last_env := [{bindings=[]; tcenv=tcenv}]
let get_env tcenv = match !last_env with 
    | [] -> failwith "No env; call init first!"
    | e::_ -> {e with tcenv=tcenv}
let set_env env = match !last_env with 
    | [] -> failwith "Empty env stack"
    | _::tl -> last_env := env::tl
let push_env () = match !last_env with 
    | [] -> failwith "Empty env stack"
    | hd::tl -> last_env := hd::hd::tl 
let pop_env () = match !last_env with 
    | [] -> failwith "Popping an empty stack"
    | _::tl -> last_env := tl

(* TOP-LEVEL API *)

let init tcenv =
    init_env tcenv;
    Z3.giveZ3 [DefPrelude]
let push () = 
    push_env ();
    varops.push(); 
    Z3.giveZ3 [Term.Push]
let pop ()  = 
    ignore <| pop_env();
    varops.pop(); 
    Z3.giveZ3 [Term.Pop]
let encode_sig tcenv se =
   let env = get_env tcenv in
   let decls, env = encode_sigelt env se in
   set_env env;
   Z3.giveZ3 decls
let encode_modul tcenv modul = 
   let env = get_env tcenv in
   let decls, env = encode_signature env modul.exports in
   set_env env;
   Z3.giveZ3 decls
let solve tcenv q =
    let env = get_env tcenv in
    push_env (); varops.push();
    let env_decls, env = encode_env_bindings env (List.filter (function Binding_sig _ -> false | _ -> true) tcenv.gamma) in
    if debug tcenv Options.Low then Util.fprint1 "Encoding query formula: %s\n" (Print.formula_to_string q);
    let phi = encode_formula q env in
    let label_suffix = [] in  //labels |> List.fold_left (fun decls (lname, t) -> decls@[Echo lname; Eval t]) theory in
    let r = Caption (Range.string_of_range (Tc.Env.get_range tcenv)) in
    ignore <| pop_env(); varops.pop();
    let decls = [Term.Push; r]
                @env_decls
                @[Term.Caption "<Query>"; Term.Assume(mkNot phi, Some "query"); Term.Caption "</Query>"; Term.CheckSat]
                @label_suffix
                @[Term.Pop; Term.Echo "Done!"] in
    Z3.queryZ3 decls
let is_trivial (tcenv:Tc.Env.env) (q:typ) : bool = 
   let env = get_env tcenv in
   push();
   let f = encode_formula q env in
   pop();
   match f.tm with 
    | True -> true
    | _ -> false

let solver = {
    init=init;
    push=push;
    pop=pop;
    encode_sig=encode_sig;
    encode_modul=encode_modul;
    solve=solve;
    is_trivial=is_trivial
}
let dummy = {
    init=(fun _ -> ());
    push=(fun _ -> ());
    pop=(fun _ -> ());
    encode_sig=(fun _ _ -> ());
    encode_modul=(fun _ _ -> ());
    solve=(fun _ _ -> true);
    is_trivial=(fun _ _ -> false)
}


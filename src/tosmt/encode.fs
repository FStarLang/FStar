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
let vargs args = List.filter (function (Inl _, _) -> false | _ -> true) args

(* ------------------------------------ *)
(* Some operations on constants *)
let escape (s:string) = Util.replace_char s '\'' '_'
let escape_null_name a = 
    if a.ppname.idText = "_"
    then a.ppname.idText ^ a.realname.idText
    else a.ppname.idText 

let mk_typ_projector_name lid (a:btvdef) = 
    escape <| format2 "%s_%s" lid.str (escape_null_name a)
let mk_term_projector_name lid (a:bvvdef) = 
    let a = {ppname=Util.unmangle_field_name a.ppname; realname=a.realname} in
    escape <| format2 "%s_%s" lid.str (escape_null_name a)
let primitive_projector_by_pos env lid i = 
    let fail () = failwith (Util.format2 "Projector %s on data constructor %s not found" (string_of_int i) (lid.str)) in
    let t = Tc.Env.lookup_datacon env lid in 
    match (Util.compress_typ t).n with 
        | Typ_fun(binders, _) -> 
          if ((i < 0) || i >= List.length binders) //this has to be within bounds!
          then fail ()
          else let b = List.nth binders i in 
               begin match fst b with 
                | Inl a -> mk_typ_projector_name lid a.v
                | Inr x -> mk_term_projector_name lid x.v 
               end
        | _ -> fail ()
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

 let unmangle (x:bvdef<'a>) : bvdef<'a> = Util.mkbvd (Util.unmangle_field_name x.ppname, Util.unmangle_field_name x.realname)
(* ---------------------------------------------------- *)
(* <Environment> *)
(* Each entry maps a Syntax variable to its encoding as a SMT2 term *)
type binding = 
    | Binding_var   of bvvdef * term
    | Binding_tvar  of btvdef * term
    | Binding_fvar  of lident * string * term (* free variables, depending on whether or not they are fully applied ...  *)
    | Binding_ftvar of lident * string * term (* ... are mapped either to SMT2 functions, or to nullary term/type tokens *)
   
type env_t = {bindings:list<binding>;
              tcenv:Env.env;
              warn:bool;
              polarity:bool;
              refinements:Util.smap<(term * list<decl>)>
              }
let negate env = {env with polarity=not env.polarity}
let print_env e = 
    e.bindings |> List.map (function 
        | Binding_var (x, t) -> Print.strBvd x
        | Binding_tvar (a, t) -> Print.strBvd a
        | Binding_fvar(l, s, t) -> Print.sli l
        | Binding_ftvar(l, s, t) -> Print.sli l) |> String.concat ", "

let lookup_binding env f = Util.find_map env.bindings f 
              
let caption_t env t = 
    if Tc.Env.debug env.tcenv Options.Low
    then Some (Print.typ_to_string t)
    else None


let fresh_bvar x s = let xsym = varops.fresh x in xsym, mkBoundV(xsym, s)
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
        
let close_all vars pred = match vars with
    | [] -> pred
    | _ -> 
        let vars, guards = List.unzip vars in 
        Term.mkForall([], vars, Term.mkImp(mk_and_l guards, pred))
        
let close env vars pred = 
    if env.polarity
    then close_ex vars pred
    else close_all vars pred

(* </Utilities> *)

(**********************************************************************************)
(* The main encoding of kinds/types/expressions/formulae: all mutually recursive  *)
(* see fstar-priv/papers/mm/encoding.txt for a semi-formal sketch of the encoding *)
(**********************************************************************************)

(* Abstractly:

      ctx = (bvvdef -> term(Term_sort)) U (btvdef -> term(Type_sort)
       ex = set (var x term(Bool))        existentially bound variables 
    [[k]] : ctx -> term(Type_sort) -> term(Bool)
    [[t]] : ctx -> term(Type_sort) * ex
    [[e]] : ctx -> term(Term_sort) * ex
    [[f]] : ctx -> term(Bool)
   [[bs]] : ctx -> (vars
                    * term(Bool)  <-- guard on bound vars
                    * ctx)   <-- context extended with bound vars
                    
    Concretely, [[*]] are the encode_* functions, for knd, typ, exp, formula, binders
    ctx is implemented using env_t
    and term( * ) is just term
 *)

type label = (var * string)
type labels = list<label>
type match_branch = {
    guard:term;       (* bool; negation of all prior pattern guards *)
    pat_vars:ex_vars; (* existentially bound pattern variables *)
    pattern:term;     (* the pattern itself *)
    rhs:term;         (* the branch translated as a term *)
}
type match_branches = list<match_branch>
type pattern = {
  pat_vars: list<(Syntax.either_var * var)>;
  pat_term: unit -> (term * ex_vars * decls_t);    (* the pattern as a term(exp) *)
  guard: term -> term;                           (* the guard condition of the pattern, as applied to a particular scrutinee term(exp) *)
  projections: term -> list<(either_var * term)> (* bound variables of the pattern, and the corresponding projected components of the scrutinee *)
 }
exception Let_rec_unencodeable of string

let encode_const = function 
    | Const_unit -> mk_Term_unit
    | Const_bool true -> boxBool mkTrue
    | Const_bool false -> boxBool mkFalse
    | Const_int32 i -> boxInt (mkInteger i)
    | Const_string(bytes, _) -> varops.string_const (Util.string_of_bytes <| bytes)
    | c -> failwith (Util.format1 "Unhandled constant: %s\n" (Print.const_to_string c))
 
let rec encode_knd (k:knd) (env:env_t) (t:term) : term  * decls_t = 
    match (Util.compress_kind k).n with 
        | Kind_type -> 
            mk_HasKind t (Term.mk_Kind_type), []

        | Kind_abbrev(_, k) -> 
            encode_knd k env t

        | Kind_uvar (uv, _) -> (* REVIEW: warn? *)
            Term.mkTrue, []

        | Kind_arrow(bs, k) -> 
            let vars, guards, env', decls, _ = encode_binders bs env in 
            let prekind = mk_tester "Kind_arrow" (mk_PreKind t) in
            let app = mk_ApplyT t vars in
            let k, decls' = encode_knd k env' app in
            Term.mkAnd(prekind,
                       Term.mkForall(app::guards, vars, mkImp(mk_and_l guards, k))), 
            decls@decls'

        | _ -> failwith (Util.format1 "Unknown kind: %s" (Print.kind_to_string k))

and encode_binders (bs:Syntax.binders) (env:env_t) : (list<var>       (* translated bound variables *)
                                                      * list<term>    (* guards *)
                                                      * env_t         (* extended context *)
                                                      * decls_t         (* top-level decls to be emitted *)
                                                      * list<either<btvdef, bvvdef>>) (* unmangled names *) =

    if Tc.Env.debug env.tcenv Options.Low then Util.fprint1 "Encoding binders %s\n" (Print.binders_to_string ", " bs);
    
    let vars, guards, env, decls, names = bs |> List.fold_left (fun (vars, guards, env, decls, names) b -> 
        let v, g, env, decls', n = match fst b with 
            | Inl {v=a; sort=k} -> 
                let a = unmangle a in
                let aasym, aa, env' = 
                    if is_null_binder b 
                    then withenv env <| fresh_bvar "a" Type_sort
                    else gen_typ_var env a in 
                let guard_a_k,decls' = encode_knd k env aa in
                (aasym, Type_sort), 
                guard_a_k,
                env', 
                decls',
                Inl a  

            | Inr {v=x; sort=t} -> 
                let x : bvvdef = unmangle x in
                let xxsym, xx, env' = 
                    if is_null_binder b   
                    then withenv env <| fresh_bvar "x" Term_sort
                    else gen_term_var env x in
                let guard_x_t, decls' = encode_typ_pred t env xx in
                (xxsym, Term_sort), 
                guard_x_t,
                env', 
                decls',
                Inr x in
        v::vars, g::guards, env, decls@decls', n::names) ([], [], env, [], []) in
    List.rev vars,
    List.rev guards,
    env, 
    decls,
    List.rev names

and encode_typ_pred (t:typ) (env:env_t) (e:term) : term * decls_t = 
    let t = Util.compress_typ t in 
    match t.n with 
        | Typ_refine(x, f) -> 
          let base_pred, decls = encode_typ_pred x.sort env e in 
          let env' = push_term_var env x.v e in
          let refinement, decls' = encode_formula f env' in
          Term.mkAnd(base_pred, refinement), decls@decls' 

        | _ -> 
            let t, ex, decls = encode_typ_term t env in 
            close_ex ex (mk_HasType e t), decls

and encode_typ_term (t:typ) (env:env_t) : (term       (* encoding of t, expects t to be in normal form already *)
                                           * ex_vars  (* new names and guards generated for this type, which must be bound in the caller's scope *)
                                           * decls_t)   (* top-level declarations to be emitted (for shared representations of existentially bound terms *) = 
    let fresh_vars tname xname = 
        let tsym = varops.fresh tname, Type_sort in
        let ttm = mkBoundV tsym in
        let fsym = varops.fresh xname, Term_sort in
        let f = mkBoundV fsym in
        tsym, ttm, fsym, f in

    let t0 = Util.compress_typ t in
    match t0.n with 
      | Typ_btvar a -> 
        lookup_typ_var env a, [], []

      | Typ_const fv -> 
        lookup_free_tvar env fv, [], []

      | Typ_fun(binders, res) -> (* TODO: add sharing *)
        let doit binders res =
            let tsym, ttm, fsym, f = fresh_vars "funtype" "f" in
            let pretype = mk_tester "Typ_fun" (mk_PreType f) in
            let t_has_kind = mk_HasKind ttm Term.mk_Kind_type in
            let f_hastype_t = mk_HasType f ttm in
            let guard, decls = 
                if not <| Util.is_pure env.tcenv res 
                then pretype, [] 
                else let vars, guards, env', decls, _ = encode_binders binders env in 
                     let app = mk_ApplyE f vars in
                     if Util.is_total_comp res
                     then let res_pred, decls' = encode_typ_pred (Util.comp_result res) env' app in
                          let app_pred = mkForall([app], vars, mkImp(mk_and_l guards, res_pred)) in
                          mkAnd(pretype, app_pred), decls@decls'
                     else pretype, decls in
            ttm, [tsym, Term.mkAnd(t_has_kind, mkForall([f_hastype_t], [fsym], mkImp(f_hastype_t, guard)))], decls in

        begin match binders |> Util.prefix_until (function (Inr _, _) -> true | _ -> false) with 
            | Some (t_binders, first_v_binder, rest) -> //explicitly curry the type-binders, since partial type-applications arise via unification commonly in ML programs
              begin match t_binders with 
                | [] -> doit binders res
                | _ -> 
                  let res = mk_Typ_fun(first_v_binder::rest, res) ktype t0.pos |> Syntax.mk_Total in
                  doit t_binders res
             end
            | None -> doit binders res 
        end
      
      | Typ_refine(x, f) ->
        let xsym = "this", Term_sort in 
        let xtm = mkBoundV xsym in 
        let base_pred, decls = encode_typ_pred x.sort env xtm in 
        let env' = push_term_var env x.v xtm in
        let refinement, decls' = encode_formula f env' in
        let encoding = Term.mkAnd(base_pred, refinement) in
        (* TODO: resolve sharing *)
        begin match Util.smap_try_find env.refinements encoding.as_str with 
            | Some (tm, _) -> tm, [], []
            | None -> 
                if Term.free_variables encoding = [xsym]
                then let tsym = varops.fresh "refinement", Type_sort in 
                     let ttm = mkFreeV tsym in 
                     let x_has_t = mk_HasType xtm ttm in
                     let t_has_kind = mk_HasKind ttm Term.mk_Kind_type in
                     let assumption = Term.mkAnd(t_has_kind, Term.mkForall([x_has_t], [xsym], mkIff(x_has_t, encoding))) in
                     let new_decls = [Term.DeclFun(fst tsym, [], Type_sort, None);
                                      Term.Assume(assumption, Some (Print.typ_to_string t))] in
                     Util.smap_add env.refinements encoding.as_str (ttm, new_decls);
                     ttm, [], decls@decls'@new_decls
                else let tsym = varops.fresh "refinet", Type_sort in
                     let ttm = mkBoundV tsym in
                     let x_has_t = mk_HasType xtm ttm in
                     let t_has_kind = mk_HasKind ttm Term.mk_Kind_type in
                     ttm, [(tsym, Term.mkAnd(t_has_kind, Term.mkForall([x_has_t], [xsym], mkIff(x_has_t, encoding))))], decls@decls'
        end

      | Typ_uvar (uv, _) ->
        let ttm = Term.mk_Typ_uvar (Unionfind.uvar_id uv) in
        let t_has_k, decls = encode_knd t.tk env ttm in //TODO: skip encoding this if it has already been encoded before
        let d = Term.Assume(t_has_k, None) in
        ttm, [], d::decls

      | Typ_app(head, args) -> (* this is in head normal form; so t must be a type variable; unification variable; or a constant *)
        let is_full_app () = match (Util.compress_kind head.tk).n with
            | Kind_arrow(formals, _) -> List.length formals = List.length args
            | _ -> false in
        let head = Util.compress_typ head in
        begin match head.n with
            | Typ_btvar a -> 
              let head = lookup_typ_var env a in
              let args, vars, decls = encode_args args env in
              let t = mk_ApplyT_args head args in
              t, vars, decls
                
            | Typ_const fv -> 
              let args, vars, decls = encode_args args env in
              if is_full_app () && !Options.z3_optimize_full_applications
              then let head = lookup_free_tvar_name env fv in
                   let t = Term.mkApp(head, List.map (function Inl t | Inr t -> t) args) in
                   t, vars, decls
              else let head = lookup_free_tvar env fv in
                   let t = mk_ApplyT_args head args in
                   t, vars, decls

            | Typ_uvar _ -> 
              encode_typ_term head env  

            | _ -> 
              let t = norm_t env t in
              (* CH: WARNING: if norm_t returns the same type it got as input
                     this code enters infinite loop (as it happened with uvars);
                     might want to do something about this!? *)
              encode_typ_term t env
        end

      | Typ_lam(bs, t) ->
        let vars, guards, env, decls, _ = encode_binders bs env in
        let name = varops.fresh (Print.tag_of_typ t0), Type_sort in 
        let tag = mkBoundV name in 
        let app = mk_ApplyT tag vars in
        let body, vars_body, decls' = encode_typ_term t env in
        let eq = close_ex vars_body (mkEq(app, body)) in
        let guard = mkForall(app::guards, vars, mkImp(mk_and_l guards, eq)) in
        tag, [(name, guard)], decls@decls'

      | Typ_ascribed(t, _) -> 
        encode_typ_term t env

      | Typ_meta _
      | Typ_delayed  _ 
      | Typ_unknown    -> failwith (format2 "(%s) Impossible: %s" (Range.string_of_range <| t.pos) (Print.tag_of_typ t))                 

and encode_exp (e:exp) (env:env_t) : (term * ex_vars * decls_t) = 
    let e = Visit.compress_exp_uvars e in 
    let e0 = e in
    match e.n with 
      | Exp_delayed _ -> (* REVIEW: dead code? *)
        encode_exp (Util.compress_exp e) env

      | Exp_bvar x -> 
        lookup_term_var env x, [], []

      | Exp_fvar(v, _) -> 
        lookup_free_var env v, [], []

      | Exp_constant c -> 
        encode_const c, [], []
      
      | Exp_ascribed(e, _)
      | Exp_meta(Meta_desugared(e, _)) -> 
        encode_exp e env

      | Exp_uvar(uv, _) ->
        (* TODO: sharing *)
        let fsym = varops.fresh "Exp_uvar", Term_sort in
        mkBoundV fsym, [(fsym, Term.mkTrue)], []
 
      | Exp_abs(bs, body) -> 
        (* TODO: sharing *)
        let esym, lam = fresh_bvar "lambda" Term_sort in
        if not <| Util.is_pure_function e.tk 
        then lam, [(esym, Term_sort), Term.mkTrue], []
        else let vars, _, envbody, decls, _ = encode_binders bs env in 
             let app = mk_ApplyE lam vars in
             let body, body_vars, decls' = encode_exp body envbody in
             let eq = close_ex body_vars (mkEq(app, body)) in
             let lam_typed, decls'' = encode_typ_pred e.tk env lam in
             let tsym, t = fresh_bvar "t" Type_sort in 
             let app_has_t = Term.mk_HasType app t in
             let app_is_typed = Term.mkExists([app_has_t], [(tsym, Type_sort)], app_has_t) in
             let app_eq = Term.mkForall([app], vars, mkImp(app_is_typed, eq)) in
             lam, [(esym, Term_sort), Term.mkAnd(app_eq, lam_typed)], decls@decls'@decls''

      | Exp_app({n=Exp_fvar(l, _)}, [(Inl _, _); (Inl _, _); (Inr v1, _); (Inr v2, _)]) when (lid_equals l.v Const.lexpair_lid) -> 
         let v1, vars1, decls1 = encode_exp v1 env in 
         let v2, vars2, decls2 = encode_exp v2 env in
         Term.mk_LexPair v1 v2, vars1@vars2, decls1@decls2

      | Exp_app(head, args) -> 
        let args, vars, decls = encode_args args env in
    
        let encode_partial_app () = 
            let head, vars', decls' = encode_exp head env in
            mk_ApplyE_args head args, vars'@vars, decls@decls' in

        let encode_full_app fv = 
            let fname = lookup_free_var_name env fv in
            let tm = Term.mkApp(fname, List.map (function Inl t | Inr t -> t) args) in
            tm, vars, decls in
        
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
                          else (if Tc.Env.debug env.tcenv Options.Low then Util.fprint2 "(%s) %s is not a full application!\n" 
                                    (Range.string_of_range e0.pos)
                                    (Print.exp_to_string e0);
                                encode_partial_app ()))
            | _ ->
                if Tc.Env.debug env.tcenv Options.Low then Util.fprint2 "(%s) %s is not a full application!\n" 
                    (Range.string_of_range e0.pos)
                    (Print.exp_to_string e0); encode_partial_app ()
        end

      | Exp_let((false, [(Inr _, _, _)]), _) -> failwith "Impossible: already handled by encoding of Sig_let" 

      | Exp_let((false, [(Inl x, t1, e1)]), e2) ->
        let xvar, x, env' = gen_term_var env x in 
        let guard, decls = encode_typ_pred t1 env x in
        let ee1, vars1, decls1 = encode_exp e1 env in
        let ee2, vars2, decls2 = encode_exp e2 env' in
        ee2, vars1@[(xvar, Term_sort), mkAnd(guard, mkEq(x, ee1))]@vars2, decls@decls1@decls2 
  
      | Exp_let((true, _), _) -> 
        let name = varops.fresh "Expression", Term_sort in
        let sym = mkBoundV name in
        Tc.Errors.warn e.pos "Nested 'let rec' is not yet fully encoded to the SMT solver; you may not be able to prove some facts";
        sym, [(name, Term.mkTrue)], []

      | Exp_match(e, pats) ->
        let scr, scr_vars, decls1 = encode_exp e env in 
        let def = varops.fresh "default", Term_sort in
        let match_tm, vars, decls = List.fold_right (fun (p, w, br) (else_case, ex_vars, decls) -> 
            let patterns = encode_pat env p in
            List.fold_right (fun (env0, pattern) (else_case, ex_vars, decls) -> 
                let guard = pattern.guard scr in
                let projections = pattern.projections scr in
                let env = projections |> List.fold_left (fun env (x, t) -> match x with 
                    | Inl a -> push_typ_var env a.v t
                    | Inr x -> push_term_var env x.v t) env in
                let guard, decls2 = match w with 
                    | None -> guard, []
                    | Some w -> 
                        let w, ex_vars, decls2 = encode_exp w env in
                        Term.mkAnd(guard, close_ex ex_vars <| Term.mkEq(w, Term.boxBool Term.mkTrue)), decls2 in
                let br, br_vars, decls3 = encode_exp br env in
                mkITE(guard, br, else_case), ex_vars@br_vars, decls@decls2@decls3)
            patterns (else_case, ex_vars, decls))
            pats (mkBoundV def, (def, Term.mkTrue)::scr_vars, decls1) in
        match_tm, vars, decls

      | Exp_meta _ -> failwith (Util.format2 "(%s): Impossible: encode_exp got %s" (Range.string_of_range e.pos) (Print.exp_to_string e))

and encode_pat env (pat:Syntax.pat) : list<(env_t * pattern)>  (* one for each disjunct *) = 
    match pat.v with 
        | Pat_disj ps -> List.map (encode_one_pat env) ps
        | _ -> [encode_one_pat env pat]

and encode_one_pat (env:env_t) pat : (env_t * pattern) = 
        if Tc.Env.debug env.tcenv Options.Low then Util.fprint1 "Encoding pattern %s\n" (Print.pat_to_string pat);
        let vars, pat_exp_or_typ = Tc.Util.decorated_pattern_as_either pat in

        let env, vars = vars |> List.fold_left (fun (env, vars) v -> match v with
            | Inl a -> 
              let aa, _, env = gen_typ_var env a.v in 
              env, (v, (aa, Type_sort))::vars   
            | Inr x -> 
              let xx, _, env = gen_term_var env x.v in 
              env, (v, (xx, Term_sort))::vars) (env, []) in
        
        let rec mk_guard pat (scrutinee:term) : term = match pat.v with 
            | Pat_disj _ -> failwith "Impossible"
            | Pat_var _ 
            | Pat_wild _ 
            | Pat_tvar _
            | Pat_twild _ 
            | Pat_dot_term _
            | Pat_dot_typ _ -> Term.mkTrue
            | Pat_constant c -> 
               Term.mkEq(scrutinee, encode_const c)
            | Pat_cons(f, args) -> 
                let is_f = mk_data_tester env f.v scrutinee in
                let sub_term_guards = args |> List.mapi (fun i arg -> 
                    let proj = primitive_projector_by_pos env.tcenv f.v i in
                    mk_guard arg (Term.mkApp(proj, [scrutinee]))) in
                Term.mk_and_l (is_f::sub_term_guards) in

         let rec mk_projections pat (scrutinee:term) =  match pat.v with
            | Pat_disj _ -> failwith "Impossible"
            
            | Pat_dot_term (x, _)
            | Pat_var x
            | Pat_wild x -> [Inr x, scrutinee] 

            | Pat_dot_typ (a, _)
            | Pat_tvar a
            | Pat_twild a -> [Inl a, scrutinee]

            | Pat_constant _ -> []

            | Pat_cons(f, args) -> 
                args 
                |> List.mapi (fun i arg -> 
                    let proj = primitive_projector_by_pos env.tcenv f.v i in
                    mk_projections arg (Term.mkApp(proj, [scrutinee]))) 
                |> List.flatten in

        let pat_term () = match pat_exp_or_typ with 
            | Inl t -> encode_typ_term t env
            | Inr e -> encode_exp e env in

        let pattern = {
                pat_vars=vars;
                pat_term=pat_term;
                guard=mk_guard pat;
                projections=mk_projections pat;
            }  in

        env, pattern 

and encode_args l env =
    let l, vars, decls = l |> List.fold_left (fun (tms, ex_vars, decls) x -> match x with
        | Inl t, _ -> let t, vs, decls' = encode_typ_term t env in Inl t::tms, vs@ex_vars, decls@decls'
        | Inr e, _ -> let t, vs, decls' = encode_exp e env in Inr t::tms, vs@ex_vars, decls@decls') ([], [], []) in
    List.rev l, vars, decls

and encode_formula (phi:typ) (env:env_t) : term * decls_t = 
    let t, vars, decls = encode_formula_with_labels phi env in
    match vars with
        | [] -> t, decls
        | _ -> failwith "Unexpected labels in formula"
        
and encode_formula_with_labels  (phi:typ) (env:env_t) : term * labels * decls_t = (* expects phi to be normalized; the existential variables are all labels *)
    let enc (f:list<term> -> term) : args -> term * labels * decls_t = fun l -> 
        let (vars, decls), args = Util.fold_map (fun (vars, decls) x -> match fst x with 
            | Inl t -> let t, vars', decls' = encode_typ_term t env in (vars@vars', decls@decls'), t
            | Inr e -> let e, vars', decls' = encode_exp e env in (vars@vars', decls@decls'), e) ([],[]) l in
        close env vars (f args), [], decls in

    let enc_prop_c polarities f : args -> term * labels * decls_t = fun l ->
        let phis, labs, decls = List.unzip3 <| List.map2 (fun p l -> 
            let env = if p then env else negate env in 
            match fst l with 
                | Inl t -> encode_formula_with_labels t env
                | _ -> failwith "Expected a formula") polarities l in
        f phis, List.flatten labs, List.flatten decls in
  

    let const_op f _ = f, [], [] in
    let un_op f l = f <| List.hd l in
    let bin_op : ((term * term) -> term) -> list<term> -> term = fun f -> function 
        | [t1;t2] -> f(t1,t2)
        | _ -> failwith "Impossible" in
    let tri_op : ((term * term * term) -> term) -> list<term> -> term = fun f -> function
        | [t1;t2;t3] -> f(t1,t2,t3)
        | _ -> failwith "Impossible" in
    let eq_op : args -> term * labels * decls_t = function 
        | [_;_;e1;e2] -> enc (bin_op mkEq) [e1;e2]
        | l ->  enc (bin_op mkEq) l in
  
    let mk_imp : args -> term * labels * decls_t = function 
        | [(Inl lhs, _); (Inl rhs, _)] -> 
          let l1, labs1, decls1 = encode_formula_with_labels rhs env in
          begin match l1.tm with 
            | True -> l1, labs1, decls1 (* Optimization: don't bother encoding the LHS of a trivial implication *)
            | _ -> 
             let l2, labs2, decls2 = encode_formula_with_labels lhs (negate env) in
             Term.mkImp(l2, l1), labs1@labs2, decls1@decls2
          end in
  
    let mk_iff : args -> term * labels * decls_t = function 
        | [(Inl lhs, _); (Inl rhs, _)] -> 
          let l1, labs1, decls1 = encode_formula_with_labels lhs (negate env) in
          let l2, labs2, decls2 = encode_formula_with_labels rhs env in

          let m1, labs3, decls3 = encode_formula_with_labels lhs env in
          let m2, labs4, decls4 = encode_formula_with_labels rhs (negate env) in

          mkAnd(mkImp(l1, l2), mkImp(m2, m1)), labs1@labs2@labs3@labs4, decls1@decls2@decls3@decls4
  
        | _ -> failwith "Impossible" in
    let unboxInt_l : (list<term> -> term) -> list<term> -> term = fun f l -> f (List.map Term.unboxInt l) in
    let connectives = [ 
                        (Const.and_lid, enc_prop_c [true;true]  <| bin_op mkAnd);
                        (Const.or_lid,  enc_prop_c [true;true]  <| bin_op mkOr);
                        (Const.imp_lid, mk_imp);
                        (Const.iff_lid, mk_iff);
                        (Const.ite_lid, enc_prop_c [false;true;true] <| tri_op mkITE);
                        (Const.not_lid, enc_prop_c [false] <| un_op mkNot);
                        (Const.lt_lid,  enc (unboxInt_l <| bin_op mkLT));
                        (Const.gt_lid,  enc (unboxInt_l <| bin_op mkGT));
                        (Const.gte_lid, enc (unboxInt_l <| bin_op mkGTE));
                        (Const.lte_lid, enc (unboxInt_l <| bin_op mkLTE));
                        (Const.eqT_lid, enc <| bin_op mkEq);
                        (Const.eq2_lid, eq_op);
                        (Const.true_lid, const_op mkTrue);
                        (Const.false_lid, const_op mkFalse);
                    ] in

    let fallback phi =  match phi.n with
        | Typ_meta(Meta_labeled(phi', msg, b)) -> 
          let phi, labs, decls = encode_formula_with_labels phi' env in
          let lvar = varops.fresh "label", Bool_sort in
          let lterm = Term.mkFreeV lvar in
          let lphi = Term.mkOr(lterm, phi) in
          lphi, (lvar, msg)::labs, decls
        
        | _ -> 
            let tt, ex_vars, decls = encode_typ_term phi env in
            close env ex_vars <| Term.mk_Valid tt, [], decls in

    let encode_q_body env (bs:Syntax.binders) (ps:args) body = 
        let vars, guards, env, decls, _ = encode_binders bs env in 
        let pats, decls' = ps |> List.map (function 
            | Inl t, _ -> encode_formula t env
            | Inr e, _ -> let t, _, decls = encode_exp e env in t, decls) |> List.unzip in 
        let body, labs, decls'' = encode_formula_with_labels body env in
            vars, pats, mk_and_l guards, body, labs, decls@List.flatten decls'@decls'' in
    
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

          let vars, pats, guard, body, labs, decls = encode_q_body env vars pats body in
          mkForall(pats, vars, mkImp(guard, body)), labs, decls

        | Some (Util.QEx(vars, pats, body)) -> 
          let vars, pats, guard, body, labs, decls = encode_q_body env vars pats body in
          mkExists(pats, vars, mkAnd(guard, body)), labs, decls

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
    let axy_t : term -> either<string, term> -> decl = fun tm v -> 
        let vars = [(asym, Type_sort); (xsym, Term_sort); (ysym, Term_sort)] in 
        eq_assumption vars (mk_tm v vars) tm in 
    let xy_t : term -> either<string,term> -> decl = fun tm v -> 
        let vars = [(xsym, Term_sort); (ysym, Term_sort)] in 
        eq_assumption vars (mk_tm v vars) tm in 
    let x_t : term -> either<string, term> -> decl = fun tm v -> 
        let vars = [(xsym, Term_sort)] in
        eq_assumption vars (mk_tm v vars) tm in 
    let prims = [
        (Const.op_Eq,          (axy_t (boxBool <| mkEq(x,y))));
        (Const.op_notEq,       (axy_t (boxBool <| mkNot(mkEq(x,y)))));
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
    let mk_unit : term -> decls_t = fun tt -> 
        let typing_pred = Term.mk_HasType x tt in
        [Term.Assume(Term.mk_HasType Term.mk_Term_unit tt,    Some "unit typing");
         Term.Assume(mkForall([typing_pred], [xx], mkImp(typing_pred, mkEq(x, Term.mk_Term_unit))),  Some "unit inversion")] in
    let mk_bool : term -> decls_t = fun tt -> 
        let typing_pred = Term.mk_HasType x tt in
        let bb = ("b", Bool_sort) in
        let b = mkBoundV bb in
        [Term.Assume(mkForall([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxBool" x)),    Some "bool inversion");
         Term.Assume(mkForall([Term.boxBool b], [bb], Term.mk_HasType (Term.boxBool b) tt),    Some "bool typing")] in
    let mk_int : term -> decls_t  = fun tt -> 
        let typing_pred = Term.mk_HasType x tt in
        let aa = ("a", Int_sort) in
        let a = mkBoundV aa in
        let bb = ("b", Int_sort) in
        let b = mkBoundV bb in
        let precedes = Term.mk_Valid <| mkApp("Prims.Precedes", [tt;tt;Term.boxInt a; Term.boxInt b]) in
        [Term.Assume(mkForall([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxInt" x)),    Some "int inversion");
         Term.Assume(mkForall([Term.boxInt b], [bb], Term.mk_HasType (Term.boxInt b) tt),    Some "int typing");
         Term.Assume(mkForall([precedes], [aa;bb], mkIff(precedes, mk_and_l [Term.mkGTE(a, Term.mkInteger 0);
                                                                             Term.mkGTE(b, Term.mkInteger 0);
                                                                             Term.mkLT(a, b)])), Some "Well-founded ordering on nats")] in
    let mk_str : term -> decls_t  = fun tt -> 
        let typing_pred = Term.mk_HasType x tt in
        let bb = ("b", String_sort) in
        let b = mkBoundV bb in
        [Term.Assume(mkForall([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxString" x)),    Some "string inversion");
         Term.Assume(mkForall([Term.boxString b], [bb], Term.mk_HasType (Term.boxString b) tt),    Some "string typing")] in
    let prims = [(Const.unit_lid,   mk_unit);
                 (Const.bool_lid,   mk_bool);
                 (Const.int_lid,    mk_int);
                 (Const.string_lid, mk_str);
                ] in
    (fun (t:lident) (tt:term) -> 
        match Util.find_opt (fun (l, _) -> lid_equals l t) prims with 
            | None -> []
            | Some(_, f) -> f tt)

let rec encode_sigelt (env:env_t) (se:sigelt) : (decls_t * env_t) = 
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
    
and encode_sigelt' (env:env_t) (se:sigelt) : (decls_t * env_t) = 
    match se with
     | Sig_typ_abbrev(_, _, _, _, [Effect], _) -> [], env

     | Sig_typ_abbrev(lid, tps, _, t, tags, _) -> 
        let tname, ttok, env = gen_free_tvar env lid in 
        let tps, t = match t.n with 
            | Typ_lam(tps', body) -> tps@tps', body
            | _ -> tps, t in 
        let vars, guards, env', binder_decls, _ = encode_binders tps env in
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
        let def, (body, ex_vars, decls1) = 
            if tags |> Util.for_some (function Logic -> true | _ -> false) (* REVIEW: This code is dead, given the previous pattern *)
            then mk_Valid app, (let f, decls = encode_formula t env' in f, [], decls)
            else app, encode_typ_term t env' in 
        let g = binder_decls@decls@decls1@[Term.Assume(mkForall([def], vars, mkImp(mk_and_l guards, close_ex ex_vars <| mkEq(def, body))), None)] in 
        g, env

     | Sig_val_decl(lid, t, quals, _) -> 
        encode_free_var env lid t quals

     | Sig_assume(l, f, _, _) -> 
        let f, decls = encode_formula f env in
        let g = [Term.Assume(f, Some (format1 "Assumption: %s" (Print.sli l)))] in 
        decls@g, env

     | Sig_tycon(t, tps, k, _, datas, quals, _) when (lid_equals t Const.precedes_lid) -> 
        let tname, ttok, env = gen_free_tvar env t in
        [], env
               
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
        let vars, guards, env', binder_decls, _ = encode_binders formals env in
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
        let kindingAx = 
            let k, decls = encode_knd res env' tapp in
            decls@[Term.Assume(mkForall([tapp], vars, mkImp(guard, k)), Some "kinding")] in
        let g = decls
                @binder_decls
                @kindingAx
                @(primitive_type_axioms t tapp)
                @(inversion_axioms tapp vars)
                @(projection_axioms tapp vars) in
        g, env

    | Sig_datacon(d, _, _, _, _) when (lid_equals d Const.lexpair_lid) -> [], env 

    | Sig_datacon(d, t, _, quals, _) -> 
        let ddconstrsym, ddtok, env = gen_free_var env d in //Print.sli d in
        let formals, t_res = match Util.function_formals t with 
            | Some (f, c) -> f, Util.comp_result c
            | None -> [], t in
        let vars, guards, env', binder_decls, names = encode_binders formals env in 
        let projectors = names |> List.map (function 
            | Inl a -> mk_typ_projector_name d a, Type_sort
            | Inr x -> mk_term_projector_name d x, Term_sort) in
        let datacons = (ddconstrsym, projectors, Term_sort, varops.next_id()) |> Term.constructor_to_decl in
        let app = mk_ApplyE ddtok vars in
        let guard = Term.mk_and_l guards in 
        let xvars = List.map mkBoundV vars in
        let dapp =  mkApp(ddconstrsym, xvars) in
        let ty_pred, decls2 = encode_typ_pred t_res env' dapp in
        let index_injectivity = match (Util.compress_typ t_res).n with 
            | Typ_app _ -> 
                let free_indices = Util.freevars_typ t_res in
                let x = varops.fresh "x", Term_sort in 
                let xterm = mkBoundV x in
                let t, vars1, decls1 = encode_typ_term t_res env' in 
                begin match vars1 with 
                    | _::_ -> decls1 (* warn? no index injectivity in this case *)
                    | _ -> 
                    let x_hastype_t = mk_HasType xterm t in
                    let x_is_d = mk_data_tester env d xterm in 
                    let env'' = List.fold_left2 (fun env formal proj -> match formal with 
                        | Inl a, _ -> push_typ_var env a.v <| Term.mkApp(fst proj, [xterm])
                        | Inr x, _ -> push_term_var env x.v <| Term.mkApp(fst proj, [xterm])) env' formals projectors in
                    let t_res_subst, ex_vars, decls2 = encode_typ_term t_res env'' in
                    let tvars = Util.set_elements free_indices.ftvs |> List.map (fun a -> 
                        let tm = lookup_typ_var env' a in 
                        boundV_sym tm, Type_sort) in
                    let vvars = Util.set_elements free_indices.fxvs |> List.map (fun x -> 
                        let tm = lookup_term_var env' x in 
                        boundV_sym tm, Term_sort) in
                    decls1@decls2@[Term.Assume(Term.mkForall([x_hastype_t], x::tvars@vvars, Term.mkImp(mkAnd(x_hastype_t, x_is_d), close_ex ex_vars (mkEq(t, t_res_subst)))), Some "index injectivity")]
                end
            | _ -> [] in
        let precedence = 
            if lid_equals d Const.lexpair_lid
            then let vars', guards', env', decls1 ,_ = encode_binders formals env' in
                 let yvars = List.map mkBoundV vars' in
                 let dapp' = mkApp(ddconstrsym, yvars) in
                 let [_; _; x1; x2] = xvars in
                 let [_; _; y1; y2] = yvars in  
                 let prec = mkForall([Term.mk_Precedes dapp dapp'], 
                                     vars@vars', 
                                     mkImp(mk_and_l (guards@guards'), 
                                           mkIff(Term.mk_Precedes dapp dapp', 
                                                 mkOr(Term.mk_Precedes x1 y1, 
                                                      mkAnd(Term.mkEq(x1, y1), Term.mk_Precedes x2 y2))))) in
                decls1@[Term.Assume(prec, Some "Ordering on lex pairs")]
            else if lid_equals d Const.lextop_lid
            then let x = varops.fresh "x", Term_sort in
                 let xtm = mkBoundV x in
                 [Term.Assume(mkForall([Term.mk_Precedes xtm dapp], [x], mkImp(mk_tester "LexPair" xtm, Term.mk_Precedes xtm dapp)), Some "lextop is top")]
            else (* subterm ordering *)
                let prec = vars |> List.collect (fun v -> match snd v with 
                    | Type_sort -> []
                    | Term_sort -> [Term.mk_Precedes (mkBoundV v) dapp]) in
                [Term.Assume(mkForall([ty_pred], vars, mkImp(guard, mk_and_l prec)), Some "subterm ordering")] in

        let g = binder_decls
                @decls2
                @[Term.DeclFun(Term.freeV_sym ddtok, [], Term_sort, Some (format1 "data constructor proxy: %s" (Print.sli d)));
                  Term.Assume(mkForall([app], vars, 
                                       mkEq(app, dapp)), Some "equality for proxy");
                  Term.Assume(mkForall([ty_pred], vars, mkIff(guard, ty_pred)), Some "data constructor typing")]
                 @precedence
                 @index_injectivity in
        datacons@g, env

    | Sig_bundle(ses, _, _) -> 
      let g, env = encode_signature env ses in
      let g', inversions = g |> List.partition (function
        | Term.Assume(_, Some "inversion axiom") -> false
        | _ -> true) in
      g'@inversions, env

    | Sig_let((is_rec, [(Inr flid, t1, e)]), _, _) when not is_rec -> 
        if not (Util.is_pure_function t1) then [], env  else
        let (f, ftok), decls, env = declare_top_level_let env flid t1 in
        let e = Util.compress_exp e in
        let binders, body = match e.n with
            | Exp_abs(binders, body) -> binders, body 
            | _ -> [], e in
        let vars, guards, env', binder_decls, _ = encode_binders binders env in
        let app = if !Options.z3_optimize_full_applications 
                  then Term.mkApp(f, List.map mkBoundV vars)
                  else mk_ApplyE ftok vars in
        let body, ex_vars, decls2 = encode_exp body env' in
        let eqn = Term.Assume(mkForall([app], vars, mkImp(mk_and_l guards, close_ex ex_vars <| mkEq(app, body))), Some (Util.format1 "Equation for %s" flid.str)) in
        decls@binder_decls@decls2@[eqn], env
     

    | Sig_let((is_rec, [(Inr flid, t, e)]), _, _) ->
      (* only encoding recursive pure functions defined immediately by cases on some subset of the arguments 
         The case where the subset of arguments is just xi looks like this:
        
                 let rec f x1 .. xi .. xn = match xi with
                   | P1 y1..ym1 -> e1 
                   | P2 y1..ym2 -> e2
                   | ... 
                  ~>
                  forall x1 .. (y1 ... ymj) .. xn. not(OR is-P{1..{j-1}) xi) ==> f x1...(Pj y1..ymj)..xn = [[ej]]

        The extension to a tuple of the arguments (in the same order as the parameters) in place of xi is tedious but straightforward.
      *)

      if not (Util.is_pure_function t) then [], env else
      let _ = if Env.debug env.tcenv Options.Low then Util.fprint1 "Encoding let rec %s\n" (Print.sli flid) in
      let (f, ftok), decls, env = declare_top_level_let env flid t in
      
      let warn why = 
        if env.warn
        then (let msg = Util.format2 "Unable to encode '%s' to SMT (because %s); try writing it by matching directly on some subset of the arguments " (Print.sli flid) why in
              Tc.Errors.warn (range_of_lid flid) msg);
        decls, env in
      let giveup : string -> 'a = fun why -> raise (Let_rec_unencodeable why) in

      (* writing these three as let rec just so that the top-level comes first; would prefer to use a "where" instead *)
      let rec doit () =     
         try
          match (Util.compress_exp e).n with 
            | Exp_abs(binders, body) -> 
                begin match (Util.unmeta_exp body).n with 
                    | Exp_match(scrutinee, cases) -> 
                          let cases = flatten_disjuncts cases in
                          let _, eqns = cases |> Util.fold_map (encode_equation binders scrutinee) [] in 
                          let decls = decls
                                      @[Caption (Util.format1 "<Equations for %s>" flid.str)]
                                      @(List.flatten eqns)
                                      @[Caption "</Equations>"] in
                          decls, env
                    | _ -> warn "the body of the function doesn't begin with a match"
                end

            | _ -> warn "it doesn't appear to be a function"
         with 
            | Let_rec_unencodeable why -> warn why

      and flatten_disjuncts cases = 
        cases |> List.collect (fun (p, w, br) -> 
            match w with 
                | Some _ -> giveup "when-clauses are not (yet) supported in the SMT encoding"
                | _ -> match p.v with 
                        | Pat_disj ps -> ps |> List.map (fun p -> (p, w, br))
                        | _ -> [(p, w, br)]) 

      and encode_equation binders scrutinee (prior_patterns:list<pattern>) case = 
            let (pat, _, br) = case in 
            if Tc.Env.debug env.tcenv Options.Low then Util.fprint1 "Encoding case at %s\n" (Range.string_of_range br.pos);
            let scrutinee = Util.unmeta_exp scrutinee in
            let sub_patterns, remake = match scrutinee.n, pat.v with
                | Exp_bvar x, _ -> [varg <| scrutinee, pat], (function [p] -> p | _ -> failwith "too many sub-terms")
           
                | Exp_app({n=Exp_fvar(d, _)}, args), Pat_cons(d', pats) when (Util.fvar_eq d d') ->
                  List.zip args pats, (fun pats -> Term.mkApp(lookup_free_var_name env d', pats))

                | _ -> giveup (Util.format2 "Not a tuple or simple pattern: scrutinee is %s, pat is %s" (Print.exp_to_string <|scrutinee) (Print.pat_to_string pat)) in
            
            let binders_until bs ax = match ax with 
                | Inl a -> Util.prefix_until (function Inl a', _ -> Util.bvar_eq a a' | _ -> false) bs
                | Inr a -> Util.prefix_until (function Inr a', _ -> Util.bvar_eq a a' | _ -> false) bs in
        
            let encode_sub_pattern env binders arg pat : (Syntax.binders * list<var> * list<term> * list<term> * term * env_t * decls_t) = 
                match fst arg with
                | Inr ({n=Exp_bvar a}) -> 
                    begin match binders_until binders (Inr a) with 
                        | Some(prefix, (Inr xi, _), suffix) -> 
                          let prefix, prefix_guards, env, decls1, _ = encode_binders prefix env in 
                          let pat_env, pattern = encode_one_pat env pat in
                          let pat_tm, pat_tm_vars, decls2 = pattern.pat_term () in
                          let ex_vars, ex_guard = List.unzip pat_tm_vars in
                          let pat_guard, decls3 = encode_typ_pred xi.sort env pat_tm in
                          let pat_env = push_term_var pat_env xi.v pat_tm in
                          let pat_vars = pattern.pat_vars |> List.map snd in
                          suffix,
                          prefix@pat_vars@ex_vars, 
                          prefix_guards@[pat_guard]@ex_guard, 
                          List.map mkBoundV prefix@[pat_tm],
                          pat_tm,
                          pat_env, 
                          decls1@decls2@decls3

                        | _ -> giveup (Util.format1 "%s is not a unique parameter" (Print.strBvd a.v))
                    end
                
               | Inl ({n=Typ_btvar a}) -> 
                    begin match binders_until binders (Inl a) with 
                        | Some(prefix, (Inl ai, _), suffix) -> 
                          let prefix, prefix_guards, env, decls1, _ = encode_binders prefix env in 
                          let pat_env, pattern = encode_one_pat env pat in
                          let pat_tm, pat_tm_vars, decls2 = pattern.pat_term () in
                          let ex_vars, ex_guard = List.unzip pat_tm_vars in
                          let pat_guard, decls3 = encode_knd ai.sort env pat_tm in
                          let pat_env = push_typ_var pat_env ai.v pat_tm in
                          let pat_vars = pattern.pat_vars |> List.map snd in
                          suffix,
                          prefix@pat_vars@ex_vars, 
                          prefix_guards@[pat_guard]@ex_guard, 
                          List.map mkBoundV prefix@[pat_tm],
                          pat_tm,
                          pat_env,
                          decls1@decls2@decls3
        

                        | _ -> giveup (Util.format1 "%s is not a unique parameter" (Print.strBvd a.v))
                    end
            
               | Inr e -> giveup (Util.format1 "scrutinee '%s' is not a parameter" (Print.exp_to_string e))
                 
               | Inl t -> 
                    (* One of the scrutinees is a type, generally an implicit type argument, in which case, its corresponding pattern should be exactly the same type. 
                       Seems hard to handle this case in full generality. 
                       Instead, we take the prefix of type binders in scope, and translate the rest of the patterns.
                     *)
                     begin match binders |> Util.prefix_until (function (Inr _, _) -> true | _ -> false) with 
                        | None -> (* no value binders! *)
                          giveup (Util.format1 "matching on a type %s" (Print.typ_to_string t))

                        | Some (prefix, first_value_binder, rest) -> 
                            let suffix = first_value_binder::rest in 
                            if suffix |> Util.for_some (function (Inl _, _) -> true | _ -> false)
                            then giveup "type-variable binders are non prenex"
                            else let prefix, prefix_guards, env, decls1, _ = encode_binders prefix env in 
                                 let pat_env, pattern = encode_one_pat env pat in
                                 match pattern.pat_vars with 
                                    | _::_ -> giveup (Util.format1 "matching on a type %s" (Print.typ_to_string t))
                                    | _ -> 
                                     let pat_tm, pat_tm_vars, decls2 = pattern.pat_term () in
                                     let ex_vars, ex_guard = List.unzip pat_tm_vars in
                                     suffix,
                                     prefix@ex_vars, 
                                     prefix_guards@ex_guard, 
                                     List.map mkBoundV prefix,
                                     pat_tm,
                                     pat_env,
                                     decls1@decls2
                     end in

          let suffix, vars, vars_guard, args, pat_sub_terms, env, decls1 = sub_patterns |> List.fold_left (fun (binders, vars, vars_guard, args, pat_sub_terms, env, decls) (arg, pat) ->
                let suffix, vars', vars_guard', args', pat_tm, env, decls' = encode_sub_pattern env binders arg pat in
                suffix, vars@vars', vars_guard@vars_guard', args@args', pat_sub_terms@[pat_tm], env, decls@decls')
                     (binders, [], [], [], [], env, []) in

          let suffix, suffix_guards, env, decls2, _ = encode_binders suffix env in 
          let vars = vars@suffix in
          let vars_guard = vars_guard@suffix_guards |> Term.mk_and_l in
          let args = args@List.map mkBoundV suffix in
          let lhs = Term.mkApp(f, args) in //NB: leaving on the case with not !Options.z3_optimize_full_applications
          let this_pattern = encode_one_pat env pat in
          let this_pattern_tm = remake pat_sub_terms in
          let not_priors = prior_patterns |> List.map (fun p -> p.guard this_pattern_tm) |> Term.mk_or_l |> Term.mkNot in
          let rhs, rhs_vars, decls3 = encode_exp br env in
          let eqn = Term.Assume(mkForall([lhs], vars, close_ex rhs_vars <| mkImp(Term.mkAnd(vars_guard, not_priors), mkEq(lhs, rhs))), Some (Util.format1 "Case %s" (Print.pat_to_string pat))) in
          prior_patterns@[snd this_pattern], decls1@decls2@decls3@[eqn] in

        doit()
          
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
        
        let vars, guards, env', decls1, _ = encode_binders formals env in
        let guard = mk_and_l guards in
        let vtok_app = mk_ApplyE vtok vars in
        
        let vapp, prim, decls2, env =    
            if !Options.z3_optimize_full_applications
            then (* Generate a token and a function symbol; equate the two, and use the function symbol for full applications *)
                let vapp = Term.mkApp(vname, List.map Term.mkBoundV vars) in
                let vname_decl = Term.DeclFun(vname, formals |> List.map (function Inl _, _ -> Type_sort | _ -> Term_sort), Term_sort, None) in
                let tok_decl, env = match formals with 
                    | [] -> 
                        let t, decls2 = encode_typ_pred t env (mkFreeV(vname, Term_sort)) in
                        let tok_typing = Term.Assume(t, Some "function token typing") in 
                        decls2@[tok_typing], push_free_var env lid vname (mkFreeV(vname, Term_sort))
                    | _ -> 
                        let vtok_decl = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, None) in
                        let t, decls2 = encode_typ_pred t env vtok in
                        let tok_typing = Term.Assume(t, Some "function token typing") in 
                        let name_tok_corr = Term.Assume(mkForall([vtok_app], vars, mkEq(vtok_app, vapp)), None) in
                        decls2@[vtok_decl;name_tok_corr;tok_typing], env in
                vapp, Inl vname, vname_decl::tok_decl, env
            else     
                let t, decls2 = encode_typ_pred t env vtok in
                let tok_typing = Term.Assume(t, Some "function token typing") in 
                let tok_decl = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, None) in
                vtok_app, Inr vtok, decls2@[tok_decl;tok_typing], env in

        let ty_pred, decls3 = encode_typ_pred res env' vapp in
        let typingAx = Term.Assume(mkForall([vapp], vars, mkImp(guard, ty_pred)), None) in
        let g = decls1@decls2@decls3@typingAx::mk_disc_proj_axioms vapp vars@mk_prim lid prim in
        g, env
       

and encode_signature env ses = 
    ses |> List.fold_left (fun (g, env) se ->            
      let g', env = encode_sigelt env se in 
      g@g', env) ([], env) 

let encode_env_bindings (env:env_t) (bindings:list<Tc.Env.binding>) : (decls_t * env_t) = 
    let encode_binding b (decls, env) = match b with
        | Env.Binding_var(x, t) -> 
            let xxsym, xx, env' = gen_free_term_var env x in 
            let t, decls' = encode_typ_pred (norm_t env t) env xx in
            let g = [Term.DeclFun(xxsym, [], Term_sort, Some (Print.strBvd x))]
                    @decls'
                    @[Term.Assume(t, None)] in
            decls@g, env'
        | Env.Binding_typ(a, k) -> 
            let aasym, aa, env' = gen_free_typ_var env a in 
            let k, decls' = encode_knd k env aa in
            let g = [Term.DeclFun(aasym, [], Type_sort, Some (Print.strBvd a))]
                    @decls'
                    @[Term.Assume(k, None)] in
            decls@g, env'
        | Env.Binding_lid(x, t) -> 
            let g, env' = encode_free_var env x t [] in
            decls@g, env'
        | Env.Binding_sig se -> 
            let g, env' = encode_sigelt env se in 
            decls@g, env' in
    List.fold_right encode_binding bindings ([], env)

let encode_labels labs = 
    let prefix = labs |> List.map (fun (l, _) -> Term.DeclFun(fst l, [], Bool_sort, None)) in
    let suffix = labs |> List.collect (fun (l, _) -> [Echo <| fst l; Eval (mkFreeV l)]) in
    prefix, suffix

(* caching encodings of the environment and the top-level API to the encoding *)
open Microsoft.FStar.Tc.Env
let last_env : ref<list<env_t>> = Util.mk_ref []
let init_env tcenv = last_env := [{bindings=[]; tcenv=tcenv; warn=true; polarity=true; refinements=Util.smap_create 20}]
let get_env tcenv = match !last_env with 
    | [] -> failwith "No env; call init first!"
    | e::_ -> {e with tcenv=tcenv}
let set_env env = match !last_env with 
    | [] -> failwith "Empty env stack"
    | _::tl -> last_env := env::tl
let push_env () = match !last_env with 
    | [] -> failwith "Empty env stack"
    | hd::tl -> 
      let refs = Util.smap_copy hd.refinements  in
      let top = {hd with refinements=refs} in
      last_env := top::hd::tl 

let pop_env () = match !last_env with 
    | [] -> failwith "Popping an empty stack"
    | _::tl -> last_env := tl

(* TOP-LEVEL API *)

let init tcenv =
    init_env tcenv;
    Z3.giveZ3 "init" (fun () -> [DefPrelude])
let push msg = 
    Z3.push msg
            (fun () ->  push_env ();
                        varops.push();
                        [])
let pop msg   = 
    Z3.pop msg (fun () -> ignore <| pop_env(); varops.pop(); [])
let encode_sig tcenv se =
   let doit () = 
       let env = get_env tcenv in
       let decls, env = encode_sigelt env se in
       set_env env; decls in
   Z3.giveZ3 ("encoding sigelt " ^ (Print.sigelt_to_string_short se)) doit
let encode_modul tcenv modul = 
   let doit () =
       if Tc.Env.debug tcenv Options.Low then Util.fprint1 "Actually encoding module externals %s\n" (modul.name.str);
       let env = get_env tcenv in
       let decls, env = encode_signature ({env with warn=false}) modul.exports in
       let msg = "Externals for module " ^ modul.name.str in
       set_env ({env with warn=true}); 
       let res = Caption msg::decls@[Caption ("End " ^ msg)] in
       if Tc.Env.debug tcenv Options.Low then Util.fprint1 "Done encoding module externals %s\n" (modul.name.str);
       res in
   Z3.giveZ3 ("encoding module externals " ^ modul.name.str)  doit
let solve tcenv q =
    let query_and_labels () = 
        push_env (); varops.push();
        let env = get_env tcenv in
        let env_decls, env = encode_env_bindings env (List.filter (function Binding_sig _ -> false | _ -> true) tcenv.gamma) in
        if debug tcenv Options.Low then Util.fprint1 "Encoding query formula: %s\n" (Print.formula_to_string q);
        let phi, labels, qdecls = encode_formula_with_labels q (negate env) in
        let label_prefix, label_suffix = encode_labels labels in
        let r = Caption (Range.string_of_range (Tc.Env.get_range tcenv)) in
        let decls = [r]
                    @env_decls
                    @label_prefix
                    @qdecls
                    @[Term.Caption "<Query>"; Term.Assume(mkNot phi, Some "query"); Term.Caption "</Query>"; Term.CheckSat]
                    @label_suffix
                    @[Term.Echo "Done!"] in
        decls, labels in
    let pop () = ignore <| pop_env(); varops.pop() in
    Z3.queryAndPop query_and_labels pop

let is_trivial (tcenv:Tc.Env.env) (q:typ) : bool = 
   let env = get_env tcenv in
   push "query";
   let f, _, _ = encode_formula_with_labels q env in
   pop "query";
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
    solve=(fun _ _ -> true, []);
    is_trivial=(fun _ _ -> false)
}


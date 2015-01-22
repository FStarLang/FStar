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
    let fresh pfx = format2 "%s_%s" pfx (string_of_int <| next_id()) in
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
              refinements:Util.smap<(term * list<decl>)>;
              nolabels:bool
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
let lookup_free_var env a =
    let name, sym = lookup_lid env a.v in
    match sym.tm with 
        | App(_, [fuel]) -> 
            if (Util.starts_with (Term.boundV_sym fuel) "fuel") 
            then Term.mk_ApplyEE(Term.mkFreeV (name, Term_sort)) fuel
            else sym
        | _ -> sym
let lookup_free_var_name env a = lookup_lid env a.v |> fst
let lookup_free_var_sym env a = 
    let name, sym = lookup_lid env a.v in
    match sym.tm with 
        | App(g, [fuel]) -> g, [fuel]
        | _ -> name, []

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
let head_normal env t =   
   let t = Util.unmeta_typ t in
   match t.n with 
    | Typ_fun _
    | Typ_refine _ 
    | Typ_btvar _
    | Typ_uvar _
    | Typ_lam _ -> true
    | Typ_const v 
    | Typ_app({n=Typ_const v}, _) -> Tc.Env.lookup_typ_abbrev env.tcenv v.v |> Option.isNone
    | _ -> false
 
let whnf env t =
    if head_normal env t then t
    else Tc.Normalize.norm_typ [Tc.Normalize.Beta;Tc.Normalize.WHNF;Tc.Normalize.DeltaHard] env.tcenv t
let norm_t env t = Tc.Normalize.norm_typ [Tc.Normalize.Beta] env.tcenv t
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

let is_lemma t =  match (Util.compress_typ t).n with 
    | Typ_fun(_, c) -> (match c.n with 
        | Comp ct -> lid_equals ct.effect_name Const.lemma_lid
        | _ -> false)
    | _ -> false

let is_smt_lemma env t = match (Util.compress_typ t).n with 
    | Typ_fun(_, c) -> (match c.n with 
        | Comp ct when (lid_equals ct.effect_name Const.lemma_lid) ->
            begin match ct.effect_args with
                | _req::_ens::(Inr pats, _)::_ ->
                  if Tc.Env.debug env.tcenv Options.Low
                  then Util.fprint1 "Inspecting lemma patterns: %s\n" (Print.exp_to_string pats);
                  begin match (Util.unmeta_exp pats).n with 
                    | Exp_app({n=Exp_fvar(fv, _)}, _) -> lid_equals fv.v Const.cons_lid
                    | _ -> false
                  end
                | _ -> false
            end
        | _ -> false)
    | _ -> false

let encode_const = function 
    | Const_unit -> mk_Term_unit
    | Const_bool true -> boxBool mkTrue
    | Const_bool false -> boxBool mkFalse
    | Const_char c -> boxInt (mkInteger (Util.int_of_char c))
    | Const_uint8 i -> boxInt (mkInteger (Util.int_of_uint8 i))
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
            let vars, guards, env', decls, _ = encode_binders false bs env in 
            let prekind = mk_tester "Kind_arrow" (mk_PreKind t) in
            let app = mk_ApplyT t vars in
            let k, decls' = encode_knd k env' app in
            Term.mkAnd(prekind,
                       Term.mkForall([app], vars, mkImp(mk_and_l guards, k))), 
            decls@decls'

        | _ -> failwith (Util.format1 "Unknown kind: %s" (Print.kind_to_string k))

and encode_binders (destruct:bool) (bs:Syntax.binders) (env:env_t) : (list<var>       (* translated bound variables *)
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
                let guard_x_t, decls' = encode_typ_pred' destruct (norm_t env t) env xx in
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

and encode_typ_pred_no_destruct t env e = encode_typ_pred' false t env e

and encode_typ_pred' (destruct:bool) (t:typ) (env:env_t) (e:term) : term * decls_t = 
    let t = Util.compress_typ t in 
    match (Util.unmeta_typ t).n with 
        | Typ_refine(x, f) -> 
          let base_pred, decls = encode_typ_pred' destruct x.sort env e in 
          let env' = push_term_var env x.v e in
          let refinement, decls' = encode_formula f env' in
          Term.mkAnd(base_pred, refinement), decls@decls' 

        | _ -> 
            let t, ex, decls = encode_typ_term t env in 
            close_ex ex (mk_HasType destruct e t), decls

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
        let doit binders (res:comp) =
            let tsym, ttm, fsym, f = fresh_vars "funtype" "f" in
            let pretype = mk_tester "Typ_fun" (mk_PreType f) in
            let t_has_kind = mk_HasKind ttm Term.mk_Kind_type in
            let f_hastype_t = mk_HasType false f ttm in
            let guard, decls = 
                if not <| Absyn.Util.is_pure_comp res
                then pretype, [] 
                else let vars, guards, env', decls, _ = encode_binders false binders env in 
                     let app = mk_ApplyE f vars in
                     if Util.is_total_comp res
                     then let res_pred, decls' = encode_typ_pred' false (Util.comp_result res) env' app in
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
        let base_pred, decls = encode_typ_pred' false x.sort env xtm in 
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
                     let x_has_t = mk_HasType false xtm ttm in
                     let t_has_kind = mk_HasKind ttm Term.mk_Kind_type in
                     let assumption = Term.mkAnd(t_has_kind, Term.mkForall([x_has_t], [xsym], mkIff(x_has_t, encoding))) in
                     let new_decls = [Term.DeclFun(fst tsym, [], Type_sort, None);
                                      Term.Assume(assumption, Some (Print.typ_to_string t))] in
                     Util.smap_add env.refinements encoding.as_str (ttm, new_decls);
                     ttm, [], decls@decls'@new_decls
                else let tsym = varops.fresh "refinet", Type_sort in
                     let ttm = mkBoundV tsym in
                     let x_has_t = mk_HasType false xtm ttm in
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
              if is_full_app () 
              then let head = lookup_free_tvar_name env fv in
                   let t = Term.mkApp(head, List.map (function Inl t | Inr t -> t) args) in
                   t, vars, decls
              else let head = lookup_free_tvar env fv in
                   let t = mk_ApplyT_args head args in
                   t, vars, decls

            | Typ_uvar(uv, _) -> 
               let ttm = Term.mk_Typ_uvar (Unionfind.uvar_id uv) in
               let t_has_k, decls = encode_knd t.tk env ttm in //TODO: skip encoding this if it has already been encoded before
               let d = Term.Assume(t_has_k, None) in
               ttm, [], d::decls  

            | _ -> 
              let t = norm_t env t in
              (* CH: WARNING: if norm_t returns the same type it got as input
                     this code enters infinite loop (as it happened with uvars);
                     might want to do something about this!? *)
              encode_typ_term t env
        end

      | Typ_lam(bs, t) ->
        let vars, guards, env, decls, _ = encode_binders false bs env in
        let name = varops.fresh (Print.tag_of_typ t0), Type_sort in 
        let tag = mkBoundV name in 
        let app = mk_ApplyT tag vars in
        let body, vars_body, decls' = encode_typ_term t env in
        let eq = close_ex vars_body (mkEq(app, body)) in
        let guard = mkForall([app], vars, mkImp(mk_and_l guards, eq)) in
        tag, [(name, guard)], decls@decls'

      | Typ_ascribed(t, _) -> 
        encode_typ_term t env

      | Typ_meta _
      | Typ_delayed  _ 
      | Typ_unknown    -> failwith (format4 "(%s) Impossible: %s\n%s\n%s\n" (Range.string_of_range <| t.pos) (Print.tag_of_typ t0) (Print.typ_to_string t0) (Print.typ_to_string t))                 

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
        let esym, lam = fresh_bvar "lambda" Term_sort in
        if not <| Util.is_pure_function e.tk 
        then lam, [(esym, Term_sort), Term.mkTrue], []
        else let t = whnf env e.tk |> Util.compress_typ in
             begin match t.n with 
                | Typ_fun(bs', c) -> 
                    let nformals = List.length bs' in
                    if nformals < List.length bs && Util.is_total_comp c (* explicit currying *)
                    then let bs0, rest = Util.first_N nformals bs in 
                         let res_t = match Util.mk_subst_binder bs0 bs' with 
                            | Some s -> Util.subst_typ s (Util.comp_result c) 
                            | _ -> failwith "Impossible" in
                         let e = mk_Exp_abs(bs0, mk_Exp_abs(rest, body) res_t body.pos) t e0.pos in
                         //Util.fprint1 "Explicitly currying %s\n" (Print.exp_to_string e);
                         encode_exp e env
                    else let vars, _, envbody, decls, _ = encode_binders false bs env in 
                         let app = mk_ApplyE lam vars in
                         let body, body_vars, decls' = encode_exp body envbody in
                         let eq = close_ex body_vars (mkEq(app, body)) in
                         let t_fun = e.tk in
                         if Tc.Env.debug env.tcenv Options.Low then Util.fprint1 "Encoding type e.tk=%s\n" (Print.typ_to_string t_fun);
                         let lam_typed, decls'' = encode_typ_pred' false t_fun env lam in
                         let tsym, t = fresh_bvar "t" Type_sort in 
                         let app_has_t = Term.mk_HasType false app t in
                         let app_is_typed = Term.mkExists([app_has_t], [(tsym, Type_sort)], app_has_t) in
                         let app_eq = Term.mkForall([app], vars, mkImp(app_is_typed, eq)) in
                         let clos = 
                            let fvars = Term.free_variables app_eq |> List.filter (fun x -> fst x <> esym) in
                            Term.mk_Closure (varops.next_id()) fvars in
                         lam, [(esym, Term_sort), mk_and_l [mkEq(lam, clos); app_eq; lam_typed]], decls@decls'@decls''
              | _ -> failwith "Impossible"
            end

      | Exp_app({n=Exp_fvar(l, _)}, [(Inl _, _); (Inr v1, _); (Inr v2, _)]) when (lid_equals l.v Const.lexcons_lid) -> 
         let v1, vars1, decls1 = encode_exp v1 env in 
         let v2, vars2, decls2 = encode_exp v2 env in
         Term.mk_LexCons v1 v2, vars1@vars2, decls1@decls2

      | Exp_app(head, args_e) -> 
        let args, vars, decls = encode_args args_e env in
    
        let encode_partial_app ht_opt = 
            let head, vars', decls' = encode_exp head env in
            let app_tm = mk_ApplyE_args head args in
            begin match ht_opt with
                | None -> app_tm, vars'@vars, decls@decls'
                | Some (formals, c) ->
                  let formals, rest = Util.first_N (List.length args_e) formals in
                  let subst = Util.formals_for_actuals formals args_e in
                  let ty = mk_Typ_fun(rest, c) ktype e0.pos |> Util.subst_typ subst in
                  let esym, partial_app = fresh_bvar "partial_app" Term_sort in
                  let has_type, decls'' = encode_typ_pred' true ty env partial_app in
                  partial_app, (vars'@vars@[((esym, Term_sort), Term.mkAnd(Term.mkEq(partial_app, app_tm), has_type))]), decls@decls'@decls''
            end in

        let encode_full_app fv = 
            let fname, fuel_args = lookup_free_var_sym env fv in
            let tm = Term.mkApp(fname, fuel_args@List.map (function Inl t | Inr t -> t) args) in
            tm, vars, decls in
        
        let head = Util.compress_exp head in
        let head_type = whnf env (Util.unrefine head.tk) in
        begin match Util.function_formals head_type with
                    | None -> failwith (Util.format3 "(%s) term is %s; head type is %s\n" 
                                        (Range.string_of_range e0.pos) (Print.exp_to_string e0) (Print.typ_to_string head.tk))
                    | Some (formals, c) -> 
                        begin match head.n with
                            | Exp_fvar (fv, _) when (List.length formals = List.length args) -> encode_full_app fv
                            | _ -> 
                                if List.length formals > List.length args
                                then encode_partial_app (Some (formals, c))
                                else encode_partial_app None

                        end
       end
        
      | Exp_let((false, [(Inr _, _, _)]), _) -> failwith "Impossible: already handled by encoding of Sig_let" 

      | Exp_let((false, [(Inl x, t1, e1)]), e2) ->
        let xvar, x, env' = gen_term_var env x in 
        let guard, decls = encode_typ_pred' false t1 env x in
        let ee1, vars1, decls1 = encode_exp e1 env in
        let ee2, vars2, decls2 = encode_exp e2 env' in
        ee2, vars1@[(xvar, Term_sort), mkAnd(guard, mkEq(x, ee1))]@vars2, decls@decls1@decls2 
  
      | Exp_let _ -> 
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
            | Pat_var (x, _)
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
  
and encode_function_type_as_formula (use_decreasing_pat:bool) (t:typ) (env:env_t) : term * decls_t = 
    let v_or_t_pat p = match (Util.unmeta_exp p).n with
        | Exp_app(_, [(Inl _, _); (Inr e, _)]) -> varg e
        | Exp_app(_, [(Inl t, _)]) -> targ t
        | _ -> failwith "Unexpected pattern term"  in
 
    let rec lemma_pats p = match (Util.unmeta_exp p).n with 
        | Exp_app(_, [_; (Inr hd, _); (Inr tl, _)]) -> v_or_t_pat hd::lemma_pats tl
        | _ -> [] in

    let binders, pre, post, patterns = match (Util.compress_typ t).n with 
        | Typ_fun(binders, {n=Comp ct}) -> 
           (match ct.effect_args with 
            | [(Inl pre, _); (Inl post, _); (Inr pats, _)] -> 
              binders, pre, post, lemma_pats pats
            | _ -> failwith "impos")
            
        | _ -> failwith "Impos" in
  
    let vars, guards, env, decls, _ = encode_binders false binders env in 
   

    let pats, decls' = patterns |> List.map (function 
        | Inl t, _ -> encode_formula t env
        | Inr e, _ -> let t, _, decls = encode_exp e env in t, decls) |> List.unzip in 
  
  
    let pats = 
        if use_decreasing_pat 
        then let rec prec_subterm (g:term) = match g.tm with 
                | And tms -> List.collect prec_subterm tms
                | _ -> if Util.starts_with g.as_str "(Valid (Prims.Precedes" then [g] else [] in
            let dec_pat = guards |> List.collect prec_subterm in
            dec_pat@pats 
        else pats in

    let env = {env with nolabels=true} in
    let pre, decls'' = encode_formula (Util.unmeta_typ pre) env in
    let post, decls''' = encode_formula (Util.unmeta_typ post) env in
    let decls = decls@(List.flatten decls')@decls''@decls''' in 

    mkForall(pats, vars, mkImp(mk_and_l (pre::guards), post)), decls

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
          end
         | _ -> failwith "impossible" in
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
                        (Const.ite_lid, enc_prop_c [true;true;true] <| tri_op mkITE); //NS: The guard appears both positively and negatively; scratching my head about this one. REVIEW!
                        (Const.not_lid, enc_prop_c [false] <| un_op mkNot);
                        (Const.eqT_lid, enc <| bin_op mkEq);
                        (Const.eq2_lid, eq_op);
                        (Const.true_lid, const_op mkTrue);
                        (Const.false_lid, const_op mkFalse);
                    ] in

    let fallback phi =  match phi.n with
        | Typ_meta(Meta_labeled(phi', msg, b)) -> 
          let phi, labs, decls = encode_formula_with_labels phi' env in
          if env.nolabels
          then phi, [], decls
          else let lvar = varops.fresh "label", Bool_sort in
               let lterm = Term.mkFreeV lvar in
               let lphi = Term.mkOr(lterm, phi) in
               lphi, (lvar, msg)::labs, decls
        
        | Typ_app({n=Typ_const ih}, [(Inl phi, _)]) when lid_equals ih.v Const.using_IH -> 
            if is_lemma phi
            then let f, decls = encode_function_type_as_formula true phi env in
                 f, [], decls
            else Term.mkTrue, [], []
            
        | _ -> 
            let tt, ex_vars, decls = encode_typ_term phi env in
            close env ex_vars <| Term.mk_Valid tt, [], decls in

    let encode_q_body env (bs:Syntax.binders) (ps:args) body = 
        let vars, guards, env, decls, _ = encode_binders true bs (negate env) in 
        let env = negate env in
        let pats, decls' = ps |> List.map (function 
            | Inl t, _ -> encode_formula t env
            | Inr e, _ -> let t, _, decls = encode_exp e env in t, decls) |> List.unzip in 
        let body, labs, decls'' = encode_formula_with_labels body env in
            vars, pats, mk_and_l guards, body, labs, decls@List.flatten decls'@decls'' in
    
    if Tc.Env.debug env.tcenv Options.Low
    then Util.fprint1 ">>>> Destructing as formula ... %s\n" (Print.formula_to_string phi);
    let phi = Util.compress_typ phi in
    match Util.destruct_typ_as_formula phi with
        | None -> 
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

type prims_t = {
    mk:lident -> string -> list<decl>;
    is:lident -> bool;
}


let prims =
    let asym, a = fresh_bvar "a" Type_sort in 
    let xsym, x = fresh_bvar "x" Term_sort in 
    let ysym, y = fresh_bvar "y" Term_sort in 
    let deffun vars body x = [Term.DefineFun(x, vars, Term_sort, body, None)] in     
    let quant vars body : string -> list<decl> = fun x ->
        let t1 = Term.mkApp(x, List.map Term.mkBoundV vars) in 
        let vname_decl = Term.DeclFun(x, vars |> List.map snd, Term_sort, None) in
        [vname_decl;
         Term.Assume(mkForall([t1], vars, mkEq(t1, body)), None)] in
    let axy = [(asym, Type_sort); (xsym, Term_sort); (ysym, Term_sort)] in 
    let xy = [(xsym, Term_sort); (ysym, Term_sort)] in
    let qx = [(xsym, Term_sort)] in
    let prims = [
        (Const.op_Eq,          (quant axy (boxBool <| mkEq(x,y))));
        (Const.op_notEq,       (quant axy (boxBool <| mkNot(mkEq(x,y)))));
        (Const.op_LT,          (quant xy  (boxBool <| mkLT(unboxInt x, unboxInt y))));
        (Const.op_LTE,         (quant xy  (boxBool <| mkLTE(unboxInt x, unboxInt y))));
        (Const.op_GT,          (quant xy  (boxBool <| mkGT(unboxInt x, unboxInt y))));
        (Const.op_GTE,         (quant xy  (boxBool <| mkGTE(unboxInt x, unboxInt y))));
        (Const.op_Subtraction, (quant xy  (boxInt  <| mkSub(unboxInt x, unboxInt y))));
        (Const.op_Minus,       (quant qx   (boxInt  <| mkMinus(unboxInt x))));
        (Const.op_Addition,    (quant xy  (boxInt  <| mkAdd(unboxInt x, unboxInt y))));
        (Const.op_Multiply,    (quant xy  (boxInt  <| mkMul(unboxInt x, unboxInt y))));
        (Const.op_Division,    (quant xy  (boxInt  <| mkDiv(unboxInt x, unboxInt y))));
        (Const.op_Modulus,     (quant xy  (boxInt  <| mkMod(unboxInt x, unboxInt y))));
        (Const.op_And,         (quant xy (boxBool <| mkAnd(unboxBool x, unboxBool y))));
        (Const.op_Or,          (quant xy (boxBool <| mkOr(unboxBool x, unboxBool y))));
        (Const.op_Negation,    (quant qx  (boxBool <| mkNot(unboxBool x))));
        ] in
    let mk : lident -> string -> list<decl> =
        fun l v -> prims |> List.filter (fun (l', _) -> lid_equals l l') |> List.collect (fun (_, b) -> b v) in
    let is : lident -> bool =
        fun l -> prims |> Util.for_some (fun (l', _) -> lid_equals l l') in
    {mk=mk;
     is=is}

let primitive_type_axioms : lident -> string -> term -> list<decl> = 
    let xx = ("x", Term_sort) in
    let x = mkBoundV xx in
    let mk_unit : string -> term -> decls_t = fun _ tt -> 
        let typing_pred = Term.mk_HasType false x tt in
        [Term.Assume(Term.mk_HasType false Term.mk_Term_unit tt,    Some "unit typing");
         Term.Assume(mkForall([typing_pred], [xx], mkImp(typing_pred, mkEq(x, Term.mk_Term_unit))),  Some "unit inversion")] in
    let mk_bool : string -> term -> decls_t = fun _ tt -> 
        let typing_pred = Term.mk_HasType false x tt in
        let bb = ("b", Bool_sort) in
        let b = mkBoundV bb in
        [Term.Assume(mkForall([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxBool" x)),    Some "bool inversion");
         Term.Assume(mkForall([Term.boxBool b], [bb], Term.mk_HasType false (Term.boxBool b) tt),    Some "bool typing")] in
    let mk_int : string -> term -> decls_t  = fun _ tt -> 
        let typing_pred = Term.mk_HasType false x tt in
        let aa = ("a", Int_sort) in
        let a = mkBoundV aa in
        let bb = ("b", Int_sort) in
        let b = mkBoundV bb in
        let precedes = Term.mk_Valid <| mkApp("Prims.Precedes", [tt;tt;Term.boxInt a; Term.boxInt b]) in
        [Term.Assume(mkForall([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxInt" x)),    Some "int inversion");
         Term.Assume(mkForall([Term.boxInt b], [bb], Term.mk_HasType false (Term.boxInt b) tt),    Some "int typing");
         Term.Assume(mkForall([precedes], [aa;bb], mkIff(precedes, mk_and_l [Term.mkGTE(a, Term.mkInteger 0);
                                                                             Term.mkGTE(b, Term.mkInteger 0);
                                                                             Term.mkLT(a, b)])), Some "Well-founded ordering on nats");
         Term.Assume(mkForall([typing_pred], [xx], mkImp(Term.mkAnd(typing_pred, Term.mkGT (Term.unboxInt x, Term.mkInteger 0)),
                                                         Term.mk_Valid <| mkApp("Precedes", [Term.boxInt <| Term.mkSub(Term.unboxInt x, Term.mkInteger 1); x]))), 
                                                            Some "well-founded ordering on nat (alt)")] in
    let mk_int_alias : string -> term -> decls_t = fun _ tt -> 
        [Term.Assume(mkEq(tt, mkFreeV(Const.int_lid.str, Type_sort)), Some "mapping to int; for now")] in
    let mk_str : string -> term -> decls_t  = fun _ tt -> 
        let typing_pred = Term.mk_HasType false x tt in
        let bb = ("b", String_sort) in
        let b = mkBoundV bb in
        [Term.Assume(mkForall([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxString" x)),    Some "string inversion");
         Term.Assume(mkForall([Term.boxString b], [bb], Term.mk_HasType false (Term.boxString b) tt),    Some "string typing")] in
    let mk_ref : string -> term -> decls_t = fun reft_name _ -> 
        let r = ("r", Ref_sort) in
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let refa = Term.mkApp(reft_name, [mkBoundV aa]) in
        let refb = Term.mkApp(reft_name, [mkBoundV bb]) in
        let typing_pred = Term.mk_HasType false x refa in
        let typing_pred_b = Term.mk_HasType false x refb in
        [Term.Assume(mkForall([typing_pred], [xx;aa], mkImp(typing_pred, Term.mk_tester "BoxRef" x)), Some "ref inversion");
         Term.Assume(mkForall([typing_pred; typing_pred_b], [xx;aa;bb], mkImp(mkAnd(typing_pred, typing_pred_b), mkEq(mkBoundV aa, mkBoundV bb))), Some "ref typing is injective")] in

    let prims = [(Const.unit_lid,   mk_unit);
                 (Const.bool_lid,   mk_bool);
                 (Const.int_lid,    mk_int);
                 (Const.string_lid, mk_str);
                 (Const.ref_lid,    mk_ref);
                 (Const.char_lid,   mk_int_alias);
                 (Const.uint8_lid,  mk_int_alias);
                ] in
    (fun (t:lident) (s:string) (tt:term) -> 
        match Util.find_opt (fun (l, _) -> lid_equals l t) prims with 
            | None -> []
            | Some(_, f) -> f s tt)

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
        let vars, guards, env', binder_decls, _ = encode_binders false tps env in
        let tok_app = mk_ApplyT ttok vars in
        let tok_decl = Term.DeclFun(Term.freeV_sym ttok, [], Type_sort, None) in
        let app = mkApp(tname, List.map mkBoundV vars) in
        let decls = [Term.DeclFun(tname, List.map snd vars, Type_sort, None);
                    tok_decl;
                    Term.Assume(mkForall([tok_app], vars, mkEq(tok_app, app)), Some "name-token correspondence")] in
        let def, (body, ex_vars, decls1) = 
            if tags |> Util.for_some (function Logic -> true | _ -> false) (* REVIEW: This code is dead, given the previous pattern *)
            then mk_Valid app, (let f, decls = encode_formula t env' in f, [], decls)
            else app, encode_typ_term t env' in 
        let g = binder_decls@decls@decls1@[Term.Assume(mkForall([def], vars, mkImp(mk_and_l guards, close_ex ex_vars <| mkEq(def, body))), None)] in 
        g, env

     | Sig_val_decl(lid, t, quals, _) -> 
        let tt = whnf env t in
        encode_free_var env lid t tt quals

     | Sig_assume(l, f, _, _) -> 
        let f, decls = encode_formula f env in
        let g = [Term.Assume(f, Some (format1 "Assumption: %s" (Print.sli l)))] in 
        decls@g, env

     | Sig_tycon(t, tps, k, _, datas, quals, _) when (lid_equals t Const.precedes_lid) -> 
        let tname, ttok, env = gen_free_tvar env t in
        [], env
               
     | Sig_tycon(t, _, _, _, _, _, _) when (lid_equals t Const.char_lid || lid_equals t Const.uint8_lid) ->
        let tname = t.str in
        let tsym = mkFreeV(tname, Type_sort) in
        let decl = Term.DeclFun(tname, [], Type_sort, None) in
        decl::primitive_type_axioms t tname tsym, push_free_tvar env t tname tsym

     | Sig_tycon(t, tps, k, _, datas, quals, _) -> 
        let is_logical = quals |> Util.for_some (function Logic -> true | _ -> false) in
        let constructor_or_logic_type_decl c = 
            if is_logical
            then let name, args, _, _ = c in 
                 [Term.DeclFun(name, args |> List.map snd, Type_sort, None)]
            else constructor_to_decl c in
 
        let inversion_axioms tapp vars = 
            if List.length datas = 0  || datas |> Util.for_some (fun l -> Tc.Env.lookup_qname env.tcenv l |> Option.isNone)
            then []
            else 
                 let xxsym, xx = fresh_bvar "x" Term_sort in
                 let data_ax, decls = datas |> List.fold_left (fun (out, decls) l -> 
                    let data_t = Tc.Env.lookup_datacon env.tcenv l in
                    let args, res = match Util.function_formals data_t with
                        | Some (formals, res) -> formals, Util.comp_result res
                        | None -> [], data_t in
                    let indices = match (Util.compress_typ res).n with 
                        | Typ_app(_, indices) -> indices
                        | _ -> [] in
                    let env = args |> List.fold_left (fun env a -> match fst a with 
                        | Inl a -> push_typ_var env a.v (Term.mkApp(mk_typ_projector_name l a.v, [xx]))
                        | Inr x -> push_term_var env x.v (Term.mkApp(mk_term_projector_name l x.v, [xx]))) env in
                    let indices, ex_vars, decls' = encode_args indices env in
                    if List.length indices <> List.length vars
                    then failwith "Impossible";
                    let eqs = List.map2 (fun v a -> match a with 
                        | Inl a -> Term.mkEq(mkBoundV v, a)
                        | Inr a -> Term.mkEq(mkBoundV v, a)) vars indices |> Term.mk_and_l |> close_ex ex_vars in
                    mkOr(out, mkAnd(mk_data_tester env l xx, eqs)), decls@decls') (mkFalse, []) in
                    let xx_has_type = mk_HasType false xx tapp in
                    decls@[Term.Assume(mkForall([xx_has_type], (xxsym, Term_sort)::vars,
                                        mkImp(xx_has_type, data_ax)), Some "inversion axiom")] in
        
        let k = Util.close_kind tps k in 
        let formals, res = match (Util.compress_kind k).n with 
            | Kind_arrow(bs, res) -> bs, res
            | _ -> [], k in
        let vars, guards, env', binder_decls, _ = encode_binders false formals env in
        
        let projection_axioms tapp vars = 
            match quals |> Util.find_opt (function Projector _ -> true | _ -> false) with
            | Some (Projector(d, Inl a)) -> 
                let rec projectee i = function 
                    | [] -> i
                    | f::tl -> 
                        (match fst f with 
                            | Inl _ -> projectee (i + 1) tl
                            | Inr x -> if x.v.ppname.idText="projectee" 
                                       then i 
                                       else projectee (i + 1) tl) in
                let projectee_pos = projectee 0 formals in          
                let xx, suffix = match Util.first_N projectee_pos vars with 
                                    | _, xx::suffix -> xx, suffix
                                    | _ -> failwith "impossible" in
                let dproj_app = mk_ApplyT (Term.mkApp(mk_typ_projector_name d a, [mkBoundV xx])) suffix in
                [Term.Assume(mkForall([tapp], vars, mkEq(tapp, dproj_app)), Some "projector axiom")]
            | _ -> [] in

        let tname, ttok, env = gen_free_tvar env t in
        let guard = mk_and_l guards in
        let tapp = Term.mkApp(tname, List.map mkBoundV vars) in
        let decls, env =
            let tname_decl = constructor_or_logic_type_decl(tname, vars, Type_sort, varops.next_id()) in
            let tok_decls, env = match vars with 
                | [] -> [], push_free_tvar env t tname (mkFreeV(tname, Type_sort)) 
                | _ -> 
                        let ttok_decl = Term.DeclFun(Term.freeV_sym ttok, [], Type_sort, Some "token") in
                        let ttok_app = mk_ApplyT ttok vars in 
                        let pats = if not is_logical && quals |> Util.for_some (function Opaque -> true | _ -> false)
                                   then [[ttok_app]; [tapp]]
                                   else [[ttok_app]] in
                        let name_tok_corr = Term.Assume(mkForall'(pats, None, vars, mkEq(ttok_app, tapp)), Some "name-token correspondence") in
                        [ttok_decl;name_tok_corr], env in
            tname_decl@tok_decls, env in
        let kindingAx = 
            let k, decls = encode_knd res env' tapp in
            decls@[Term.Assume(mkForall([tapp], vars, mkImp(guard, k)), Some "kinding")] in
        let aux = 
            if is_logical 
            then projection_axioms tapp vars 
            else kindingAx
                @(primitive_type_axioms t tname tapp)
                @(inversion_axioms tapp vars)
                @(projection_axioms tapp vars) in
 
        let g = decls
                @binder_decls
                @aux in
        g, env

    | Sig_datacon(d, _, _, _, _) when (lid_equals d Const.lexcons_lid) -> [], env 

    | Sig_datacon(d, t, _, quals, _) -> 
        let ddconstrsym, ddtok, env = gen_free_var env d in //Print.sli d in
        let formals, t_res = match Util.function_formals t with 
            | Some (f, c) -> f, Util.comp_result c
            | None -> [], t in
        let vars, guards, env', binder_decls, names = encode_binders false formals env in 
        let projectors = names |> List.map (function 
            | Inl a -> mk_typ_projector_name d a, Type_sort
            | Inr x -> mk_term_projector_name d x, Term_sort) in
        let datacons = (ddconstrsym, projectors, Term_sort, varops.next_id()) |> Term.constructor_to_decl in
        let app = mk_ApplyE ddtok vars in
        let guard = Term.mk_and_l guards in 
        let xvars = List.map mkBoundV vars in
        let dapp =  mkApp(ddconstrsym, xvars) in
        let ty_pred, decls2 = encode_typ_pred' false t_res env' dapp in
        let precedence = 
            if lid_equals d Const.lextop_lid
            then let x = varops.fresh "x", Term_sort in
                 let xtm = mkBoundV x in
                 [Term.Assume(mkForall([Term.mk_Precedes xtm dapp], [x], mkImp(mk_tester "LexCons" xtm, Term.mk_Precedes xtm dapp)), Some "lextop is top")]
            else (* subterm ordering *)
                let prec = vars |> List.collect (fun v -> match snd v with 
                    | Type_sort -> []
                    | Term_sort -> [Term.mk_Precedes (mkBoundV v) dapp]
                    | _ -> failwith "unexpected sort") in
                [Term.Assume(mkForall([ty_pred], vars, mkImp(guard, mk_and_l prec)), Some "subterm ordering")] in

        let tok_typing, decls3 = encode_typ_pred' true t env ddtok in
        let g = binder_decls
                @decls2
                @decls3
                @[Term.DeclFun(Term.freeV_sym ddtok, [], Term_sort, Some (format1 "data constructor proxy: %s" (Print.sli d)));
                  Term.Assume(tok_typing, Some "typing for data constructor proxy"); 
                  Term.Assume(mkForall([app], vars, 
                                       mkEq(app, dapp)), Some "equality for proxy");
                  Term.Assume(mkForall([ty_pred], vars, mkIff(guard, ty_pred)), Some "data constructor typing")]
                 @precedence in
        datacons@g, env

    | Sig_bundle(ses, _, _) -> 
      let g, env = encode_signature env ses in
      let g', inversions = g |> List.partition (function
        | Term.Assume(_, Some "inversion axiom") -> false
        | _ -> true) in
      g'@inversions, env

    | Sig_let((is_rec, [(Inr flid, t1, e)]), _, _, masked_effect) -> 
        if is_smt_lemma env t1 then encode_smt_lemma env flid t1, env else
        let t1_norm = whnf env t1 |> Util.compress_typ in
        let (f, ftok), decls, env = declare_top_level_let env flid t1 t1_norm in
        if not (Util.is_pure_function t1_norm) || masked_effect
        then decls, env  else
        let e = Util.compress_exp e in
        
        let eta_expand binders formals body t =
            let nbinders = List.length binders in
            let formals, extra_formals = Util.first_N nbinders formals in
            let subst = List.map2 (fun formal binder -> match fst formal, fst binder with 
                | Inl a, Inl b -> Inl (a.v, Util.btvar_to_typ b) 
                | Inr x, Inr y -> Inr (x.v, Util.bvar_to_exp y)
                | _ -> failwith "Impossible") formals binders in
            let extra_formals = Util.subst_binders subst extra_formals |> Util.name_binders in 
            let body = Syntax.mk_Exp_app_flat(body, snd <| Util.args_of_binders extra_formals) (Util.subst_typ subst t) body.pos in
            binders@extra_formals, body in
                         
        let binders, body, formals, tres = match e.n with
            | Exp_abs(binders, body) -> 
                begin match t1_norm.n with 
                 | Typ_fun(formals, c) -> 
                    let nformals = List.length formals in
                    let nbinders = List.length binders in
                    let tres = Util.comp_result c in                   
                    if nformals < nbinders && Util.is_total_comp c (* explicit currying *)
                    then let bs0, rest = Util.first_N nformals binders in 
                         let tres = match Util.mk_subst_binder bs0 formals with
                            | Some s -> Util.subst_typ s tres 
                            | _ -> failwith "impossible" in
                         let body = mk_Exp_abs(rest, body) tres body.pos in
                         bs0, body, formals, tres
                    
                    else if nformals > nbinders (* eta-expand before translating it *)
                    then let binders, body = eta_expand binders formals body tres in
                         binders, body, formals, tres
                    
                    else binders, body, formals, tres
                 | _ -> 
                     failwith (Util.format3 "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n" flid.str (Print.exp_to_string e) (Print.typ_to_string t1_norm))
                end
            | _ -> 
                begin match t1_norm.n with 
                    | Typ_fun(formals, c) -> 
                        let tres = Util.comp_result c in
                        let binders, body = eta_expand [] formals e tres in
                        binders, body, formals, tres
                    | _ -> [], e, [], t1_norm
                end in
                
        
        if is_rec (* guard equation with fuel *)
        then let g = varops.new_fvar flid in
             let gtok = varops.new_fvar flid in
             let fuel = varops.fresh "fuel", Term_sort in
             let fuel_tm = mkBoundV fuel in
             let env0 = env in 
             let env = push_free_var env flid gtok (Term.mkApp(g, [fuel_tm])) in
             let vars, guards, env', binder_decls, _ = encode_binders false binders env in
             let vars_tm = List.map mkBoundV vars in
             let app = Term.mkApp(f, vars_tm) in 
             let gsapp = Term.mkApp(g, Term.mkApp("SFuel", [fuel_tm])::vars_tm) in
             let gmax = Term.mkApp(g, Term.mkFreeV("MaxFuel", Term_sort)::vars_tm) in
             let body_tm, ex_vars, decls2 = encode_exp body env' in
             let decl_g = Term.DeclFun(g, Term_sort::List.map snd vars, Term_sort, Some "Fuel-instrumented function name") in
             let decl_g_tok = Term.DeclFun(gtok, [], Term_sort, Some "Token for fuel-instrumented partial applications") in
             let eqn_g = Term.Assume(mkForall([gsapp], fuel::vars, mkImp(mk_and_l guards, close_ex ex_vars <| mkEq(gsapp, body_tm))), Some (Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.str)) in
             let eqn_f = Term.Assume(mkForall([app], vars, mkEq(app, gmax)), Some "Correspondence of recursive function to instrumented version") in
             let eqn_g' = Term.Assume(mkForall([gsapp], fuel::vars, mkEq(gsapp,  Term.mkApp(g, mkBoundV fuel::vars_tm))), Some "Fuel irrelevance") in
             let g_typing = 
                let vars, _, env, binder_decls, _ = encode_binders false formals env0 in
                let vars_tm = List.map mkBoundV vars in
                let app = Term.mkApp(f, vars_tm) in 
                let gapp = Term.mkApp(g, fuel_tm::vars_tm) in
                let g_typing, d3 = encode_typ_pred' true tres env gapp in
                let f_typing, d4 = encode_typ_pred' true tres env app in
                let tok_corr = 
                    let tok_app = mk_ApplyE (Term.mkFreeV (gtok, Term_sort)) (fuel::vars) in
                    Term.Assume(mkForall([tok_app], fuel::vars, mkEq(tok_app, gapp)), Some "Fuel token correspondence") in
                binder_decls@d3@d4@[Term.Assume(mkForall([gapp], fuel::vars, mkImp(f_typing, g_typing)), None); tok_corr] in
             decls@binder_decls@decls2@[decl_g;decl_g_tok;eqn_g;eqn_g';eqn_f]@g_typing, env0
        
        else let vars, guards, env', binder_decls, _ = encode_binders false binders env in
             let app = match vars with [] -> Term.mkFreeV(f, Term_sort) | _ -> Term.mkApp(f, List.map mkBoundV vars) in
             let body, ex_vars, decls2 = encode_exp body env' in
             let eqn = Term.Assume(mkForall([app], vars, mkImp(mk_and_l guards, close_ex ex_vars <| mkEq(app, body))), Some (Util.format1 "Equation for %s" flid.str)) in
             decls@binder_decls@decls2@[eqn], env     
                 
    | Sig_let((_,lbs), _, _, _) -> //TODO: mutual recursion
        let msg = lbs |> List.map (fun (lb, _, _) -> Print.lbname_to_string lb) |> String.concat " and " in
        [], env

    | Sig_main _
    | Sig_monads _ -> [], env

and declare_top_level_let env x t t_norm =
    match try_lookup_lid env x with 
        | None -> (* Need to introduce a new name decl *)
            let decls, env = encode_free_var env x t t_norm [] in
            lookup_lid env x, decls, env 
        | Some (n, x) -> (* already declared, only need an equation *)
            (n, x), [], env

and encode_smt_lemma env lid t = 
    let form, decls = encode_function_type_as_formula false t env in 
    decls@[Term.Assume(form, Some ("Lemma: " ^ lid.str))]

and encode_free_var env lid tt t_norm quals = 
    if not <| Util.is_pure_function t_norm || is_smt_lemma env t_norm
    then let vname, vtok, env = gen_free_var env lid in
         let arg_sorts = match t_norm.n with 
            | Typ_fun(binders, _) -> binders |> List.map (function (Inl _, _) -> Type_sort | _ -> Term_sort) 
            | _ -> [] in
         let d = Term.DeclFun(vname, arg_sorts, Term_sort, Some "Uninterpreted function symbol for impure function or lemma") in
         let dd = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, Some "Uninterpreted name for impure function or lemma") in
         [d;dd], env
    else let formals, res = match Util.function_formals t_norm with 
            | Some (args, comp) -> args, Util.comp_result comp 
            | None -> [], t_norm in

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
        
        let vars, guards, env', decls1, _ = encode_binders false formals env in
        let guard = mk_and_l guards in
        let vtok_app = mk_ApplyE vtok vars in
        
        let vapp = Term.mkApp(vname, List.map Term.mkBoundV vars) in
        let decls2, env =
            if prims.is lid 
            then let definition = prims.mk lid vname in
                 let env = push_free_var env lid vname (mkFreeV(vname, Term_sort)) in 
                 definition, env
            else
                let vname_decl = Term.DeclFun(vname, formals |> List.map (function Inl _, _ -> Type_sort | _ -> Term_sort), Term_sort, None) in
                    (* Generate a token and a function symbol; equate the two, and use the function symbol for full applications *)
                    let tok_decl, env = match formals with 
                        | [] -> 
                            let t, decls2 = 
                                if not(head_normal env tt) 
                                then encode_typ_pred' true tt env (mkFreeV(vname, Term_sort))
                                else encode_typ_pred' true t_norm env (mkFreeV(vname, Term_sort)) in
                            let tok_typing = Term.Assume(t, Some "function token typing") in 
                            decls2@[tok_typing], push_free_var env lid vname (mkFreeV(vname, Term_sort))
                        | _ -> 
                              let vtok_decl = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, None) in
                              let name_tok_corr = Term.Assume(mkForall([vtok_app], vars, mkEq(vtok_app, vapp)), None) in
                              let tok_typing, decls2 = 
                                if not(head_normal env tt) 
                                then encode_typ_pred' true tt env vtok 
                                else encode_typ_pred' true t_norm env vtok in
                              let tok_typing = Term.Assume(tok_typing, Some "function token typing") in
                              decls2@[vtok_decl;name_tok_corr;tok_typing], env in
                    vname_decl::tok_decl, env in
        let ty_pred, decls3 = encode_typ_pred' true res env' vapp in
        let tt_typing, decls4 = 
            if not(head_normal env tt) 
            then let tok_typing, decls4 = encode_typ_pred' true tt env vtok in
                 [Term.Assume(tok_typing, None)], decls4
            else [], [] in
            
//        let tpat_var = varops.fresh "tt", Type_sort in
//        let pat = Term.mk_HasType false vapp (mkBoundV tpat_var) in
        let typingAx = Term.Assume(mkForall([vapp], vars, mkImp(guard, ty_pred)), Some "free var typing") in
        let g = decls1@decls2@decls3@decls4@typingAx::tt_typing@mk_disc_proj_axioms vapp vars in
        g, env
       

and encode_signature env ses = 
    ses |> List.fold_left (fun (g, env) se ->            
      let g', env = encode_sigelt env se in 
      g@g', env) ([], env) 

let encode_env_bindings (env:env_t) (bindings:list<Tc.Env.binding>) : (decls_t * env_t) = 
    let encode_binding b (decls, env) = match b with
        | Env.Binding_var(x, t0) -> 
            let xxsym, xx, env' = gen_free_term_var env x in 
            let t1 = norm_t env t0 in
            let t, decls' = encode_typ_pred' true t1 env xx in
            let caption = 
                if !Options.logQueries 
                then Some (Util.format3 "%s : %s (%s)" (Print.strBvd x) (Print.typ_to_string t0) (Print.typ_to_string t1))
                else None in  
            let g = [Term.DeclFun(xxsym, [], Term_sort, caption)]
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
            let t_norm = whnf env t in
            let g, env' = encode_free_var env x t t_norm [] in
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
let init_env tcenv = last_env := [{bindings=[]; tcenv=tcenv; warn=true; polarity=true; refinements=Util.smap_create 20; nolabels=false}]
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
    push (Util.format1 "Starting query at %s" (Range.string_of_range <| Env.get_range tcenv));
    let bg = Z3.flush_scopes () in
    let prefix, labels, qry, suffix =
        let env = get_env tcenv in
        let env_decls, env = encode_env_bindings env (List.filter (function Binding_sig _ -> false | _ -> true) tcenv.gamma) in
        if debug tcenv Options.Low then Util.fprint1 "Encoding query formula: %s\n" (Normalize.formula_norm_to_string tcenv q);
        let phi, labels, qdecls = encode_formula_with_labels q (negate env) in
        let label_prefix, label_suffix = encode_labels labels in
        let query_prelude = 
            env_decls
            @label_prefix
            @qdecls in
        let qry = Term.Assume(mkNot phi, Some "query") in
        let suffix = label_suffix@[Term.Echo "Done!"]  in
        query_prelude, labels, qry, suffix in
    
    let bg = bg@prefix in
    
    let with_fuel n = 
        [Term.Caption (Util.format1 "<fuel='%s'>" (string_of_int n)); 
         Term.Assume(mkEq(mkFreeV("MaxFuel", Term_sort), n_fuel n), None);
         qry;
         Term.CheckSat]@suffix in
    
    let check () =
        let ok, errs = Z3.ask bg labels (with_fuel !Options.initial_fuel) in
        let retry n = Z3.ask [] labels (with_fuel n) in
        if ok then ok, errs
        else let ok, _ = if !Options.max_fuel > !Options.initial_fuel then retry !Options.max_fuel else false, [] in 
             if ok then ok, []
             else match errs with 
                    | [] -> if !Options.min_fuel <> !Options.initial_fuel then retry !Options.min_fuel else false, [] (* don't have an error message .. try with less fuel *)
                    | _ -> false, errs  in

    let result = check () in 
    pop (Util.format1 "Ending query at %s" (Range.string_of_range <| Env.get_range tcenv));
    result

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


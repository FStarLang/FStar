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
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Tc
open Microsoft.FStar.ToSMT.Term

let add_fuel x tl = if !Options.unthrottle_inductives then tl else x::tl 
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
    | Binding_fvar  of lident * string * term * option<term> (* free variables, depending on whether or not they are fully applied ...  *)
    | Binding_ftvar of lident * string * term (* ... are mapped either to SMT2 functions, or to nullary term/type tokens *)

type closure_var = either<(btvdef*term), (bvvdef*term)>
type closure_vars = list<closure_var>
let cvar_binders cs = cs |> List.map (function 
    | Inl (_, {tm=BoundV(x,s)}) 
    | Inr (_, {tm=BoundV(x,s)}) -> x,s
    | _ -> failwith "impossible")
let cvar_sorts cs = cs |> List.map (function
    | Inl _ -> Type_sort
    | Inr _ -> Term_sort)
let cvar_terms cs = cs |> List.map (function
    | Inl (_, t)
    | Inr (_, t) -> t)
let exclude_cvars (bs:Syntax.binders) (cvars:closure_vars) : closure_vars = 
    let cvars = cvars |> Util.remove_dups (fun c1 c2 -> match c1, c2 with
        | Inl (_, {tm=BoundV(x, _)}), Inl (_, {tm=BoundV(y, _)})
        | Inr (_, {tm=BoundV(x, _)}), Inr (_, {tm=BoundV(y, _)}) -> x=y
        | _ -> false) in
    cvars |> List.filter (function
        | Inl (a, {tm=BoundV _}) -> bs |> Util.for_some (function (Inl a', _) -> Util.bvd_eq a a'.v | _ -> false) |> not
        | Inr (x, {tm=BoundV _}) -> bs |> Util.for_some (function (Inr x', _) -> Util.bvd_eq x x'.v | _ -> false) |> not
        | _ -> false)

let binder_of_eithervar v = (v, None)
type env_t = {bindings:list<binding>;
              tcenv:Env.env;
              warn:bool;
              refinements:Util.smap<(term * list<decl>)>;
              nolabels:bool;
              use_zfuel_name:bool;
              }
let print_env e = 
    e.bindings |> List.map (function 
        | Binding_var (x, t) -> Print.strBvd x
        | Binding_tvar (a, t) -> Print.strBvd a
        | Binding_fvar(l, s, t, _) -> Print.sli l
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
    match lookup_binding env (function Binding_var(b, t) when Util.bvd_eq b a.v -> Some (b,t) | _ -> None) with
    | None -> failwith (format1 "Bound term variable not found: %s" (Print.strBvd a.v))
    | Some (b,t) -> t, Inr(b,t)

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
   match lookup_binding env (function Binding_tvar(b, t) when Util.bvd_eq b a.v -> Some (b,t) | _ -> None) with 
    | None -> failwith (format1 "Bound type variable not found: %s" (Print.strBvd a.v))
    | Some (b,t) -> t, Inl(b,t)

(* Qualified term names *)
let gen_free_var (env:env_t) (x:lident) =
    let fname = varops.new_fvar x in
    let ftok = mkFreeV(varops.new_fvar x , Term_sort) in
    fname, ftok, {env with bindings=Binding_fvar(x, fname, ftok, None)::env.bindings}
let try_lookup_lid env a = 
    lookup_binding env (function Binding_fvar(b, t1, t2, t3) when lid_equals b a -> Some (t1, t2, t3) | _ -> None) 
let lookup_lid env a = 
    match lookup_binding env (function Binding_fvar(b, t1, t2, t3) when lid_equals b a -> Some (t1, t2, t3) | _ -> None) with
    | None -> failwith (format1 "Name not found: %s" (Print.sli a))
    | Some s -> s
let push_free_var env (x:lident) fname ftok = 
    {env with bindings=Binding_fvar(x, fname, ftok, None)::env.bindings}
let push_zfuel_name env (x:lident) f = 
    let t1, t2, _ = lookup_lid env x in
    let t3 = Term.mkApp(f, [Term.mkFreeV("ZFuel", Term.Fuel_sort)]) in
    {env with bindings=Binding_fvar(x, t1, t2, Some t3)::env.bindings}
let lookup_free_var env a =
    let name, sym, zf_opt = lookup_lid env a.v in
    match zf_opt with 
        | Some f when (env.use_zfuel_name) -> f
        | _ -> 
          match sym.tm with 
            | App(_, [fuel]) -> 
                if (Util.starts_with (Term.boundV_sym fuel) "fuel") 
                then Term.mk_ApplyEF(Term.mkFreeV (name, Term_sort)) fuel
                else sym
            | _ -> sym
let lookup_free_var_name env a = let x, _, _ = lookup_lid env a.v in x
let lookup_free_var_sym env a = 
    let name, sym, zf_opt = lookup_lid env a.v in
    match zf_opt with 
        | Some({tm=App(g, zf)}) when env.use_zfuel_name -> g, zf
        | _ -> 
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

let mkForall_fuel' n (pats, vars, body) = 
    let fallback () = Term.mkForall(pats, vars, body) in
    if !Options.unthrottle_inductives
    then fallback ()
    else let fsym, fterm = fresh_bvar "f" Fuel_sort in 
         let pats = pats |> List.map (fun p -> match p.tm with 
            | Term.App("HasType", args) -> Term.mkApp("HasTypeFuel", fterm::args)
            | _ -> p) in
            let vars = (fsym, Fuel_sort)::vars in 
         Term.mkForall(pats, vars, body)
  
let mkForall_fuel = mkForall_fuel' 1

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
let whnf_e env e = Tc.Normalize.norm_exp [Tc.Normalize.Beta;Tc.Normalize.WHNF] env.tcenv e
let norm_t env t = Tc.Normalize.norm_typ [Tc.Normalize.Beta] env.tcenv t
let norm_k env k = Tc.Normalize.normalize_kind env.tcenv k
let trivial_post t : typ = mk_Typ_lam([null_v_binder t], Util.ftv Const.true_lid ktype) 
                                     None t.pos

let mk_ApplyE e vars =  
    vars |> List.fold_left (fun out var -> match snd var with 
            | Type_sort -> mk_ApplyET out (Term.mkBoundV var)
            | Fuel_sort -> mk_ApplyEF out (Term.mkBoundV var)
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

//let close_ex vars pred = match vars with 
//    | [] -> pred
//    | _ -> 
//        let vars, guards = List.unzip vars in 
//        Term.mkExists([], vars, mk_and_l (pred::guards))
//        
//let close_all vars pred = match vars with
//    | [] -> pred
//    | _ -> 
//        let vars, guards = List.unzip vars in 
//        Term.mkForall([], vars, Term.mkImp(mk_and_l guards, pred))
        

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

type label = (var * string * Range.range)
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
  pat_term: unit -> (term * closure_vars * decls_t);    (* the pattern as a term(exp) *)
  guard: term -> term;                                  (* the guard condition of the pattern, as applied to a particular scrutinee term(exp) *)
  projections: term -> list<(either_var * term)>        (* bound variables of the pattern, and the corresponding projected components of the scrutinee *)
 }
exception Let_rec_unencodeable 

let encode_const = function 
    | Const_unit -> mk_Term_unit
    | Const_bool true -> boxBool mkTrue
    | Const_bool false -> boxBool mkFalse
    | Const_char c -> boxInt (mkInteger (Util.int_of_char c))
    | Const_uint8 i -> boxInt (mkInteger (Util.int_of_uint8 i))
    | Const_int32 i -> boxInt (mkInteger i)
    | Const_string(bytes, _) -> varops.string_const (Util.string_of_bytes <| bytes)
    | c -> failwith (Util.format1 "Unhandled constant: %s\n" (Print.const_to_string c))
 
let rec encode_knd' (prekind:bool) (k:knd) (env:env_t) (t:term) : term  * closure_vars * decls_t = 
    match (Util.compress_kind k).n with 
        | Kind_type -> 
            mk_HasKind t (Term.mk_Kind_type), [], []

        | Kind_abbrev(_, k) -> 
            encode_knd' prekind k env t

        | Kind_uvar (uv, _) -> (* REVIEW: warn? *)
            Term.mkTrue, [], []

        | Kind_arrow(bs, k) -> 
            let vars, cvars, guards, env', decls, _ = encode_binders None bs env in 
            let app = mk_ApplyT t vars in
            let k, cvars', decls' = encode_knd' prekind k env' app in
            let term = Term.mkForall([app], vars, mkImp(mk_and_l guards, k)) in
            let term = 
                if prekind
                then Term.mkAnd(mk_tester "Kind_arrow" (mk_PreKind t), 
                                term)
                else term in 
            term,
            exclude_cvars bs (cvars@cvars'),
            decls@decls'

        | _ -> failwith (Util.format1 "Unknown kind: %s" (Print.kind_to_string k))

and encode_knd (k:knd) (env:env_t) (t:term) = encode_knd' true k env t

and encode_binders (fuel_opt:option<term>) (bs:Syntax.binders) (env:env_t) : 
                            (list<var>                      (* translated bound variables *)
                            * closure_vars
                            * list<term>                    (* guards *)
                            * env_t                         (* extended context *)
                            * decls_t                       (* top-level decls to be emitted *)
                            * list<either<btvdef, bvvdef>>) (* unmangled names *) =

    if Tc.Env.debug env.tcenv Options.Low then Util.fprint1 "Encoding binders %s\n" (Print.binders_to_string ", " bs);
    
    let vars, cvars, guards, env, decls, names = bs |> List.fold_left (fun (vars, cvars, guards, env, decls, names) b -> 
        let v, cvars', g, env, decls', n = match fst b with 
            | Inl {v=a; sort=k} -> 
                let a = unmangle a in
                let aasym, aa, env' = 
                    if is_null_binder b 
                    then withenv env <| fresh_bvar "a" Type_sort
                    else gen_typ_var env a in 
                let guard_a_k, cvars, decls' = encode_knd' false k env aa in
                (aasym, Type_sort), 
                cvars,
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
                let guard_x_t, cvars, decls' = encode_typ_pred' fuel_opt (norm_t env t) env xx in
                (xxsym, Term_sort),
                cvars, 
                guard_x_t,
                env', 
                decls',
                Inr x in
        v::vars, cvars@cvars', g::guards, env, decls@decls', n::names) ([], [], [], env, [], []) in
    List.rev vars,
    cvars,
    List.rev guards,
    env, 
    decls,
    List.rev names

and encode_typ_pred' (fuel_opt:option<term>) (t:typ) (env:env_t) (e:term) : term * closure_vars * decls_t = 
    let t = Util.compress_typ t in 
    let t, cvars, decls = encode_typ_term t env in 
    mk_HasTypeWithFuel fuel_opt e t, cvars, decls

and encode_typ_term (t:typ) (env:env_t) : (term           (* encoding of t, expects t to be in normal form already *)
                                           * closure_vars (* captured varaiables in the term encoding *)
                                           * decls_t)     (* top-level declarations to be emitted (for shared representations of existentially bound terms *) = 
    let fresh_vars tname xname = 
        let tsym = varops.fresh tname, Type_sort in
        let ttm = mkBoundV tsym in
        let fsym = varops.fresh xname, Term_sort in
        let f = mkBoundV fsym in
        tsym, ttm, fsym, f in

    let t0 = Util.compress_typ t in
    match t0.n with 
      | Typ_btvar a -> 
        let t, c = lookup_typ_var env a in
        t, [c], []

      | Typ_const fv -> 
        lookup_free_tvar env fv, [], []

      | Typ_fun(binders, res) -> 
        (* TODO: sharing; check that currying works properly; handling non-total functions *)
        if   Absyn.Util.is_total_comp res
        then let vars, cvars, guards, env', decls, _ = encode_binders None binders env in 
             let fsym = varops.fresh "f", Term_sort in
             let f = mkBoundV fsym in
             let app = mk_ApplyE f vars in      
             let res_pred, cvars', decls' = encode_typ_pred' None (Util.comp_result res) env' app in

             let cvars = exclude_cvars binders (cvars@cvars') in
             let cvar_binders = cvar_binders cvars in

             let tsym = varops.fresh "Typ_fun" in
             let tdecl = Term.DeclFun(tsym, cvar_sorts cvars, Type_sort, None) in
             let t = Term.mkApp(tsym, cvar_terms cvars) in
             let t_has_kind = mk_HasKind t Term.mk_Kind_type in


             let k_assumption = Term.Assume(Term.mkForall([t_has_kind], cvar_binders, t_has_kind), None) in
             let f_has_t = mk_HasType f t in
             let t_interp = Term.Assume(mkForall_fuel([f_has_t], fsym::cvar_binders, 
                                                      mkIff(f_has_t, 
                                                            mkAnd(mk_tester "Typ_fun" (mk_PreType f), 
                                                                  mkForall([app], vars,  
                                                                              mkImp(mk_and_l guards, res_pred))))), 
                                       Some (tsym ^ " interpretation")) in 
            
             t, cvars, decls@decls'@[tdecl; k_assumption; t_interp]              

        else let tsym = varops.fresh "funtype" in
             let t = Term.mkFreeV(tsym, Type_sort) in
             let tdecl = Term.DeclFun(tsym, [], Type_sort, None) in
             t, [], [tdecl] (* TODO: At least preserve alpha-equivalence of non-pure function types *)
      
      | Typ_refine _ -> 
        let x, f = match Tc.Normalize.normalize_refinement env.tcenv t0 with 
            | {n=Typ_refine(x, f)} -> x, f
            | _ -> failwith "impossible" in
        let xsym = "this", Term_sort in 
        let xtm = mkBoundV xsym in 
        let base_pred, cvars, decls = encode_typ_pred' None x.sort env xtm in 
        let env' = push_term_var env x.v xtm in
        let refinement, cvars', decls' = encode_formula f env' in

        let encoding = Term.mkAnd(base_pred, refinement) in
        let cvars = exclude_cvars [(Inr x, None)] (cvars@cvars') in
      
        (* TODO: resolve sharing *)
        begin match Util.smap_try_find env.refinements encoding.as_str with 
            | Some (tm, _) -> tm, [], []
            | None -> 
              let tsym = varops.fresh "Typ_refine" in
              let tdecl = Term.DeclFun(tsym, cvar_sorts cvars, Type_sort, None) in
              let t = Term.mkApp(tsym, cvar_terms cvars) in
              let x_has_t = mk_HasType xtm t in
              let t_has_kind = mk_HasKind t Term.mk_Kind_type in
              let t_kinding = mkForall_fuel([t_has_kind], cvar_binders cvars, x_has_t) in //TODO: guard by typing of cvars
              let assumption = mkForall_fuel([x_has_t], xsym::cvar_binders cvars, mkIff(x_has_t, encoding)) in
              let new_decls = [tdecl;
                               Term.Assume(t_kinding, None);
                               Term.Assume(assumption, Some (Print.typ_to_string t0))] in
              Util.smap_add env.refinements encoding.as_str (t, new_decls);
              t, cvars, decls@decls'@new_decls
         end       
            

      | Typ_uvar (uv, k) ->
        let ttm = Term.mk_Typ_uvar (Unionfind.uvar_id uv) in
        let t_has_k, cvars, decls = encode_knd k env ttm in //TODO: skip encoding this if it has already been encoded before
        assert (cvars = []);
        let d = Term.Assume(t_has_k, None) in
        ttm, [], d::decls

      | Typ_app(head, args) -> 
        let is_full_app () = 
            let kk = Tc.Recheck.recompute_kind head in //so, this should be very cheap to recompute
            let formals, _ = Util.kind_formals kk in
            List.length formals = List.length args in
        let head = Util.compress_typ head in
        begin match head.n with
            | Typ_btvar a -> 
              let head, cvar = lookup_typ_var env a in
              let args, cvars, decls = encode_args args env in
              let t = mk_ApplyT_args head args in
              t, cvar::cvars, decls
                
            | Typ_const fv -> 
              let args, cvars, decls = encode_args args env in
              if is_full_app () 
              then let head = lookup_free_tvar_name env fv in
                   let t = Term.mkApp(head, List.map (function Inl t | Inr t -> t) args) in
                   t, cvars, decls
              else let head = lookup_free_tvar env fv in
                   let t = mk_ApplyT_args head args in
                   t, cvars, decls

            | Typ_uvar(uv, k) -> 
               let ttm = Term.mk_Typ_uvar (Unionfind.uvar_id uv) in
               let t_has_k, cvars, decls = encode_knd k env ttm in //TODO: skip encoding this if it has already been encoded before
               assert (cvars=[]);
               let d = Term.Assume(t_has_k, None) in
               ttm, [], d::decls  

            | _ -> (* not in head normal form; so reduce and retry *)
              let t = norm_t env t in
              (* CH: WARNING: if norm_t returns the same type it got as input
                     this code enters infinite loop (as it happened with uvars);
                     might want to do something about this!? *)
              encode_typ_term t env
        end

      | Typ_lam(bs, body) ->
        let vars, cvars, guards, env, decls, _ = encode_binders None bs env in
        let body, cvars', decls' = encode_typ_term body env in
        
        let cvars = exclude_cvars bs (cvars@cvars') in
      
        let tsym = varops.fresh "Typ_lam" in
        let tdecl = Term.DeclFun(tsym, cvar_sorts cvars, Type_sort, None) in
        let t = Term.mkApp(tsym, cvar_terms cvars) in

        let app = mk_ApplyT t vars in
        let interp = Term.Assume(mkForall([app], vars@cvar_binders cvars, mkImp(mk_and_l guards, mkEq(app,body))), 
                                 Some "Typ_lam interpretation") in
        let kinding =    
            let ktm, _, decls'' = encode_knd (Tc.Recheck.recompute_kind t0) env t in
            decls''@[Term.Assume(mkForall([t], cvar_binders cvars, ktm), Some "Typ_lam kinding")] in

        t, cvars, decls@decls'@interp::kinding

      | Typ_ascribed(t, _) -> 
        encode_typ_term t env

      | Typ_meta _
      | Typ_delayed  _ 
      | Typ_unknown    -> failwith (format4 "(%s) Impossible: %s\n%s\n%s\n" (Range.string_of_range <| t.pos) (Print.tag_of_typ t0) (Print.typ_to_string t0) (Print.typ_to_string t))                 

and encode_exp (e:exp) (env:env_t) : (term 
                                      * closure_vars
                                      * decls_t) = 
    let e = Visit.compress_exp_uvars e in 
    let e0 = e in
    match e.n with 
      | Exp_delayed _ -> (* REVIEW: dead code? *)
        encode_exp (Util.compress_exp e) env

      | Exp_bvar x -> 
        let t, c = lookup_term_var env x in
        t, [c], []

      | Exp_fvar(v, _) -> 
        lookup_free_var env v, [], []

      | Exp_constant c -> 
        encode_const c, [], []
      
      | Exp_ascribed(e, t) -> 
        e.tk := Some t;
        encode_exp e env

      | Exp_meta(Meta_desugared(e, _)) -> 
        encode_exp e env

      | Exp_uvar(uv, _) ->
        (* TODO: typing axiom for uvar? *)
        let e = Term.mk_Exp_uvar (Unionfind.uvar_id uv) in
        e, [], []
 
      | Exp_abs(bs, body) -> 

        let tfun = Tc.Util.force_tk e in
        if not <| Util.is_pure_function tfun
        then let f = varops.fresh "f" in
             let decl = Term.DeclFun(f, [], Term_sort, None) in
             Term.mkFreeV(f, Term_sort), [], [decl]
        else let tfun = whnf env tfun |> Util.compress_typ in
             begin match tfun.n with 
                | Typ_fun(bs', c) -> 
                    let nformals = List.length bs' in
//                    Printf.printf "Encoding Exp_abs %s\nType tfun is %s\ngot n_formals(typ)=%d and n_formals(term)=%d; total_comp=%A" 
//                    (Print.exp_to_string e)
//                    (Print.typ_to_string tfun)
//                    nformals 
//                    (List.length bs) 
//                    (Util.is_total_comp c);
                   
                    if nformals < List.length bs && Util.is_total_comp c (* explicit currying *)
                    then let bs0, rest = Util.first_N nformals bs in 
                         let res_t = match Util.mk_subst_binder bs0 bs' with 
                            | Some s -> Util.subst_typ s (Util.comp_result c) 
                            | _ -> failwith "Impossible" in
                         let e = mk_Exp_abs(bs0, mk_Exp_abs(rest, body) (Some res_t) body.pos) (Some tfun) e0.pos in
                         //Util.fprint1 "Explicitly currying %s\n" (Print.exp_to_string e);
                         encode_exp e env

                    else let vars, cvars, guards, envbody, decls, _ = encode_binders None bs env in 
                         let body, cvars', decls' = encode_exp body envbody in
                         
                         let cvars = exclude_cvars bs (cvars@cvars') in
                         let cvar_binders = cvar_binders cvars in 

                         let f = varops.fresh "f" in
                         let decl_f = Term.DeclFun(f, cvar_sorts cvars, Term_sort, None) in
                         let lam = Term.mkApp(f, cvar_terms cvars) in
                         let lam_typed, _, decls'' = encode_typ_pred' None tfun env lam in
                         let typing_f = Term.Assume(Term.mkForall([lam], cvar_binders, mkImp(Term.mk_and_l guards, lam_typed)), 
                                                    Some (f ^ " typing")) in 
                         
                         let app = mk_ApplyE lam vars in
                         let app_is_typed = 
                            let tsym, t = fresh_bvar "t" Type_sort in 
                            let app_has_t = Term.mk_HasType app t in
                            Term.mkExists([app_has_t], [(tsym, Type_sort)], app_has_t) in
                         let interp_f = Term.Assume(Term.mkForall([app], vars@cvar_binders, mkImp(app_is_typed, mkEq(app, body))), 
                                                    Some (f ^ " interpretation")) in
                         
                         lam, cvars, decls@decls'@[decl_f; typing_f; interp_f]

              | _ -> failwith "Impossible"
            end

      | Exp_app({n=Exp_fvar(l, _)}, [(Inl _, _); (Inr v1, _); (Inr v2, _)]) when (lid_equals l.v Const.lexcons_lid) -> 
         let v1, vars1, decls1 = encode_exp v1 env in 
         let v2, vars2, decls2 = encode_exp v2 env in
         Term.mk_LexCons v1 v2, vars1@vars2, decls1@decls2

      | Exp_app({n=Exp_abs _}, _) -> 
        encode_exp (whnf_e env e) env

      | Exp_app(head, args_e) -> 
        let args, cvars, decls = encode_args args_e env in
    
        let encode_partial_app ht_opt = 
            let head, cvars', decls' = encode_exp head env in
            let app_tm = mk_ApplyE_args head args in
            begin match ht_opt with
                | None -> app_tm, cvars'@cvars, decls@decls'
                | Some (formals, c) ->
                  let formals, rest = Util.first_N (List.length args_e) formals in
                  let subst = Util.formals_for_actuals formals args_e in
                  let ty = mk_Typ_fun(rest, c) (Some ktype) e0.pos |> Util.subst_typ subst in

                  let has_type, cvars'', decls'' = encode_typ_pred' None ty env app_tm in
                  let cvars = exclude_cvars [] (cvars@cvars'@cvars'') in
                  let interp_e = Term.Assume(Term.mkForall([has_type], cvar_binders cvars, has_type), None) in
                  app_tm, cvars, decls@decls'@decls''@[interp_e]
            end in

        let encode_full_app fv = 
            let fname, fuel_args = lookup_free_var_sym env fv in
            let tm = Term.mkApp(fname, fuel_args@List.map (function Inl t | Inr t -> t) args) in
            tm, cvars, decls in
        
        let head = Util.compress_exp head in
       
                if Env.debug env.tcenv <| Options.Other "186"
                then Util.fprint2 "Recomputing type for %s\nFull term is %s\n" (Print.exp_to_string head) (Print.exp_to_string e);
       
        let head_type = Util.unrefine <| whnf env (Util.unrefine (Tc.Recheck.recompute_typ head)) in //head should be a variable, so this should be fast to recompute
                
                if Tc.Env.debug env.tcenv <| Options.Other "Encoding"
                then Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" (Print.exp_to_string head) (Print.tag_of_exp head) (Print.typ_to_string head_type);
       
        begin match Util.function_formals head_type with
                    | None -> failwith (Util.format3 "(%s) term is %s; head type is %s\n" 
                                        (Range.string_of_range e0.pos) (Print.exp_to_string e0) (Print.typ_to_string head_type))
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
        let ee1, cvars1, decls1 = encode_exp e1 env in
        let env' = push_term_var env x ee1 in
        let ee2, cvars2, decls2 = encode_exp e2 env' in
        let cvars = exclude_cvars [(Inr (Util.bvd_to_bvar_s x t1), None)] (cvars1@cvars2) in
        ee2, cvars, decls1@decls2 
  
      | Exp_let _ -> 
        Tc.Errors.warn e.pos "Nested 'let rec' is not yet fully encoded to the SMT solver; you may not be able to prove some facts";
        let e = varops.fresh "let-rec" in
        let decl_e = Term.DeclFun(e, [], Term_sort, None) in
        Term.mkFreeV(e, Term_sort), [], [decl_e]

      | Exp_match(e, pats) ->
        let scr, cvars, decls = encode_exp e env in 

        let def = varops.fresh "default" in
        let decl_def = Term.DeclFun(def, [], Term_sort, None) in

        let match_tm, cvars, decls = List.fold_right (fun (p, w, br) (else_case, cvars, decls) -> 
            let patterns = encode_pat env p in
            List.fold_right (fun (env0, pattern) (else_case, cvars, decls) -> 
                let guard = pattern.guard scr in
                let projections = pattern.projections scr in
                let env = projections |> List.fold_left (fun env (x, t) -> match x with 
                    | Inl a -> push_typ_var env a.v t
                    | Inr x -> push_term_var env x.v t) env in
                let guard, cvars_w, decls2 = match w with 
                    | None -> guard, [], []
                    | Some w -> 
                        let w, cvars', decls2 = encode_exp w env in
                        Term.mkAnd(guard, Term.mkEq(w, Term.boxBool Term.mkTrue)), cvars', decls2 in
                let br, cvars_br, decls3 = encode_exp br env in
                let cvars_br = exclude_cvars (projections |> List.map (fun (x, _) -> binder_of_eithervar x)) (cvars_w@cvars_br) in
                mkITE(guard, br, else_case), cvars@cvars_br, decls@decls2@decls3)
            patterns (else_case, cvars, decls))
            pats 
            (Term.mkFreeV(def, Term_sort), cvars, decls) in
        match_tm, cvars, decls

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

and encode_formula (phi:typ) (env:env_t) : term * closure_vars * decls_t = 
    let t, cvars, vars, decls = encode_formula_with_labels phi env in
    match vars with
        | [] -> t, cvars, decls
        | _ -> failwith "Unexpected labels in formula"
  
and encode_function_type_as_formula (use_decreasing_pat:bool) (t:typ) (env:env_t) : term * closure_vars * decls_t = 
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
  
    let vars, cvars, guards, env, decls, _ = encode_binders None binders env in 
   

    let pats, cvars', decls' = patterns |> List.map (function 
        | Inl t, _ -> encode_formula t env
        | Inr e, _ -> encode_exp e ({env with use_zfuel_name=true})) |> List.unzip3 in 
  
  
    let pats = 
        if use_decreasing_pat 
        then let rec prec_subterm (g:term) = match g.tm with 
                | And tms -> List.collect prec_subterm tms
                | _ -> if Util.starts_with g.as_str "(Valid (Prims.Precedes" then [g] else [] in
            let dec_pat = guards |> List.collect prec_subterm in
            dec_pat@pats 
        else pats in

    let env = {env with nolabels=true} in
    let pre, cvars'', decls'' = encode_formula (Util.unmeta_typ pre) env in
    let post, cvars''', decls''' = encode_formula (Util.unmeta_typ post) env in
    let decls = decls@(List.flatten decls')@decls''@decls''' in 
    let cvars = exclude_cvars binders (cvars@List.flatten cvars'@cvars''@cvars''') in

    mkForall(pats, vars, mkImp(mk_and_l (pre::guards), post)), cvars, decls

and encode_formula_with_labels (phi:typ) (env:env_t) : (term * closure_vars * labels * decls_t)  = (* expects phi to be normalized; the existential variables are all labels *)
    let enc (f:list<term> -> term) : args -> (term * closure_vars * labels * decls_t) = fun l -> 
        let (cvars, decls), args = Util.fold_map (fun (vars, decls) x -> match fst x with 
            | Inl t -> let t, vars', decls' = encode_typ_term t env in (vars@vars', decls@decls'), t
            | Inr e -> let e, vars', decls' = encode_exp e env in (vars@vars', decls@decls'), e) ([],[]) l in
        (f args, cvars, [], decls) in

    let enc_prop_c f : args -> (term * closure_vars * labels * decls_t) = fun l ->
        let phis, cvars, labs, decls = 
            List.fold_right (fun t (phis, cvars, labs, decls) -> 
                match fst t with 
                | Inl t -> 
                    let phi, cvars', labs', decls' = encode_formula_with_labels t env in
                    (phi::phis, cvars'@cvars, labs'@labs, decls'@decls)
                | _ -> failwith "Expected a formula") 
                l ([], [], [], []) in
        (f phis, cvars, labs, decls) in
  

    let const_op f _ = (f, [], [], []) in
    let un_op f l = f <| List.hd l in
    let bin_op : ((term * term) -> term) -> list<term> -> term = fun f -> function 
        | [t1;t2] -> f(t1,t2)
        | _ -> failwith "Impossible" in
    let tri_op : ((term * term * term) -> term) -> list<term> -> term = fun f -> function
        | [t1;t2;t3] -> f(t1,t2,t3)
        | _ -> failwith "Impossible" in
    let eq_op : args -> (term * closure_vars * labels * decls_t) = function 
        | [_;_;e1;e2] -> enc (bin_op mkEq) [e1;e2]
        | l ->  enc (bin_op mkEq) l in
  
    let mk_imp : args -> (term * closure_vars * labels * decls_t) = function 
        | [(Inl lhs, _); (Inl rhs, _)] -> 
          let l1, cvars1, labs1, decls1 = encode_formula_with_labels rhs env in
          begin match l1.tm with 
            | True -> (l1, cvars1, labs1, decls1) (* Optimization: don't bother encoding the LHS of a trivial implication *)
            | _ -> 
             let l2, cvars2, labs2, decls2 = encode_formula_with_labels lhs env in
             (Term.mkImp(l2, l1), cvars2@cvars2, labs1@labs2, decls1@decls2)
          end
         | _ -> failwith "impossible" in

    let mk_ite : args -> (term * closure_vars * labels * decls_t) = function
        | [(Inl guard, _); (Inl _then, _); (Inl _else, _)] -> 
          let (g, cvars1, labs1, decls1) = encode_formula_with_labels guard env in
          let (t, cvars2, labs2, decls2) = encode_formula_with_labels _then env in 
          let (e, cvars3, labs3, decls3) = encode_formula_with_labels _else env in 
          let res = Term.mkITE(g, t, e) in
          res, cvars1@cvars2@cvars3, labs1@labs2@labs3, decls1@decls2@decls3
        | _ -> failwith "impossible" in 

   
    let unboxInt_l : (list<term> -> term) -> list<term> -> term = fun f l -> f (List.map Term.unboxInt l) in
    let connectives = [ 
        (Const.and_lid,   enc_prop_c <| bin_op mkAnd);
        (Const.or_lid,    enc_prop_c <| bin_op mkOr);
        (Const.imp_lid,   mk_imp);
        (Const.iff_lid,   enc_prop_c <| bin_op mkIff);
        (Const.ite_lid,   mk_ite); 
        (Const.not_lid,   enc_prop_c <| un_op mkNot);
        (Const.eqT_lid,   enc <| bin_op mkEq);
        (Const.eq2_lid,   eq_op);
        (Const.true_lid,  const_op mkTrue);
        (Const.false_lid, const_op mkFalse);
    ] in

    let fallback phi =  match phi.n with
        | Typ_meta(Meta_labeled(phi', msg, r, b)) -> 
          let phi, cvars, labs, decls = encode_formula_with_labels phi' env in
          if env.nolabels
          then (phi, cvars, [], decls)
          else let lvar = varops.fresh "label", Bool_sort in
               let lterm = Term.mkFreeV lvar in
               let lphi = Term.mkOr(lterm, phi) in
               (lphi, cvars, (lvar, msg, r)::labs, decls)
        
        | Typ_app({n=Typ_const ih}, [(Inl phi, _)]) when lid_equals ih.v Const.using_IH -> 
            if Util.is_lemma phi
            then let f, cvars, decls = encode_function_type_as_formula true phi env in
                 let _ = assert (cvars = []) in
                 (f, cvars, [], decls)
            else (Term.mkTrue, [], [], [])
            
        | _ -> 
            let tt, cvars, decls = encode_typ_term phi env in
            Term.mk_Valid tt, cvars, [], decls in

    let encode_q_body env (bs:Syntax.binders) (ps:args) body = 
        let vars, cvars, guards, env, decls, _ = encode_binders None bs env in
        let pats, cvars', decls' = ps |> List.map (function 
            | Inl t, _ -> encode_formula t env
            | Inr e, _ -> encode_exp e ({env with use_zfuel_name=true})) |> List.unzip3 in 
        let body, cvars'', labs, decls'' = encode_formula_with_labels body env in
        let cvars = exclude_cvars bs (cvars@(List.flatten cvars')@cvars'') in
        vars, pats, mk_and_l guards, body, cvars, labs, decls@List.flatten decls'@decls'' in
    
    if Tc.Env.debug env.tcenv Options.Low
    then Util.fprint1 ">>>> Destructing as formula ... %s\n" (Print.formula_to_string phi);
    let phi = Util.compress_typ phi in
    match Util.destruct_typ_as_formula phi with
        | None -> fallback phi
        
        | Some (Util.BaseConn(op, arms)) -> 
          (match connectives |> List.tryFind (fun (l, _) -> lid_equals op l) with 
             | None -> fallback phi
             | Some (_, f) -> f arms)

        | Some (Util.QAll(vars, pats, body)) -> 
          if Tc.Env.debug env.tcenv Options.Low
          then Util.fprint1 ">>>> Got QALL [%s]\n" (vars |> Print.binders_to_string "; ");

          let vars, pats, guard, body, cvars, labs, decls = encode_q_body env vars pats body in
          (mkForall(pats, vars, mkImp(guard, body)), cvars, labs, decls)

        | Some (Util.QEx(vars, pats, body)) -> 
          let vars, pats, guard, body, cvars, labs, decls = encode_q_body env vars pats body in
          (mkExists(pats, vars, mkAnd(guard, body)), cvars, labs, decls)

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

    let yy = ("y", Term_sort) in
    let y = mkBoundV yy in

    let mk_unit : string -> term -> decls_t = fun _ tt -> 
        let typing_pred = Term.mk_HasType x tt in
        [Term.Assume(Term.mk_HasType Term.mk_Term_unit tt,    Some "unit typing");
         Term.Assume(mkForall_fuel([typing_pred], [xx], mkImp(typing_pred, mkEq(x, Term.mk_Term_unit))),  Some "unit inversion")] in
    let mk_bool : string -> term -> decls_t = fun _ tt -> 
        let typing_pred = Term.mk_HasType x tt in
        let bb = ("b", Bool_sort) in
        let b = mkBoundV bb in
        [Term.Assume(mkForall_fuel([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxBool" x)),    Some "bool inversion");
         Term.Assume(mkForall([Term.boxBool b], [bb], Term.mk_HasType (Term.boxBool b) tt),    Some "bool typing")] in
    let mk_int : string -> term -> decls_t  = fun _ tt -> 
        let typing_pred = Term.mk_HasType x tt in
        let typing_pred_y = Term.mk_HasType y tt in
        let aa = ("a", Int_sort) in
        let a = mkBoundV aa in
        let bb = ("b", Int_sort) in
        let b = mkBoundV bb in
        let precedes = Term.mk_Valid <| mkApp("Prims.Precedes", [tt;tt;Term.boxInt a; Term.boxInt b]) in
        let precedes_y_x = Term.mk_Valid <| mkApp("Precedes", [y; x]) in
        [Term.Assume(mkForall_fuel([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxInt" x)),    Some "int inversion");
         Term.Assume(mkForall([Term.boxInt b], [bb], Term.mk_HasType (Term.boxInt b) tt),    Some "int typing");
         Term.Assume(mkForall_fuel([typing_pred; typing_pred_y;precedes_y_x], 
                                   [xx;yy], 
                                   mkImp(mk_and_l [typing_pred; 
                                                   typing_pred_y; 
                                                   Term.mkGT (Term.unboxInt x, Term.mkInteger 0);
                                                   Term.mkGTE (Term.unboxInt y, Term.mkInteger 0);
                                                   Term.mkLT (Term.unboxInt y, Term.unboxInt x)],
                                         precedes_y_x)),
                                  Some "well-founded ordering on nat (alt)")] in
    let mk_int_alias : string -> term -> decls_t = fun _ tt -> 
        [Term.Assume(mkEq(tt, mkFreeV(Const.int_lid.str, Type_sort)), Some "mapping to int; for now")] in
    let mk_str : string -> term -> decls_t  = fun _ tt -> 
        let typing_pred = Term.mk_HasType x tt in
        let bb = ("b", String_sort) in
        let b = mkBoundV bb in
        [Term.Assume(mkForall_fuel([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxString" x)),    Some "string inversion");
         Term.Assume(mkForall([Term.boxString b], [bb], Term.mk_HasType (Term.boxString b) tt),    Some "string typing")] in
    let mk_ref : string -> term -> decls_t = fun reft_name _ -> 
        let r = ("r", Ref_sort) in
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let refa = Term.mkApp(reft_name, [mkBoundV aa]) in
        let refb = Term.mkApp(reft_name, [mkBoundV bb]) in
        let typing_pred = Term.mk_HasType x refa in
        let typing_pred_b = Term.mk_HasType x refb in
        [Term.Assume(mkForall_fuel([typing_pred], [xx;aa], mkImp(typing_pred, Term.mk_tester "BoxRef" x)), Some "ref inversion");
         Term.Assume(mkForall_fuel' 2 ([typing_pred; typing_pred_b], [xx;aa;bb], mkImp(mkAnd(typing_pred, typing_pred_b), mkEq(mkBoundV aa, mkBoundV bb))), Some "ref typing is injective")] in

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
         <| (Print.sigelt_to_string se);//Util.lids_of_sigelt se |> List.map Print.sli |> String.concat ", ");
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

     | Sig_typ_abbrev(lid, _, _, _, _, _) when (lid_equals lid Const.b2t_lid) ->
       let tname, ttok, env = gen_free_tvar env lid in 
       let xx = ("x", Term_sort) in
       let x = mkBoundV xx in
       let valid_b2t_x = mk_Valid(Term.mkApp("Prims.b2t", [x])) in
//       (assert (forall ((@x Term))
//                (! (= (Valid (Prims.b2t @x))
//                      (and (HasType @x Prims.bool)
//                           (= BoxBool_proj_0 @x)))
//                   
//                   :pattern ((Valid (Prims.b2t @x))))))
       let decls = [Term.DeclFun(tname, [Term_sort], Type_sort, None);
                    Term.Assume(Term.mkForall([valid_b2t_x], [xx], 
                                              Term.mkEq(valid_b2t_x, 
                                                        Term.mkAnd(Term.mk_HasType x (Term.mkFreeV("Prims.bool", Type_sort)), 
                                                                   Term.mkApp("BoxBool_proj_0", [x])))),                                     
                                Some "b2t def")] in
       decls, env
      
     | Sig_typ_abbrev(lid, tps, _, t, tags, _) -> 
        let tname, ttok, env = gen_free_tvar env lid in 
        let tps, t = match t.n with 
            | Typ_lam(tps', body) -> tps@tps', body
            | _ -> tps, t in 
        let vars, cvars, guards, env', binder_decls, _ = encode_binders None tps env in
        assert (exclude_cvars tps cvars = []);
        let tok_app = mk_ApplyT ttok vars in
        let tok_decl = Term.DeclFun(Term.freeV_sym ttok, [], Type_sort, None) in
        let app = mkApp(tname, List.map mkBoundV vars) in
        let fresh_tok = match vars with 
            | [] -> []
            | _ -> [Term.fresh_token(Term.freeV_sym ttok, Type_sort) (varops.next_id())] in
        let decls = [Term.DeclFun(tname, List.map snd vars, Type_sort, None);
                    tok_decl]
                    @fresh_tok
                    @[Term.Assume(mkForall([tok_app], vars, mkEq(tok_app, app)), Some "name-token correspondence")] in
        let def, (body, _, decls1) = 
            if tags |> Util.for_some (function Logic -> true | _ -> false) 
            then mk_Valid app, encode_formula t env'
            else app, encode_typ_term t env' in 
        let abbrev_def = Term.Assume(mkForall([def], vars, mkImp(mk_and_l guards, mkEq(def, body))), Some "abbrev. elimination") in
//        let intro = if tags |> Util.for_some (function Logic -> true | _ -> false) 
//                    then []
//                    else let xxsym, x = fresh_bvar "x" Term_sort in
//                         let _ = encode_typ_pred 
//                         [Term.Assume(mkForall([mk_HasType x def], (xxsym, Term_sort)::vars, mkImp(close_ex ex_vars mkTrue, mk_HasType x def)), Some "abbrev. intro")] in
        let kindingAx = 
            let k, cvars, decls = encode_knd (Recheck.recompute_kind t) env' app in
            assert (exclude_cvars tps cvars = []);
            decls@[Term.Assume(mkForall([app], vars, mkImp(mk_and_l guards, k)), Some "abbrev. kinding")] in
        let g = binder_decls@decls@decls1@abbrev_def::kindingAx in
        g, env

     | Sig_val_decl(lid, t, quals, _) -> 
        let tt = whnf env t in
        let decls, env = encode_free_var env lid t tt quals in
        if Util.is_smt_lemma t && (quals |> List.contains Assumption || env.tcenv.is_iface)
        then decls@encode_smt_lemma env lid t, env
        else decls, env

     | Sig_assume(l, f, _, _) -> 
        let f, cvars, decls = encode_formula f env in
        assert (cvars=[]);
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
                    let indices, _, decls' = encode_args indices env in
                    if List.length indices <> List.length vars
                    then failwith "Impossible";
                    let eqs = List.map2 (fun v a -> match a with 
                        | Inl a -> Term.mkEq(mkBoundV v, a)
                        | Inr a -> Term.mkEq(mkBoundV v, a)) vars indices |> Term.mk_and_l in
                    mkOr(out, mkAnd(mk_data_tester env l xx, eqs)), decls@decls') (mkFalse, []) in
                    let ffsym, ff = fresh_bvar "f" Fuel_sort in
                    let xx_has_type = mk_HasTypeFuel (Term.mkApp("SFuel", [ff])) xx tapp in
                    decls@[Term.Assume(mkForall([xx_has_type], add_fuel (ffsym, Fuel_sort) ((xxsym, Term_sort)::vars),
                                        mkImp(xx_has_type, data_ax)), Some "inversion axiom")] in
        
        let k = Util.close_kind tps k in 
        let is_kind_arrow, formals, res = match (Util.compress_kind k).n with 
            | Kind_arrow(bs, res) -> true, bs, res
            | _ -> false, [], k in
        let vars, _cvars, guards, env', binder_decls, _ = encode_binders None formals env in
        
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
                        let ttok_fresh = Term.fresh_token (Term.freeV_sym ttok, Type_sort) (varops.next_id()) in
                        let ttok_app = mk_ApplyT ttok vars in 
                        let pats = if not is_logical && quals |> Util.for_some (function Opaque -> true | _ -> false)
                                   then [[ttok_app]; [tapp]]
                                   else [[ttok_app]] in
                        let name_tok_corr = Term.Assume(mkForall'(pats, None, vars, mkEq(ttok_app, tapp)), Some "name-token correspondence") in
                        [ttok_decl; ttok_fresh; name_tok_corr], env in
            tname_decl@tok_decls, env in
        let kindingAx = 
            let k, _, decls = encode_knd res env' tapp in
            let karr = 
                if is_kind_arrow 
                then [Term.Assume(mk_tester "Kind_arrow" (mk_PreKind ttok), Some "kinding")] 
                else [] in
            decls@karr@[Term.Assume(mkForall([tapp], vars, mkImp(guard, k)), Some "kinding")] in
        let aux = 
            if is_logical 
            then kindingAx@projection_axioms tapp vars 
            else kindingAx
                @(primitive_type_axioms t tname tapp)
                @(inversion_axioms tapp vars)
                @(projection_axioms tapp vars) in
 
        let g = decls
                @binder_decls
                @aux in
        g, env

    | Sig_datacon(d, _, _, _, _, _) when (lid_equals d Const.lexcons_lid) -> [], env 

    | Sig_datacon(d, t, _, quals, _, _) -> 
        let ddconstrsym, ddtok, env = gen_free_var env d in //Print.sli d in
        let formals, t_res = match Util.function_formals t with 
            | Some (f, c) -> f, Util.comp_result c
            | None -> [], t in
        let fuel_var, fuel_tm = fresh_bvar "f" Fuel_sort in
        let s_fuel_tm = Term.mkApp("SFuel", [fuel_tm]) in
        let vars, _, guards, env', binder_decls, names = encode_binders (Some fuel_tm) formals env in 
        let projectors = names |> List.map (function 
            | Inl a -> mk_typ_projector_name d a, Type_sort
            | Inr x -> mk_term_projector_name d x, Term_sort) in
        let datacons = (ddconstrsym, projectors, Term_sort, varops.next_id()) |> Term.constructor_to_decl in
        let app = mk_ApplyE ddtok vars in
        let guard = Term.mk_and_l guards in 
        let xvars = List.map mkBoundV vars in
        let dapp =  mkApp(ddconstrsym, xvars) in
        let ty_pred, _, decls2 = encode_typ_pred' (Some s_fuel_tm) t_res env' dapp in
        let precedence = 
            if lid_equals d Const.lextop_lid
            then let x = varops.fresh "x", Term_sort in
                 let xtm = mkBoundV x in
                 [Term.Assume(mkForall([Term.mk_Precedes xtm dapp], [x], mkImp(mk_tester "LexCons" xtm, Term.mk_Precedes xtm dapp)), Some "lextop is top")]
            else (* subterm ordering *)
                let prec = vars |> List.collect (fun v -> match snd v with 
                    | Type_sort
                    | Fuel_sort -> []
                    | Term_sort -> [Term.mk_Precedes (mkBoundV v) dapp]
                    | _ -> failwith "unexpected sort") in
                [Term.Assume(mkForall([ty_pred], add_fuel (fuel_var, Fuel_sort) vars, mkImp(guard, mk_and_l prec)), Some "subterm ordering")] in

        let tok_typing, _, decls3 = encode_typ_pred' None t env ddtok in

        let vars', _, guards', env'', _, _ = encode_binders (Some s_fuel_tm) formals env in
        let ty_pred', _, _ = 
             let xvars = List.map mkBoundV vars' in
             let dapp =  mkApp(ddconstrsym, xvars) in
             encode_typ_pred' (Some fuel_tm) t_res env'' dapp in 
        let guard' = Term.mk_and_l guards' in
        let proxy_fresh = match formals with 
            | [] -> []
            | _ -> [Term.fresh_token (Term.freeV_sym ddtok, Term_sort) (varops.next_id())] in
        let g = binder_decls
                @decls2
                @decls3
                @[Term.DeclFun(Term.freeV_sym ddtok, [], Term_sort, Some (format1 "data constructor proxy: %s" (Print.sli d)))]
                @proxy_fresh
                @[Term.Assume(tok_typing, Some "typing for data constructor proxy"); 
                  Term.Assume(mkForall([app], vars, 
                                       mkEq(app, dapp)), Some "equality for proxy");
                  Term.Assume(mkForall([ty_pred], add_fuel (fuel_var, Fuel_sort) vars, mkImp(ty_pred, guard)), Some "data constructor typing elim");
                  Term.Assume(mkForall([ty_pred'],add_fuel (fuel_var, Fuel_sort) vars', mkImp(guard', ty_pred')), Some "data constructor typing intro");
                  ]
                 @precedence in
        datacons@g, env

    | Sig_bundle(ses, _, _) -> 
      let g, env = encode_signature env ses in
      let g', inversions = g |> List.partition (function
        | Term.Assume(_, Some "inversion axiom") -> false
        | _ -> true) in
      g'@inversions, env

    | Sig_let((is_rec, bindings), _, _, quals) ->
        let eta_expand binders formals body t =
            let nbinders = List.length binders in
            let formals, extra_formals = Util.first_N nbinders formals in
            let subst = List.map2 (fun formal binder -> match fst formal, fst binder with 
                | Inl a, Inl b -> Inl (a.v, Util.btvar_to_typ b) 
                | Inr x, Inr y -> Inr (x.v, Util.bvar_to_exp y)
                | _ -> failwith "Impossible") formals binders in
            let extra_formals = Util.subst_binders subst extra_formals |> Util.name_binders in 
            let body = Syntax.mk_Exp_app_flat(body, snd <| Util.args_of_binders extra_formals) (Some <| Util.subst_typ subst t) body.pos in
            binders@extra_formals, body in

        let destruct_bound_function flid t_norm e = match e.n with
            | Exp_ascribed({n=Exp_abs(binders, body)}, _)
            | Exp_abs(binders, body) -> 
                begin match t_norm.n with 
                 | Typ_fun(formals, c) -> 
                    let nformals = List.length formals in
                    let nbinders = List.length binders in
                    let tres = Util.comp_result c in       
                    if nformals < nbinders && Util.is_total_comp c (* explicit currying *)
                    then let bs0, rest = Util.first_N nformals binders in 
                         let tres = match Util.mk_subst_binder bs0 formals with
                            | Some s -> Util.subst_typ s tres 
                            | _ -> failwith "impossible" in
                         let body = mk_Exp_abs(rest, body) (Some tres) body.pos in
                         bs0, body, bs0, tres
                    
                    else if nformals > nbinders (* eta-expand before translating it *)
                    then let binders, body = eta_expand binders formals body tres in
                         binders, body, formals, tres
                    
                    else binders, body, formals, tres
                 | _ -> 
                     failwith (Util.format3 "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n" 
                              flid.str (Print.exp_to_string e) (Print.typ_to_string t_norm))
                end
            | _ -> 
                begin match t_norm.n with 
                    | Typ_fun(formals, c) -> 
                        let tres = Util.comp_result c in
                        let binders, body = eta_expand [] formals e tres in
                        binders, body, formals, tres
                    | _ -> [], e, [], t_norm
                end in
             
        begin try 
                 if quals |> Util.for_some (function Opaque -> true | _ -> false)
                 then [], env
                 else if   bindings |> Util.for_some (fun (_, t, _) -> Util.is_smt_lemma t) 
                 then bindings |> List.collect (fun (flid, t, _) -> 
                        if Util.is_smt_lemma t
                        then encode_smt_lemma env (right flid) t
                        else raise Let_rec_unencodeable), env
                 else let toks, typs, decls, env = 
                    bindings |> List.fold_left (fun (toks, typs, decls, env) (flid, t, _) -> 
                        if Util.is_smt_lemma t then raise Let_rec_unencodeable;
                        let t_norm = whnf env t |> Util.compress_typ in
                        let tok, decl, env = declare_top_level_let env (right flid) t t_norm in
                        (right flid, tok)::toks, t_norm::typs, decl::decls, env) ([], [], [], env) in
                 let toks = List.rev toks in 
                 let decls = List.rev decls |> List.flatten in
                 let typs = List.rev typs in
                 if   quals |> Util.for_some (function HasMaskedEffect -> true | _ -> false)
                 || typs |> Util.for_some (fun t -> Util.is_lemma t || not <| Util.is_pure_function t) 
                 then decls, env
                 else if not is_rec
                 then match bindings, typs, toks with 
                        | [(_, _, e)], [t_norm], [(flid, (f, ftok))] ->
                          let binders, body, formals, tres = destruct_bound_function flid t_norm e in
                          let vars, _, guards, env', binder_decls, _ = encode_binders None binders env in
                          let app = match vars with [] -> Term.mkFreeV(f, Term_sort) | _ -> Term.mkApp(f, List.map mkBoundV vars) in
                          let body, _, decls2 = encode_exp body env' in
                          let eqn = Term.Assume(mkForall([app], vars, mkImp(mk_and_l guards, mkEq(app, body))), Some (Util.format1 "Equation for %s" flid.str)) in
                          decls@binder_decls@decls2@[eqn], env      
                        | _ -> failwith "Impossible"
                 else let fuel = varops.fresh "fuel", Fuel_sort in
                      let fuel_tm = mkBoundV fuel in
                      let env0 = env in 
                      let gtoks, env = toks |> List.fold_left (fun (gtoks, env) (flid, (f, ftok)) -> 
                         let g = varops.new_fvar flid in
                         let gtok = varops.new_fvar flid in
                         let env = push_free_var env flid gtok (Term.mkApp(g, [fuel_tm])) in
                         (flid, f, ftok, g, gtok)::gtoks, env) ([], env) in
                      let gtoks = List.rev gtoks in
                      let encode_one_binding env0 (flid, f, ftok, g, gtok) t_norm (_, _, e) = 
                         let binders, body, formals, tres = destruct_bound_function flid t_norm e in
                         let vars, _, guards, env', binder_decls, _ = encode_binders None binders env in
                         let decl_g = Term.DeclFun(g, Fuel_sort::List.map snd vars, Term_sort, Some "Fuel-instrumented function name") in
                         let env0 = push_zfuel_name env0 flid g in
                         let decl_g_tok = Term.DeclFun(gtok, [], Term_sort, Some "Token for fuel-instrumented partial applications") in
                         let vars_tm = List.map mkBoundV vars in
                         let app = Term.mkApp(f, vars_tm) in 
                         let gsapp = Term.mkApp(g, Term.mkApp("SFuel", [fuel_tm])::vars_tm) in
                         let gmax = Term.mkApp(g, Term.mkFreeV("MaxFuel", Term_sort)::vars_tm) in
                         let body_tm, _, decls2 = encode_exp body env' in
                         let eqn_g = Term.Assume(mkForall([gsapp], fuel::vars, mkImp(mk_and_l guards, mkEq(gsapp, body_tm))), Some (Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.str)) in
                         let eqn_f = Term.Assume(mkForall([app], vars, mkEq(app, gmax)), Some "Correspondence of recursive function to instrumented version") in
                         let eqn_g' = Term.Assume(mkForall([gsapp], fuel::vars, mkEq(gsapp,  Term.mkApp(g, mkBoundV fuel::vars_tm))), Some "Fuel irrelevance") in
                         let g_typing = 
                            let vars, _, v_guards, env, binder_decls, _ = encode_binders None formals env0 in
                            let vars_tm = List.map mkBoundV vars in
                            let gapp = Term.mkApp(g, fuel_tm::vars_tm) in
                            let tok_corr = 
                                let tok_app = mk_ApplyE (Term.mkFreeV (gtok, Term_sort)) (fuel::vars) in
                                Term.Assume(mkForall([tok_app], fuel::vars, mkEq(tok_app, gapp)), Some "Fuel token correspondence") in
                            let typing_corr = 
                                let g_typing, _, d3 = encode_typ_pred' None tres env gapp in
                                d3@[Term.Assume(mkForall([gapp], fuel::vars, mkImp(Term.mk_and_l v_guards, g_typing)), None)] in
                            binder_decls@typing_corr@[tok_corr] in
                        binder_decls@[decl_g;decl_g_tok], decls2@[eqn_g;eqn_g';eqn_f]@g_typing, env0 in
                        let decls, eqns, env0 = List.fold_left (fun (decls, eqns, env0) (gtok, ty, bs) -> 
                            let decls', eqns', env0 = encode_one_binding env0 gtok ty bs in
                            decls'@decls, eqns'@eqns, env0) ([], [], env0) (List.zip3 gtoks typs bindings) in
                        let prefix_decls = List.rev decls in
                        let eqns = List.rev eqns in
                        ( prefix_decls)@( eqns), env0
        with Let_rec_unencodeable -> 
             let msg = bindings |> List.map (fun (lb, _, _) -> Print.lbname_to_string lb) |> String.concat " and " in
             let decl = Caption ("let rec unencodeable: Skipping: " ^msg) in
             [decl], env
        end

    | Sig_pragma _
    | Sig_main _
    | Sig_monads _ -> [], env

and declare_top_level_let env x t t_norm =
    match try_lookup_lid env x with 
        | None -> (* Need to introduce a new name decl *)
            let decls, env = encode_free_var env x t t_norm [] in
            let n, x, _ = lookup_lid env x in
            (n, x), decls, env 
        | Some (n, x, _) -> (* already declared, only need an equation *)
            (n, x), [], env

and encode_smt_lemma env lid t = 
    let form, cvars, decls = encode_function_type_as_formula false t env in 
    assert (cvars=[]);
    decls@[Term.Assume(form, Some ("Lemma: " ^ lid.str))]

and encode_free_var env lid tt t_norm quals = 
    if not <| Util.is_pure_function t_norm || Util.is_lemma t_norm
    then let vname, vtok, env = gen_free_var env lid in
         let arg_sorts = match t_norm.n with 
            | Typ_fun(binders, _) -> binders |> List.map (function (Inl _, _) -> Type_sort | _ -> Term_sort) 
            | _ -> [] in
         let d = Term.DeclFun(vname, arg_sorts, Term_sort, Some "Uninterpreted function symbol for impure function") in
         let dd = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, Some "Uninterpreted name for impure function") in
         [d;dd], env
    else let formals, res = match Util.function_formals t_norm with 
            | Some (args, comp) -> args, Util.comp_result comp 
            | None -> [], t_norm in
         let vname, vtok, env = gen_free_var env lid in 
         if prims.is lid
         then let definition = prims.mk lid vname in
              let env = push_free_var env lid vname (mkFreeV(vname, Term_sort)) in 
              definition, env
         else let mk_disc_proj_axioms vapp vars = quals |> List.collect (function 
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
              let vars, _, guards, env', decls1, _ = encode_binders None formals env in
              let guard = mk_and_l guards in
              let vtok_app = mk_ApplyE vtok vars in
        
              let vapp = Term.mkApp(vname, List.map Term.mkBoundV vars) in
              let decls2, env =
                let vname_decl = Term.DeclFun(vname, formals |> List.map (function Inl _, _ -> Type_sort | _ -> Term_sort), Term_sort, None) in
                    (* Generate a token and a function symbol; equate the two, and use the function symbol for full applications *)
                    let tok_decl, env = match formals with 
                        | [] -> 
                            let t, _, decls2 = 
                                if not(head_normal env tt) 
                                then encode_typ_pred' None tt env (mkFreeV(vname, Term_sort))
                                else encode_typ_pred' None t_norm env (mkFreeV(vname, Term_sort)) in
                            let tok_typing = Term.Assume(t, Some "function token typing") in 
                            decls2@[tok_typing], push_free_var env lid vname (mkFreeV(vname, Term_sort))
                        | _ -> 
                                let vtok_decl = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, None) in
                                let vtok_fresh = Term.fresh_token (Term.freeV_sym vtok, Term_sort) (varops.next_id()) in
                                let name_tok_corr = Term.Assume(mkForall([vtok_app], vars, mkEq(vtok_app, vapp)), None) in
                                let tok_typing, _, decls2 = 
                                    if not(head_normal env tt) 
                                    then encode_typ_pred' None tt env vtok 
                                    else encode_typ_pred' None t_norm env vtok in
                                let tok_typing = Term.Assume(tok_typing, Some "function token typing") in
                                decls2@[vtok_decl;vtok_fresh;name_tok_corr;tok_typing], env in
                    vname_decl::tok_decl, env in
              let ty_pred, _, decls3 = encode_typ_pred' None res env' vapp in
              let tt_typing, decls4 = 
                    if not(head_normal env tt) 
                    then let tok_typing, _, decls4 = encode_typ_pred' None tt env vtok in
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
            let t, _, decls' = encode_typ_pred' None t1 env xx in
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
            let k, _, decls' = encode_knd k env aa in
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
    let prefix = labs |> List.map (fun (l, _, _) -> Term.DeclFun(fst l, [], Bool_sort, None)) in
    let suffix = labs |> List.collect (fun (l, _, _) -> [Echo <| fst l; Eval (mkFreeV l)]) in
    prefix, suffix

(* caching encodings of the environment and the top-level API to the encoding *)
open Microsoft.FStar.Tc.Env
let last_env : ref<list<env_t>> = Util.mk_ref []
let init_env tcenv = last_env := [{bindings=[]; tcenv=tcenv; warn=true; refinements=Util.smap_create 20; nolabels=false; use_zfuel_name=false}]
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
    Z3.init ();
    Z3.giveZ3 [DefPrelude]
let push msg = 
    push_env ();
    varops.push();
    Z3.push msg
let pop msg   = 
    ignore <| pop_env(); 
    varops.pop();
    Z3.pop msg
let encode_sig tcenv se =
   let caption decls = 
    if !Options.logQueries
    then Term.Caption ("encoding sigelt " ^ (Print.sigelt_to_string_short se))::decls
    else decls in    
   let env = get_env tcenv in
   let decls, env = encode_sigelt env se in
   set_env env; 
   Z3.giveZ3 (caption decls)

let encode_modul tcenv modul = 
    let name = Util.format2 "%s %s" (if modul.is_interface then "interface" else "module")  modul.name.str in
    if Tc.Env.debug tcenv Options.Low 
    then Util.fprint2 "Encoding externals for %s ... %s exports\n" name (List.length modul.exports |> string_of_int);
    let env = get_env tcenv in
    let decls, env = encode_signature ({env with warn=false}) modul.exports in
    let caption decls = 
    if !Options.logQueries
    then let msg = "Externals for " ^ name in
         Caption msg::decls@[Caption ("End " ^ msg)]
    else decls in
    set_env ({env with warn=true}); 
    if Tc.Env.debug tcenv Options.Low then Util.fprint1 "Done encoding externals for %s\n" name;
    let decls = caption decls in
    Z3.giveZ3 decls

let solve tcenv q : unit =
    push (Util.format1 "Starting query at %s" (Range.string_of_range <| Env.get_range tcenv));
    let pop () = pop (Util.format1 "Ending query at %s" (Range.string_of_range <| Env.get_range tcenv)) in
    let prefix, labels, qry, suffix =
        let env = get_env tcenv in
        let env_decls, env = encode_env_bindings env (List.filter (function Binding_sig _ -> false | _ -> true) tcenv.gamma) in
        if debug tcenv Options.Low then Util.fprint1 "Encoding query formula: %s\n" (Print.formula_to_string q);//(Normalize.formula_norm_to_string tcenv q);
        let phi, _, labels, qdecls = encode_formula_with_labels q env in
        let label_prefix, label_suffix = encode_labels labels in
        let query_prelude = 
            env_decls
            @label_prefix
            @qdecls in
        let qry = Term.Assume(mkNot phi, Some "query") in
        let suffix = label_suffix@[Term.Echo "Done!"]  in
        query_prelude, labels, qry, suffix in
    begin match qry with 
        | Assume({tm=False}, _) -> pop(); ()
        | _ when tcenv.admit -> pop(); ()
        | Assume(q, _) ->
            let fresh = String.length q.as_str >= 2048 in   
            Z3.giveZ3 prefix;

            let with_fuel (n, i) = 
                [Term.Caption (Util.format1 "<fuel='%s'>" (string_of_int n)); 
                    Term.Assume(mkEq(mkFreeV("MaxFuel", Fuel_sort), n_fuel n), None);
                    Term.Assume(mkEq(mkFreeV("MaxIFuel", Fuel_sort), n_fuel i), None);
                    qry;
                    Term.CheckSat]@suffix in
    
            let check () =
                let initial_config = (!Options.initial_fuel, !Options.initial_ifuel) in
                let alt_configs = List.flatten [(if !Options.max_ifuel > !Options.initial_ifuel then [(!Options.initial_fuel, !Options.max_ifuel)] else []);
                                                (if !Options.max_fuel / 2 > !Options.initial_fuel then [(!Options.max_fuel / 2, !Options.max_ifuel)] else []);
                                                (if !Options.max_fuel > !Options.initial_fuel && !Options.max_ifuel > !Options.initial_ifuel then [(!Options.max_fuel, !Options.max_ifuel)] else []);
                                                (if !Options.min_fuel < !Options.initial_fuel then [(!Options.min_fuel, 1)] else [])] in

                let report (ok, errs) = 
                    if ok then () 
                    else let errs = match errs with 
                            | [] -> [("Unknown assertion failed", dummyRange)]
                            | _ -> errs in 
                            Tc.Errors.add_errors tcenv errs in

                let rec try_alt_configs errs = function 
                    | [] -> report (false, errs)
                    | [mi] -> 
                        begin match errs with 
                        | [] -> Z3.ask fresh labels (with_fuel mi) (cb [])
                        | _ -> report (false, errs)
                        end

                    | mi::tl -> 
                        Z3.ask fresh labels (with_fuel mi) (fun (ok, errs') -> 
                        match errs with 
                            | [] -> cb tl (ok, errs')  
                            | _ -> cb tl (ok, errs))

                and cb alt (ok, errs) = if ok then () else try_alt_configs errs alt in
                Z3.ask fresh labels (with_fuel initial_config) (cb alt_configs)  in
            if !Options.admit_smt_queries then () else check ();
            pop ()
    end

let is_trivial (tcenv:Tc.Env.env) (q:typ) : bool = 
   let env = get_env tcenv in
   push "query";
   let f, _, _, _ = encode_formula_with_labels q env in
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
    is_trivial=is_trivial;
    finish=Z3.finish;
    refresh=Z3.refresh;
}
let dummy = {
    init=(fun _ -> ());
    push=(fun _ -> ());
    pop=(fun _ -> ());
    encode_sig=(fun _ _ -> ());
    encode_modul=(fun _ _ -> ());
    solve=(fun _ _ -> ());
    is_trivial=(fun _ _ -> false);
    finish=(fun () -> ());
    refresh=(fun () -> ());
}


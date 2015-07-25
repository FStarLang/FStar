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

open Microsoft.FStar.ToSMT.SplitQueryCases

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
let mk_data_tester env l x = Term.mk_tester (escape l.str) x
(* ------------------------------------ *)
(* New name generation *)
type varops_t = {
    push: unit -> unit;
    pop: unit -> unit;
    mark: unit -> unit;
    reset_mark: unit -> unit;
    commit_mark: unit -> unit;
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
    let mark () = push () in
    let reset_mark () = pop () in
    let commit_mark () = match !scopes with 
        | (hd1, hd2)::(next1, next2)::tl -> 
          Util.smap_fold hd1 (fun key value v  -> Util.smap_add next1 key value) ();
          Util.smap_fold hd2 (fun key value v  -> Util.smap_add next2 key value) ();
          scopes := (next1, next2)::tl
        | _ -> failwith "Impossible" in
    {push=push;
     pop=pop;
     mark=mark;
     reset_mark=reset_mark;
     commit_mark=commit_mark;
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
    | Binding_fvar  of lident * string * option<term> * option<term> (* free variables, depending on whether or not they are fully applied ...  *)
    | Binding_ftvar of lident * string * option<term>                (* ... are mapped either to SMT2 functions, or to nullary term/type tokens *)

let binder_of_eithervar v = (v, None)
type env_t = {
    bindings:list<binding>;
    depth:int; //length of local var/tvar bindings
    tcenv:Env.env;
    warn:bool;
    cache:Util.smap<(string * list<sort> * list<decl>)>;
    nolabels:bool;
    use_zfuel_name:bool;
    encode_non_total_function_typ:bool;
}
let print_env e = 
    e.bindings |> List.map (function 
        | Binding_var  (x, t) -> Print.strBvd x
        | Binding_tvar (a, t) -> Print.strBvd a
        | Binding_fvar (l, s, t, _) -> Print.sli l
        | Binding_ftvar(l, s, t) -> Print.sli l) |> String.concat ", "

let lookup_binding env f = Util.find_map env.bindings f 
              
let caption_t env t = 
    if Tc.Env.debug env.tcenv Options.Low
    then Some (Print.typ_to_string t)
    else None

let fresh_fvar x s = let xsym = varops.fresh x in xsym, mkFreeV(xsym, s)
(* generate terms corresponding to a variable and record the mapping in the environment *)

(* Bound term variables *)
let gen_term_var (env:env_t) (x:bvvdef) = 
    let ysym = "@x"^(string_of_int env.depth) in
    let y = mkFreeV(ysym, Term_sort) in
    ysym, y, {env with bindings=Binding_var(x, y)::env.bindings; depth=env.depth + 1}
let new_term_constant (env:env_t) (x:bvvdef) = 
    let ysym = varops.new_var x.ppname x.realname in 
    let y = mkApp(ysym, []) in
    ysym, y, {env with bindings=Binding_var(x, y)::env.bindings}
let push_term_var (env:env_t) (x:bvvdef) (t:term) = 
    {env with bindings=Binding_var(x,t)::env.bindings}
let lookup_term_var env a = 
    match lookup_binding env (function Binding_var(b, t) when Util.bvd_eq b a.v -> Some (b,t) | _ -> None) with
    | None -> failwith (format1 "Bound term variable not found: %s" (Print.strBvd a.v))
    | Some (b,t) -> t

(* Bound type variables *)
let gen_typ_var (env:env_t) (x:btvdef) = 
    let ysym = "@a"^(string_of_int env.depth) in
    let y = mkFreeV(ysym, Type_sort) in
    ysym, y, {env with bindings=Binding_tvar(x, y)::env.bindings; depth=env.depth + 1}
let new_typ_constant (env:env_t) (x:btvdef) = 
    let ysym = varops.new_var x.ppname x.realname in 
    let y = mkApp(ysym, []) in
    ysym, y, {env with bindings=Binding_tvar(x,y)::env.bindings}
let push_typ_var (env:env_t) (x:btvdef) (t:term) = 
    {env with bindings=Binding_tvar(x,t)::env.bindings}
 let lookup_typ_var env a = 
   match lookup_binding env (function Binding_tvar(b, t) when Util.bvd_eq b a.v -> Some (b,t) | _ -> None) with 
    | None -> failwith (format1 "Bound type variable not found: %s" (Print.strBvd a.v))
    | Some (b,t) -> t

(* Qualified term names *)
let new_term_constant_and_tok_from_lid (env:env_t) (x:lident) =
    let fname = varops.new_fvar x in
    let ftok = fname^"@tok" in
    fname, ftok, {env with bindings=Binding_fvar(x, fname, Some <| mkApp(ftok,[]), None)::env.bindings}
let try_lookup_lid env a = 
    lookup_binding env (function Binding_fvar(b, t1, t2, t3) when lid_equals b a -> Some (t1, t2, t3) | _ -> None) 
let lookup_lid env a = 
    match try_lookup_lid env a with
    | None -> failwith (format1 "Name not found: %s" (Print.sli a))
    | Some s -> s
let push_free_var env (x:lident) fname ftok = 
    {env with bindings=Binding_fvar(x, fname, ftok, None)::env.bindings}
let push_zfuel_name env (x:lident) f = 
    let t1, t2, _ = lookup_lid env x in
    let t3 = Term.mkApp(f, [Term.mkApp("ZFuel", [])]) in
    {env with bindings=Binding_fvar(x, t1, t2, Some t3)::env.bindings}
let lookup_free_var env a =
    let name, sym, zf_opt = lookup_lid env a.v in
    match zf_opt with 
        | Some f when (env.use_zfuel_name) -> f
        | _ -> 
          match sym with 
            | Some t -> 
                begin match t.tm with 
                    | App(_, [fuel]) -> 
                        if (Util.starts_with (Term.fv_of_term fuel |> fst) "fuel") 
                        then Term.mk_ApplyEF(Term.mkFreeV (name, Term_sort)) fuel
                        else t
                    | _ -> t
                end
            | _ -> failwith (format1 "Name not found: %s" (Print.sli a.v))
let lookup_free_var_name env a = let x, _, _ = lookup_lid env a.v in x
let lookup_free_var_sym env a = 
    let name, sym, zf_opt = lookup_lid env a.v in
    match zf_opt with 
        | Some({tm=App(g, zf)}) when env.use_zfuel_name -> g, zf
        | _ -> 
            match sym with 
                | None -> Var name, []
                | Some sym -> 
                    match sym.tm with 
                        | App(g, [fuel]) -> g, [fuel]
                        | _ -> Var name, []

(* Qualified type names *)
let new_typ_constant_and_tok_from_lid (env:env_t) (x:lident) =
    let fname = varops.new_fvar x in
    let ftok = fname^"@tok" in
    fname, ftok, {env with bindings=Binding_ftvar(x, fname, Some <| mkApp(ftok, []))::env.bindings}
let lookup_tlid env a = 
    match lookup_binding env (function Binding_ftvar(b, t1, t2) when lid_equals b a -> Some (t1, t2) | _ -> None) with
    | None -> failwith (format1 "Type name not found: %s" (Print.sli a))
    | Some s -> s
let push_free_tvar env (x:lident) fname ftok = 
    {env with bindings=Binding_ftvar(x, fname, ftok)::env.bindings}
let lookup_free_tvar env a = 
    match lookup_tlid env a.v |> snd with 
        | None -> failwith (format1 "Type name not found: %s" (Print.sli a.v))
        | Some t -> t
let lookup_free_tvar_name env a = lookup_tlid env a.v |> fst

let tok_of_name env nm = 
    Util.find_map env.bindings (function 
        | Binding_fvar(_, nm', tok, _) 
        | Binding_ftvar(_, nm', tok) when (nm=nm') -> tok
        | _ -> None)

(* </Environment> *)
(*---------------------------------------------------------------------------------*)
(* <Utilities> *)

let mkForall_fuel' n (pats, vars, body) = 
    let fallback () = Term.mkForall(pats, vars, body) in
    if !Options.unthrottle_inductives
    then fallback ()
    else let fsym, fterm = fresh_fvar "f" Fuel_sort in 
         let pats = pats |> List.map (fun p -> match p.tm with 
            | Term.App(Var "HasType", args) -> Term.mkApp("HasTypeFuel", fterm::args)
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
            | Type_sort -> mk_ApplyET out (Term.mkFreeV var)
            | Fuel_sort -> mk_ApplyEF out (Term.mkFreeV var)
            | _ -> mk_ApplyEE out (Term.mkFreeV var)) e
let mk_ApplyE_args e args = 
    args |> List.fold_left (fun out arg -> match arg with 
            | Inl t -> mk_ApplyET out t
            | Inr e -> mk_ApplyEE out e) e

let mk_ApplyT t vars = 
    vars |> List.fold_left (fun out var -> match snd var with 
            | Type_sort -> mk_ApplyTT out (Term.mkFreeV var)
            | _ -> mk_ApplyTE out (Term.mkFreeV var)) t
let mk_ApplyT_args t args = 
    args |> List.fold_left (fun out arg -> match arg with 
            | Inl t -> mk_ApplyTT out t
            | Inr e -> mk_ApplyTE out e) t
let is_app = function 
    | Var "ApplyTT"
    | Var "ApplyTE"
    | Var "ApplyET"
    | Var "ApplyEE" -> true
    | _ -> false

let is_eta env vars t = 
    let rec aux t xs = match t.tm, xs with 
        | App(app, [f; {tm=FreeV y}]), x::xs 
          when (is_app app && Term.fv_eq x y) -> aux f xs
        | App(Var f, args), _ -> 
          if List.length args = List.length vars 
          && List.forall2 (fun a v -> match a.tm with 
            | FreeV fv -> fv_eq fv v
            | _ -> false) args vars
          then tok_of_name env f 
          else None
        | _, [] -> 
          let fvs = Term.free_variables t in
          if fvs |> List.for_all (fun fv -> not (Util.for_some (fv_eq fv) vars)) //t doesn't contain any of the bound variables
          then Some t
          else None
        | _ -> None in
  aux t (List.rev vars)

            

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

type label = (fv * string * Range.range)
type labels = list<label>
type pattern = {
  pat_vars: list<(Syntax.either_var * fv)>;
  pat_term: unit -> (term * decls_t);                   (* the pattern as a term(exp) *)
  guard: term -> term;                                  (* the guard condition of the pattern, as applied to a particular scrutinee term(exp) *)
  projections: term -> list<(either_var * term)>        (* bound variables of the pattern, and the corresponding projected components of the scrutinee *)
 }
exception Let_rec_unencodeable 

let encode_const = function 
    | Const_unit -> mk_Term_unit
    | Const_bool true -> boxBool mkTrue
    | Const_bool false -> boxBool mkFalse
    | Const_char c -> boxInt (mkInteger' (Util.int_of_char c))
    | Const_uint8 i -> boxInt (mkInteger' (Util.int_of_uint8 i))
    | Const_int i  -> boxInt (mkInteger i)
    | Const_int32 i -> Term.mkApp("Int32.Int32", [boxInt (mkInteger' i)])
    | Const_string(bytes, _) -> varops.string_const (Util.string_of_bytes <| bytes)
    | c -> failwith (Util.format1 "Unhandled constant: %s\n" (Print.const_to_string c))
 
let as_function_typ env t0 = 
    let rec aux norm t =
        let t = Util.compress_typ t in
        match t.n with 
            | Typ_fun _ -> t
            | Typ_refine _ -> aux true (Util.unrefine t)
            | _ -> if norm 
                   then aux false (whnf env t) 
                   else failwith (Util.format2 "(%s) Expected a function typ; got %s" (Range.string_of_range t0.pos) (Print.typ_to_string t0))
    in aux true t0

let rec encode_knd_term (k:knd) (env:env_t) : (term * decls_t) = 
    match (Util.compress_kind k).n with 
        | Kind_type -> Term.mk_Kind_type, []

        | Kind_abbrev(_, k0) ->
          if Tc.Env.debug env.tcenv (Options.Other "Encoding")
          then Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" (Print.kind_to_string k) (Print.kind_to_string k0);
          encode_knd_term k0 env

        | Kind_uvar (uv, _) -> (* REVIEW: warn? *)
          Term.mk_Kind_uvar (Unionfind.uvar_id uv), []

        | Kind_arrow(bs, kbody) -> 
          let tsym = varops.fresh "t", Type_sort in
          let t = mkFreeV tsym in
          let vars, guards, env', decls, _ = encode_binders None bs env in 
          let app = mk_ApplyT t vars in
          let kbody, decls' = encode_knd kbody env' app in
          //this gives kinds to every partial application of t
          let rec aux app vars guards = match vars, guards with 
            | [], [] -> kbody
            | x::vars, g::guards -> 
              let app = mk_ApplyT app [x] in
              let body = aux app vars guards in
              let body = match vars with 
                | [] -> body 
                | _ -> Term.mkAnd(mk_tester "Kind_arrow" (mk_PreKind app), body) in
              Term.mkForall([app], [x], mkImp(g, body))
              
            | _ -> failwith "Impossible: vars and guards are in 1-1 correspondence" in
          let k_interp = aux t vars guards in
          let cvars = Term.free_variables k_interp |> List.filter (fun (x, _) -> x <> fst tsym) in
          let tkey = Term.mkForall([], tsym::cvars, k_interp) in
          begin match Util.smap_try_find env.cache tkey.hash with 
                | Some (k', sorts, _) ->  
                  Term.mkApp(k', cvars |> List.map mkFreeV), []

                | None -> 
                  let ksym = varops.fresh "Kind_arrow" in
                  let cvar_sorts = List.map snd cvars in
                  let caption = 
                    if !Options.logQueries
                    then Some (Normalize.kind_norm_to_string env.tcenv k)
                    else None in


                  let kdecl = Term.DeclFun(ksym, cvar_sorts, Kind_sort, caption) in
                
                  let k = Term.mkApp(ksym, List.map mkFreeV cvars) in
                  let t_has_k = mk_HasKind t k in
                  let k_interp = Term.Assume(mkForall([t_has_k], tsym::cvars, 
                                                      mkIff(t_has_k, 
                                                            mkAnd(mk_tester "Kind_arrow" (mk_PreKind t),
                                                                  k_interp))),
                                             Some (ksym ^ " interpretation")) in 

                  let k_decls = decls@decls'@[kdecl; k_interp] in
                  Util.smap_add env.cache tkey.hash  (ksym, cvar_sorts, k_decls);
                  k, k_decls
          end

        | _ -> failwith (Util.format1 "Unknown kind: %s" (Print.kind_to_string k))


and encode_knd (k:knd) (env:env_t) (t:term) = 
    let k, decls = encode_knd_term k env in
    mk_HasKind t k, decls

and encode_binders (fuel_opt:option<term>) (bs:Syntax.binders) (env:env_t) : 
                            (list<fv>                       (* translated bound variables *)
                            * list<term>                    (* guards *)
                            * env_t                         (* extended context *)
                            * decls_t                       (* top-level decls to be emitted *)
                            * list<either<btvdef, bvvdef>>) (* unmangled names *) =

    if Tc.Env.debug env.tcenv Options.Low then Util.fprint1 "Encoding binders %s\n" (Print.binders_to_string ", " bs);
    
    let vars, guards, env, decls, names = bs |> List.fold_left (fun (vars, guards, env, decls, names) b -> 
        let v, g, env, decls', n = match fst b with 
            | Inl {v=a; sort=k} -> 
                let a = unmangle a in
                let aasym, aa, env' = gen_typ_var env a in 
                if Tc.Env.debug env.tcenv (Options.Other "Encoding") 
                then Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" (Print.strBvd a) aasym (Print.kind_to_string k);
                let guard_a_k, decls' = encode_knd k env aa in //encode_knd' false k env aa in
                (aasym, Type_sort), 
                guard_a_k,
                env', 
                decls',
                Inl a  

            | Inr {v=x; sort=t} -> 
                let x = unmangle x in
                let xxsym, xx, env' = gen_term_var env x in
                let guard_x_t, decls' = encode_typ_pred' fuel_opt (norm_t env t) env xx in
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

and encode_typ_pred' (fuel_opt:option<term>) (t:typ) (env:env_t) (e:term) : term * decls_t = 
    let t = Util.compress_typ t in 
    let t, decls = encode_typ_term t env in 
    mk_HasTypeWithFuel fuel_opt e t, decls

and encode_typ_term (t:typ) (env:env_t) : (term           (* encoding of t, expects t to be in normal form already *)
                                           * decls_t)     (* top-level declarations to be emitted (for shared representations of existentially bound terms *) = 
    let t0 = Util.compress_typ t in
    match t0.n with 
      | Typ_btvar a -> 
        lookup_typ_var env a, []
        
      | Typ_const fv -> 
        lookup_free_tvar env fv, []

      | Typ_fun(binders, res) -> 
        (* TODO: handling non-total functions *)
        if  (env.encode_non_total_function_typ 
             && Absyn.Util.is_pure_or_ghost_comp res)
             || Absyn.Util.is_tot_or_gtot_comp res
        then let vars, guards, env', decls, _ = encode_binders None binders env in 
             let fsym = varops.fresh "f", Term_sort in
             let f = mkFreeV fsym in
             let app = mk_ApplyE f vars in  
             let pre_opt, res_t = Tc.Util.pure_or_ghost_pre_and_post env.tcenv res in
             let res_pred, decls' = encode_typ_pred' None res_t env' app in
             let guards, guard_decls = match pre_opt with 
                | None -> mk_and_l guards, decls
                | Some pre -> 
                  let guard, decls0 = encode_formula pre env' in
                  mk_and_l (guard::guards), decls@decls0  in
             let t_interp = 
                       mkForall([app], 
                                vars,  
                                mkImp(guards, res_pred)) in
                   
             let cvars = Term.free_variables t_interp |> List.filter (fun (x, _) -> x <> fst fsym) in
             let tkey = Term.mkForall([], fsym::cvars, t_interp) in
             begin match Util.smap_try_find env.cache tkey.hash with 
                | Some (t', sorts, _) ->  
                  Term.mkApp(t', cvars |> List.map mkFreeV), []

                | None -> 
                  let tsym = varops.fresh "Typ_fun" in
                  let cvar_sorts = List.map snd cvars in
                  let caption = 
                    if !Options.logQueries
                    then Some (Normalize.typ_norm_to_string env.tcenv t0)
                    else None in

                  let tdecl = Term.DeclFun(tsym, cvar_sorts, Type_sort, caption) in
 
                  let t = Term.mkApp(tsym, List.map mkFreeV cvars) in
                  let t_has_kind = mk_HasKind t Term.mk_Kind_type in
 
                  let k_assumption = Term.Assume(Term.mkForall([t_has_kind], cvars, t_has_kind), Some (tsym ^ " kinding")) in

                  let f_has_t = mk_HasType f t in
                  let pre_typing = Term.Assume(mkForall_fuel([f_has_t], fsym::cvars, mkImp(f_has_t, mk_tester "Typ_fun" (mk_PreType f))), Some "pre-typing for functions") in
                  let t_interp = Term.Assume(mkForall_fuel([f_has_t], fsym::cvars, mkIff(f_has_t, t_interp)),
                                             Some (tsym ^ " interpretation")) in 

                  let t_decls = decls@decls'@[tdecl; k_assumption; pre_typing; t_interp] in
                  Util.smap_add env.cache tkey.hash  (tsym, cvar_sorts, t_decls);
                  t, t_decls
             end

        else let tsym = varops.fresh "Non_total_Typ_fun" in
             let tdecl = Term.DeclFun(tsym, [], Type_sort, None) in
             let t = Term.mkApp(tsym, []) in
             let t_kinding = Term.Assume(mk_HasKind t Term.mk_Kind_type, None) in
             let fsym = "f", Term_sort in
             let f = mkFreeV fsym in
             let f_has_t = mk_HasType f t in
             let t_interp = Term.Assume(mkForall_fuel([f_has_t], [fsym],
                                                      mkImp(f_has_t, 
                                                            mk_tester "Typ_fun" (mk_PreType f))), Some "pre-typing") in 
             
             t, [tdecl; t_kinding; t_interp] (* TODO: At least preserve alpha-equivalence of non-pure function types *)
      
      | Typ_refine _ -> 
        let x, f = match Tc.Normalize.normalize_refinement env.tcenv t0 with 
            | {n=Typ_refine(x, f)} -> x, f
            | _ -> failwith "impossible" in

        let base_t, decls = encode_typ_term x.sort env in
        let x, xtm, env' = gen_term_var env x.v in
        let refinement, decls' = encode_formula f env' in
        let encoding = Term.mkAnd(mk_HasType xtm base_t, refinement) in

        let cvars = Term.free_variables encoding |> List.filter (fun (y, _) -> y <> x) in 
        let xfv = (x, Term_sort) in
        let tkey = Term.mkForall([], xfv::cvars, encoding) in

        begin match Util.smap_try_find env.cache tkey.hash with 
            | Some (t, _, _) -> 
              Term.mkApp(t, cvars |> List.map mkFreeV), []

            | None -> 
              let tsym = varops.fresh "Typ_refine" in
              let cvar_sorts = List.map snd cvars in 
              let tdecl = Term.DeclFun(tsym, cvar_sorts, Type_sort, None) in
              let t = Term.mkApp(tsym, List.map mkFreeV cvars) in

              let x_has_t = mk_HasType xtm t in
              let t_has_kind = mk_HasKind t Term.mk_Kind_type in
              
              let t_kinding = mkForall([t_has_kind], cvars, t_has_kind) in //TODO: guard by typing of cvars?; not necessary since we have pattern-guarded 
              let assumption = mkForall_fuel([x_has_t], xfv::cvars, mkIff(x_has_t, encoding)) in
              
              let t_decls = decls
                            @decls'
                            @[tdecl;
                              Term.Assume(t_kinding, None);
                              Term.Assume(assumption, Some (Print.typ_to_string t0))] in
              Util.smap_add env.cache tkey.hash (tsym, cvar_sorts, t_decls);
              t, t_decls
        end 

      | Typ_uvar (uv, k) ->
        let ttm = Term.mk_Typ_uvar (Unionfind.uvar_id uv) in
        let t_has_k, decls = encode_knd k env ttm in //TODO: skip encoding this if it has already been encoded before
        let d = Term.Assume(t_has_k, None) in
        ttm, d::decls

      | Typ_app(head, args) -> 
        let is_full_app () = 
            let kk = Tc.Recheck.recompute_kind head in //so, this should be very cheap to recompute
            let formals, _ = Util.kind_formals kk in
            List.length formals = List.length args in
        let head = Util.compress_typ head in
        begin match head.n with
            | Typ_btvar a -> 
              let head = lookup_typ_var env a in
              let args, decls = encode_args args env in
              let t = mk_ApplyT_args head args in
              t, decls
                
            | Typ_const fv -> 
              let args, decls = encode_args args env in
              if is_full_app () 
              then let head = lookup_free_tvar_name env fv in
                   let t = Term.mkApp(head, List.map (function Inl t | Inr t -> t) args) in
                   t, decls
              else let head = lookup_free_tvar env fv in
                   let t = mk_ApplyT_args head args in
                   t, decls

            | Typ_uvar(uv, k) -> 
               let ttm = Term.mk_Typ_uvar (Unionfind.uvar_id uv) in
               let t_has_k, decls = encode_knd k env ttm in //TODO: skip encoding this if it has already been encoded before
               let d = Term.Assume(t_has_k, None) in
               ttm, d::decls  

            | _ -> (* not in head normal form; so reduce and retry *)
              let t = norm_t env t in
              (* CH: WARNING: if norm_t returns the same type it got as input
                     this code enters infinite loop (as it happened with uvars);
                     might want to do something about this!? *)
              encode_typ_term t env
        end

      | Typ_lam(bs, body) ->
        let vars, guards, env, decls, _ = encode_binders None bs env in
        let body, decls' = encode_typ_term body env in
        
        let key_body = mkForall([], vars, mkImp(mk_and_l guards, body)) in
        let cvars = Term.free_variables key_body in
        let tkey = mkForall([], cvars, key_body) in

        begin match Util.smap_try_find env.cache tkey.hash with 
            | Some (t, _, _) -> 
              mkApp(t, List.map mkFreeV cvars), []

            | None -> 
                   //First, try to collapse needless eta-expansions
              begin match is_eta env vars body with 
                | Some head -> head, []
                | None -> 
                  //Otherwise, introduce a new function symbol 
                  let cvar_sorts = List.map snd cvars in
                  let tsym = varops.fresh "Typ_lam" in
                  let tdecl = Term.DeclFun(tsym, cvar_sorts, Type_sort, None) in
                  let t = Term.mkApp(tsym, List.map mkFreeV cvars) in
                  let app = mk_ApplyT t vars in

                  let interp = Term.Assume(mkForall([app], vars@cvars, mkImp(mk_and_l guards, mkEq(app,body))), 
                                           Some "Typ_lam interpretation") in
        
                  let kinding =    
                    let ktm, decls'' = encode_knd (Tc.Recheck.recompute_kind t0) env t in
                    decls''@[Term.Assume(mkForall([t], cvars, ktm), Some "Typ_lam kinding")] in

                  let t_decls = decls@decls'@tdecl::interp::kinding in 

                  Util.smap_add env.cache tkey.hash (tsym, cvar_sorts, t_decls);
                  t, t_decls
             end
        end

      | Typ_ascribed(t, _) -> 
        encode_typ_term t env

      | Typ_meta _ -> 
        encode_typ_term (Util.unmeta_typ t0) env

      | Typ_delayed  _ 
      | Typ_unknown    -> failwith (format4 "(%s) Impossible: %s\n%s\n%s\n" (Range.string_of_range <| t.pos) (Print.tag_of_typ t0) (Print.typ_to_string t0) (Print.typ_to_string t))                 

and encode_exp (e:exp) (env:env_t) : (term 
                                      * decls_t) = 
    let e = Visit.compress_exp_uvars e in 
    let e0 = e in
    match e.n with 
      | Exp_delayed _ -> (* REVIEW: dead code? *)
        encode_exp (Util.compress_exp e) env

      | Exp_bvar x -> 
        let t = lookup_term_var env x in
        t, []

      | Exp_fvar(v, _) -> 
        lookup_free_var env v, []

      | Exp_constant c -> 
        encode_const c, []
      
      | Exp_ascribed(e, t, _) -> 
        e.tk := Some t;
        encode_exp e env

      | Exp_meta(Meta_desugared(e, _)) -> 
        encode_exp e env

      | Exp_uvar(uv, _) ->
        (* TODO: typing axiom for uvar? *)
        let e = Term.mk_Exp_uvar (Unionfind.uvar_id uv) in
        e, []
 
      | Exp_abs(bs, body) -> 
        let fallback () =
            let f = varops.fresh "Exp_abs" in
            let decl = Term.DeclFun(f, [], Term_sort, None) in
            Term.mkFreeV(f, Term_sort), [decl] in

        begin match !e.tk with 
            | None ->
              Tc.Errors.warn e.pos ("Losing precision when encoding a function literal");
              fallback ()
            | Some tfun -> 
            if not <| Util.is_pure_or_ghost_function tfun
            then fallback ()
            else let tfun = as_function_typ env tfun in 
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

                        else //much like the encoding of Typ_lam
                             let vars, guards, envbody, decls, _ = encode_binders None bs env in 
                             let body, decls' = encode_exp body envbody in
                         
                             let key_body = mkForall([], vars, mkImp(mk_and_l guards, body)) in
                             let cvars = Term.free_variables key_body in
                             let tkey = mkForall([], cvars, key_body) in

                             begin match Util.smap_try_find env.cache tkey.hash with 
                                | Some (t, _, _) -> 
                                  Term.mkApp(t, List.map mkFreeV cvars), []

                                | None -> 
                                  begin match is_eta env vars body with 
                                    | Some t -> 
                                      t, []
                                    | None -> 
                                      let cvar_sorts = List.map snd cvars in
                                      let fsym = varops.fresh "Exp_abs" in
                                      let fdecl = Term.DeclFun(fsym, cvar_sorts, Term_sort, None) in
                                      let f = Term.mkApp(fsym, List.map mkFreeV cvars) in
                                      let app = mk_ApplyE f vars in

                                      let f_has_t, decls'' = encode_typ_pred' None tfun env f in
                                      let typing_f = Term.Assume(Term.mkForall([f], cvars, f_has_t), 
                                                                Some (fsym ^ " typing")) in 
                         
                                      let interp_f = Term.Assume(Term.mkForall([app], vars@cvars, mkImp(Term.mk_IsTyped app, mkEq(app, body))), 
                                                                Some (fsym ^ " interpretation")) in

                                      let f_decls = decls@decls'@(fdecl::decls'')@[typing_f;interp_f] in
                              
                                      Util.smap_add env.cache tkey.hash (fsym, cvar_sorts, f_decls);

                                      f, f_decls
                                end
                            end

                  | _ -> failwith "Impossible"
                end
            end
      | Exp_app({n=Exp_fvar(l, _)}, [(Inl _, _); (Inr v1, _); (Inr v2, _)]) when (lid_equals l.v Const.lexcons_lid) -> 
         let v1, decls1 = encode_exp v1 env in 
         let v2, decls2 = encode_exp v2 env in
         Term.mk_LexCons v1 v2, decls1@decls2

      | Exp_app({n=Exp_abs _}, _) -> 
        encode_exp (whnf_e env e) env

      | Exp_app(head, args_e) -> 
        let args, decls = encode_args args_e env in
    
        let encode_partial_app ht_opt = 
            let head, decls' = encode_exp head env in
            let app_tm = mk_ApplyE_args head args in
            begin match ht_opt with
                | None -> app_tm, decls@decls'
                | Some (formals, c) ->
                  let formals, rest = Util.first_N (List.length args_e) formals in
                  let subst = Util.formals_for_actuals formals args_e in
                  let ty = mk_Typ_fun(rest, c) (Some ktype) e0.pos |> Util.subst_typ subst in
                  let has_type, decls'' = encode_typ_pred' None ty env app_tm in
                  let cvars = Term.free_variables has_type in
                  let e_typing = Term.Assume(Term.mkForall([has_type], cvars, has_type), None) in
                  app_tm, decls@decls'@decls''@[e_typing]
            end in

        let encode_full_app fv = 
            let fname, fuel_args = lookup_free_var_sym env fv in
            let tm = Term.mkApp'(fname, fuel_args@List.map (function Inl t | Inr t -> t) args) in
            tm, decls in
        
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
        
      | Exp_let((false, [{lbname=Inr _}]), _) -> failwith "Impossible: already handled by encoding of Sig_let" 

      | Exp_let((false, [{lbname=Inl x; lbtyp=t1; lbdef=e1}]), e2) ->
        let ee1, decls1 = encode_exp e1 env in
        let env' = push_term_var env x ee1 in
        let ee2, decls2 = encode_exp e2 env' in
        ee2, decls1@decls2 
  
      | Exp_let _ -> 
        Tc.Errors.warn e.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
        let e = varops.fresh "let-rec" in
        let decl_e = Term.DeclFun(e, [], Term_sort, None) in
        Term.mkFreeV(e, Term_sort), [decl_e]

      | Exp_match(e, pats) ->
        let scr, decls = encode_exp e env in 


        let match_tm, decls = List.fold_right (fun (p, w, br) (else_case, decls) -> 
            let patterns = encode_pat env p in
            List.fold_right (fun (env0, pattern) (else_case, decls) -> 
                let guard = pattern.guard scr in
                let projections = pattern.projections scr in
                let env = projections |> List.fold_left (fun env (x, t) -> match x with 
                    | Inl a -> push_typ_var env a.v t
                    | Inr x -> push_term_var env x.v t) env in
                let guard, decls2 = match w with 
                    | None -> guard, []
                    | Some w -> 
                        let w, decls2 = encode_exp w env in
                        Term.mkAnd(guard, Term.mkEq(w, Term.boxBool Term.mkTrue)), decls2 in
                let br, decls3 = encode_exp br env in
                mkITE(guard, br, else_case), decls@decls2@decls3)
            patterns (else_case, decls))
            pats 
            (Term.mk_Term_unit(* default; should be unreachable *), decls) in
        match_tm, decls

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

and encode_args l env : (list<either<term,term>> * decls_t)  =
    let l, decls = l |> List.fold_left (fun (tms, decls) x -> match x with
        | Inl t, _ -> let t, decls' = encode_typ_term t env in Inl t::tms, decls@decls'
        | Inr e, _ -> let t, decls' = encode_exp e env in Inr t::tms, decls@decls') ([], []) in
    List.rev l, decls

and encode_formula (phi:typ) (env:env_t) : term * decls_t = 
    let t, vars, decls = encode_formula_with_labels phi env in
    match vars with
        | [] -> t, decls
        | _ -> failwith "Unexpected labels in formula"
  
and encode_function_type_as_formula (induction_on:option<term>) (t:typ) (env:env_t) : term * decls_t = 
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
  
    let vars, guards, env, decls, _ = encode_binders None binders env in 
   

    let pats, decls' = patterns |> List.map (function 
        | Inl t, _ -> encode_formula t env
        | Inr e, _ -> encode_exp e ({env with use_zfuel_name=true})) |> List.unzip in 
  
  
    let pats = 
        match induction_on with 
            | None -> pats
            | Some e -> 
               begin match vars with 
                | [] -> pats
                | [l] -> Term.mk_Precedes (Term.mkFreeV l) e::pats
                | _ -> 
                  let rec aux tl vars = match vars with
                    | [] -> Term.mk_Precedes tl e::pats
                    | (x, Term_sort)::vars -> aux (Term.mk_LexCons (Term.mkFreeV(x,Term_sort)) tl) vars
                    | _ -> pats in
                  aux (Term.mkFreeV ("Prims.LexTop", Term_sort)) vars 
               end in
               
    let env = {env with nolabels=true} in
    let pre, decls'' = encode_formula (Util.unmeta_typ pre) env in
    let post, decls''' = encode_formula (Util.unmeta_typ post) env in
    let decls = decls@(List.flatten decls')@decls''@decls''' in 
    mkForall(pats, vars, mkImp(mk_and_l (pre::guards), post)), decls

and encode_formula_with_labels (phi:typ) (env:env_t) : (term * labels * decls_t)  = (* expects phi to be normalized; the existential variables are all labels *)
    let enc (f:list<term> -> term) : args -> (term * labels * decls_t) = fun l -> 
        let decls, args = Util.fold_map (fun decls x -> match fst x with 
            | Inl t -> let t, decls' = encode_typ_term t env in decls@decls', t
            | Inr e -> let e, decls' = encode_exp e env in decls@decls', e) [] l in
        (f args, [], decls) in

    let enc_prop_c f : args -> (term * labels * decls_t) = fun l ->
        let phis, labs, decls = 
            List.fold_right (fun t (phis, labs, decls) -> 
                match fst t with 
                | Inl t -> 
                    let phi, labs', decls' = encode_formula_with_labels t env in
                    (phi::phis, labs'@labs, decls'@decls)
                | _ -> failwith "Expected a formula") 
                l ([], [], []) in
        (f phis, labs, decls) in
  

    let const_op f _ = (f, [], []) in
    let un_op f l = f <| List.hd l in
    let bin_op : ((term * term) -> term) -> list<term> -> term = fun f -> function 
        | [t1;t2] -> f(t1,t2)
        | _ -> failwith "Impossible" in
    let tri_op : ((term * term * term) -> term) -> list<term> -> term = fun f -> function
        | [t1;t2;t3] -> f(t1,t2,t3)
        | _ -> failwith "Impossible" in
    let eq_op : args -> (term * labels * decls_t) = function 
        | [_;_;e1;e2] -> enc (bin_op mkEq) [e1;e2]
        | l ->  enc (bin_op mkEq) l in
  
    let mk_imp : args -> (term * labels * decls_t) = function 
        | [(Inl lhs, _); (Inl rhs, _)] -> 
          let l1, labs1, decls1 = encode_formula_with_labels rhs env in
          begin match l1.tm with 
            | App(True, _) -> (l1, labs1, decls1) (* Optimization: don't bother encoding the LHS of a trivial implication *)
            | _ -> 
             let l2, labs2, decls2 = encode_formula_with_labels lhs env in
             (Term.mkImp(l2, l1), labs1@labs2, decls1@decls2)
          end
         | _ -> failwith "impossible" in

    let mk_ite : args -> (term * labels * decls_t) = function
        | [(Inl guard, _); (Inl _then, _); (Inl _else, _)] -> 
          let (g, labs1, decls1) = encode_formula_with_labels guard env in
          let (t, labs2, decls2) = encode_formula_with_labels _then env in 
          let (e, labs3, decls3) = encode_formula_with_labels _else env in 
          let res = Term.mkITE(g, t, e) in
          res, labs1@labs2@labs3, decls1@decls2@decls3
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
          let phi, labs, decls = encode_formula_with_labels phi' env in
          if env.nolabels
          then (phi, [], decls)
          else let lvar = varops.fresh "label", Bool_sort in
               let lterm = Term.mkFreeV lvar in
               let lphi = Term.mkOr(lterm, phi) in
               (lphi, (lvar, msg, r)::labs, decls)
        
        | Typ_app({n=Typ_const ih}, [_;(Inr l, _); (Inl phi, _)]) when lid_equals ih.v Const.using_IH -> 
            if Util.is_lemma phi
            then let e, decls = encode_exp l env in
                 let f, decls' = encode_function_type_as_formula (Some e) phi env in
                 (f, [], decls@decls')
            else (Term.mkTrue, [], [])
            
        | _ -> 
            let tt, decls = encode_typ_term phi env in
            Term.mk_Valid tt, [], decls in

    let encode_q_body env (bs:Syntax.binders) (ps:args) body = 
        let vars, guards, env, decls, _ = encode_binders None bs env in
        let pats, decls' = ps |> List.map (function 
            | Inl t, _ -> encode_typ_term t env 
            | Inr e, _ -> encode_exp e ({env with use_zfuel_name=true})) |> List.unzip in 
        let body, labs, decls'' = encode_formula_with_labels body env in
        vars, pats, mk_and_l guards, body, labs, decls@List.flatten decls'@decls'' in
    
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

          let vars, pats, guard, body, labs, decls = encode_q_body env vars pats body in
          (mkForall(pats, vars, mkImp(guard, body)), labs, decls)

        | Some (Util.QEx(vars, pats, body)) -> 
          let vars, pats, guard, body, labs, decls = encode_q_body env vars pats body in
          (mkExists(pats, vars, mkAnd(guard, body)), labs, decls)

(***************************************************************************************************)
(* end main encoding of kinds/types/exps/formulae *)
(***************************************************************************************************)

(* ----------------------------------------------------------------------------------------------- *)

type prims_t = {
    mk:lident -> string -> list<decl>;
    is:lident -> bool;
}


let prims =
    let asym, a = fresh_fvar "a" Type_sort in 
    let xsym, x = fresh_fvar "x" Term_sort in 
    let ysym, y = fresh_fvar "y" Term_sort in 
    let deffun vars body x = [Term.DefineFun(x, vars, Term_sort, body, None)] in     
    let quant vars body : string -> list<decl> = fun x ->
        let t1 = Term.mkApp(x, List.map Term.mkFreeV vars) in 
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
    let x = mkFreeV xx in

    let yy = ("y", Term_sort) in
    let y = mkFreeV yy in

    let mk_unit : string -> term -> decls_t = fun _ tt -> 
        let typing_pred = Term.mk_HasType x tt in
        [Term.Assume(Term.mk_HasType Term.mk_Term_unit tt,    Some "unit typing");
         Term.Assume(mkForall_fuel([typing_pred], [xx], mkImp(typing_pred, mkEq(x, Term.mk_Term_unit))),  Some "unit inversion")] in
    let mk_bool : string -> term -> decls_t = fun _ tt -> 
        let typing_pred = Term.mk_HasType x tt in
        let bb = ("b", Bool_sort) in
        let b = mkFreeV bb in
        [Term.Assume(mkForall_fuel([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxBool" x)),    Some "bool inversion");
         Term.Assume(mkForall([Term.boxBool b], [bb], Term.mk_HasType (Term.boxBool b) tt),    Some "bool typing")] in
    let mk_int : string -> term -> decls_t  = fun _ tt -> 
        let typing_pred = Term.mk_HasType x tt in
        let typing_pred_y = Term.mk_HasType y tt in
        let aa = ("a", Int_sort) in
        let a = mkFreeV aa in
        let bb = ("b", Int_sort) in
        let b = mkFreeV bb in
        let precedes = Term.mk_Valid <| mkApp("Prims.Precedes", [tt;tt;Term.boxInt a; Term.boxInt b]) in
        let precedes_y_x = Term.mk_Valid <| mkApp("Precedes", [y; x]) in
        [Term.Assume(mkForall_fuel([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxInt" x)),    Some "int inversion");
         Term.Assume(mkForall([Term.boxInt b], [bb], Term.mk_HasType (Term.boxInt b) tt),    Some "int typing");
         Term.Assume(mkForall_fuel([typing_pred; typing_pred_y;precedes_y_x], 
                                   [xx;yy], 
                                   mkImp(mk_and_l [typing_pred; 
                                                   typing_pred_y; 
                                                   Term.mkGT (Term.unboxInt x, Term.mkInteger' 0);
                                                   Term.mkGTE (Term.unboxInt y, Term.mkInteger' 0);
                                                   Term.mkLT (Term.unboxInt y, Term.unboxInt x)],
                                         precedes_y_x)),
                                  Some "well-founded ordering on nat (alt)")] in
    let mk_int_alias : string -> term -> decls_t = fun _ tt -> 
        [Term.Assume(mkEq(tt, mkApp(Const.int_lid.str, [])), Some "mapping to int; for now")] in
    let mk_str : string -> term -> decls_t  = fun _ tt -> 
        let typing_pred = Term.mk_HasType x tt in
        let bb = ("b", String_sort) in
        let b = mkFreeV bb in
        [Term.Assume(mkForall_fuel([typing_pred], [xx], mkImp(typing_pred, Term.mk_tester "BoxString" x)),    Some "string inversion");
         Term.Assume(mkForall([Term.boxString b], [bb], Term.mk_HasType (Term.boxString b) tt),    Some "string typing")] in
    let mk_ref : string -> term -> decls_t = fun reft_name _ -> 
        let r = ("r", Ref_sort) in
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let refa = Term.mkApp(reft_name, [mkFreeV aa]) in
        let refb = Term.mkApp(reft_name, [mkFreeV bb]) in
        let typing_pred = Term.mk_HasType x refa in
        let typing_pred_b = Term.mk_HasType x refb in
        [Term.Assume(mkForall_fuel([typing_pred], [xx;aa], mkImp(typing_pred, Term.mk_tester "BoxRef" x)), Some "ref inversion");
         Term.Assume(mkForall_fuel' 2 ([typing_pred; typing_pred_b], [xx;aa;bb], mkImp(mkAnd(typing_pred, typing_pred_b), mkEq(mkFreeV aa, mkFreeV bb))), Some "ref typing is injective")] in

    let mk_false_interp : string -> term -> decls_t = fun _ false_tm -> 
        let valid = Term.mkApp("Valid", [false_tm]) in
        [Term.Assume(mkIff(mkFalse, valid), Some "False interpretation")] in
    let mk_and_interp : string -> term -> decls_t = fun conj _ -> 
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = Term.mkApp("Valid", [Term.mkApp(conj, [a;b])]) in
        let valid_a = Term.mkApp("Valid", [a]) in
        let valid_b = Term.mkApp("Valid", [b]) in
        [Term.Assume(mkForall([valid], [aa;bb], mkIff(mkAnd(valid_a, valid_b), valid)), Some "/\ interpretation")] in
    let mk_or_interp : string -> term -> decls_t = fun disj _ -> 
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = Term.mkApp("Valid", [Term.mkApp(disj, [a;b])]) in
        let valid_a = Term.mkApp("Valid", [a]) in
        let valid_b = Term.mkApp("Valid", [b]) in
        [Term.Assume(mkForall([valid], [aa;bb], mkIff(mkOr(valid_a, valid_b), valid)), Some "\/ interpretation")] in
    let mk_eq2_interp : string -> term -> decls_t = fun eq2 tt -> 
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let xx = ("x", Term_sort) in
        let yy = ("y", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let x = mkFreeV xx in
        let y = mkFreeV yy in
        let valid = Term.mkApp("Valid", [Term.mkApp(eq2, [a;b;x;y])]) in
        [Term.Assume(mkForall([valid], [aa;bb;xx;yy], mkIff(mkEq(x, y), valid)), Some "Eq2 interpretation")] in
    let mk_imp_interp : string -> term -> decls_t = fun imp tt -> 
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = Term.mkApp("Valid", [Term.mkApp(imp, [a;b])]) in
        let valid_a = Term.mkApp("Valid", [a]) in
        let valid_b = Term.mkApp("Valid", [b]) in
        [Term.Assume(mkForall([valid], [aa;bb], mkIff(mkImp(valid_a, valid_b), valid)), Some "==> interpretation")] in
    let mk_iff_interp : string -> term -> decls_t = fun iff tt -> 
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = Term.mkApp("Valid", [Term.mkApp(iff, [a;b])]) in
        let valid_a = Term.mkApp("Valid", [a]) in
        let valid_b = Term.mkApp("Valid", [b]) in
        [Term.Assume(mkForall([valid], [aa;bb], mkIff(mkIff(valid_a, valid_b), valid)), Some "<==> interpretation")] in
    let mk_forall_interp : string -> term -> decls_t = fun for_all tt -> 
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let xx = ("x", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let x = mkFreeV xx in
        let valid = Term.mkApp("Valid", [Term.mkApp(for_all, [a;b])]) in
        let valid_b_x = Term.mkApp("Valid", [mk_ApplyTE b x]) in
        [Term.Assume(mkForall([valid], [aa;bb], mkIff(mkForall([mk_HasType x a], [xx], mkImp(mk_HasType x a, valid_b_x)), valid)), Some "forall interpretation")] in
    let mk_exists_interp : string -> term -> decls_t = fun for_all tt -> 
        let aa = ("a", Type_sort) in
        let bb = ("b", Type_sort) in
        let xx = ("x", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let x = mkFreeV xx in
        let valid = Term.mkApp("Valid", [Term.mkApp(for_all, [a;b])]) in
        let valid_b_x = Term.mkApp("Valid", [mk_ApplyTE b x]) in
        [Term.Assume(mkForall([valid], [aa;bb], mkIff(mkExists([mk_HasType x a], [xx], mkImp(mk_HasType x a, valid_b_x)), valid)), Some "exists interpretation")] in
    let mk_foralltyp_interp : string -> term -> decls_t = fun for_all tt -> 
        let kk = ("k", Kind_sort) in
        let aa = ("aa", Type_sort) in
        let bb = ("bb", Term_sort) in
        let k = mkFreeV kk in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = Term.mkApp("Valid", [Term.mkApp(for_all, [k;a])]) in
        let valid_a_b = Term.mkApp("Valid", [mk_ApplyTE a b]) in
        [Term.Assume(mkForall([valid], [kk;aa], mkIff(mkForall([mk_HasKind b k], [bb], mkImp(mk_HasKind b k, valid_a_b)), valid)), Some "ForallTyp interpretation")] in
    let mk_existstyp_interp : string -> term -> decls_t = fun for_some tt -> 
        let kk = ("k", Kind_sort) in
        let aa = ("aa", Type_sort) in
        let bb = ("bb", Term_sort) in
        let k = mkFreeV kk in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = Term.mkApp("Valid", [Term.mkApp(for_some, [k;a])]) in
        let valid_a_b = Term.mkApp("Valid", [mk_ApplyTE a b]) in
        [Term.Assume(mkForall([valid], [kk;aa], mkIff(mkExists([mk_HasKind b k], [bb], mkImp(mk_HasKind b k, valid_a_b)), valid)), Some "ExistsTyp interpretation")] in  
    
    let prims = [(Const.unit_lid,   mk_unit);
                 (Const.bool_lid,   mk_bool);
                 (Const.int_lid,    mk_int);
                 (Const.string_lid, mk_str);
                 (Const.ref_lid,    mk_ref);
                 (Const.char_lid,   mk_int_alias);
                 (Const.uint8_lid,  mk_int_alias);
                 (Const.false_lid,  mk_false_interp);
                 (Const.and_lid,    mk_and_interp);
                 (Const.or_lid,     mk_or_interp);
                 (Const.eq2_lid,    mk_eq2_interp);
                 (Const.imp_lid,    mk_imp_interp);
                 (Const.iff_lid,    mk_iff_interp);
                 (Const.forall_lid, mk_forall_interp);
                 (Const.exists_lid, mk_exists_interp);
//                 (Const.allTyp_lid, mk_foralltyp_interp);
//                 (Const.exTyp_lid,  mk_existstyp_interp)
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
    let should_skip (l:lident) = 
        Util.starts_with l.str "Prims.pure_"
        || Util.starts_with l.str "Prims.ex_"
        || Util.starts_with l.str "Prims.st_"
        || Util.starts_with l.str "Prims.all_" in
        
    match se with
     | Sig_typ_abbrev(_, _, _, _, [Effect], _) -> [], env

     | Sig_typ_abbrev(lid, _, _, _, _, _) when should_skip lid -> [], env
     | Sig_typ_abbrev(lid, _, _, _, _, _) when (lid_equals lid Const.b2t_lid) ->
       let tname, ttok, env = new_typ_constant_and_tok_from_lid env lid in 
       let xx = ("x", Term_sort) in
       let x = mkFreeV xx in
       let valid_b2t_x = mk_Valid(Term.mkApp("Prims.b2t", [x])) in
       let decls = [Term.DeclFun(tname, [Term_sort], Type_sort, None);
                    Term.Assume(Term.mkForall([valid_b2t_x], [xx], 
                                              Term.mkEq(valid_b2t_x, Term.mkApp("BoxBool_proj_0", [x]))),                                     
                                Some "b2t def")] in
       decls, env
      
     | Sig_typ_abbrev(lid, tps, _, t, tags, _) -> 
        let tname, ttok, env = new_typ_constant_and_tok_from_lid env lid in 
        let tps, t = match t.n with 
            | Typ_lam(tps', body) -> tps@tps', body
            | _ -> tps, t in 
        let vars, guards, env', binder_decls, _ = encode_binders None tps env in
        let tok_app = mk_ApplyT (mkApp(ttok, [])) vars in
        let tok_decl = Term.DeclFun(ttok, [], Type_sort, None) in
        let app = mkApp(tname, List.map mkFreeV vars) in
        let fresh_tok = match vars with 
            | [] -> []
            | _ -> [Term.fresh_token(ttok, Type_sort) (varops.next_id())] in
        let decls = [Term.DeclFun(tname, List.map snd vars, Type_sort, None);
                    tok_decl]
                    @fresh_tok
                    @[Term.Assume(mkForall([tok_app], vars, mkEq(tok_app, app)), Some "name-token correspondence")] in
        let t = whnf env t in
        let def, (body, decls1) = 
            if tags |> Util.for_some (function Logic -> true | _ -> false) 
            then mk_Valid app, encode_formula t env'
            else app, encode_typ_term t env' in 
        let abbrev_def = Term.Assume(mkForall([def], vars, mkImp(mk_and_l guards, mkEq(def, body))), Some "abbrev. elimination") in
        let kindingAx = 
            let k, decls = encode_knd (Recheck.recompute_kind t) env' app in
            decls@[Term.Assume(mkForall([app], vars, mkImp(mk_and_l guards, k)), Some "abbrev. kinding")] in
        let g = binder_decls@decls@decls1@abbrev_def::kindingAx@(primitive_type_axioms lid tname app)
               in
        g, env

     | Sig_val_decl(lid, t, quals, _) -> 
        let tt = whnf env t in
        let decls, env = encode_free_var env lid t tt quals in
        if Util.is_smt_lemma t && (quals |> List.contains Assumption || env.tcenv.is_iface)
        then decls@encode_smt_lemma env lid t, env
        else decls, env

     | Sig_assume(l, f, _, _) -> 
        let f, decls = encode_formula f env in
        let g = [Term.Assume(f, Some (format1 "Assumption: %s" (Print.sli l)))] in 
        decls@g, env

     | Sig_tycon(t, tps, k, _, datas, quals, _) when (lid_equals t Const.precedes_lid) -> 
        let tname, ttok, env = new_typ_constant_and_tok_from_lid env t in
        [], env
               
     | Sig_tycon(t, _, _, _, _, _, _) when (lid_equals t Const.char_lid || lid_equals t Const.uint8_lid) ->
        let tname = t.str in
        let tsym = mkFreeV(tname, Type_sort) in
        let decl = Term.DeclFun(tname, [], Type_sort, None) in
        decl::primitive_type_axioms t tname tsym, push_free_tvar env t tname (Some tsym)

     | Sig_tycon(t, tps, k, _, datas, quals, _) -> 
        let is_logical = quals |> Util.for_some (function Logic | Assumption -> true | _ -> false) in
        let constructor_or_logic_type_decl c = 
            if is_logical
            then let name, args, _, _ = c in 
                 [Term.DeclFun(name, args |> List.map snd, Type_sort, None)]
            else constructor_to_decl c in
 
        let inversion_axioms tapp vars = 
            if List.length datas = 0  || datas |> Util.for_some (fun l -> Tc.Env.lookup_qname env.tcenv l |> Option.isNone)
            then []
            else 
                 let xxsym, xx = fresh_fvar "x" Term_sort in
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
                    let indices, decls' = encode_args indices env in
                    if List.length indices <> List.length vars
                    then failwith "Impossible";
                    let eqs = List.map2 (fun v a -> match a with 
                        | Inl a -> Term.mkEq(mkFreeV v, a)
                        | Inr a -> Term.mkEq(mkFreeV v, a)) vars indices |> Term.mk_and_l in
                    mkOr(out, mkAnd(mk_data_tester env l xx, eqs)), decls@decls') (mkFalse, []) in
                    let ffsym, ff = fresh_fvar "f" Fuel_sort in
                    let xx_has_type = mk_HasTypeFuel (Term.mkApp("SFuel", [ff])) xx tapp in
                    decls@[Term.Assume(mkForall([xx_has_type], add_fuel (ffsym, Fuel_sort) ((xxsym, Term_sort)::vars),
                                        mkImp(xx_has_type, data_ax)), Some "inversion axiom")] in
        
        let k = Util.close_kind tps k in 
        let is_kind_arrow, formals, res = match (Util.compress_kind k).n with 
            | Kind_arrow(bs, res) -> true, bs, res
            | _ -> false, [], k in
        let vars, guards, env', binder_decls, _ = encode_binders None formals env in
        
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
                let dproj_app = mk_ApplyT (Term.mkApp(mk_typ_projector_name d a, [mkFreeV xx])) suffix in
                [Term.Assume(mkForall([tapp], vars, mkEq(tapp, dproj_app)), Some "projector axiom")]
            | _ -> [] in

        let pretype_axioms tapp vars = 
            let xxsym, xx = fresh_fvar "x" Term_sort in
            let ffsym, ff = fresh_fvar "f" Fuel_sort in
            let xx_has_type = mk_HasTypeFuel ff xx tapp in
            [Term.Assume(mkForall([xx_has_type], (xxsym, Term_sort)::(ffsym, Fuel_sort)::vars, 
                                  mkImp(xx_has_type, mkEq(tapp, mkApp("PreType", [xx])))), Some "pretyping")] in

        let tname, ttok, env = new_typ_constant_and_tok_from_lid env t in
        let ttok_tm = mkApp(ttok, []) in
        let guard = mk_and_l guards in
        let tapp = Term.mkApp(tname, List.map mkFreeV vars) in
        let decls, env =
            let tname_decl = constructor_or_logic_type_decl(tname, vars |> List.map (fun (n, s) -> (tname^n,s)), Type_sort, varops.next_id()) in
            let tok_decls, env = match vars with 
                | [] -> [], push_free_tvar env t tname (Some <| mkApp(tname, [])) 
                | _ -> 
                        let ttok_decl = Term.DeclFun(ttok, [], Type_sort, Some "token") in
                        let ttok_fresh = Term.fresh_token (ttok, Type_sort) (varops.next_id()) in
                        let ttok_app = mk_ApplyT ttok_tm vars in 
                        let pats = if not is_logical && quals |> Util.for_some (function Opaque -> true | _ -> false)
                                   then [[ttok_app]; [tapp]]
                                   else [[ttok_app]] in
                        let name_tok_corr = Term.Assume(mkForall'(pats, None, vars, mkEq(ttok_app, tapp)), Some "name-token correspondence") in
                        [ttok_decl; ttok_fresh; name_tok_corr], env in
            tname_decl@tok_decls, env in
        let kindingAx = 
            let k, decls = encode_knd res env' tapp in
            let karr = 
                if is_kind_arrow 
                then [Term.Assume(mk_tester "Kind_arrow" (mk_PreKind ttok_tm), Some "kinding")] 
                else [] in
            decls@karr@[Term.Assume(mkForall([tapp], vars, mkImp(guard, k)), Some "kinding")] in
        let aux = 
            if is_logical 
            then kindingAx@projection_axioms tapp vars 
            else kindingAx
                @(primitive_type_axioms t tname tapp)
                @(inversion_axioms tapp vars)
                @(projection_axioms tapp vars)
                @(pretype_axioms tapp vars) in
 
        let g = decls
                @binder_decls
                @aux in
        g, env

    | Sig_datacon(d, _, _, _, _, _) when (lid_equals d Const.lexcons_lid) -> [], env 

    | Sig_datacon(d, t, _, quals, _, drange) -> 
        let ddconstrsym, ddtok, env = new_term_constant_and_tok_from_lid env d in 
        let ddtok_tm = mkApp(ddtok, []) in
        let formals, t_res = match Util.function_formals t with 
            | Some (f, c) -> f, Util.comp_result c
            | None -> [], t in
        let fuel_var, fuel_tm = fresh_fvar "f" Fuel_sort in
        let s_fuel_tm = Term.mkApp("SFuel", [fuel_tm]) in
        let vars, guards, env', binder_decls, names = encode_binders (Some fuel_tm) formals env in 
        let projectors = names |> List.map (function 
            | Inl a -> mk_typ_projector_name d a, Type_sort
            | Inr x -> mk_term_projector_name d x, Term_sort) in
        let datacons = (ddconstrsym, projectors, Term_sort, varops.next_id()) |> Term.constructor_to_decl in
        let app = mk_ApplyE ddtok_tm vars in
        let guard = Term.mk_and_l guards in 
        let xvars = List.map mkFreeV vars in
        let dapp =  mkApp(ddconstrsym, xvars) in

        let tok_typing, decls3 = encode_typ_pred' None t env ddtok_tm in

        let vars', guards', env'', decls_formals, _ = encode_binders (Some s_fuel_tm) formals env in
        let ty_pred', decls_pred = 
             let xvars = List.map mkFreeV vars' in
             let dapp =  mkApp(ddconstrsym, xvars) in
             encode_typ_pred' (Some fuel_tm) t_res env'' dapp in 
        let guard' = Term.mk_and_l guards' in
        let proxy_fresh = match formals with 
            | [] -> []
            | _ -> [Term.fresh_token (ddtok, Term_sort) (varops.next_id())] in

        let encode_elim () = 
            let head, args = Util.head_and_args t_res in 
            match (Util.compress_typ head).n with 
                | Typ_const fv -> 
                  let encoded_head = lookup_free_tvar_name env' fv in
                  let encoded_args, arg_decls = encode_args args env' in
                  let _, arg_vars, eqns = List.fold_left (fun (env, arg_vars, eqns) arg -> 
                       match arg with 
                        | Inl targ -> 
                          let _, tv, env = gen_typ_var env (Util.new_bvd None) in
                          (env, tv::arg_vars, Term.mkEq(targ, tv)::eqns)
                        | Inr varg -> 
                          let _, xv, env = gen_term_var env (Util.new_bvd None) in
                          (env, xv::arg_vars, Term.mkEq(varg, xv)::eqns)) (env', [], []) encoded_args in
                  let arg_vars = List.rev arg_vars in
                  let ty = Term.mkApp(encoded_head, arg_vars) in
                  let xvars = List.map mkFreeV vars in
                  let dapp =  mkApp(ddconstrsym, xvars) in
                  let ty_pred = mk_HasTypeWithFuel (Some s_fuel_tm) dapp ty in
                  let arg_binders = List.map fv_of_term arg_vars in
                  let typing_inversion =
                    Term.Assume(mkForall([ty_pred], 
                                        add_fuel (fuel_var, Fuel_sort) (vars@arg_binders), 
                                        mkImp(ty_pred, Term.mk_and_l (eqns@guards))), 
                               Some "data constructor typing elim") in
                  let subterm_ordering = 
                    if lid_equals d Const.lextop_lid
                    then let x = varops.fresh "x", Term_sort in
                         let xtm = mkFreeV x in
                         Term.Assume(mkForall([Term.mk_Precedes xtm dapp], [x], mkImp(mk_tester "LexCons" xtm, Term.mk_Precedes xtm dapp)), Some "lextop is top")
                    else (* subterm ordering *)
                        let prec = vars |> List.collect (fun v -> match snd v with 
                            | Type_sort
                            | Fuel_sort -> []
                            | Term_sort -> [Term.mk_Precedes (mkFreeV v) dapp]
                            | _ -> failwith "unexpected sort") in
                        Term.Assume(mkForall([ty_pred], add_fuel (fuel_var, Fuel_sort) (vars@arg_binders), mkImp(ty_pred, mk_and_l prec)), Some "subterm ordering") in
                  arg_decls, [typing_inversion; subterm_ordering]

                | _ -> 
                  Tc.Errors.warn drange (Util.format2 "Constructor %s builds an unexpected type %s\n" (Print.sli d) (Print.typ_to_string head));
                  [], [] in
        let decls2, elim = encode_elim () in
        let g = binder_decls
                @decls2
                @decls3
                @[Term.DeclFun(ddtok, [], Term_sort, Some (format1 "data constructor proxy: %s" (Print.sli d)))]
                @proxy_fresh
                @decls_formals
                @decls_pred
                @[Term.Assume(tok_typing, Some "typing for data constructor proxy"); 
                  Term.Assume(mkForall([app], vars, 
                                       mkEq(app, dapp)), Some "equality for proxy");
                  Term.Assume(mkForall([ty_pred'],add_fuel (fuel_var, Fuel_sort) vars', mkImp(guard', ty_pred')), Some "data constructor typing intro");
                  ]
                @elim in
        datacons@g, env

    | Sig_bundle(ses, _, _, _) -> 
      let g, env = encode_signature env ses in
      let g', inversions = g |> List.partition (function
        | Term.Assume(_, Some "inversion axiom") -> false
        | _ -> true) in
      let decls, rest = g' |> List.partition (function 
        | Term.DeclFun _ -> true
        | _ -> false) in
      decls@rest@inversions, env

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
            | Exp_ascribed({n=Exp_abs(binders, body)}, _, _)
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
                 else if   bindings |> Util.for_some (fun lb -> Util.is_smt_lemma lb.lbtyp) 
                 then bindings |> List.collect (fun lb -> 
                        if Util.is_smt_lemma lb.lbtyp
                        then encode_smt_lemma env (right lb.lbname) lb.lbtyp
                        else raise Let_rec_unencodeable), env
                 else let toks, typs, decls, env = 
                    bindings |> List.fold_left (fun (toks, typs, decls, env) lb ->
                        if Util.is_smt_lemma lb.lbtyp then raise Let_rec_unencodeable;
                        let t_norm = whnf env lb.lbtyp |> Util.compress_typ in
                        let tok, decl, env = declare_top_level_let env (right lb.lbname) lb.lbtyp t_norm in
                        (right lb.lbname, tok)::toks, t_norm::typs, decl::decls, env) ([], [], [], env) in
                 let toks = List.rev toks in 
                 let decls = List.rev decls |> List.flatten in
                 let typs = List.rev typs in
                 if quals |> Util.for_some (function HasMaskedEffect -> true | _ -> false)
                 || typs  |> Util.for_some (fun t -> Util.is_lemma t || not <| Util.is_pure_or_ghost_function t) 
                 then decls, env
                 else if not is_rec
                 then match bindings, typs, toks with 
                        | [{lbdef=e}], [t_norm], [(flid, (f, ftok))] ->
                          let binders, body, formals, tres = destruct_bound_function flid t_norm e in
                          let vars, guards, env', binder_decls, _ = encode_binders None binders env in
                          let app = match vars with [] -> Term.mkFreeV(f, Term_sort) | _ -> Term.mkApp(f, List.map mkFreeV vars) in
                          let body, decls2 = encode_exp body env' in
                          let eqn = Term.Assume(mkForall([app], vars, mkImp(mk_and_l guards, mkEq(app, body))), Some (Util.format1 "Equation for %s" flid.str)) in
                          decls@binder_decls@decls2@[eqn], env      
                        | _ -> failwith "Impossible"
                 else let fuel = varops.fresh "fuel", Fuel_sort in
                      let fuel_tm = mkFreeV fuel in
                      let env0 = env in 
                      let gtoks, env = toks |> List.fold_left (fun (gtoks, env) (flid, (f, ftok)) -> 
                         let g = varops.new_fvar flid in
                         let gtok = varops.new_fvar flid in
                         let env = push_free_var env flid gtok (Some <| Term.mkApp(g, [fuel_tm])) in
                         (flid, f, ftok, g, gtok)::gtoks, env) ([], env) in
                      let gtoks = List.rev gtoks in
                      let encode_one_binding env0 (flid, f, ftok, g, gtok) t_norm ({lbdef=e}) = 
                         let binders, body, formals, tres = destruct_bound_function flid t_norm e in
                         let vars, guards, env', binder_decls, _ = encode_binders None binders env in
                         let decl_g = Term.DeclFun(g, Fuel_sort::List.map snd vars, Term_sort, Some "Fuel-instrumented function name") in
                         let env0 = push_zfuel_name env0 flid g in
                         let decl_g_tok = Term.DeclFun(gtok, [], Term_sort, Some "Token for fuel-instrumented partial applications") in
                         let vars_tm = List.map mkFreeV vars in
                         let app = Term.mkApp(f, vars_tm) in 
                         let gsapp = Term.mkApp(g, Term.mkApp("SFuel", [fuel_tm])::vars_tm) in
                         let gmax = Term.mkApp(g, Term.mkApp("MaxFuel", [])::vars_tm) in
                         let body_tm, decls2 = encode_exp body env' in
                         let eqn_g = Term.Assume(mkForall([gsapp], fuel::vars, mkImp(mk_and_l guards, mkEq(gsapp, body_tm))), Some (Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.str)) in
                         let eqn_f = Term.Assume(mkForall([app], vars, mkEq(app, gmax)), Some "Correspondence of recursive function to instrumented version") in
                         let eqn_g' = Term.Assume(mkForall([gsapp], fuel::vars, mkEq(gsapp,  Term.mkApp(g, mkFreeV fuel::vars_tm))), Some "Fuel irrelevance") in
                         let aux_decls, g_typing = 
                            let vars, v_guards, env, binder_decls, _ = encode_binders None formals env0 in
                            let vars_tm = List.map mkFreeV vars in
                            let gapp = Term.mkApp(g, fuel_tm::vars_tm) in
                            let tok_corr = 
                                let tok_app = mk_ApplyE (Term.mkFreeV (gtok, Term_sort)) (fuel::vars) in
                                Term.Assume(mkForall([tok_app], fuel::vars, mkEq(tok_app, gapp)), Some "Fuel token correspondence") in
                            let aux_decls, typing_corr = 
                                let g_typing, d3 = encode_typ_pred' None tres env gapp in
                                d3, [Term.Assume(mkForall([gapp], fuel::vars, mkImp(Term.mk_and_l v_guards, g_typing)), None)] in
                            binder_decls@aux_decls, typing_corr@[tok_corr] in
                        binder_decls@decls2@aux_decls@[decl_g;decl_g_tok], [eqn_g;eqn_g';eqn_f]@g_typing, env0 in
                        let decls, eqns, env0 = List.fold_left (fun (decls, eqns, env0) (gtok, ty, bs) -> 
                            let decls', eqns', env0 = encode_one_binding env0 gtok ty bs in
                            decls'::decls, eqns'@eqns, env0) ([decls], [], env0) (List.zip3 gtoks typs bindings) in
                        let prefix_decls, rest = decls |> List.flatten |> List.partition (function 
                            | DeclFun _ -> true
                            | _ -> false) in
                        let eqns = List.rev eqns in
                        prefix_decls@rest@eqns, env0
        with Let_rec_unencodeable -> 
             let msg = bindings |> List.map (fun lb -> Print.lbname_to_string lb.lbname) |> String.concat " and " in
             let decl = Caption ("let rec unencodeable: Skipping: " ^msg) in
             [decl], env
        end

    | Sig_pragma _
    | Sig_main _
    | Sig_new_effect _
    | Sig_effect_abbrev _
    | Sig_kind_abbrev _ 
    | Sig_sub_effect _ -> [], env

and declare_top_level_let env x t t_norm =
    match try_lookup_lid env x with 
        | None -> (* Need to introduce a new name decl *)
            let decls, env = encode_free_var env x t t_norm [] in
            let n, x', _ = lookup_lid env x in
            (n, x'), decls, env 
        | Some (n, x, _) -> (* already declared, only need an equation *)
            (n, x), [], env

and encode_smt_lemma env lid t = 
    let form, decls = encode_function_type_as_formula None t env in 
    decls@[Term.Assume(form, Some ("Lemma: " ^ lid.str))]

and encode_free_var env lid tt t_norm quals = 
    if not <| Util.is_pure_or_ghost_function t_norm || Util.is_lemma t_norm
    then let vname, vtok, env = new_term_constant_and_tok_from_lid env lid in
         let arg_sorts = match t_norm.n with 
            | Typ_fun(binders, _) -> binders |> List.map (function (Inl _, _) -> Type_sort | _ -> Term_sort) 
            | _ -> [] in
         let d = Term.DeclFun(vname, arg_sorts, Term_sort, Some "Uninterpreted function symbol for impure function") in
         let dd = Term.DeclFun(vtok, [], Term_sort, Some "Uninterpreted name for impure function") in
         [d;dd], env
    else if prims.is lid
         then let vname = varops.new_fvar lid in
              let definition = prims.mk lid vname in
              let env = push_free_var env lid vname None in
              definition, env
         else let encode_non_total_function_typ = lid.nsstr <> "Prims" in
              let formals, (pre_opt, res_t) = match Util.function_formals t_norm with 
                | Some (args, comp) -> 
                  if encode_non_total_function_typ 
                  then args, Tc.Util.pure_or_ghost_pre_and_post env.tcenv comp 
                  else args, (None, Util.comp_result comp)
                | None -> [], (None, t_norm) in
              let vname, vtok, env = new_term_constant_and_tok_from_lid env lid in 
              let vtok_tm = match formals with 
                | [] -> mkFreeV(vname, Term_sort) 
                | _ -> mkApp(vtok, []) in
              let mk_disc_proj_axioms vapp vars = quals |> List.collect (function 
                | Discriminator d -> 
                    let _, (xxsym, _) = Util.prefix vars in
                    let xx = mkFreeV(xxsym, Term_sort) in
                    [Term.Assume(mkForall([vapp], vars,
                                            mkEq(vapp, Term.boxBool <| Term.mk_tester (escape d.str) xx)), None)]

                | Projector(d, Inr f) -> 
                    let _, (xxsym, _) = Util.prefix vars in
                    let xx = mkFreeV(xxsym, Term_sort) in
                    [Term.Assume(mkForall([vapp], vars,
                                            mkEq(vapp, Term.mkApp(mk_term_projector_name d f, [xx]))), None)]
                | _ -> []) in
              let vars, guards, env', decls1, _ = encode_binders None formals env in
              let guard, decls1 = match pre_opt with 
                | None -> mk_and_l guards, decls1
                | Some p -> let g, ds = encode_formula p env' in mk_and_l (g::guards), decls1@ds in
              let vtok_app = mk_ApplyE vtok_tm vars in
        
              let vapp = Term.mkApp(vname, List.map Term.mkFreeV vars) in
              let decls2, env =
                let vname_decl = Term.DeclFun(vname, formals |> List.map (function Inl _, _ -> Type_sort | _ -> Term_sort), Term_sort, None) in
                let tok_typing, decls2 = 
                    let env = {env with encode_non_total_function_typ=encode_non_total_function_typ} in
                    if not(head_normal env tt) 
                    then encode_typ_pred' None tt env vtok_tm 
                    else encode_typ_pred' None t_norm env vtok_tm in //NS:Unfortunately, this is duplicated work --- we effectively encode the function type twice
                let tok_typing = Term.Assume(tok_typing, Some "function token typing") in
                let tok_decl, env = match formals with 
                        | [] -> decls2@[tok_typing], push_free_var env lid vname (Some <| mkFreeV(vname, Term_sort))
                        | _ ->  (* Generate a token and a function symbol; equate the two, and use the function symbol for full applications *)
                                let vtok_decl = Term.DeclFun(vtok, [], Term_sort, None) in
                                let vtok_fresh = Term.fresh_token (vtok, Term_sort) (varops.next_id()) in
                                let name_tok_corr = Term.Assume(mkForall([vtok_app], vars, mkEq(vtok_app, vapp)), None) in
                                decls2@[vtok_decl;vtok_fresh;name_tok_corr;tok_typing], env in
                vname_decl::tok_decl, env in
              let ty_pred, decls3 = encode_typ_pred' None res_t env' vapp in 
              let typingAx = Term.Assume(mkForall([vapp], vars, mkImp(guard, ty_pred)), Some "free var typing") in
              let g = decls1@decls2@decls3@typingAx::mk_disc_proj_axioms vapp vars in
              g, env
       

and encode_signature env ses = 
    ses |> List.fold_left (fun (g, env) se ->            
      let g', env = encode_sigelt env se in 
      g@g', env) ([], env) 

let encode_env_bindings (env:env_t) (bindings:list<Tc.Env.binding>) : (decls_t * env_t) = 
    let encode_binding b (decls, env) = match b with
        | Env.Binding_var(x, t0) -> 
            let xxsym, xx, env' = new_term_constant env x in 
            let t1 = Normalize.norm_typ [Normalize.DeltaHard; Normalize.Beta; Normalize.Eta; Normalize.Simplify] env.tcenv t0 in//whnf env t0 in
            let t, decls' = encode_typ_pred' None t1 env xx in
            let caption = 
                if !Options.logQueries 
                then Some (Util.format3 "%s : %s (%s)" (Print.strBvd x) (Print.typ_to_string t0) (Print.typ_to_string t1))
                else None in  
            let g = [Term.DeclFun(xxsym, [], Term_sort, caption)]
                    @decls'
                    @[Term.Assume(t, None)] in
            decls@g, env'
        | Env.Binding_typ(a, k) -> 
            let aasym, aa, env' = new_typ_constant env a in 
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
    let prefix = labs |> List.map (fun (l, _, _) -> Term.DeclFun(fst l, [], Bool_sort, None)) in
    let suffix = labs |> List.collect (fun (l, _, _) -> [Echo <| fst l; Eval (mkFreeV l)]) in
    prefix, suffix

(* caching encodings of the environment and the top-level API to the encoding *)
open Microsoft.FStar.Tc.Env
let last_env : ref<list<env_t>> = Util.mk_ref []
let init_env tcenv = last_env := [{bindings=[]; tcenv=tcenv; warn=true; depth=0; 
                                   cache=Util.smap_create 100; nolabels=false; use_zfuel_name=false;
                                   encode_non_total_function_typ=true}]
let get_env tcenv = match !last_env with 
    | [] -> failwith "No env; call init first!"
    | e::_ -> {e with tcenv=tcenv}
let set_env env = match !last_env with 
    | [] -> failwith "Empty env stack"
    | _::tl -> last_env := env::tl
let push_env () = match !last_env with 
    | [] -> failwith "Empty env stack"
    | hd::tl -> 
      Term.push();
      let refs = Util.smap_copy hd.cache  in
      let top = {hd with cache=refs} in
      last_env := top::hd::tl 
let pop_env () = match !last_env with 
    | [] -> failwith "Popping an empty stack"
    | _::tl -> Term.pop(); last_env := tl
let mark_env () = push_env()
let reset_mark_env () = pop_env()
let commit_mark_env () = 
    Term.commit_mark();
    match !last_env with 
        | hd::_::tl -> last_env := hd::tl
        | _ -> failwith "Impossible"
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
let mark msg = 
    mark_env();
    varops.mark();
    Z3.mark msg
let reset_mark msg = 
    reset_mark_env();
    varops.reset_mark();
    Z3.reset_mark msg
let commit_mark msg = 
    commit_mark_env();
    varops.commit_mark();
    Z3.commit_mark msg
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
        let bindings = Tc.Env.fold_env tcenv (fun bs b -> b::bs) [] in
        let env_decls, env = encode_env_bindings env (List.filter (function Binding_sig _ -> false | _ -> true) bindings) in
        if debug tcenv Options.Low then Util.fprint1 "Encoding query formula: %s\n" (Print.formula_to_string q);//(Normalize.formula_norm_to_string tcenv q);
        let phi, labels, qdecls = encode_formula_with_labels q env in
        let label_prefix, label_suffix = encode_labels labels in
        let query_prelude = 
            env_decls
            @label_prefix
            @qdecls in
        let qry = Term.Assume(mkNot phi, Some "query") in
        let suffix = label_suffix@[Term.Echo "Done!"]  in
        query_prelude, labels, qry, suffix in
    begin match qry with 
        | Assume({tm=App(False, _)}, _) -> pop(); ()
        | _ when tcenv.admit -> pop(); ()
        | Assume(q, _) ->
            let fresh = String.length q.hash >= 2048 in   
            Z3.giveZ3 prefix;

            let with_fuel p (n, i) = 
                [Term.Caption (Util.format1 "<fuel='%s'>" (string_of_int n)); 
                    Term.Assume(mkEq(mkApp("MaxFuel", []), n_fuel n), None);
                    Term.Assume(mkEq(mkApp("MaxIFuel", []), n_fuel i), None);
                    p;
                    Term.CheckSat]@suffix in
    
            let check (p:decl) =
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

                let rec try_alt_configs (p:decl) errs = function 
                    | [] -> report (false, errs)
                    | [mi] -> 
                        begin match errs with 
                        | [] -> Z3.ask fresh labels (with_fuel p mi) (cb p [])
                        | _ -> report (false, errs)
                        end

                    | mi::tl -> 
                        Z3.ask fresh labels (with_fuel p mi) (fun (ok, errs') -> 
                        match errs with 
                            | [] -> cb p tl (ok, errs')  
                            | _ -> cb p tl (ok, errs))

                and cb (p:decl) alt (ok, errs) = if ok then () else try_alt_configs p errs alt in
                Z3.ask fresh labels (with_fuel p initial_config) (cb p alt_configs)  in

            let process_query (q:decl) :unit =
                if !Options.split_cases > 0 then
                    let (b, cb) = SplitQueryCases.can_handle_query !Options.split_cases q in
                    if b then SplitQueryCases.handle_query cb check else check q
                else check q
            in

            if !Options.admit_smt_queries then () else process_query qry;
            pop ()
    end

let is_trivial (tcenv:Tc.Env.env) (q:typ) : bool = 
   let env = get_env tcenv in
   push "query";
   let f, _, _ = encode_formula_with_labels q env in
   pop "query";
   match f.tm with 
    | App(True, _) -> true
    | _ -> false

let solver = {
    init=init;
    push=push;
    pop=pop;
    mark=mark;
    reset_mark=reset_mark;
    commit_mark=commit_mark;
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
    mark=(fun _ -> ());
    reset_mark=(fun _ -> ());
    commit_mark=(fun _ -> ());
    encode_sig=(fun _ _ -> ());
    encode_modul=(fun _ _ -> ());
    solve=(fun _ _ -> ());
    is_trivial=(fun _ _ -> false);
    finish=(fun () -> ());
    refresh=(fun () -> ());
}


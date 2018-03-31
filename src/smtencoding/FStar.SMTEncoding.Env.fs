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

module FStar.SMTEncoding.Env
open FStar.ST
open FStar.Exn
open FStar.All
open Prims
open FStar
open FStar.TypeChecker.Env
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker
open FStar.SMTEncoding.Term
open FStar.Ident
open FStar.SMTEncoding.Util
module SS = FStar.Syntax.Subst
module BU = FStar.Util
module U = FStar.Syntax.Util

exception Inner_let_rec

let add_fuel x tl = if (Options.unthrottle_inductives()) then tl else x::tl
let withenv c (a, b) = (a,b,c)
let vargs args = List.filter (function (BU.Inl _, _) -> false | _ -> true) args
(* ------------------------------------ *)
(* Some operations on constants *)
let escape (s:string) = BU.replace_char s '\'' '_'
let mk_term_projector_name lid (a:bv) =
    let a = {a with ppname=U.unmangle_field_name a.ppname} in
    escape <| BU.format2 "%s_%s" lid.str a.ppname.idText
let primitive_projector_by_pos env lid i =
    let fail () = failwith (BU.format2 "Projector %s on data constructor %s not found" (string_of_int i) (lid.str)) in
    let _, t = Env.lookup_datacon env lid in
    match (SS.compress t).n with
        | Tm_arrow(bs, c) ->
          let binders, _ = SS.open_comp bs c in
          if ((i < 0) || i >= List.length binders) //this has to be within bounds!
          then fail ()
          else let b = List.nth binders i in
                mk_term_projector_name lid (fst b)
        | _ -> fail ()
let mk_term_projector_name_by_pos lid (i:int) = escape <| BU.format2 "%s_%s" lid.str (string_of_int i)
let mk_term_projector (lid:lident) (a:bv) : term =
    mkFreeV(mk_term_projector_name lid a, Arrow(Term_sort, Term_sort))
let mk_term_projector_by_pos (lid:lident) (i:int) : term =
    mkFreeV(mk_term_projector_name_by_pos lid i, Arrow(Term_sort, Term_sort))
let mk_data_tester env l x = mk_tester (escape l.str) x
(* ------------------------------------ *)
(* New name generation *)
type varops_t = {
    push: unit -> unit;
    pop: unit -> unit;
    new_var:ident -> int -> string; (* each name is distinct and has a prefix corresponding to the name used in the program text *)
    new_fvar:lident -> string;
    fresh:string -> string;
    string_const:string -> term;
    next_id: unit -> int;
    mk_unique:string -> string;
}
let varops =
    let initial_ctr = 100 in
    let ctr = BU.mk_ref initial_ctr in
    let new_scope () = (BU.smap_create 100, BU.smap_create 100) in (* a scope records all the names and string constants used in that scope *)
    let scopes = BU.mk_ref [new_scope ()] in
    let mk_unique y =
        let y = escape y in
        let y = match BU.find_map (!scopes) (fun (names, _) -> BU.smap_try_find names y) with
                  | None -> y
                  | Some _ -> BU.incr ctr; y ^ "__" ^ (string_of_int !ctr) in
        let top_scope = fst <| List.hd !scopes in
        BU.smap_add top_scope y true; y in
    let new_var pp rn = mk_unique <| pp.idText ^ "__" ^ (string_of_int rn) in
    let new_fvar lid = mk_unique lid.str in
    let next_id () = BU.incr ctr; !ctr in
    let fresh pfx = BU.format2 "%s_%s" pfx (string_of_int <| next_id()) in
    let string_const s = match BU.find_map !scopes (fun (_, strings) -> BU.smap_try_find strings s) with
        | Some f -> f
        | None ->
            let id = next_id () in
            let f = Term.boxString <| mk_String_const id in
            let top_scope = snd <| List.hd !scopes in
            BU.smap_add top_scope s f;
            f in
    let push () = scopes := new_scope()::!scopes in
    let pop () = scopes := List.tl !scopes in
    {push=push;
     pop=pop;
     new_var=new_var;
     new_fvar=new_fvar;
     fresh=fresh;
     string_const=string_const;
     next_id=next_id;
     mk_unique=mk_unique}

 let unmangle (x:bv) : bv = {x with ppname=U.unmangle_field_name x.ppname}
(* ---------------------------------------------------- *)
(* <Environment> *)
(* Each entry maps a Syntax variable to its encoding as a SMT2 term *)
(* free variables, depending on whether or not they are fully applied ...  *)
(* ... are mapped either to SMT2 functions, or to nullary tokens *)
type fvar_binding = {
    fvar_lid:  lident;
    smt_arity: int;
    smt_id:    string;
    smt_token: option<term>;
    smt_fuel_partial_app:option<term>
}

type binding =
    | Binding_var   of bv * term
    | Binding_fvar  of fvar_binding //lident * string * option<term> * option<term>

let binder_of_eithervar v = (v, None)
type cache_entry = {
    cache_symbol_name: string;
    cache_symbol_arg_sorts: list<sort>;
    cache_symbol_decls: list<decl>;
    cache_symbol_assumption_names: list<string>
}
type env_t = {
    bindings:list<binding>;
    depth:int; //length of local var/tvar bindings
    tcenv:Env.env;
    warn:bool;
    cache:BU.smap<cache_entry>;
    nolabels:bool;
    use_zfuel_name:bool;
    encode_non_total_function_typ:bool;
    current_module_name:string;
}
let mk_cache_entry env tsym cvar_sorts t_decls =
    let names =
        t_decls
        |> List.collect
              (function
               | Assume a -> [a.assumption_name]
               | _ -> [])
    in
    {
        cache_symbol_name=tsym;
        cache_symbol_arg_sorts=cvar_sorts;
        cache_symbol_decls=t_decls;
        cache_symbol_assumption_names=names
    }
let use_cache_entry ce =
    [Term.RetainAssumptions ce.cache_symbol_assumption_names]
let print_env e =
    e.bindings |> List.map (function
        | Binding_var  (x, _) -> Print.bv_to_string x
        | Binding_fvar fvb -> Print.lid_to_string fvb.fvar_lid) |> String.concat ", "

let lookup_binding env f = BU.find_map env.bindings f

let fresh_fvar x s = let xsym = varops.fresh x in xsym, mkFreeV(xsym, s)
(* generate terms corresponding to a variable and record the mapping in the environment *)

(* Bound term variables *)
let gen_term_var (env:env_t) (x:bv) =
    let ysym = "@x"^(string_of_int env.depth) in
    let y = mkFreeV(ysym, Term_sort) in
    ysym, y, {env with bindings=Binding_var(x, y)::env.bindings; depth=env.depth + 1}
let new_term_constant (env:env_t) (x:bv) =
    let ysym = varops.new_var x.ppname x.index in
    let y = mkApp(ysym, []) in
    ysym, y, {env with bindings=Binding_var(x, y)::env.bindings}
let new_term_constant_from_string (env:env_t) (x:bv) str =
    let ysym = varops.mk_unique str in
    let y = mkApp(ysym, []) in
    ysym, y, {env with bindings=Binding_var(x, y)::env.bindings}
let push_term_var (env:env_t) (x:bv) (t:term) =
    {env with bindings=Binding_var(x,t)::env.bindings}
let lookup_term_var env a =
    let aux a' = lookup_binding env (function Binding_var(b, t) when Syntax.bv_eq b a' -> Some (b,t) | _ -> None) in
    match aux a with
    | None ->
        //AR: this is a temporary fix, use reserved u__ for mangling names
        let a2 = unmangle a in
        (match aux a2 with
            | None -> failwith (BU.format2 "Bound term variable not found (after unmangling): %s in environment: %s" (Print.bv_to_string a2) (print_env env))
            | Some (b,t) -> t)
    | Some (b,t) -> t

(* Qualified term names *)
let mk_fvb lid fname arity ftok fuel_partial_app = {
        fvar_lid  = lid;
        smt_arity = arity;
        smt_id    = fname;
        smt_token = ftok;
        smt_fuel_partial_app = fuel_partial_app
}
let new_term_constant_and_tok_from_lid (env:env_t) (x:lident) arity =
    let fname = varops.new_fvar x in
    let ftok_name = fname^"@tok" in
    let ftok = mkApp(ftok_name, []) in
    let fvb = mk_fvb x fname arity (Some ftok) None in
//    Printf.printf "Pushing %A @ %A, %A\n" x fname ftok;
    fname, ftok_name, {env with bindings=(Binding_fvar fvb)::env.bindings}
let try_lookup_lid env a =
    lookup_binding env (function
      | Binding_fvar fvb
            when lid_equals fvb.fvar_lid a ->
        Some fvb
      | _ -> None)
let contains_name env (s:string) =
    lookup_binding env (function
      | Binding_fvar fvb
            when (fvb.fvar_lid.str=s) ->
        Some ()
      | _ -> None) |> Option.isSome
let lookup_lid env a =
    match try_lookup_lid env a with
    | None -> failwith (BU.format1 "Name not found: %s" (Print.lid_to_string a))
    | Some s -> s
let push_free_var env (x:lident) arity fname ftok =
    let fvb = mk_fvb x fname arity ftok None in
    {env with bindings=Binding_fvar fvb::env.bindings}
let push_zfuel_name env (x:lident) f =
    let fvb = lookup_lid env x in
    let t3 = mkApp(f, [mkApp("ZFuel", [])]) in
    let fvb = mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token (Some t3) in
    {env with bindings=Binding_fvar fvb::env.bindings}
let try_lookup_free_var env l =
    match try_lookup_lid env l with
    | None -> None
    | Some fvb ->
      begin
      match fvb.smt_fuel_partial_app with
      | Some f when env.use_zfuel_name -> Some f
      | _ ->
        begin
        match fvb.smt_token with
        | Some t ->
          begin
          match t.tm with
          | App(_, [fuel]) ->
            if (BU.starts_with (Term.fv_of_term fuel |> fst) "fuel")
            then Some <| mk_ApplyTF(mkFreeV (fvb.smt_id, Term_sort)) fuel
            else Some t
          | _ -> Some t
          end
        | _ -> None
        end
      end
let lookup_free_var env a =
    match try_lookup_free_var env a.v with
        | Some t -> t
        | None -> failwith (BU.format1 "Name not found: %s" (Print.lid_to_string a.v))
let lookup_free_var_name env a =
    let fvb = lookup_lid env a.v in
    fvb.smt_id, fvb.smt_arity
let lookup_free_var_sym env a =
    let fvb = lookup_lid env a.v in
    match fvb.smt_fuel_partial_app with
    | Some({tm=App(g, zf)})
        when env.use_zfuel_name ->
        g, zf, fvb.smt_arity + 1
    | _ ->
        begin
        match fvb.smt_token with
        | None ->
            Var fvb.smt_id, [], fvb.smt_arity
        | Some sym ->
            begin
            match sym.tm with
            | App(g, [fuel]) ->
                g, [fuel], fvb.smt_arity + 1
            | _ ->
                Var fvb.smt_id, [], fvb.smt_arity
            end
        end

let tok_of_name env nm =
    BU.find_map env.bindings (function
        | Binding_fvar fvb
            when fvb.smt_id=nm ->
          fvb.smt_token
        | _ -> None)

(* </Environment> *)

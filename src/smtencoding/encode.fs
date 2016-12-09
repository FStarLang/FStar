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

module FStar.SMTEncoding.Encode

open FStar
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker
open FStar.SMTEncoding.Term
open FStar.Ident
open FStar.Const
open FStar.SMTEncoding.SplitQueryCases
open FStar.SMTEncoding.Util
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N = FStar.TypeChecker.Normalize

let add_fuel x tl = if (Options.unthrottle_inductives()) then tl else x::tl
let withenv c (a, b) = (a,b,c)
let vargs args = List.filter (function (Inl _, _) -> false | _ -> true) args
let subst_lcomp_opt s l = match l with
    | Some (Inl l) -> Some (Inl (Util.lcomp_of_comp <| SS.subst_comp s (l.comp())))
    | _ -> l
(* ------------------------------------ *)
(* Some operations on constants *)
let escape (s:string) = Util.replace_char s '\'' '_'
let mk_term_projector_name lid (a:bv) =
    let a = {a with ppname=Util.unmangle_field_name a.ppname} in
    escape <| format2 "%s_%s" lid.str a.ppname.idText
let primitive_projector_by_pos env lid i =
    let fail () = failwith (Util.format2 "Projector %s on data constructor %s not found" (string_of_int i) (lid.str)) in
    let _, t = Env.lookup_datacon env lid in
    match (SS.compress t).n with
        | Tm_arrow(bs, c) ->
          let binders, _ = SS.open_comp bs c in
          if ((i < 0) || i >= List.length binders) //this has to be within bounds!
          then fail ()
          else let b = List.nth binders i in
                mk_term_projector_name lid (fst b)
        | _ -> fail ()
let mk_term_projector_name_by_pos lid (i:int) = escape <| format2 "%s_%s" lid.str (string_of_int i)
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
    mark: unit -> unit;
    reset_mark: unit -> unit;
    commit_mark: unit -> unit;
    new_var:ident -> int -> string; (* each name is distinct and has a prefix corresponding to the name used in the program text *)
    new_fvar:lident -> string;
    fresh:string -> string;
    string_const:string -> term;
    next_id: unit -> int;
    mk_unique:string -> string;
}
let varops =
    let initial_ctr = 100 in
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
    let new_var pp rn = mk_unique <| pp.idText ^ "__" ^ (string_of_int rn) in
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
     next_id=next_id;
     mk_unique=mk_unique}

 let unmangle (x:bv) : bv = {x with ppname=Util.unmangle_field_name x.ppname}
(* ---------------------------------------------------- *)
(* <Environment> *)
(* Each entry maps a Syntax variable to its encoding as a SMT2 term *)
type binding =
    | Binding_var   of bv * term
    | Binding_fvar  of lident * string * option<term> * option<term> (* free variables, depending on whether or not they are fully applied ...  *)
                                                                     (* ... are mapped either to SMT2 functions, or to nullary tokens *)

let binder_of_eithervar v = (v, None)
type env_t = {
    bindings:list<binding>;
    depth:int; //length of local var/tvar bindings
    tcenv:Env.env;
    warn:bool;
    cache:Util.smap<(string * list<sort> * list<decl>)>;
    nolabels:bool;
    use_zfuel_name:bool;
    encode_non_total_function_typ:bool
}
let print_env e =
    e.bindings |> List.map (function
        | Binding_var  (x, _) -> Print.bv_to_string x
        | Binding_fvar (l, _, _, _) -> Print.lid_to_string l) |> String.concat ", "

let lookup_binding env f = Util.find_map env.bindings f

let caption_t env t =
    if Env.debug env.tcenv Options.Low
    then Some (Print.term_to_string t)
    else None

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
        let a = unmangle a in
        (match aux a with
            | None -> failwith (format1 "Bound term variable not found (after unmangling): %s" (Print.bv_to_string a))
            | Some (b,t) -> t)
    | Some (b,t) -> t

(* Qualified term names *)
let new_term_constant_and_tok_from_lid (env:env_t) (x:lident) =
    let fname = varops.new_fvar x in
    let ftok = fname^"@tok" in
//    Printf.printf "Pushing %A @ %A, %A\n" x fname ftok;
    fname, ftok, {env with bindings=Binding_fvar(x, fname, Some <| mkApp(ftok,[]), None)::env.bindings}
let try_lookup_lid env a =
    lookup_binding env (function Binding_fvar(b, t1, t2, t3) when lid_equals b a -> Some (t1, t2, t3) | _ -> None)
let contains_name env (s:string) =
    lookup_binding env (function Binding_fvar(b, t1, t2, t3) when (b.str=s) -> Some () | _ -> None) |> Option.isSome
let lookup_lid env a =
    match try_lookup_lid env a with
    | None -> failwith (format1 "Name not found: %s" (Print.lid_to_string a))
    | Some s -> s
let push_free_var env (x:lident) fname ftok =
    {env with bindings=Binding_fvar(x, fname, ftok, None)::env.bindings}
let push_zfuel_name env (x:lident) f =
    let t1, t2, _ = lookup_lid env x in
    let t3 = mkApp(f, [mkApp("ZFuel", [])]) in
    {env with bindings=Binding_fvar(x, t1, t2, Some t3)::env.bindings}
let try_lookup_free_var env l =
    match try_lookup_lid env l with
        | None -> None
        | Some (name, sym, zf_opt) ->
            match zf_opt with
                | Some f when (env.use_zfuel_name) -> Some f
                | _ ->
                  match sym with
                    | Some t ->
                        begin match t.tm with
                            | App(_, [fuel]) ->
                                if (Util.starts_with (Term.fv_of_term fuel |> fst) "fuel")
                                then Some <| mk_ApplyTF(mkFreeV (name, Term_sort)) fuel
                                else Some t
                            | _ -> Some t
                        end
                    | _ -> None
let lookup_free_var env a =
    match try_lookup_free_var env a.v with
        | Some t -> t
        | None -> failwith (format1 "Name not found: %s" (Print.lid_to_string a.v))
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

let tok_of_name env nm =
    Util.find_map env.bindings (function
        | Binding_fvar(_, nm', tok, _) when (nm=nm') -> tok
        | _ -> None)

(* </Environment> *)
(*---------------------------------------------------------------------------------*)
(* <Utilities> *)

let mkForall_fuel' n (pats, vars, body) =
    let fallback () = mkForall(pats, vars, body) in
    if (Options.unthrottle_inductives())
    then fallback ()
    else let fsym, fterm = fresh_fvar "f" Fuel_sort in
         let add_fuel tms =
            tms |> List.map (fun p -> match p.tm with
            | Term.App(Var "HasType", args) -> mkApp("HasTypeFuel", fterm::args)
            | _ -> p) in
         let pats = List.map add_fuel pats in
         let body = match body.tm with
            | Term.App(Imp, [guard; body']) ->
              let guard = match guard.tm with
                | App(And, guards) -> mk_and_l (add_fuel guards)
                | _ -> add_fuel [guard] |> List.hd in
              mkImp(guard,body')
            | _ -> body in
         let vars = (fsym, Fuel_sort)::vars in
         mkForall(pats, vars, body)

let mkForall_fuel = mkForall_fuel' 1

let head_normal env t =
   let t = Util.unmeta t in
   match t.n with
    | Tm_arrow _
    | Tm_refine _
    | Tm_bvar _
    | Tm_uvar _
    | Tm_abs _
    | Tm_constant _ -> true
    | Tm_fvar fv
    | Tm_app({n=Tm_fvar fv}, _) -> Env.lookup_definition [Env.Eager_unfolding_only] env.tcenv fv.fv_name.v |> Option.isNone
    | _ -> false

let head_redex env t =
    match (FStar.Syntax.Util.un_uinst t).n with
    | Tm_abs(_, _, Some (Inr (l, flags))) ->
      Ident.lid_equals l Const.effect_Tot_lid
      || Ident.lid_equals l Const.effect_GTot_lid
      || List.existsb (function TOTAL -> true | _ -> false) flags

    | Tm_abs(_, _, Some (Inl lc)) ->
      Util.is_tot_or_gtot_lcomp lc

    | Tm_fvar fv ->
      Env.lookup_definition [Env.Eager_unfolding_only] env.tcenv fv.fv_name.v |> Option.isSome

    | _ -> false

let whnf env t =
    if head_normal env t then t
    else N.normalize [N.Beta; N.WHNF; N.Eager_unfolding; N.EraseUniverses] env.tcenv t
let norm env t = N.normalize [N.Beta; N.Eager_unfolding; N.EraseUniverses] env.tcenv t

let trivial_post t : Syntax.term =
    Util.abs [null_binder t]
             (Syntax.fvar Const.true_lid Delta_constant None)
             None

let mk_Apply e vars =
    vars |> List.fold_left (fun out var -> match snd var with
            | Fuel_sort -> mk_ApplyTF out (mkFreeV var)
            | s -> assert (s=Term_sort); mk_ApplyTT out (mkFreeV var)) e
let mk_Apply_args e args = args |> List.fold_left mk_ApplyTT e

let is_app = function
    | Var "ApplyTT"
    | Var "ApplyTF" -> true
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
(* The main encoding of terms and formulae: mutually recursive                    *)
(* see fstar-priv/papers/mm/encoding.txt for a semi-formal sketch of the encoding *)
(**********************************************************************************)

(* Abstractly:

      ctx = (bvvdef -> term(Term_sort))
       ex = set (var x term(Bool))        existentially bound variables
    [[e]] : ctx -> term(Term_sort) * ex
    [[f]] : ctx -> term(Bool)
   [[bs]] : ctx -> (vars
                    * term(Bool)  <-- guard on bound vars
                    * ctx)   <-- context extended with bound vars

    Concretely, [[*]] are the encode_* functions, for exp, formula, binders
    ctx is implemented using env_t
    and term( * ) is just term
 *)

type label = (fv * string * Range.range)
type labels = list<label>
type pattern = {
  pat_vars: list<(bv * fv)>;
  pat_term: unit -> (term * decls_t);                   (* the pattern as a term(exp) *)
  guard: term -> term;                                  (* the guard condition of the pattern, as applied to a particular scrutinee term(exp) *)
  projections: term -> list<(bv * term)>                (* bound variables of the pattern, and the corresponding projected components of the scrutinee *)
 }
exception Let_rec_unencodeable

let encode_const = function
    | Const_unit -> mk_Term_unit
    | Const_bool true -> boxBool mkTrue
    | Const_bool false -> boxBool mkFalse
    | Const_char c -> mkApp("FStar.Char.Char", [boxInt (mkInteger' (Util.int_of_char c))])
    | Const_int (i, None)  -> boxInt (mkInteger i)
    | Const_int (i, Some _) -> failwith "Machine integers should be desugared"
    | Const_string(bytes, _) -> varops.string_const (Util.string_of_bytes <| bytes)
    | Const_range r -> mk_Range_const
    | Const_effect -> mk_Term_type
    | c -> failwith (Util.format1 "Unhandled constant: %s" (Print.const_to_string c))

let as_function_typ env t0 =
    let rec aux norm t =
        let t = SS.compress t in
        match t.n with
            | Tm_arrow _ -> t
            | Tm_refine _ -> aux true (Util.unrefine t)
            | _ -> if norm
                   then aux false (whnf env t)
                   else failwith (Util.format2 "(%s) Expected a function typ; got %s" (Range.string_of_range t0.pos) (Print.term_to_string t0))
    in aux true t0

let curried_arrow_formals_comp k =
    let k = Subst.compress k in
    match k.n with
        | Tm_arrow(bs, c) -> Subst.open_comp bs c
        | _ -> [], Syntax.mk_Total k


let rec encode_binders (fuel_opt:option<term>) (bs:Syntax.binders) (env:env_t) :
                            (list<fv>                       (* translated bound variables *)
                            * list<term>                    (* guards *)
                            * env_t                         (* extended context *)
                            * decls_t                       (* top-level decls to be emitted *)
                            * list<bv>)                     (* unmangled names *) =

    if Env.debug env.tcenv Options.Low then Util.print1 "Encoding binders %s\n" (Print.binders_to_string ", " bs);

    let vars, guards, env, decls, names = bs |> List.fold_left (fun (vars, guards, env, decls, names) b ->
        let v, g, env, decls', n =
            let x = unmangle (fst b) in
            let xxsym, xx, env' = gen_term_var env x in
            let guard_x_t, decls' = encode_term_pred fuel_opt (norm env x.sort) env xx in //if we had polarities, we could generate a mkHasTypeZ here in the negative case
            (xxsym, Term_sort),
            guard_x_t,
            env',
            decls',
            x in
        v::vars, g::guards, env, decls@decls', n::names) ([], [], env, [], []) in

    List.rev vars,
    List.rev guards,
    env,
    decls,
    List.rev names

and encode_term_pred (fuel_opt:option<term>) (t:typ) (env:env_t) (e:term) : term * decls_t =
    let t, decls = encode_term t env in
    mk_HasTypeWithFuel fuel_opt e t, decls

and encode_term_pred' (fuel_opt:option<term>) (t:typ) (env:env_t) (e:term) : term * decls_t =
    let t, decls = encode_term t env in
    match fuel_opt with
        | None -> mk_HasTypeZ e t, decls
        | Some f -> mk_HasTypeFuel f e t, decls

and encode_term (t:typ) (env:env_t) : (term         (* encoding of t, expects t to be in normal form already *)
                                     * decls_t)     (* top-level declarations to be emitted (for shared representations of existentially bound terms *) =

    let t0 = SS.compress t in
    if Env.debug env.tcenv <| Options.Other "SMTEncoding"
    then Util.print3 "(%s) (%s)   %s\n" (Print.tag_of_term t) (Print.tag_of_term t0) (Print.term_to_string t0);
    match t0.n with
      | Tm_delayed  _
      | Tm_unknown    -> failwith (format4 "(%s) Impossible: %s\n%s\n%s\n" (Range.string_of_range <| t.pos) (Print.tag_of_term t0) (Print.term_to_string t0) (Print.term_to_string t))

      | Tm_bvar x ->
        failwith (Util.format1 "Impossible: locally nameless; got %s" (Print.bv_to_string x))

      | Tm_ascribed(t, k, _) ->
        encode_term t env

      | Tm_meta(t, _) ->
        encode_term t env

      | Tm_name x ->
        let t = lookup_term_var env x in
        t, []

      | Tm_fvar v ->
        lookup_free_var env v.fv_name, []

      | Tm_type _ ->
        mk_Term_type, [] 

      | Tm_uinst(t, _) ->
        encode_term t env

      | Tm_constant c ->
        encode_const c, []

      | Tm_arrow(binders, c) ->
        let binders, res = SS.open_comp binders c in
        if  (env.encode_non_total_function_typ
             && Util.is_pure_or_ghost_comp res)
             || Util.is_tot_or_gtot_comp res
        then let vars, guards, env', decls, _ = encode_binders None binders env in
             let fsym = varops.fresh "f", Term_sort in
             let f = mkFreeV fsym in
             let app = mk_Apply f vars in
             let pre_opt, res_t = Util.pure_or_ghost_pre_and_post ({env.tcenv with lax=true}) res in
             let res_pred, decls' = encode_term_pred None res_t env' app in
             let guards, guard_decls = match pre_opt with
                | None -> mk_and_l guards, []
                | Some pre ->
                  let guard, decls0 = encode_formula pre env' in
                  mk_and_l (guard::guards), decls0  in
             let t_interp =
                       mkForall([[app]],
                                vars,
                                mkImp(guards, res_pred)) in

             let cvars = Term.free_variables t_interp |> List.filter (fun (x, _) -> x <> fst fsym) in
             let tkey = mkForall([], fsym::cvars, t_interp) in
             let tkey_hash = hash_of_term tkey in 
             begin match Util.smap_try_find env.cache tkey_hash with
                | Some (t', sorts, _) ->
                  mkApp(t', cvars |> List.map mkFreeV), []

                | None ->
                  let tsym = varops.mk_unique ("Tm_arrow_" ^ (Util.digest_of_string tkey_hash)) in
                  let cvar_sorts = List.map snd cvars in
                  let caption =
                    if Options.log_queries()
                    then Some (N.term_to_string env.tcenv t0)
                    else None in

                  let tdecl = Term.DeclFun(tsym, cvar_sorts, Term_sort, caption) in

                  let t = mkApp(tsym, List.map mkFreeV cvars) in
                  let t_has_kind = mk_HasType t mk_Term_type in

                  let k_assumption =
                    let a_name = Some ("kinding_"^tsym) in
                    Term.Assume(mkForall([[t_has_kind]], cvars, t_has_kind), a_name, a_name) in

                  let f_has_t = mk_HasType f t in
                  let f_has_t_z = mk_HasTypeZ f t in
                  let pre_typing =
                    let a_name = Some ("pre_typing_"^tsym) in
                    Term.Assume(mkForall_fuel([[f_has_t]], fsym::cvars, mkImp(f_has_t, mk_tester "Tm_arrow" (mk_PreType f))), Some "pre-typing for functions", a_name) in
                  let t_interp =
                    let a_name = Some ("interpretation_"^tsym) in
                    Term.Assume(mkForall([[f_has_t_z]], fsym::cvars, mkIff(f_has_t_z, t_interp)), a_name, a_name) in

                  let t_decls = tdecl::decls@decls'@guard_decls@[k_assumption; pre_typing; t_interp] in
                  Util.smap_add env.cache tkey_hash  (tsym, cvar_sorts, t_decls);
                  t, t_decls
             end

        else let tsym = varops.fresh "Non_total_Tm_arrow" in
             let tdecl = Term.DeclFun(tsym, [], Term_sort, None) in
             let t = mkApp(tsym, []) in
             let t_kinding = 
                let a_name = Some ("non_total_function_typing_" ^tsym) in
                Term.Assume(mk_HasType t mk_Term_type, Some "Typing for non-total arrows", a_name) in
             let fsym = "f", Term_sort in
             let f = mkFreeV fsym in
             let f_has_t = mk_HasType f t in
             let t_interp =
                 let a_name = Some ("pre_typing_" ^tsym) in
                 Term.Assume(mkForall_fuel([[f_has_t]], [fsym],
                                            mkImp(f_has_t,
                                                  mk_tester "Tm_arrow" (mk_PreType f))),
                             a_name, a_name) in

             t, [tdecl; t_kinding; t_interp] (* TODO: At least preserve alpha-equivalence of non-pure function types *)

      | Tm_refine _ ->
        let x, f = match N.normalize_refinement [N.WHNF; N.EraseUniverses] env.tcenv t0 with
            | {n=Tm_refine(x, f)} ->
               let b, f = SS.open_term [x, None] f in
               fst (List.hd b), f
            | _ -> failwith "impossible" in

        let base_t, decls = encode_term x.sort env in
        let x, xtm, env' = gen_term_var env x in
        let refinement, decls' = encode_formula f env' in

        let fsym, fterm = fresh_fvar "f" Fuel_sort in

        let encoding = mkAnd(mk_HasTypeWithFuel (Some fterm) xtm base_t, refinement) in

        let cvars = Term.free_variables encoding |> List.filter (fun (y, _) -> y <> x && y <> fsym) in
        let xfv = (x, Term_sort) in
        let ffv = (fsym, Fuel_sort) in
        let tkey = mkForall([], ffv::xfv::cvars, encoding) in
        let tkey_hash = Term.hash_of_term tkey in
        begin match Util.smap_try_find env.cache tkey_hash with
            | Some (t, _, _) ->
              mkApp(t, cvars |> List.map mkFreeV), []

            | None ->
              let tsym = varops.mk_unique ("Tm_refine_" ^ (Util.digest_of_string tkey_hash)) in
              let cvar_sorts = List.map snd cvars in
              let tdecl = Term.DeclFun(tsym, cvar_sorts, Term_sort, None) in
              let t = mkApp(tsym, List.map mkFreeV cvars) in

              let x_has_t = mk_HasTypeWithFuel (Some fterm) xtm t in
              let t_has_kind = mk_HasType t mk_Term_type in

              //add hasEq axiom for this refinement type
              let t_haseq_base = mk_haseq base_t in
              let t_haseq_ref = mk_haseq t in

              let t_haseq = Assume (mkForall ([[t_haseq_ref]], cvars, (mkIff (t_haseq_ref, t_haseq_base))),
                                    Some ("haseq for " ^ tsym), Some ("haseq" ^ tsym)) in

              let t_kinding = Assume(mkForall([[t_has_kind]], cvars, t_has_kind),
                                     Some "refinement kinding",
                                     Some ("refinement_kinding_" ^tsym)) in //TODO: guard by typing of cvars?; not necessary since we have pattern-guarded
              let t_interp = Assume(mkForall([[x_has_t]], ffv::xfv::cvars, mkIff(x_has_t, encoding)),
                                    Some (Print.term_to_string t0),
                                    Some("refinement_interpretation_"^tsym)) in

              let t_decls = decls
                            @decls'
                            @[tdecl;
                              t_kinding;
                              t_interp;t_haseq] in
              Util.smap_add env.cache tkey_hash (tsym, cvar_sorts, t_decls);
              t, t_decls
        end

      | Tm_uvar (uv, k) ->
        let ttm = mk_Term_uvar (Unionfind.uvar_id uv) in
        let t_has_k, decls = encode_term_pred None k env ttm in //TODO: skip encoding this if it has already been encoded before
        let d = Term.Assume(t_has_k, Some "Uvar typing", Some (varops.mk_unique (Util.format1 "uvar_typing_%s" (Util.string_of_int <| Unionfind.uvar_id uv)))) in
        ttm, decls@[d]

      | Tm_app _ ->
        let head, args_e = Util.head_and_args t0 in
        (* if Env.debug env.tcenv <| Options.Other "SMTEncoding" *)
        (* then printfn "Encoding app head=%s, n_args=%d" (Print.term_to_string head) (List.length args_e); *)
        begin match (SS.compress head).n, args_e with
            | _, _ when head_redex env head -> encode_term (whnf env t) env

            | Tm_uinst({n=Tm_fvar fv}, _), [_; (v1, _); (v2, _)]
            | Tm_fvar fv,  [_; (v1, _); (v2, _)] when S.fv_eq_lid fv Const.lexcons_lid ->
              //lex tuples are primitive
              let v1, decls1 = encode_term v1 env in
              let v2, decls2 = encode_term v2 env in
              mk_LexCons v1 v2, decls1@decls2

            | Tm_constant Const_reify, (_::_::_) ->
              let e0 = S.mk (S.Tm_app(head, [List.hd args_e])) None head.pos in
              let e = S.mk (S.Tm_app(e0, List.tl args_e)) None t0.pos in
              encode_term e env

            | Tm_constant Const_reify, [(arg, _)] -> 
              let tm, decls = encode_term arg env in 
              mkApp("Reify", [tm]), decls

            | Tm_constant (Const_reflect _), [(arg, _)] ->
              encode_term arg env

            | _ ->
            let args, decls = encode_args args_e env in

            let encode_partial_app ht_opt =
                let head, decls' = encode_term head env in
                let app_tm = mk_Apply_args head args in
                begin match ht_opt with
                    | None -> app_tm, decls@decls'
                    | Some (formals, c) ->
                        let formals, rest = Util.first_N (List.length args_e) formals in
                        let subst = List.map2 (fun (bv, _) (a, _) -> Syntax.NT(bv, a)) formals args_e in
                        let ty = Util.arrow rest c |> SS.subst subst in
                        let has_type, decls'' = encode_term_pred None ty env app_tm in
                        let cvars = Term.free_variables has_type in
                        let e_typing = Term.Assume(mkForall([[has_type]], cvars, has_type), 
                                                   Some "Partial app typing", 
                                                   Some (varops.mk_unique ("partial_app_typing_" ^ 
                                                        (Util.digest_of_string (Term.hash_of_term app_tm))))) in
                        app_tm, decls@decls'@decls''@[e_typing]
                end in

            let encode_full_app fv =
                let fname, fuel_args = lookup_free_var_sym env fv in
                let tm = mkApp'(fname, fuel_args@args) in
                tm, decls in

            let head = SS.compress head in

            let head_type = match head.n with
                | Tm_uinst({n=Tm_name x}, _)
                | Tm_name x -> Some x.sort
                | Tm_uinst({n=Tm_fvar fv}, _)
                | Tm_fvar fv -> Some (Env.lookup_lid env.tcenv fv.fv_name.v |> snd)
                | Tm_ascribed(_, Inl t, _) -> Some t
                | Tm_ascribed(_, Inr c, _) -> Some (Util.comp_result c)
                | _ -> None in

            begin match head_type with
                | None -> encode_partial_app None
                | Some head_type ->
                  let head_type = Util.unrefine <| N.normalize_refinement [N.WHNF; N.EraseUniverses] env.tcenv head_type in
                  let formals, c = curried_arrow_formals_comp head_type in
                  begin match head.n with
                        | Tm_uinst({n=Tm_fvar fv}, _)
                        | Tm_fvar fv when (List.length formals = List.length args) -> encode_full_app fv.fv_name
                        | _ ->
                            if List.length formals > List.length args
                            then encode_partial_app (Some (formals, c))
                            else encode_partial_app None

                 end
            end
      end

      | Tm_abs(bs, body, lopt) ->
          let bs, body, opening = SS.open_term' bs body in
          let fallback () =
            let f = varops.fresh "Tm_abs" in
            let decl = Term.DeclFun(f, [], Term_sort, Some "Imprecise function encoding") in
            mkFreeV(f, Term_sort), [decl] 
          in

          let is_impure = function
            | Inl lc -> not (Util.is_pure_or_ghost_lcomp lc)
            | Inr (eff, _) -> TypeChecker.Util.is_pure_or_ghost_effect env.tcenv eff |> not
          in

          let codomain_eff lc = match lc with
            | Inl lc -> SS.subst_comp opening (lc.comp()) |> Some
            | Inr (eff, flags) ->
                let new_uvar () = FStar.TypeChecker.Rel.new_uvar Range.dummyRange [] (Util.ktype0) |> fst in
                if Ident.lid_equals eff Const.effect_Tot_lid
                then S.mk_Total (new_uvar()) |> Some
                else if Ident.lid_equals eff Const.effect_GTot_lid
                then S.mk_GTotal (new_uvar()) |> Some
                (* TODO (KM) : shouldn't we do something when flags contains TOTAL ? *)
                else None
          in

          begin match lopt with
            | None -> //we don't even know if this is a pure function, so give up
              Errors.warn t0.pos (Util.format1 "Losing precision when encoding a function literal: %s" (Print.term_to_string t0));
              fallback ()

            | Some lc ->
              if is_impure lc
              then fallback() //we know it's not pure; so don't encode it precisely
              else let vars, guards, envbody, decls, _ = encode_binders None bs env in
                   let body, decls' = encode_term body envbody in
                   let key_body = mkForall([], vars, mkImp(mk_and_l guards, body)) in
                   let cvars = Term.free_variables key_body in
                   let tkey = mkForall([], cvars, key_body) in
                   let tkey_hash = Term.hash_of_term tkey in
                   match Util.smap_try_find env.cache tkey_hash with
                   | Some (t, _, _) -> mkApp(t, List.map mkFreeV cvars), []
                   | None ->
                     match is_eta env vars body with
                     | Some t -> t, []
                     | None ->
                        let cvar_sorts = List.map snd cvars in
                        let fsym = varops.mk_unique ("Tm_abs_" ^ (Util.digest_of_string tkey_hash)) in
                        let fdecl = Term.DeclFun(fsym, cvar_sorts, Term_sort, None) in
                        let f = mkApp(fsym, List.map mkFreeV cvars) in
                        let app = mk_Apply f vars in
                        let typing_f =
                            match codomain_eff lc with
                            | None -> [] //no typing axiom for this lambda, because we don't have enough info
                            | Some c ->
                                let tfun = Util.arrow bs c in
                                let f_has_t, decls'' = encode_term_pred None tfun env f in
                                let a_name = Some("typing_"^fsym) in
                                decls''@[Term.Assume(mkForall([[f]], cvars, f_has_t), a_name, a_name)] in
                        let interp_f = 
                            let a_name = Some ("interpretation_" ^fsym) in
                            Term.Assume(mkForall([[app]], vars@cvars, mkEq(app, body)), a_name, a_name) in
                        let f_decls = decls@decls'@(fdecl::typing_f)@[interp_f] in
                        Util.smap_add env.cache tkey_hash (fsym, cvar_sorts, f_decls);
                        f, f_decls
          end

      | Tm_let((_, {lbname=Inr _}::_), _) ->
        failwith "Impossible: already handled by encoding of Sig_let"

      | Tm_let((false, [{lbname=Inl x; lbtyp=t1; lbdef=e1}]), e2) ->
        encode_let x t1 e1 e2 env encode_term

      | Tm_let _ ->
        Errors.diag t0.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
        let e = varops.fresh "let-rec" in
        let decl_e = Term.DeclFun(e, [], Term_sort, None) in
        mkFreeV(e, Term_sort), [decl_e]

      | Tm_match(e, pats) ->
        encode_match e pats mk_Term_unit env encode_term

and encode_let x t1 e1 e2 env (encode_body:S.term -> env_t -> (term * decls_t)) : term * decls_t =
    let ee1, decls1 = encode_term e1 env in
    let xs, e2 = SS.open_term [(x, None)] e2 in
    let x, _ = List.hd xs in
    let env' = push_term_var env x ee1 in
    let ee2, decls2 = encode_body e2 env' in
    ee2, decls1@decls2

and encode_match e pats default_case env (encode_br:S.term -> env_t -> (term * decls_t)) : term * decls_t =
    let scr, decls = encode_term e env in
    let match_tm, decls = List.fold_right (fun b (else_case, decls) ->
        let p, w, br = SS.open_branch b in
        let patterns = encode_pat env p in
        List.fold_right (fun (env0, pattern) (else_case, decls) ->
            let guard = pattern.guard scr in
            let projections = pattern.projections scr in
            let env = projections |> List.fold_left (fun env (x, t) -> push_term_var env x t) env in
            let guard, decls2 = match w with
                | None -> guard, []
                | Some w ->
                    let w, decls2 = encode_term w env in
                    mkAnd(guard, mkEq(w, Term.boxBool mkTrue)), decls2 in
            let br, decls3 = encode_br br env in
            mkITE(guard, br, else_case), decls@decls2@decls3)
        patterns (else_case, decls))
        pats
        (default_case (* default; should be unreachable *), decls) in
    match_tm, decls


and encode_pat env (pat:Syntax.pat) : list<(env_t * pattern)>  (* one for each disjunct *) =
    match pat.v with
        | Pat_disj ps -> List.map (encode_one_pat env) ps
        | _ -> [encode_one_pat env pat]

and encode_one_pat (env:env_t) pat : (env_t * pattern) =
        if Env.debug env.tcenv Options.Low then Util.print1 "Encoding pattern %s\n" (Print.pat_to_string pat);
        let vars, pat_term = Util.decorated_pattern_as_term pat in

        let env, vars = vars |> List.fold_left (fun (env, vars) v ->
              let xx, _, env = gen_term_var env v in
              env, (v, (xx, Term_sort))::vars) (env, []) in

        let rec mk_guard pat (scrutinee:term) : term = match pat.v with
            | Pat_disj _ -> failwith "Impossible"
            | Pat_var _
            | Pat_wild _
            | Pat_dot_term _ -> mkTrue
            | Pat_constant c ->
               mkEq(scrutinee, encode_const c)
            | Pat_cons(f, args) ->
                let is_f = mk_data_tester env f.fv_name.v scrutinee in
                let sub_term_guards = args |> List.mapi (fun i (arg, _) ->
                    let proj = primitive_projector_by_pos env.tcenv f.fv_name.v i in
                    mk_guard arg (mkApp(proj, [scrutinee]))) in
                mk_and_l (is_f::sub_term_guards) in

         let rec mk_projections pat (scrutinee:term) =  match pat.v with
            | Pat_disj _ -> failwith "Impossible"

            | Pat_dot_term (x, _)
            | Pat_var x
            | Pat_wild x -> [x, scrutinee]

            | Pat_constant _ -> []

            | Pat_cons(f, args) ->
                args
                |> List.mapi (fun i (arg, _) ->
                    let proj = primitive_projector_by_pos env.tcenv f.fv_name.v i in
                    mk_projections arg (mkApp(proj, [scrutinee])))
                |> List.flatten in

        let pat_term () = encode_term pat_term env in

        let pattern = {
                pat_vars=vars;
                pat_term=pat_term;
                guard=mk_guard pat;
                projections=mk_projections pat;
            }  in

        env, pattern

and encode_args l env : (list<term> * decls_t)  =
    let l, decls = l |> List.fold_left
        (fun (tms, decls) (t, _) -> let t, decls' = encode_term t env in t::tms, decls@decls')
        ([], []) in
    List.rev l, decls

(* this assumes t is a Lemma *)
and encode_function_type_as_formula (induction_on:option<term>) (new_pats:option<S.term>) (t:typ) (env:env_t) : term * decls_t =
    let list_elements (e:S.term) : list<S.term> =
      match Syntax.Util.list_elements e with
      | Some l -> l
      | None -> Errors.warn e.pos "SMT pattern is not a list literal; ignoring the pattern"; [] in

    let one_pat p =
        let head, args = Util.unmeta p |> Util.head_and_args in
        match (Util.un_uinst head).n, args with
        | Tm_fvar fv, [(_, _); (e, _)] when S.fv_eq_lid fv Const.smtpat_lid -> (e, None)
        | Tm_fvar fv, [(e, _)] when S.fv_eq_lid fv Const.smtpatT_lid -> (e, None)
        | _ -> failwith "Unexpected pattern term"  in

    let lemma_pats p =
        let elts = list_elements p in
        let smt_pat_or t =
            let head, args = Util.unmeta t |> Util.head_and_args in
            match (Util.un_uinst head).n, args with
                | Tm_fvar fv, [(e, _)] when S.fv_eq_lid fv Const.smtpatOr_lid ->
                  Some e
                | _ -> None in
        match elts with
            | [t] ->
             begin match smt_pat_or t with
                | Some e ->
                  list_elements e |>  List.map (fun branch -> (list_elements branch) |> List.map one_pat)
                | _ -> [elts |> List.map one_pat]
              end
            | _ -> [elts |> List.map one_pat] in

    let binders, pre, post, patterns = match (SS.compress t).n with
        | Tm_arrow(binders, c) ->
          let binders, c = SS.open_comp binders c in
          begin match c.n with
            | Comp ({effect_args=[(pre, _); (post, _); (pats, _)]}) ->
              let pats' = (match new_pats with
                          | Some new_pats' -> new_pats'
                          | None           -> pats) in
              binders, pre, post, lemma_pats pats'
            | _ -> failwith "impos"
          end

        | _ -> failwith "Impos" in

    let vars, guards, env, decls, _ = encode_binders None binders env in


    let pats, decls' = patterns |> List.map (fun branch ->
        let pats, decls = branch |> List.map (fun (t, _) ->  encode_term t ({env with use_zfuel_name=true})) |> List.unzip in
        pats, decls) |> List.unzip in

    let decls' = List.flatten decls' in

    let pats =
        match induction_on with
            | None -> pats
            | Some e ->
               begin match vars with
                | [] -> pats
                | [l] -> pats |> List.map (fun p -> mk_Precedes (mkFreeV l) e::p)
                | _ ->
                  let rec aux tl vars = match vars with
                    | [] -> pats |> List.map (fun p -> mk_Precedes tl e::p)
                    | (x, Term_sort)::vars -> aux (mk_LexCons (mkFreeV(x,Term_sort)) tl) vars
                    | _ -> pats in
                  aux (mkFreeV ("Prims.LexTop", Term_sort)) vars
               end in

    let env = {env with nolabels=true} in
    let pre, decls'' = encode_formula (Util.unmeta pre) env in
    let post, decls''' = encode_formula (Util.unmeta post) env in
    let decls = decls@(List.flatten decls')@decls''@decls''' in
    mkForall(pats, vars, mkImp(mk_and_l (pre::guards), post)), decls

and encode_formula (phi:typ) (env:env_t) : (term * decls_t)  = (* expects phi to be normalized; the existential variables are all labels *)
    let debug phi =
       if Env.debug env.tcenv <| Options.Other "SMTEncoding"
       then Util.print2 "Formula (%s)  %s\n"
                     (Print.tag_of_term phi)
                     (Print.term_to_string phi) in
    let enc (f:list<term> -> term) : Range.range -> args -> (term * decls_t) = fun r l ->
        let decls, args = Util.fold_map (fun decls x -> let t, decls' = encode_term (fst x) env in decls@decls', t) [] l in
        ({f args with rng=r}, decls) in

    let const_op f r _ = (f r, []) in
    let un_op f l = f <| List.hd l in
    let bin_op : ((term * term) -> term) -> list<term> -> term = fun f -> function
        | [t1;t2] -> f(t1,t2)
        | _ -> failwith "Impossible" in

    let enc_prop_c f : Range.range -> args -> (term * decls_t) = fun r l ->
        let decls, phis =
            Util.fold_map (fun decls (t, _) ->
                let phi, decls' = encode_formula t env in
                decls@decls', phi)
            [] l in
        ({f phis with rng=r}, decls) in

    let eq_op r : args -> (term * decls_t) = function
        | [_; e1; e2]
        | [_;_;e1;e2] -> enc  (bin_op mkEq) r [e1;e2]
        | l -> enc (bin_op mkEq) r l in

    let mk_imp r : args -> (term * decls_t) = function
        | [(lhs, _); (rhs, _)] ->
          let l1, decls1 = encode_formula rhs env in
          begin match l1.tm with
            | App(True, _) -> (l1, decls1) (* Optimization: don't bother encoding the LHS of a trivial implication *)
            | _ ->
             let l2, decls2 = encode_formula lhs env in
             (Term.mkImp(l2, l1) r, decls1@decls2)
          end
         | _ -> failwith "impossible" in

    let mk_ite  r: args -> (term * decls_t) = function
        | [(guard, _); (_then, _); (_else, _)] ->
          let (g, decls1) = encode_formula guard env in
          let (t, decls2) = encode_formula _then env in
          let (e, decls3) = encode_formula _else env in
          let res = Term.mkITE(g, t, e) r in
          res, decls1@decls2@decls3
        | _ -> failwith "impossible" in


    let unboxInt_l : (list<term> -> term) -> list<term> -> term = fun f l -> f (List.map Term.unboxInt l) in
    let connectives = [
        (Const.and_lid,   enc_prop_c <| bin_op mkAnd);
        (Const.or_lid,    enc_prop_c <| bin_op mkOr);
        (Const.imp_lid,   mk_imp);
        (Const.iff_lid,   enc_prop_c <| bin_op mkIff);
        (Const.ite_lid,   mk_ite);
        (Const.not_lid,   enc_prop_c <| un_op mkNot);
        (Const.eq2_lid,   eq_op);
        (Const.eq3_lid,   eq_op);
        (Const.true_lid,  const_op Term.mkTrue);
        (Const.false_lid, const_op Term.mkFalse);
    ] in

    let rec fallback phi =  match phi.n with
        | Tm_meta(phi', Meta_labeled(msg, r, b)) ->
          let phi, decls = encode_formula phi' env in
          mk (Term.Labeled(phi, msg, r)) r, decls

        | Tm_meta _ ->
          encode_formula (Util.unmeta phi) env

        | Tm_match(e, pats) -> 
           let t, decls = encode_match e pats mkFalse env encode_formula in
           t, decls

        | Tm_let((false, [{lbname=Inl x; lbtyp=t1; lbdef=e1}]), e2) ->
           let t, decls = encode_let x t1 e1 e2 env encode_formula in
           t, decls

        | Tm_app(head, args) ->
          let head = Util.un_uinst head in
          begin match head.n, args with
            | Tm_fvar fv, [_; (x, _); (t, _)] when S.fv_eq_lid fv Const.has_type_lid -> //interpret Prims.has_type as HasType
              let x, decls = encode_term x env in
              let t, decls' = encode_term t env in
              mk_HasType x t, decls@decls'

            | Tm_fvar fv, [(r, _); (msg, _); (phi, _)] when S.fv_eq_lid fv Const.labeled_lid -> //interpret (labeled r msg t) as Tm_meta(t, Meta_labeled(msg, r, false)
              begin match (SS.compress r).n, (SS.compress msg).n with
                | Tm_constant (Const_range r), Tm_constant (Const_string (s, _)) ->
                  let phi = S.mk (Tm_meta(phi,  Meta_labeled(Util.string_of_unicode s, r, false))) None r in
                  fallback phi
                | _ ->
                  fallback phi
              end

            | _ when head_redex env head ->
              encode_formula (whnf env phi) env

            | _ ->
              let tt, decls = encode_term phi env in
              mk_Valid ({tt with rng=phi.pos}), decls
          end

        | _ ->
            let tt, decls = encode_term phi env in
            mk_Valid ({tt with rng=phi.pos}), decls in

    let encode_q_body env (bs:Syntax.binders) (ps:list<args>) body =
        let vars, guards, env, decls, _ = encode_binders None bs env in
        let pats, decls' = ps |> List.map (fun p ->
          let p, decls = p |> List.map (fun (t, _) -> encode_term t ({env with use_zfuel_name=true})) |> List.unzip in
           p, List.flatten decls) |> List.unzip in
        let body, decls'' = encode_formula body env in
    let guards = match pats with
	  | [[{tm=App(Var gf, [p])}]] when Ident.text_of_lid Const.guard_free = gf -> []
	  | _ -> guards in
        vars, pats, mk_and_l guards, body, decls@List.flatten decls'@decls'' in

    debug phi;

    let phi = Util.unascribe phi in
    let check_pattern_vars vars pats =
        let pats = pats |> List.map (fun (x, _) -> N.normalize [N.Beta;N.AllowUnboundUniverses;N.EraseUniverses] env.tcenv x) in
        begin match pats with
        | [] -> ()
        | hd::tl ->
          let pat_vars = List.fold_left (fun out x -> Util.set_union out (Free.names x)) (Free.names hd) tl in
          match vars |> Util.find_opt (fun (b, _) -> not(Util.set_mem b pat_vars)) with
          | None -> ()
          | Some (x,_) ->
            let pos = List.fold_left (fun out t -> Range.union_ranges out t.pos) hd.pos tl in
            Errors.warn pos (Util.format1 "Pattern misses at least one bound variable: %s" (Print.bv_to_string x))
        end
    in
    match Util.destruct_typ_as_formula phi with
        | None -> fallback phi

        | Some (Util.BaseConn(op, arms)) ->
          (match connectives |> List.tryFind (fun (l, _) -> lid_equals op l) with
             | None -> fallback phi
             | Some (_, f) -> f phi.pos arms)

        | Some (Util.QAll(vars, pats, body)) ->
          pats |> List.iter (check_pattern_vars vars);
          let vars, pats, guard, body, decls = encode_q_body env vars pats body in
          let tm = Term.mkForall(pats, vars, mkImp(guard, body)) phi.pos in
          tm, decls

        | Some (Util.QEx(vars, pats, body)) ->
          pats |> List.iter (check_pattern_vars vars);
          let vars, pats, guard, body, decls = encode_q_body env vars pats body in
          Term.mkExists(pats, vars, mkAnd(guard, body)) phi.pos, decls

(***************************************************************************************************)
(* end main encoding of kinds/types/exps/formulae *)
(***************************************************************************************************)

(* ----------------------------------------------------------------------------------------------- *)

type prims_t = {
    mk:lident -> string -> term * list<decl>;
    is:lident -> bool;
}


let prims =
    let asym, a = fresh_fvar "a" Term_sort in
    let xsym, x = fresh_fvar "x" Term_sort in
    let ysym, y = fresh_fvar "y" Term_sort in
    let quant vars body : string -> term * list<decl> = fun x ->
        let xname_decl = Term.DeclFun(x, vars |> List.map snd, Term_sort, None) in
        let xtok = x ^ "@tok" in
        let xtok_decl = Term.DeclFun(xtok, [], Term_sort, None) in
        let xapp = mkApp(x, List.map mkFreeV vars) in
        let xtok = mkApp(xtok, []) in
        let xtok_app = mk_Apply xtok vars in
        xtok,
        [xname_decl;
         xtok_decl;
         Term.Assume(mkForall([[xapp]], vars, mkEq(xapp, body)), None, Some ("primitive_" ^x));
         Term.Assume(mkForall([[xtok_app]], vars, mkEq(xtok_app, xapp)),
                                                                Some "Name-token correspondence",
                                                                Some ("token_correspondence_"^x))]
    in
    let axy = [(asym, Term_sort); (xsym, Term_sort); (ysym, Term_sort)] in
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
        (Const.op_Minus,       (quant qx  (boxInt  <| mkMinus(unboxInt x))));
        (Const.op_Addition,    (quant xy  (boxInt  <| mkAdd(unboxInt x, unboxInt y))));
        (Const.op_Multiply,    (quant xy  (boxInt  <| mkMul(unboxInt x, unboxInt y))));
        (Const.op_Division,    (quant xy  (boxInt  <| mkDiv(unboxInt x, unboxInt y))));
        (Const.op_Modulus,     (quant xy  (boxInt  <| mkMod(unboxInt x, unboxInt y))));
        (Const.op_And,         (quant xy  (boxBool <| mkAnd(unboxBool x, unboxBool y))));
        (Const.op_Or,          (quant xy  (boxBool <| mkOr(unboxBool x, unboxBool y))));
        (Const.op_Negation,    (quant qx  (boxBool <| mkNot(unboxBool x))));
        ] in
    let mk : lident -> string -> term * list<decl> =
        fun l v -> prims |> List.find (fun (l', _) -> lid_equals l l') |> Option.map (fun (_, b) -> b v) |> Option.get in
    let is : lident -> bool =
        fun l -> prims |> Util.for_some (fun (l', _) -> lid_equals l l') in
    {mk=mk;
     is=is}

let pretype_axiom tapp vars =
    let xxsym, xx = fresh_fvar "x" Term_sort in
    let ffsym, ff = fresh_fvar "f" Fuel_sort in
    let xx_has_type = mk_HasTypeFuel ff xx tapp in
    let tapp_hash = Term.hash_of_term tapp in
    Term.Assume(mkForall([[xx_has_type]], (xxsym, Term_sort)::(ffsym, Fuel_sort)::vars,
                         mkImp(xx_has_type, mkEq(tapp, mkApp("PreType", [xx])))), Some "pretyping", Some (varops.mk_unique ("pretyping_" ^ (Util.digest_of_string tapp_hash))))

let primitive_type_axioms : env -> lident -> string -> term -> list<decl> =
    let xx = ("x", Term_sort) in
    let x = mkFreeV xx in

    let yy = ("y", Term_sort) in
    let y = mkFreeV yy in

    let mk_unit : env -> string -> term -> decls_t = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        [Term.Assume(mk_HasType mk_Term_unit tt, Some "unit typing", Some "unit_typing");
         Term.Assume(mkForall_fuel([[typing_pred]], [xx], mkImp(typing_pred, mkEq(x, mk_Term_unit))),  Some "unit inversion", Some "unit_inversion");] in
    let mk_bool : env -> string -> term -> decls_t = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        let bb = ("b", Bool_sort) in
        let b = mkFreeV bb in
        [Term.Assume(mkForall([[Term.boxBool b]], [bb], mk_HasType (Term.boxBool b) tt), Some "bool typing", Some "bool_typing");
         Term.Assume(mkForall_fuel([[typing_pred]], [xx], mkImp(typing_pred, mk_tester "BoxBool" x)), Some "bool inversion", Some "bool_inversion")] in
    let mk_int : env -> string -> term -> decls_t  = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        let typing_pred_y = mk_HasType y tt in
        let aa = ("a", Int_sort) in
        let a = mkFreeV aa in
        let bb = ("b", Int_sort) in
        let b = mkFreeV bb in
        let precedes = mk_Valid <| mkApp("Prims.Precedes", [tt;tt;Term.boxInt a; Term.boxInt b]) in
        let precedes_y_x = mk_Valid <| mkApp("Precedes", [y; x]) in
        [Term.Assume(mkForall([[Term.boxInt b]], [bb], mk_HasType (Term.boxInt b) tt), Some "int typing", Some "int_typing");
         Term.Assume(mkForall_fuel([[typing_pred]], [xx], mkImp(typing_pred, mk_tester "BoxInt" x)), Some "int inversion", Some "int_inversion");
         Term.Assume(mkForall_fuel([[typing_pred; typing_pred_y;precedes_y_x]],
                                   [xx;yy],
                                   mkImp(mk_and_l [typing_pred;
                                                   typing_pred_y;
                                                   mkGT (Term.unboxInt x, mkInteger' 0);
                                                   mkGTE (Term.unboxInt y, mkInteger' 0);
                                                   mkLT (Term.unboxInt y, Term.unboxInt x)],
                                         precedes_y_x)),
                                  Some "well-founded ordering on nat (alt)", Some "well-founded-ordering-on-nat")] in
    let mk_str : env -> string -> term -> decls_t  = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        let bb = ("b", String_sort) in
        let b = mkFreeV bb in
        [Term.Assume(mkForall([[Term.boxString b]], [bb], mk_HasType (Term.boxString b) tt), Some "string typing", Some "string_typing");
         Term.Assume(mkForall_fuel([[typing_pred]], [xx], mkImp(typing_pred, mk_tester "BoxString" x)),  Some "string inversion", Some "string_inversion")] in
    let mk_ref : env -> string -> term -> decls_t = fun env reft_name _ ->
        let r = ("r", Ref_sort) in
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let refa = mkApp(reft_name, [mkFreeV aa]) in
        let refb = mkApp(reft_name, [mkFreeV bb]) in
        let typing_pred = mk_HasType x refa in
        let typing_pred_b = mk_HasType x refb in
        [Term.Assume(mkForall_fuel([[typing_pred]], [xx;aa], mkImp(typing_pred, mk_tester "BoxRef" x)), Some "ref inversion", Some "ref_inversion");
         Term.Assume(mkForall_fuel' 2 ([[typing_pred; typing_pred_b]], [xx;aa;bb], mkImp(mkAnd(typing_pred, typing_pred_b), mkEq(mkFreeV aa, mkFreeV bb))), Some "ref typing is injective", Some "ref_injectivity")] in
    let mk_true_interp : env -> string -> term -> decls_t = fun env nm true_tm ->
        let valid = mkApp("Valid", [true_tm]) in
        [Term.Assume(valid, Some "True interpretation", Some "true_interp")] in
    let mk_false_interp : env -> string -> term -> decls_t = fun env nm false_tm ->
        let valid = mkApp("Valid", [false_tm]) in
        [Term.Assume(mkIff(mkFalse, valid), Some "False interpretation", Some "false_interp")] in
    let mk_and_interp : env -> string -> term -> decls_t = fun env conj _ ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = mkApp("Valid", [mkApp(conj, [a;b])]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        [Term.Assume(mkForall([[valid]], [aa;bb], mkIff(mkAnd(valid_a, valid_b), valid)), Some "/\ interpretation", Some "l_and-interp")] in
    let mk_or_interp : env -> string -> term -> decls_t = fun env disj _ ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = mkApp("Valid", [mkApp(disj, [a;b])]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        [Term.Assume(mkForall([[valid]], [aa;bb], mkIff(mkOr(valid_a, valid_b), valid)), Some "\/ interpretation", Some "l_or-interp")] in
    let mk_eq2_interp : env -> string -> term -> decls_t = fun env eq2 tt ->
        let aa = ("a", Term_sort) in
        let xx = ("x", Term_sort) in
        let yy = ("y", Term_sort) in
        let a = mkFreeV aa in
        let x = mkFreeV xx in
        let y = mkFreeV yy in
        let valid = mkApp("Valid", [mkApp(eq2, [a;x;y])]) in
        [Term.Assume(mkForall([[valid]], [aa;xx;yy], mkIff(mkEq(x, y), valid)), Some "Eq2 interpretation", Some "eq2-interp")] in
    let mk_eq3_interp : env -> string -> term -> decls_t = fun env eq3 tt ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let xx = ("x", Term_sort) in
        let yy = ("y", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let x = mkFreeV xx in
        let y = mkFreeV yy in
        let valid = mkApp("Valid", [mkApp(eq3, [a;b;x;y])]) in
        [Term.Assume(mkForall([[valid]], [aa;bb;xx;yy], mkIff(mkEq(x, y), valid)), Some "Eq3 interpretation", Some "eq3-interp")] in
    let mk_imp_interp : env -> string -> term -> decls_t = fun env imp tt ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = mkApp("Valid", [mkApp(imp, [a;b])]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        [Term.Assume(mkForall([[valid]], [aa;bb], mkIff(mkImp(valid_a, valid_b), valid)), Some "==> interpretation", Some "l_imp-interp")] in
    let mk_iff_interp : env -> string -> term -> decls_t = fun env iff tt ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let valid = mkApp("Valid", [mkApp(iff, [a;b])]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        [Term.Assume(mkForall([[valid]], [aa;bb], mkIff(mkIff(valid_a, valid_b), valid)), Some "<==> interpretation", Some "l_iff-interp")] in
    let mk_not_interp : env -> string -> term -> decls_t = fun env l_not tt ->
        let aa = ("a", Term_sort) in
        let a = mkFreeV aa in
        let valid = mkApp("Valid", [mkApp(l_not, [a])]) in
        let not_valid_a = mkNot <| mkApp("Valid", [a]) in
        [Term.Assume(mkForall([[valid]], [aa], mkIff(not_valid_a, valid)), Some "not interpretation", Some "l_not-interp")] in
    let mk_forall_interp : env -> string -> term -> decls_t = fun env for_all tt ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let xx = ("x", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let x = mkFreeV xx in
        let valid = mkApp("Valid", [mkApp(for_all, [a;b])]) in
        let valid_b_x = mkApp("Valid", [mk_ApplyTT b x]) in
        [Term.Assume(mkForall([[valid]], [aa;bb], mkIff(mkForall([[mk_HasTypeZ x a]], [xx], mkImp(mk_HasTypeZ x a, valid_b_x)), valid)), 
                     Some "forall interpretation", 
                     Some "forall-interp")] in
    let mk_exists_interp : env -> string -> term -> decls_t = fun env for_some tt ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let xx = ("x", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let x = mkFreeV xx in
        let valid = mkApp("Valid", [mkApp(for_some, [a;b])]) in
        let valid_b_x = mkApp("Valid", [mk_ApplyTT b x]) in
        [Term.Assume(mkForall([[valid]], [aa;bb], mkIff(mkExists([[mk_HasTypeZ x a]], [xx], mkImp(mk_HasTypeZ x a, valid_b_x)), valid)), 
                     Some "exists interpretation", 
                     Some "exists-interp")] in
   let mk_range_interp : env -> string -> term -> decls_t = fun env range tt ->
        let range_ty = mkApp(range, []) in
        [Term.Assume(mk_HasTypeZ mk_Range_const range_ty, Some "Range_const typing", Some (varops.mk_unique "typing_range_const"))] in

   let prims =  [(Const.unit_lid,   mk_unit);
                 (Const.bool_lid,   mk_bool);
                 (Const.int_lid,    mk_int);
                 (Const.string_lid, mk_str);
                 (Const.ref_lid,    mk_ref);
                 (Const.true_lid,   mk_true_interp);
                 (Const.false_lid,  mk_false_interp);
                 (Const.and_lid,    mk_and_interp);
                 (Const.or_lid,     mk_or_interp);
                 (Const.eq2_lid,    mk_eq2_interp);
                 (Const.eq3_lid,    mk_eq3_interp);
                 (Const.imp_lid,    mk_imp_interp);
                 (Const.iff_lid,    mk_iff_interp);
                 (Const.not_lid,    mk_not_interp);
                 (Const.forall_lid, mk_forall_interp);
                 (Const.exists_lid, mk_exists_interp);
                 (Const.range_lid,  mk_range_interp);
                ] in
    (fun (env:env) (t:lident) (s:string) (tt:term) ->
        match Util.find_opt (fun (l, _) -> lid_equals l t) prims with
            | None -> []
            | Some(_, f) -> f env s tt)

let encode_smt_lemma env fv t =
    let lid = fv.fv_name.v in
    let form, decls = encode_function_type_as_formula None None t env in
    decls@[Term.Assume(form, Some ("Lemma: " ^ lid.str), Some ("lemma_"^lid.str))]

let encode_free_var env fv tt t_norm quals =
    let lid = fv.fv_name.v in
    if not <| Util.is_pure_or_ghost_function t_norm
    || Util.is_lemma t_norm
    then let vname, vtok, env = new_term_constant_and_tok_from_lid env lid in
         let arg_sorts = match (SS.compress t_norm).n with
            | Tm_arrow(binders, _) -> binders |> List.map (fun _ -> Term_sort)
            | _ -> [] in
         let d = Term.DeclFun(vname, arg_sorts, Term_sort, Some "Uninterpreted function symbol for impure function") in
         let dd = Term.DeclFun(vtok, [], Term_sort, Some "Uninterpreted name for impure function") in
         [d;dd], env
    else if prims.is lid
         then let vname = varops.new_fvar lid in
              let tok, definition = prims.mk lid vname in
              let env = push_free_var env lid vname (Some tok) in
              definition, env
         else let encode_non_total_function_typ = lid.nsstr <> "Prims" in
              let formals, (pre_opt, res_t) =
                let args, comp = curried_arrow_formals_comp t_norm in
                if encode_non_total_function_typ
                then args, TypeChecker.Util.pure_or_ghost_pre_and_post env.tcenv comp
                else args, (None, Util.comp_result comp) in
              let vname, vtok, env = new_term_constant_and_tok_from_lid env lid in
              let vtok_tm = match formals with
                | [] -> mkFreeV(vname, Term_sort)
                | _ -> mkApp(vtok, []) in
              let mk_disc_proj_axioms guard encoded_res_t vapp vars = quals |> List.collect (function
                | Discriminator d ->
                    let _, (xxsym, _) = Util.prefix vars in
                    let xx = mkFreeV(xxsym, Term_sort) in
                    [Term.Assume(mkForall([[vapp]], vars,
                                            mkEq(vapp, Term.boxBool <| mk_tester (escape d.str) xx)), 
                                          Some "Discriminator equation", 
                                          Some ("disc_equation_"^escape d.str))]

                | Projector(d, f) ->
                    let _, (xxsym, _) = Util.prefix vars in
                    let xx = mkFreeV(xxsym, Term_sort) in
                    let f = {ppname=f; index=0; sort=tun} in
                    let tp_name = mk_term_projector_name d f in
                    let prim_app = mkApp(tp_name, [xx]) in
                    [Term.Assume(mkForall([[vapp]], vars,
                                            mkEq(vapp, prim_app)), Some "Projector equation", Some ("proj_equation_"^tp_name))]
                | _ -> []) in
              let vars, guards, env', decls1, _ = encode_binders None formals env in
              let guard, decls1 = match pre_opt with
                | None -> mk_and_l guards, decls1
                | Some p -> let g, ds = encode_formula p env' in mk_and_l (g::guards), decls1@ds in
              let vtok_app = mk_Apply vtok_tm vars in

              let vapp = mkApp(vname, List.map mkFreeV vars) in
              let decls2, env =
                let vname_decl = Term.DeclFun(vname, formals |> List.map (fun _ -> Term_sort), Term_sort, None) in
                let tok_typing, decls2 =
                    let env = {env with encode_non_total_function_typ=encode_non_total_function_typ} in
                    if not(head_normal env tt)
                    then encode_term_pred None tt env vtok_tm
                    else encode_term_pred None t_norm env vtok_tm in //NS:Unfortunately, this is duplicated work --- we effectively encode the function type twice
                let tok_typing = Term.Assume(tok_typing, Some "function token typing", Some ("function_token_typing_"^vname)) in
                let tok_decl, env = match formals with
                        | [] -> decls2@[tok_typing], push_free_var env lid vname (Some <| mkFreeV(vname, Term_sort))
                        | _ ->  (* Generate a token and a function symbol; equate the two, and use the function symbol for full applications *)
                                let vtok_decl = Term.DeclFun(vtok, [], Term_sort, None) in
                                let vtok_fresh = Term.fresh_token (vtok, Term_sort) (varops.next_id()) in
                                let name_tok_corr = Term.Assume(mkForall([[vtok_app]; [vapp]], vars, mkEq(vtok_app, vapp)),
                                                                Some "Name-token correspondence",
                                                                Some ("token_correspondence_"^vname)) in
                                decls2@[vtok_decl;vtok_fresh;name_tok_corr;tok_typing], env in
                vname_decl::tok_decl, env in
              let encoded_res_t, ty_pred, decls3 =
                   let res_t = SS.compress res_t in
                   let encoded_res_t, decls = encode_term res_t env' in
                   encoded_res_t, mk_HasType vapp encoded_res_t, decls in //occurs positively, so add fuel
              let typingAx = Term.Assume(mkForall([[vapp]], vars, mkImp(guard, ty_pred)),
                                         Some "free var typing",
                                         Some ("typing_"^vname)) in
              let freshness =
                if quals |> List.contains New
                then [Term.fresh_constructor (vname, vars |> List.map snd, Term_sort, varops.next_id());
                      pretype_axiom vapp vars]
                else [] in
              let g = decls1@decls2@decls3@freshness@typingAx::mk_disc_proj_axioms guard encoded_res_t vapp vars in
              g, env


let declare_top_level_let env x t t_norm =
    match try_lookup_lid env x.fv_name.v with
        | None -> (* Need to introduce a new name decl *)
            let decls, env = encode_free_var env x t t_norm [] in
            let n, x', _ = lookup_lid env x.fv_name.v in
            (n, x'), decls, env
        | Some (n, x, _) -> (* already declared, only need an equation *)
            (n, x), [], env


let encode_top_level_val env lid t quals =
    let tt = norm env t in
//        if Env.debug env.tcenv <| Options.Other "SMTEncoding"
//        then Printf.printf "Encoding top-level val %s : %s\Normalized to is %s\n"
//            (Print.lid_to_string lid)
//            (Print.term_to_string t)
//            (Print.term_to_string tt);
    let decls, env = encode_free_var env lid t tt quals in
    if Util.is_smt_lemma t
    then decls@encode_smt_lemma env lid tt, env
    else decls, env

let encode_top_level_vals env bindings quals =
    bindings |> List.fold_left (fun (decls, env) lb ->
        let decls', env = encode_top_level_val env (right lb.lbname) lb.lbtyp quals in
        decls@decls', env) ([], env)

let encode_top_level_let env (is_rec, bindings) quals =
    let eta_expand binders formals body t =
        let nbinders = List.length binders in
        let formals, extra_formals = Util.first_N nbinders formals in
        let subst = List.map2 (fun (formal, _) (binder, _) -> NT(formal, S.bv_to_name binder)) formals binders in
        let extra_formals = extra_formals |> List.map (fun (x, i) -> {x with sort=SS.subst subst x.sort}, i) |> Util.name_binders in
        let body = Syntax.extend_app_n (SS.compress body) (snd <| Util.args_of_binders extra_formals) (Some <| (SS.subst subst t).n) body.pos in
        binders@extra_formals, body in

    let destruct_bound_function flid t_norm e
        : (S.binders    //arguments of the lambda abstraction
        * S.term        //body of the lambda abstraction
        * S.binders     //arguments of the function type, length of this component is equal to the first
        * S.typ)        //result type
        * bool          //if set, we should generate a curried application of f
        =
        let rec aux norm t_norm =
            match (Util.unascribe e).n with
            | Tm_abs(binders, body, lopt) ->
                let binders, body, opening = SS.open_term' binders body in
                begin match (SS.compress t_norm).n with
                    | Tm_arrow(formals, c) ->
                        let formals, c = SS.open_comp formals c in
                        let nformals = List.length formals in
                        let nbinders = List.length binders in
                        let tres = Util.comp_result c in
                        if nformals < nbinders && Util.is_total_comp c (* explicit currying *)
                        then let lopt = subst_lcomp_opt opening lopt in
                             let bs0, rest = Util.first_N nformals binders in
                             let c =
                                 let subst = List.map2 (fun (b, _) (x, _) -> NT(b, S.bv_to_name x)) bs0 formals in
                                 SS.subst_comp subst c in
                             let body = Util.abs rest body lopt in
                             (bs0, body, bs0, Util.comp_result c), false
                        else if nformals > nbinders (* eta-expand before translating it *)
                        then let binders, body = eta_expand binders formals body tres in
                             (binders, body, formals, tres), false
                        else (binders, body, formals, tres), false

                    | Tm_refine(x, _) ->
                        fst (aux norm x.sort), true

                    | _ when not norm -> //have another go, after unfolding all definitions
                        let t_norm = N.normalize [N.AllowUnboundUniverses; N.Beta; N.WHNF; N.UnfoldUntil Delta_constant; N.EraseUniverses] env.tcenv t_norm in
                        aux true t_norm

                    | _ ->
                        failwith (Util.format3 "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                flid.str (Print.term_to_string e) (Print.term_to_string t_norm))
                end
            | _ ->
                begin match (SS.compress t_norm).n with
                    | Tm_arrow(formals, c) ->
                        let formals, c = SS.open_comp formals c in
                        let tres = Util.comp_result c in
                        let binders, body = eta_expand [] formals e tres in
                        (binders, body, formals, tres), false
                    | _ -> ([], e, [], t_norm), false
                end in
        aux false t_norm in
    try
        if bindings |> Util.for_all (fun lb -> Util.is_lemma lb.lbtyp)
        then encode_top_level_vals env bindings quals
        else let toks, typs, decls, env =
                bindings |> List.fold_left (fun (toks, typs, decls, env) lb ->
                    if Util.is_lemma lb.lbtyp then raise Let_rec_unencodeable; //some, but not all are lemmas; impossible
                    let t_norm = whnf env lb.lbtyp in
                    let tok, decl, env = declare_top_level_let env (right lb.lbname) lb.lbtyp t_norm in
                    (right lb.lbname, tok)::toks, t_norm::typs, decl::decls, env) ([], [], [], env) in
            let toks = List.rev toks in
            let decls = List.rev decls |> List.flatten in
            let typs = List.rev typs in
            let mk_app curry f ftok vars =
                match vars with
                | [] -> mkFreeV(f, Term_sort)
                | _ -> if curry
                       then match ftok with
                            | Some ftok -> mk_Apply ftok vars
                            | None -> mk_Apply (mkFreeV(f, Term_sort)) vars
                       else mkApp(f, List.map mkFreeV vars) in
            if quals |> Util.for_some (function HasMaskedEffect -> true | _ -> false)
            || typs  |> Util.for_some (fun t -> not <| Util.is_pure_or_ghost_function t)
            then decls, env
            else if not is_rec
            then match bindings, typs, toks with //Encoding non-recursive definitions
                | [{lbdef=e}], [t_norm], [(flid_fv, (f, ftok))] ->
                    let e = SS.compress e in
                    let flid = flid_fv.fv_name.v in
                    let (binders, body, _, _), curry = destruct_bound_function flid t_norm e in
                    let vars, guards, env', binder_decls, _ = encode_binders None binders env in
                    let app = mk_app curry f ftok vars in
                    let app, (body, decls2) =
                        if quals |> List.contains Logic
                        then mk_Valid app, encode_formula body env'
                        else app, encode_term body env' in
                    //NS 05.25: This used to be mkImp(mk_and_l guards, mkEq(app, body))),
                    //But the guard is unnecessary given the pattern
                    let eqn = Term.Assume(mkForall([[app]], vars, mkEq(app,body)),
                                        Some (Util.format1 "Equation for %s" flid.str),
                                        Some ("equation_"^f)) in
                    decls@binder_decls@decls2@[eqn]@primitive_type_axioms env.tcenv flid f app,
                    env

                | _ -> failwith "Impossible"
            else let fuel = varops.fresh "fuel", Fuel_sort in //encoding recursive definitions using fuel to throttle unfoldings
                 let fuel_tm = mkFreeV fuel in
                 let env0 = env in
                 let gtoks, env = toks |> List.fold_left (fun (gtoks, env) (flid_fv, (f, ftok)) ->
                    let flid = flid_fv.fv_name.v in
                    let g = varops.new_fvar (Ident.lid_add_suffix flid "fuel_instrumented") in
                    let gtok = varops.new_fvar (Ident.lid_add_suffix flid "fuel_instrumented_token") in
                    let env = push_free_var env flid gtok (Some <| mkApp(g, [fuel_tm])) in
                    (flid, f, ftok, g, gtok)::gtoks, env) ([], env) in
                let gtoks = List.rev gtoks in
                let encode_one_binding env0 (flid, f, ftok, g, gtok) t_norm ({lbdef=e}) =
                    let (binders, body, formals, tres), curry = destruct_bound_function flid t_norm e in
                    let _ = if curry then failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type" in
                    let vars, guards, env', binder_decls, _ = encode_binders None binders env in
                    let decl_g = Term.DeclFun(g, Fuel_sort::List.map snd vars, Term_sort, Some "Fuel-instrumented function name") in
                    let env0 = push_zfuel_name env0 flid g in
                    let decl_g_tok = Term.DeclFun(gtok, [], Term_sort, Some "Token for fuel-instrumented partial applications") in
                    let vars_tm = List.map mkFreeV vars in
                    let app = mkApp(f, List.map mkFreeV vars) in
                    let gsapp = mkApp(g, mkApp("SFuel", [fuel_tm])::vars_tm) in
                    let gmax = mkApp(g, mkApp("MaxFuel", [])::vars_tm) in
                    let body_tm, decls2 = encode_term body env' in
                    //NS 05.25: This used to be  mkImp(mk_and_l guards, mkEq(gsapp, body_tm)
                    //But, the pattern ensures that this only applies to well-typed terms
                    //NS 08/10: Setting the weight of this quantifier to 0, since its instantiations are controlled by F* fuel
                    let eqn_g = Term.Assume(mkForall'([[gsapp]], Some 0, fuel::vars, mkEq(gsapp, body_tm)),
                                            Some (Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.str),
                                            Some ("equation_with_fuel_" ^g)) in
                    let eqn_f = Term.Assume(mkForall([[app]], vars, mkEq(app, gmax)),
                                            Some "Correspondence of recursive function to instrumented version",
                                            Some ("fuel_correspondence_"^g)) in
                    let eqn_g' = Term.Assume(mkForall([[gsapp]], fuel::vars, mkEq(gsapp,  mkApp(g, Term.n_fuel 0::vars_tm))), 
                                            Some "Fuel irrelevance", 
                                            Some ("fuel_irrelevance_" ^g)) in
                    let aux_decls, g_typing =
                    let vars, v_guards, env, binder_decls, _ = encode_binders None formals env0 in
                    let vars_tm = List.map mkFreeV vars in
                    let gapp = mkApp(g, fuel_tm::vars_tm) in
                    let tok_corr =
                        let tok_app = mk_Apply (mkFreeV (gtok, Term_sort)) (fuel::vars) in
                        Term.Assume(mkForall([[tok_app]], fuel::vars, mkEq(tok_app, gapp)), 
                                    Some "Fuel token correspondence", 
                                    Some ("fuel_token_correspondence_"^gtok)) in
                    let aux_decls, typing_corr =
                        let g_typing, d3 = encode_term_pred None tres env gapp in
                        d3, [Term.Assume(mkForall([[gapp]], fuel::vars, mkImp(mk_and_l v_guards, g_typing)), 
                                            Some "Typing correspondence of token to term", 
                                            Some ("token_correspondence_"^g))] in
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

let rec encode_sigelt (env:env_t) (se:sigelt) : (decls_t * env_t) =
    if Env.debug env.tcenv <| Options.Other "SMTEncoding"
    then Util.print1 ">>>>Encoding [%s]\n"
         <| (Print.sigelt_to_string se);//Util.lids_of_sigelt se |> List.map Print.sli |> String.concat ", ");
    let nm = match Util.lid_of_sigelt se with
        | None -> ""
        | Some l -> l.str in
    let g, e = encode_sigelt' env se in
    match g with
     | [] -> [Caption (format1 "<Skipped %s/>" nm)], e
     | _ -> Caption (format1 "<Start encoding %s>" nm)::g@[Caption (format1 "</end encoding %s>" nm)], e

and encode_sigelt' (env:env_t) (se:sigelt) : (decls_t * env_t) =
    let should_skip (l:lident) = false in
//        Util.starts_with l.str "Prims.pure_"
//        || Util.starts_with l.str "Prims.ex_"
//        || Util.starts_with l.str "Prims.st_"
//        || Util.starts_with l.str "Prims.all_"

    match se with
     | Sig_new_effect_for_free _ ->
         failwith "impossible -- removed by tc.fs"
     | Sig_pragma _
     | Sig_main _
     | Sig_effect_abbrev _
     | Sig_sub_effect _ -> [], env

     | Sig_new_effect(ed, _) ->
       if ed.qualifiers |> List.contains Reifiable |> not
       then [], env
       else (* The basic idea:
                    1. Encode M.bind_repr: a:Type -> b:Type -> wp_a -> wp_b -> f:st_repr a wp_a -> g:(a -> st_repr b) : st_repr b
                                       = e
                       by encoding a function (erasing type arguments)
                       M.bind_repr (f Term) (g Term) : [[e]]]

                    2. Likewise for M.return_repr

                    3. For each action, a : x1:n -> ... -> xn:tn -> st_repr t wp = fun x1..xn -> e
                        encode forall x1..xn. Reify (Apply a x1 ... xn) = [[e]]
            *)
            let close_effect_params tm =
                match ed.binders with
                | [] -> tm
                | _ -> S.mk (Tm_abs(ed.binders, tm, Some <| Inr (Const.effect_Tot_lid, [TOTAL]))) None tm.pos
            in

            let encode_action env (a:S.action) =
                let aname, atok, env = new_term_constant_and_tok_from_lid env a.action_name in
                let formals, _ = Util.arrow_formals_comp a.action_typ in
                let tm, decls = encode_term (close_effect_params a.action_defn) env in
                let a_decls =
                    [Term.DeclFun(aname, formals |> List.map (fun _ -> Term_sort), Term_sort, Some "Action");
                     Term.DeclFun(atok, [], Term_sort, Some "Action token")] in
                let xs_sorts, xs = formals |> List.map (fun (bv, _) -> let xxsym, xx, _ = gen_term_var env bv in (xxsym, Term_sort), xx) |> List.split in
                let app = mkApp("Reify", [mkApp(aname, xs)]) in
                let a_eq = Term.Assume(mkForall([[app]], xs_sorts, mkEq(app, mk_Apply tm xs_sorts)), 
                                       Some "Action equality", 
                                       Some (aname ^"_equality")) in
                let tok_correspondence = 
                    let tok_term = mkFreeV(atok,Term_sort) in
                    let tok_app = mk_Apply tok_term xs_sorts in
                    Term.Assume(mkForall([[tok_app]], xs_sorts, mkEq(tok_app, app)), 
                                Some "Action token correspondence", Some (aname ^ "_token_correspondence")) in
                env, decls@a_decls@[a_eq; tok_correspondence]
            in

            let env, decls2 = Util.fold_map encode_action env ed.actions in
            List.flatten decls2, env

     | Sig_declare_typ(lid, _, _, _, _) when (lid_equals lid Const.precedes_lid) ->
        let tname, ttok, env = new_term_constant_and_tok_from_lid env lid in
        [], env

     | Sig_declare_typ(lid, _, t, quals, _) ->
        let will_encode_definition = not (quals |> Util.for_some (function
            | Assumption | Projector _ | Discriminator _ | Irreducible -> true
            | _ -> false)) in
        if will_encode_definition
        then [], env //nothing to do at the declaration; wait to encode the definition
        else let fv = S.lid_as_fv lid Delta_constant None in
             let decls, env = encode_top_level_val env fv t quals in
             let tname = lid.str in
             let tsym = mkFreeV(tname, Term_sort) in
             decls
             @ primitive_type_axioms env.tcenv lid tname tsym,
             env

     | Sig_assume(l, f, _, _) ->
        let f, decls = encode_formula f env in
        let g = [Term.Assume(f, Some (format1 "Assumption: %s" (Print.lid_to_string l)), Some (varops.mk_unique ("assumption_"^l.str)))] in
        decls@g, env

     | Sig_let(lbs, r, _, quals) when (quals |> List.contains S.Irreducible) ->
       let env, decls = Util.fold_map (fun env lb ->
        let lid = (right lb.lbname).fv_name.v in
        if Option.isNone <| Env.try_lookup_val_decl env.tcenv lid
        then let val_decl = Sig_declare_typ(lid, lb.lbunivs, lb.lbtyp, quals, r) in
             let decls, env = encode_sigelt' env val_decl in
             env, decls
        else env, []) env (snd lbs) in
       List.flatten decls, env

     | Sig_let((_, [{lbname=Inr b2t}]), _, _, _) when S.fv_eq_lid b2t Const.b2t_lid ->
       let tname, ttok, env = new_term_constant_and_tok_from_lid env b2t.fv_name.v in
       let xx = ("x", Term_sort) in
       let x = mkFreeV xx in
       let valid_b2t_x = mkApp("Valid", [mkApp("Prims.b2t", [x])]) in //NS: Explicitly avoid the Vaild(b2t t) inlining 
       let decls = [Term.DeclFun(tname, [Term_sort], Term_sort, None);
                    Term.Assume(mkForall([[valid_b2t_x]], [xx],
                                              mkEq(valid_b2t_x, mkApp("BoxBool_proj_0", [x]))),
                                Some "b2t def", 
                                Some "b2t_def")] in
       decls, env

    | Sig_let(_, _, _, quals) when (quals |> Util.for_some (function Discriminator _ -> true | _ -> false)) ->
      //Discriminators are encoded directly via (our encoding of) theory of datatypes
      [], env

    | Sig_let(_, _, lids, quals) when (lids |> Util.for_some (fun (l:lident) -> (List.hd l.ns).idText = "Prims")
                                    && quals |> Util.for_some (function Unfold_for_unification_and_vcgen -> true | _ -> false)) ->
        //inline lets from prims are never encoded as definitions --- since they will be inlined
      [], env

    | Sig_let((false, [lb]), _, _, quals) when (quals |> Util.for_some (function Projector _ -> true | _ -> false)) ->
     //Projectors are also are encoded directly via (our encoding of) theory of datatypes
     //Except in some cases where the front-end does not emit a declare_typ for some projector, because it doesn't know how to compute it
     let fv = right lb.lbname in
     let l = fv.fv_name.v in
     begin match try_lookup_free_var env l with
        | Some _ ->
          [], env //already encoded
        | None ->
          let se = Sig_declare_typ(l, lb.lbunivs, lb.lbtyp, quals, Ident.range_of_lid l) in
          encode_sigelt env se
     end

    | Sig_let((false, [lb]), _, _, quals) when (quals |> List.contains Reifiable) ->
      begin match (SS.compress lb.lbdef).n with
        | Tm_abs(bs, body, _) ->
          let body = Util.mk_reify body in
          let tm = S.mk (Tm_abs(bs, body, None)) None lb.lbdef.pos in
          let tm' = N.normalize [N.Beta; N.Reify; N.Eager_unfolding; N.EraseUniverses; N.AllowUnboundUniverses] env.tcenv tm in
          let lb_typ =
            let formals, comp = Util.arrow_formals_comp lb.lbtyp in
            let reified_typ = FStar.TypeChecker.Util.reify_comp ({env.tcenv with lax=true}) (Util.lcomp_of_comp comp) U_unknown in
            Util.arrow formals (S.mk_Total reified_typ) in
          let lb = {lb with lbdef=tm'; lbtyp=lb_typ} in
          (* printfn "%s: Reified %s\nto %s\n"  *)
          (*       (Print.lbname_to_string lb.lbname)  *)
          (*       (Print.term_to_string tm)  *)
          (*       (Print.term_to_string tm');  *)
          encode_top_level_let env (false, [lb]) quals
        | _ -> [], env
      end

    | Sig_let((is_rec, bindings), _, _, quals) ->
      encode_top_level_let env (is_rec, bindings) quals

    | Sig_bundle(ses, _, _, _) ->
       let g, env = encode_signature env ses in
       let g', inversions = g |> List.partition (function
        | Term.Assume(_, Some "inversion axiom", _) -> false
        | _ -> true) in
       let decls, rest = g' |> List.partition (function
        | Term.DeclFun _ -> true
        | _ -> false) in
       decls@rest@inversions, env

     | Sig_inductive_typ(t, _, tps, k, _, datas, quals, _) ->
        let is_logical = quals |> Util.for_some (function Logic | Assumption -> true | _ -> false) in
        let constructor_or_logic_type_decl c =
            if is_logical
            then let name, args, _, _, _ = c in
                 [Term.DeclFun(name, args |> List.map snd, Term_sort, None)]
            else constructor_to_decl c in

        let inversion_axioms tapp vars =
            if datas |> Util.for_some (fun l -> Env.try_lookup_lid env.tcenv l |> Option.isNone) //Q: Why would this happen?
            then []
            else
                 let xxsym, xx = fresh_fvar "x" Term_sort in
                 let data_ax, decls = datas |> List.fold_left (fun (out, decls) l ->
                    let _, data_t = Env.lookup_datacon env.tcenv l in
                    let args, res = Util.arrow_formals data_t in
                    let indices = match (SS.compress res).n with
                        | Tm_app(_, indices) -> indices
                        | _ -> [] in
                    let env = args |> List.fold_left 
                        (fun env (x, _) -> push_term_var env x (mkApp(mk_term_projector_name l x, [xx]))) 
                        env in
                    let indices, decls' = encode_args indices env in
                    if List.length indices <> List.length vars
                    then failwith "Impossible";
                    let eqs = List.map2 (fun v a -> mkEq(mkFreeV v, a)) vars indices |> mk_and_l in
                    mkOr(out, mkAnd(mk_data_tester env l xx, eqs)), decls@decls') (mkFalse, []) in
                let ffsym, ff = fresh_fvar "f" Fuel_sort in
                let fuel_guarded_inversion =
                    let xx_has_type_sfuel =
                        if List.length datas > 1
                        then mk_HasTypeFuel (mkApp("SFuel", [ff])) xx tapp  
                        else mk_HasTypeFuel ff xx tapp in //no point requiring non-zero fuel if there are no disjunctions
                    Term.Assume(mkForall([[xx_has_type_sfuel]], add_fuel (ffsym, Fuel_sort) ((xxsym, Term_sort)::vars),
                                        mkImp(xx_has_type_sfuel, data_ax)),
                                Some "inversion axiom", //this name matters! see Sig_bundle case near line 1493
                                Some (varops.mk_unique ("fuel_guarded_inversion_"^t.str))) in
                let pattern_guarded_inversion =
                    if contains_name env "Prims.inversion"
                    && List.length datas > 1 //no point emitting this if there's only 1 constructor; it's already covered by the previous inversion
                    then let xx_has_type_fuel = mk_HasTypeFuel ff xx tapp in
                         let pattern_guard = mkApp("Prims.inversion", [tapp]) in
                         [Term.Assume(mkForall([[xx_has_type_fuel; pattern_guard]], add_fuel (ffsym, Fuel_sort) ((xxsym, Term_sort)::vars),
                                             mkImp(xx_has_type_fuel, data_ax)),
                                      Some "inversion axiom",  //this name matters! see Sig_bundle case near line 1493
                                      Some (varops.mk_unique ("pattern_guarded_inversion_"^t.str)))]
                    else [] in
                decls
                @[fuel_guarded_inversion]
                @pattern_guarded_inversion in

        let formals, res = match (SS.compress k).n with
                | Tm_arrow(formals, kres) ->
                  tps@formals, Util.comp_result kres
                | _ ->
                  tps, k in

        let formals, res = SS.open_term formals res in
        let vars, guards, env', binder_decls, _ = encode_binders None formals env in

        let tname, ttok, env = new_term_constant_and_tok_from_lid env t in
        let ttok_tm = mkApp(ttok, []) in
        let guard = mk_and_l guards in
        let tapp = mkApp(tname, List.map mkFreeV vars) in
        let decls, env =
            let tname_decl = constructor_or_logic_type_decl(tname, vars |> List.map (fun (n, s) -> (tname^n,s)), Term_sort, varops.next_id(), false) in
            let tok_decls, env = match vars with
                | [] -> [], push_free_var env t tname (Some <| mkApp(tname, []))
                | _ ->
                        let ttok_decl = Term.DeclFun(ttok, [], Term_sort, Some "token") in
                        let ttok_fresh = Term.fresh_token (ttok, Term_sort) (varops.next_id()) in
                        let ttok_app = mk_Apply ttok_tm vars in
                        let pats = [[ttok_app]; [tapp]] in
                        // These patterns allow rewriting (ApplyT T@tok args) to (T args) and vice versa
                        // This seems necessary for some proofs, but the bidirectional rewriting may be inefficient
                        let name_tok_corr = Term.Assume(mkForall'(pats, None, vars, mkEq(ttok_app, tapp)),
                                                        Some "name-token correspondence",
                                                        Some ("token_correspondence_"^ttok)) in
                        [ttok_decl; ttok_fresh; name_tok_corr], env in
            tname_decl@tok_decls, env in
        let kindingAx =
            let k, decls = encode_term_pred None res env' tapp in
            let karr =
                if List.length formals > 0
                then [Term.Assume(mk_tester "Tm_arrow" (mk_PreType ttok_tm), Some "kinding", Some ("pre_kinding_"^ttok))]
                else [] in
            decls@karr@[Term.Assume(mkForall([[tapp]], vars, mkImp(guard, k)), None, Some ("kinding_"^ttok))] in
        let aux =
            kindingAx
            @(inversion_axioms tapp vars)
            @[pretype_axiom tapp vars] in

        let g = decls
                @binder_decls
                @aux in
        g, env

    | Sig_datacon(d, _, _, _, _, _, _, _) when (lid_equals d Const.lexcons_lid) -> [], env

    | Sig_datacon(d, _, t, _, n_tps, quals, _, drange) ->
        let ddconstrsym, ddtok, env = new_term_constant_and_tok_from_lid env d in
        let ddtok_tm = mkApp(ddtok, []) in
        let formals, t_res = Util.arrow_formals t in
        let fuel_var, fuel_tm = fresh_fvar "f" Fuel_sort in
        let s_fuel_tm = mkApp("SFuel", [fuel_tm]) in
        let vars, guards, env', binder_decls, names = encode_binders (Some fuel_tm) formals env in
        let projectors = names |> List.map (fun x -> mk_term_projector_name d x, Term_sort) in
        let datacons = (ddconstrsym, projectors, Term_sort, varops.next_id(), true) |> Term.constructor_to_decl in
        let app = mk_Apply ddtok_tm vars in
        let guard = mk_and_l guards in
        let xvars = List.map mkFreeV vars in
        let dapp =  mkApp(ddconstrsym, xvars) in

        let tok_typing, decls3 = encode_term_pred None t env ddtok_tm in

        let vars', guards', env'', decls_formals, _ = encode_binders (Some fuel_tm) formals env in //NS/CH: used to be s_fuel_tm
        let ty_pred', decls_pred =
             let xvars = List.map mkFreeV vars' in
             let dapp =  mkApp(ddconstrsym, xvars) in
             encode_term_pred (Some fuel_tm) t_res env'' dapp in
        let guard' = mk_and_l guards' in
        let proxy_fresh = match formals with
            | [] -> []
            | _ -> [Term.fresh_token (ddtok, Term_sort) (varops.next_id())] in

        let encode_elim () =
            let head, args = Util.head_and_args t_res in
            match (SS.compress head).n with
                | Tm_uinst({n=Tm_fvar fv}, _)
                | Tm_fvar fv ->
                  let encoded_head = lookup_free_var_name env' fv.fv_name in
                  let encoded_args, arg_decls = encode_args args env' in
                  let _, arg_vars, eqns = List.fold_left (fun (env, arg_vars, eqns) arg ->
                          let _, xv, env = gen_term_var env (S.new_bv None tun) in
                          (env, xv::arg_vars, mkEq(arg, xv)::eqns)) (env', [], []) encoded_args in
                  let arg_vars = List.rev arg_vars in
                  let ty = mkApp(encoded_head, arg_vars) in
                  let xvars = List.map mkFreeV vars in
                  let dapp =  mkApp(ddconstrsym, xvars) in
                  let ty_pred = mk_HasTypeWithFuel (Some s_fuel_tm) dapp ty in
                  let arg_binders = List.map fv_of_term arg_vars in
                  let typing_inversion =
                    Term.Assume(mkForall([[ty_pred]],
                                        add_fuel (fuel_var, Fuel_sort) (vars@arg_binders),
                                        mkImp(ty_pred, mk_and_l (eqns@guards))),
                               Some "data constructor typing elim", 
                               Some ("data_elim_" ^ ddconstrsym)) in
                  let subterm_ordering =
                    if lid_equals d Const.lextop_lid
                    then let x = varops.fresh "x", Term_sort in
                         let xtm = mkFreeV x in
                         Term.Assume(mkForall([[mk_Precedes xtm dapp]], [x], mkImp(mk_tester "LexCons" xtm, mk_Precedes xtm dapp)), 
                                     Some "lextop is top", 
                                     Some (varops.mk_unique "lextop"))
                    else (* subterm ordering *)
                        let prec = vars |> List.collect (fun v -> match snd v with
                            | Fuel_sort -> []
                            | Term_sort -> [mk_Precedes (mkFreeV v) dapp]
                            | _ -> failwith "unexpected sort") in
                        Term.Assume(mkForall([[ty_pred]], add_fuel (fuel_var, Fuel_sort) (vars@arg_binders), mkImp(ty_pred, mk_and_l prec)),
                                    Some "subterm ordering",
                                    Some ("subterm_ordering_"^ddconstrsym)) in
                  arg_decls, [typing_inversion; subterm_ordering]

                | _ ->
                  Errors.warn drange (Util.format2 "Constructor %s builds an unexpected type %s\n"
                        (Print.lid_to_string d) (Print.term_to_string head));
                  [], [] in
        let decls2, elim = encode_elim () in
        let g = binder_decls
                @decls2
                @decls3
                @[Term.DeclFun(ddtok, [], Term_sort, Some (format1 "data constructor proxy: %s" (Print.lid_to_string d)))]
                @proxy_fresh
                @decls_formals
                @decls_pred
                @[Term.Assume(tok_typing, Some "typing for data constructor proxy", Some ("typing_tok_"^ddtok));
                  Term.Assume(mkForall([[app]], vars,
                                       mkEq(app, dapp)), Some "equality for proxy", Some ("equality_tok_"^ddtok));
                  Term.Assume(mkForall([[ty_pred']],add_fuel (fuel_var, Fuel_sort) vars', mkImp(guard', ty_pred')),
                              Some "data constructor typing intro",
                              Some ("data_typing_intro_"^ddtok));
                  ]
                @elim in
        datacons@g, env

and encode_signature env ses =
    ses |> List.fold_left (fun (g, env) se ->
      let g', env = encode_sigelt env se in
      g@g', env) ([], env)

let encode_env_bindings (env:env_t) (bindings:list<Env.binding>) : (decls_t * env_t) =
     (* Encoding Binding_var and Binding_typ as local constants leads to breakages in hash consing.

               Consider:

                type t
                type Good : nat -> Type
                type s (ps:nat) = m:t{Good ps}
                let f (ps':nat) (pi:(s ps' * unit))  =  e

               When encoding a goal formula derived from e, ps' and pi are Binding_var in the environment.
               They get encoded to constants, declare-fun ps', pi etc.
               Now, when encoding the type of pi, we encode the (s ps') as a refinement type (m:t{Good ps'}).
               So far so good.
               But, the trouble is that since ps' is a constant, we build a formula for the refinement type that does not
               close over ps'---constants are not subject to closure.
               So, we get a formula that is syntactically different than what we get when encoding the type s, where (ps:nat) is
               a locally bound free variable and _is_ subject to closure.
               The syntactic difference leads to the hash consing lookup failing.

               So:
                  Instead of encoding Binding_vars as declare-funs, we can try to close the query formula over the vars in the context,
                  thus demoting them to free variables subject to closure.

    *)
    let encode_binding b (i, decls, env) = match b with
        | Binding_univ _ ->
          i+1, [], env

        | Env.Binding_var x ->
            let t1 = N.normalize [N.Beta; N.Eager_unfolding; N.Simplify; N.EraseUniverses] env.tcenv x.sort in
            if Env.debug env.tcenv <| Options.Other "SMTEncoding"
            then (Util.print3 "Normalized %s : %s to %s\n" (Print.bv_to_string x) (Print.term_to_string x.sort) (Print.term_to_string t1));
            let t, decls' = encode_term t1 env in
            let t_hash = Term.hash_of_term t in
            let xxsym, xx, env' =
                new_term_constant_from_string env x
                    ("x_" ^ Util.digest_of_string t_hash ^ "_" ^ (string_of_int i)) in
            let t = mk_HasTypeWithFuel None xx t in
            let caption =
                if Options.log_queries()
                then Some (Util.format3 "%s : %s (%s)" (Print.bv_to_string x) (Print.term_to_string x.sort) (Print.term_to_string t1))
                else None in
            let ax =
                let a_name = Some ("binder_"^xxsym) in
                Term.Assume(t, a_name, a_name) in
            let g = [Term.DeclFun(xxsym, [], Term_sort, caption)]
                    @decls'
                    @[ax] in
            i+1, decls@g, env'

        | Env.Binding_lid(x, (_, t)) ->
            let t_norm = whnf env t in
            let fv = S.lid_as_fv x Delta_constant None in
//            Printf.printf "Encoding %s at type %s\n" (Print.lid_to_string x) (Print.term_to_string t);
            let g, env' = encode_free_var env fv t t_norm [] in
            i+1, decls@g, env'

        | Env.Binding_sig_inst(_, se, _)
        | Env.Binding_sig (_, se) ->
            let g, env' = encode_sigelt env se in
            i+1, decls@g, env' in

    let _, decls, env = List.fold_right encode_binding bindings (0, [], env) in
    decls, env

let encode_labels labs =
    let prefix = labs |> List.map (fun (l, _, _) -> Term.DeclFun(fst l, [], Bool_sort, None)) in
    let suffix = labs |> List.collect (fun (l, _, _) -> [Echo <| fst l; Eval (mkFreeV l)]) in
    prefix, suffix

(* caching encodings of the environment and the top-level API to the encoding *)
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
      let refs = Util.smap_copy hd.cache  in
      let top = {hd with cache=refs} in
      last_env := top::hd::tl
let pop_env () = match !last_env with
    | [] -> failwith "Popping an empty stack"
    | _::tl -> last_env := tl
let mark_env () = push_env()
let reset_mark_env () = pop_env()
let commit_mark_env () =
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
    if Options.log_queries()
    then Term.Caption ("encoding sigelt " ^ (Util.lids_of_sigelt se |> List.map Print.lid_to_string |> String.concat ", "))::decls
    else decls in
   let env = get_env tcenv in
   let decls, env = encode_sigelt env se in
   set_env env;
   Z3.giveZ3 (caption decls)

let encode_modul tcenv modul =
    let name = Util.format2 "%s %s" (if modul.is_interface then "interface" else "module")  modul.name.str in
    if Env.debug tcenv Options.Low
    then Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name (List.length modul.exports |> string_of_int);
    let env = get_env tcenv in
    let decls, env = encode_signature ({env with warn=false}) modul.exports in
    let caption decls =
    if Options.log_queries()
    then let msg = "Externals for " ^ name in
         Caption msg::decls@[Caption ("End " ^ msg)]
    else decls in
    set_env ({env with warn=true});
    if Env.debug tcenv Options.Low then Util.print1 "Done encoding externals for %s\n" name;
    let decls = caption decls in
    Z3.giveZ3 decls

open FStar.SMTEncoding.Z3
let encode_query use_env_msg tcenv q
  : list<decl>  //prelude, translation of tcenv
  * list<ErrorReporting.label> //labels in the query
  * decl        //the query itself
  * list<decl>  //suffix, evaluating labels in the model, etc.
  = Z3.query_logging.set_module_name (TypeChecker.Env.current_module tcenv).str;
    let env = get_env tcenv in
    let bindings = Env.fold_env tcenv (fun bs b -> b::bs) [] in
    let q, bindings =
        let rec aux bindings = match bindings with
            | Env.Binding_var x::rest ->
                let out, rest = aux rest in
                let t = N.normalize [N.Eager_unfolding; N.Beta; N.Simplify; N.EraseUniverses] env.tcenv x.sort in
                Syntax.mk_binder ({x with sort=t})::out, rest
            | _ -> [], bindings in
        let closing, bindings = aux bindings in
        Util.close_forall (List.rev closing) q, bindings
    in
    let env_decls, env = encode_env_bindings env (List.filter (function Binding_sig _ -> false | _ -> true) bindings) in
    if debug tcenv Options.Low
    || debug tcenv <| Options.Other "SMTEncoding"
    || debug tcenv <| Options.Other "SMTQuery"
    then Util.print1 "Encoding query formula: %s\n" (Print.term_to_string q);
    let phi, qdecls = encode_formula q env in
    let labels, phi = ErrorReporting.label_goals use_env_msg (Env.get_range tcenv) phi in
    let label_prefix, label_suffix = encode_labels labels in
    let query_prelude =
        env_decls
        @label_prefix
        @qdecls in
    let qry = Term.Assume(mkNot phi, Some "query", Some (varops.mk_unique "@query")) in
    let suffix = label_suffix@(if Options.print_z3_statistics() then [PrintStats] else [])@[Term.Echo "Done!"] in
    query_prelude, labels, qry, suffix

let is_trivial (tcenv:Env.env) (q:typ) : bool =
   let env = get_env tcenv in
   push "query";
   let f, _ = encode_formula q env in
   pop "query";
   match f.tm with
    | App(True, _) -> true
    | _ -> false


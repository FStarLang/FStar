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
type varops_t = {
    push: unit -> unit;
    pop: unit -> unit;
    new_var:ident -> ident -> string; (* each name is distinct and has a prefix corresponding to the name used in the program text *)
    new_fvar:lident -> string;
    fresh:string -> string;
    string_const:string -> term * list<decl>;
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
        | Some f -> f, []
        | None -> 
            let fsym = fresh "string" in
            let f = mkFreeV(fsym, Term_sort) in
            let g = [Term.DeclFun(fsym, [], String_sort, Some s);
                     Term.Assume(mkEq(f, mk_String_const !ctr), Some "String equality axiom")] in 
            let top_scope = snd <| List.hd !scopes in
            Util.smap_add top_scope s f;
            f, g in
    let push () = scopes := new_scope()::!scopes in
    let pop () = scopes := List.tl !scopes in
    {push=push;
     pop=pop;
     new_var=new_var;
     new_fvar=new_fvar;
     fresh=fresh;
     string_const=string_const;
     next_id=next_id}

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
(* ---------------------------------------------------- *)
(* Closing a set of declarations ds with a set of binders, 
   building a quantified assertion guarded by patterns *)
let close (binders:list<(string * sort * list<pat>)>) ds : decls = 
    let close1 d : decl = match d with 
      | Assume(tm, c) -> 
        let fvs = freevars tm in
        let tm' = binders |> List.fold_left (fun tm (x,s,p) -> 
           if Util.for_some (fun (y, _) -> x=y) fvs
           then Term.collapseForall(p, [(x,s)], tm)
           else tm) tm in
        Assume(tm', c)
      | _ -> d in
    ds |> List.map close1 

let close_vars vars ds = close (vars |> List.map (fun (x,y) -> (x,y,[]))) ds

(* Packaging the (translation of a source) term with its free variables *)
let closure vars t = 
    List.fold_left (fun out (v, t) -> match t with 
        | Type_sort -> Term.mk_ApplyTT out (mkBoundV(v,t))
        | Term_sort -> Term.mk_ApplyTE out (mkBoundV(v,t))) t vars

(*---------------------------------------------------------------------------------*)
let norm_t env t = Tc.Normalize.norm_typ [Tc.Normalize.Delta;Tc.Normalize.Beta] env.tcenv t
let norm_k env k = Tc.Normalize.normalize_kind env.tcenv k
let trivial_post t : typ = mk_Typ_lam([null_v_binder t], Util.ftv Const.true_lid ktype) 
                                     (mk_Kind_arrow([null_v_binder t], ktype) t.pos) t.pos

(**********************************************************************************)
(* The main encoding of kinds/types/expressions/formulae: all mutually recursive  *)
(* see fstar-priv/papers/mm/encoding.txt for a semi-formal sketch of the encoding *)
(**********************************************************************************)

type res = (
    term     (* the translation of a knd/typ/exp/formula *)
  * decls    (* auxiliary top-level assertions in support of the term *)
 )

let rec encode_knd (env:env_t) (k:knd)  : res = 
    let k0 = k in
    match (Util.compress_kind k).n with 
        | Kind_type -> 
            Term.mk_Kind_type, []

        | Kind_arrow(bs, k) -> 
            let bs, binders, env, gs = encode_binders env bs in 
            let kk, g2 = encode_knd env k in 
            let ksym, k = fresh_fvar "kind" Kind_sort in 
            let fsym, f = fresh_bvar "f" Type_sort in
            let app, guards = bs |> List.fold_left (fun (f, guards) (sym, sort, guards') -> 
                let app = match sort with 
                    | Type_sort -> mk_ApplyTT f (mkBoundV(sym, sort))
                    | Term_sort -> mk_ApplyTE f (mkBoundV(sym,sort)) in
                app, guards'@guards) (f, []) in
            let g = [Term.DeclFun(ksym, [], Kind_sort, (if Tc.Env.debug env.tcenv Options.Medium then Some (Print.kind_to_string k0) else None));
                     Term.Assume(mk_tester "Kind_arrow" k, None);
                     Term.Assume(mkForall ([mk_HasKind f k; app]@guards,
                                            (fsym, Type_sort)::binders, 
                                            mkImp(mk_and_l (mk_HasKind f k::guards),
                                                  mk_HasKind app kk)), None)] in
            k, (gs@close bs g2@g)
            
        | Kind_abbrev(_, k) -> 
            encode_knd env k

        | Kind_uvar (uv, _) -> 
            let ksym = format1 "Kind_uvar_%s" (string_of_int <| Unionfind.uvar_id uv) in
            let g = [Term.DeclFun(ksym, [], Kind_sort, None)] in
            mkFreeV(ksym, Kind_sort), g

        | _ -> failwith (Util.format1 "Unknown kind: %s" (Print.kind_to_string k))

and encode_binders env bs : (list<(string * sort * list<pat>)> (* Translation of each binder *)
                             * list<(string * sort)>           (* Each binder and all its free variables*)
                             * env_t                           (* Env, extended with bindings for the (translation of) bs *)
                             * list<decl>) =                   (* Aux. declarations associated with the translation of bs *)
    let bs, binders, env, gs = bs |> List.fold_left (fun (bs, binders, env, gs) b -> 
        match fst b with 
        | Inl {v=a; sort=k} -> 
            let kk, g1 = encode_knd env k in 
            let aasym, aa, env = 
                if is_null_binder b 
                then withenv env <| fresh_bvar "a" Type_sort
                else gen_typ_var env a in 

            (aasym, Type_sort, [mk_HasKind aa kk])::bs, 
            (aasym, Type_sort)::freevars kk@binders, 
            env,
            g1@gs

        | Inr {v=x; sort=t} -> 
            let tt, g1 = encode_typ env t in 
            let xxsym, xx, env = 
                if is_null_binder b   
                then withenv env <| fresh_bvar "x" Term_sort
                else gen_term_var env x in
            (xxsym, Term_sort, [mk_HasType xx tt])::bs, 
            (xxsym, Term_sort)::freevars tt@binders,
            env, 
            g1@gs) ([], [], env, []) in
    List.rev bs, List.rev binders, env, gs

and encode_typ (env:env_t) (t:typ) : res = (* expects t to be in normal form already *)
    let t0 = Util.compress_typ t in
    match t0.n with 
      | Typ_btvar a -> 
        lookup_typ_var env a, []

      | Typ_const fv -> 
        lookup_free_tvar env fv, []

      | Typ_refine(x, f) ->
        let t = x.sort in 
        let x = x.v in
        let tt, g1 = encode_typ env t in 
        let xxsym, xx, env' = gen_term_var env x in
        let ff, g2 = encode_formula env' f in 
        let tsym, n = fresh_fvar "type" Type_sort in
        let t = closure (fv_minus ff [(xxsym, Term_sort)]) n in
        let g = [Term.DeclFun(tsym, [], Type_sort, caption_t env t0);
                 Term.Assume(mkForall([mk_HasType xx t], [(xxsym, Term_sort)], 
                                    mkIff(mk_HasType xx t, mkAnd(mk_HasType xx tt, ff))), None)] in 
        t, g1@close [(xxsym, Term_sort, [mk_HasType xx t])] g2@g
     
      | Typ_fun(formals, res) -> 
        if not <| Util.is_pure env.tcenv res 
        then let tsym, t = fresh_fvar "type" Type_sort in
             let fsym, f = fresh_bvar "f" Term_sort in 
             let g = [Term.DeclFun(tsym, [], Type_sort, caption_t env t0);
                      Term.Assume(mk_tester "Typ_fun" t, None);
                      Term.Assume(mkForall([mk_HasType f t], [(fsym, Term_sort)], 
                                         mkImp(mk_HasType f t, mk_tester "Typ_fun" (mk_PreType f))), None)] in
             t, g
        else (* TODO: change this to use encode_binders instead *)
          let vars, env = formals |> List.fold_left (fun (v,env) b -> match b with
            | Inl({v=a; sort=k}), _ -> 
                let aasym, aa, env = gen_typ_var env a in
                ((aasym, aa, Inl k), Type_sort)::v, env
            | Inr({v=x; sort=t}), _ ->
                let xxsym, xx, env = if is_null_binder b
                                     then let s, xx = fresh_bvar "x" Term_sort in s, xx, env
                                     else gen_term_var env x in
                ((xxsym, xx, Inr t), Term_sort)::v, env) ([], env) in
          let vars = List.rev vars in
          let tsym, t = fresh_fvar "type" Type_sort in
          let fsym, f = fresh_bvar "f" Term_sort in 
          let app, args, sort = List.fold_left (fun (tm, args, sort) ((_, ax, _), s) -> match s with 
            | Type_sort -> Term.mk_ApplyET tm ax, ax::args, Arrow(s, sort)
            | Term_sort -> Term.mk_ApplyEE tm ax, ax::args, Arrow(s, sort)) (f, [], Term_sort) vars in
          let guards, decls, vars = vars |> List.map (function
            | (aa, a, Inl k), s ->
                let kk, g = encode_knd env k in
                Term.mk_HasKind a kk, g, (aa,s,[])
            | (xx, x, Inr t), s ->  
                let tt, g = encode_typ env t in
                Term.mk_HasType x tt, g, (xx,s,[])) |> List.unzip3 in
          let guard = Term.mk_and_l guards in 
          let t2, wp2, _ = Tc.Util.destruct_comp (Util.comp_to_comp_typ <| Normalize.normalize_comp env.tcenv res) in
          let tt2, g2 = encode_typ env t2 in
          let wp2', g3 = encode_formula env (norm_t env <| (syn t2.pos ktype <| Syntax.mk_Typ_app(wp2, [targ <| trivial_post t2]))) in 
          let decls = close vars (List.flatten (g2::g3::decls)) in
          let vars = vars |> List.map (fun (x, s, _) -> (x,s)) in
          let g = [Term.DeclFun(tsym, [], Type_sort, caption_t env t0);
                   Term.Assume(mk_tester "Typ_fun" t, None);
                   Term.Assume(mkForall([app; mk_HasType f t], vars@[(fsym, Term_sort)], 
                                         mkImp(mk_HasType f t, 
                                               mkAnd(mk_tester "Typ_fun" (mk_PreType f),
                                                     mkImp(mkAnd(guard, wp2'),
                                                            mk_HasType app tt2)))), None)] in
          t, decls@g

      | Typ_app(t, args) -> 
        let args, g2 = encode_args env args in
        
        let encode_partial_app () = 
        let ee, g1 = encode_typ env t in
        let tm = args |> List.fold_left (fun out -> function 
            | Inl t -> mk_ApplyTT out t
            | Inr v -> mk_ApplyTE out v) ee in
        tm, g1@g2 in

        let encode_full_app fv = 
            let fname = lookup_free_tvar_name env fv in
            let tm = Term.mkApp(fname, List.map (function Inl t | Inr t -> t) args) in
            tm, g2 in
        
        begin match (Util.compress_typ t).n with 
            | Typ_const fv ->
                if not <| !Options.z3_optimize_full_applications
                then encode_partial_app()
                else
                    (match (Util.compress_kind t.tk).n with
                        | Kind_arrow(formals, _) -> 
                          if List.length formals = List.length args
                          then encode_full_app fv
                          else (Util.fprint1 "%s is not a full application!\n" (Print.typ_to_string t0);
                                encode_partial_app ())

                        | _ -> failwith (Util.format3 "(%s) term is %s; head type is %s\n" 
                                        (Range.string_of_range t0.pos) (Print.typ_to_string t0) (Print.kind_to_string t.tk))) 
            | _ -> encode_partial_app ()
        end

      | Typ_lam(bs, t) -> 
        let bs, binders, env, gs = encode_binders env bs in
        let tt, g2 = encode_typ env t in 
        let tsym, t = fresh_fvar "type" Type_sort in
        let app, guards = bs |> List.fold_left (fun (f, guards) (sym, sort, guards') -> 
            let app = match sort with 
                | Type_sort -> mk_ApplyTT f (mkBoundV(sym, sort))
                | Term_sort -> mk_ApplyTE f (mkBoundV(sym,sort)) in
            app, guards'@guards) (t, []) in
        let g = [Term.DeclFun(tsym, [], Type_sort, caption_t env t0);
                 Term.Assume(mkForall([app], binders, 
                                    mkImp(mk_and_l guards,  
                                        mkEq(app, tt))), None)] in
        t, gs@close bs g2@g

      | Typ_ascribed(t, _) -> 
        encode_typ env t

      | Typ_uvar(uv, _) -> 
        let tsym = format1 "Typ_uvar_%s" (string_of_int <| Unionfind.uvar_id uv) in
        let g = [Term.DeclFun(tsym, [], Type_sort, caption_t env t0)] in 
        mkFreeV(tsym, Type_sort), g

      | Typ_meta _
      | Typ_delayed  _ 
      | Typ_unknown    -> failwith (format2 "(%s) Impossible: %s" (Range.string_of_range <| t.pos) (Print.tag_of_typ t))                 
       
and encode_exp (env:env_t) (e:exp) : res =
    let e = Visit.compress_exp_uvars e in 
    let e0 = e in
    let encode_const = function 
        | Const_unit -> mk_Term_unit, []
        | Const_bool true -> boxBool mkTrue, []
        | Const_bool false -> boxBool mkFalse, []
        | Const_int32 i -> boxInt (mkInteger i), []
        | Const_string(bytes, _) -> varops.string_const (Util.string_of_bytes <| bytes)
        | c -> 
        let esym, e = fresh_fvar "const" Term_sort in 
        let g = [Term.DeclFun(esym, [], Term_sort, Some (format1 "Constant: %s" <| Print.const_to_string c))] in 
        e, g in
    match e.n with 
      | Exp_delayed _ -> encode_exp env (Util.compress_exp e)
       
      | Exp_abs(bs, body) -> 
        let tfun = e.tk in 
        let e = body in
        begin match (Util.compress_typ tfun).n with 
            | Typ_fun(_, c) -> 
                if not <| Util.is_pure env.tcenv c
                then let esym, e = fresh_fvar "impure_fun" Term_sort in
                     e, [Term.DeclFun(esym, [], Term_sort, None)]
                else let tres, wp2, _ = Tc.Util.destruct_comp (Util.comp_to_comp_typ c) in
                     let bs, binders, env, gs = encode_binders env bs in
                     let tt, g2 = encode_typ env tres in
                     let wp2', g3 = encode_formula env (syn tres.pos ktype <| Syntax.mk_Typ_app(wp2, [targ <| trivial_post tres])) in
                     let ee, g4 = encode_exp env e in
                     let fsym, f = fresh_fvar "fun" Term_sort in
                     let app, guards = bs |> List.fold_left (fun (f, guards) (sym, sort, guards') -> 
                        let app = match sort with 
                            | Type_sort -> mk_ApplyET f (mkBoundV(sym, sort))
                            | Term_sort -> mk_ApplyEE f (mkBoundV(sym,sort)) in
                        app, guards'@guards) (f, []) in
                     let g = [Term.DeclFun(fsym, [], Term_sort, None);
                              Term.Assume(mkForall([app], binders, 
                                                 mkImp(mk_and_l (wp2'::guards), 
                                                     mkAnd(mkEq(app, ee),
                                                           mk_HasType ee tt))), None)] in
                     f, gs@(close bs g2@g3@g4)@g
            | _ -> failwith "Impossible"
        end

      | Exp_meta(Meta_desugared(e, _)) -> encode_exp env e

      | Exp_bvar x -> 
        lookup_term_var env x, []

      | Exp_fvar(v, _) -> 
        lookup_free_var env v, []

      | Exp_constant c -> 
        encode_const c

      | Exp_app(e, args) -> 
        let args, g2 = encode_args env args in 
    
        let encode_partial_app () = 
            let ee, g1 = encode_exp env e in
            let tm = args |> List.fold_left (fun out -> function 
                | Inl t -> mk_ApplyET out t
                | Inr v -> mk_ApplyEE out v) ee in
            tm, g1@g2 in

        let encode_full_app fv = 
            let fname = lookup_free_var_name env fv in
            let tm = Term.mkApp(fname, List.map (function Inl t | Inr t -> t) args) in
            tm, g2 in
        
        begin match (Util.compress_exp e).n with 
            | Exp_fvar(fv, _) -> 
                if not <| !Options.z3_optimize_full_applications
                then encode_partial_app()
                else
                    (match Util.function_formals e.tk with 
                        | None -> failwith (Util.format3 "(%s) term is %s; head type is %s\n" 
                                           (Range.string_of_range e0.pos) (Print.exp_to_string e0) (Print.typ_to_string e.tk))
                        | Some (formals, _) -> 
                          if List.length formals = List.length args
                          then encode_full_app fv
                          else (Util.fprint1 "%s is not a full application!\n" (Print.exp_to_string e0);
                                encode_partial_app ()))
            | _ -> encode_partial_app ()
        end

        
      | Exp_let((true, _), _) -> failwith "Nested let recs not yet supported in SMT encoding" 
      | Exp_let((_, (Inr l, _, _)::_), _) -> failwith "Unexpected top-level binding"
      | Exp_let((false, [(Inl x, t1, e1)]), e2) ->
        let ee1, g1 = encode_exp env e1 in
        let tt1, g2 = encode_typ env t1 in 
        let env' = push_term_var env x ee1 in
        let ee2, g3 = encode_exp env' e2 in
        let g = [Term.Assume(mk_HasType ee1 tt1, None)] in
        ee2, g1@g2@g@g3
      
      | Exp_let _ -> failwith "Impossible"

        
      | Exp_match(e, pats) -> 
        let encode_pat env ee pat wopt b = 
            let rec top_level_pats x = match x with
                | Pat_withinfo(p, _) -> top_level_pats p 
                | Pat_disj pats -> pats
                | p -> [p] in
            let rec mk_guard_env env d pat = match pat with 
                | Pat_disj _ -> failwith "Impossible"
                | Pat_withinfo(p, _) -> mk_guard_env env d p
                | Pat_var x -> mkTrue, push_term_var env x d, []     
                | Pat_tvar a -> mkTrue, push_typ_var env a d, [] 
                | Pat_wild
                | Pat_twild -> mkTrue, env, []
                | Pat_constant c -> 
                  let c, g = encode_const c in
                  mkEq(d, c), env, g 
                | Pat_cons(lid, pats) -> 
                  let guard = mk_data_tester env lid d in
                  let formals =  match Util.function_formals <| Tc.Env.lookup_datacon env.tcenv lid with 
                    | Some (args, _) -> args
                    | _ -> [] in  
                  let guards, env, g, _ = List.fold_left2 (fun (guards, env, g, i) formal pat -> match fst formal with 
                    | Inl {v=a; sort=k} -> 
                      let t = mk_typ_projector lid a in
                      let aa = Term.mk_ApplyTE t d in 
                      let guard, env, g' = mk_guard_env env aa pat in
                      (guard::guards, env, g@g', i+1)
                    | Inr {v=x; sort=t} -> 
                      let t = if is_null_binder formal
                              then mk_term_projector_by_pos lid i
                              else mk_term_projector lid x in
                      let xx = Term.mk_ApplyTE t d in 
                      let guard, env, g' = mk_guard_env env xx pat in
                      (guard::guards, env, g@g', i+1))
                      ([], env, [], 0) formals pats in
                  let guard = Term.mk_and_l (guard::guards) in 
                  guard, env, g in
            top_level_pats pat |> 
            List.map (mk_guard_env env ee) |>
            List.map (fun (guard, env, g) -> 
                let bb, g1 = encode_exp env b in
                let guard, g2 = match wopt with 
                    | None -> guard, []
                    | Some e -> 
                        let w, g = encode_exp env e in  
                        mkAnd(guard, mkEq(w, boxBool mkTrue)), g in
                guard, bb, g@g1@g2) in

        let ee, g1 = encode_exp env e in 
        let branches, g = List.fold_right (fun (pat, wopt, b) (def, g) -> 
            let gbgs = encode_pat env ee pat wopt b in 
            List.fold_right (fun (guard, branch, g') (def, g) -> 
               mkITE(guard, branch, def), g@g') gbgs (def, g))
            pats (Term.boxBool mkFalse, []) in
        branches, g@g1
      
      | Exp_ascribed(e, t) -> encode_exp env e

      | Exp_meta(Meta_uvar_e_app(e, _)) -> 
        encode_exp env e

      | Exp_uvar(uv, _) ->
        let esym = format1 "Exp_uvar_%s" (string_of_int <| Unionfind.uvar_id uv) in
        let g = [Term.DeclFun(esym, [], Term_sort, None)] in 
        mkFreeV(esym, Term_sort), g

      | Exp_abs _
      | Exp_meta _ -> failwith (Util.format2 "(%s): Impossible: encode_exp got %s" (Range.string_of_range e.pos) (Print.exp_to_string e))

and encode_fe env l = 
    let l, g'' = l |> List.fold_left (fun (pats, g) x -> match x with 
        | Inl t, _ -> let p, g' = encode_formula env t in p::pats, g@g'
        | Inr e, _ -> let p, g' = encode_exp env e in p::pats, g@g') ([], []) in
    List.rev l, g''

and encode_args env l = 
    let l, g'' = l |> List.fold_left (fun (out, g) x -> match x with
        | Inl t, _ -> let p, g' = encode_typ env t in Inl p::out, g@g'
        | Inr e, _ -> let p, g' = encode_exp env e in Inr p::out, g@g') ([], []) in
    List.rev l, g''

and encode_formula (env:env_t) (phi:typ) : res = (* expects phi to be normalized *)
    let enc : (list<term> -> term) -> args -> term * list<decl> = fun f l -> let l, g = encode_fe env l in f l, g in
    let const_op f _ = f, [] in
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
        let t, args = Util.head_and_args phi in
//        let _ = printfn "Falling back on %s\n" (Print.typ_to_string phi) in
//        let _ = printfn "Failed to destruct %s (%s) (%s)\n" (Print.typ_to_string t) (Print.tag_of_typ t) (args |> List.map (function Inl t -> Print.tag_of_typ t | Inr e -> Print.exp_to_string e) |> String.concat ", ") in
        let tt, g = encode_typ env phi in
        Term.mk_Valid tt, g in

    let encode_q_body env (vars:Syntax.binders) (pats:args) body = 
      let env, (vars, guard), g = vars |> List.fold_left (fun (env, (vars, guard), g) x -> match x with 
            | Inl ({v=a; sort=k}), _ -> 
              let kk, g' = encode_knd env k in 
              let aasym, aa, env = gen_typ_var env a in 
              let pat = mk_HasKind aa kk in
              (env, ((aasym, Type_sort, [pat])::vars, mkAnd(guard, pat)), g@g')
            | Inr ({v=x; sort=t}), _ ->
              let tt, g' = encode_typ env t in 
              let xxsym, xx, env = gen_term_var env x in 
              let pat = mk_HasType xx tt in
              (env, ((xxsym, Term_sort, [pat])::vars, mkAnd(guard, pat)), g@g')) (env, ([], mkTrue), []) in
      let body, g' = encode_formula env body in 
      let pats, _ = encode_fe env pats in
      List.rev vars |> List.map (fun (x, y, _) -> (x,y)), guard, List.rev pats, body, (close vars (g@g')) in
   
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

          let vars, guard, pats, body, g = encode_q_body env vars pats body in
          mkForall(pats, vars, mkImp(guard, body)), g

        | Some (Util.QEx(vars, pats, body)) -> 
          let vars, guard, pats, body, g = encode_q_body env vars pats body in
          mkExists(pats, vars, mkAnd(guard, body)), g

(***************************************************************************************************)
(* end main encoding of kinds/types/exps/formulae *)
(***************************************************************************************************)

(* ----------------------------------------------------------------------------------------------- *)
let mk_ApplyE e args =  
    args |> List.fold_left (fun out arg -> match snd arg with 
            | Type_sort -> mk_ApplyET out (Term.mkBoundV arg)
            | _ -> mk_ApplyEE out (Term.mkBoundV arg)) e
let mk_ApplyT t args = 
    args |> List.fold_left (fun out arg -> match snd arg with 
            | Type_sort -> mk_ApplyTT out (Term.mkBoundV arg)
            | _ -> mk_ApplyTE out (Term.mkBoundV arg)) t

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
    let env_of_tpars env tps tt =  (* TODO: use encode_binders instead *)
     let vars, env, app = tps |> List.fold_left (fun (vars, env, t) x -> match x with
            | Inl ({v=a; sort=k'}), _ -> 
                let aasym, aa, env = gen_typ_var env a in 
                let t = Term.mk_ApplyTT t aa in
                ((aasym, Type_sort)::vars, env, t)
            | Inr ({v=x; sort=t'}), _ -> 
                let xxsym, xx, env = gen_term_var env x in 
                let t = Term.mk_ApplyTE t xx in
                ((xxsym, Term_sort)::vars, env, t)) ([], env, tt) in
       List.rev vars, app, env in
    match se with
     | Sig_typ_abbrev(_, _, _, _, [Effect], _) 
     | Sig_typ_abbrev(_, _, _, _, [Logic], _) -> [], env

     | Sig_typ_abbrev(lid, tps, _, t, tags, _) -> 
        let tname, ttok, env = gen_free_tvar env lid in 
        let vars, app, env' = env_of_tpars env tps ttok in 
        let t = norm_t env t in
        let def, (body, g1) = if tags |> Util.for_some (function Logic -> true | _ -> false) (* REVIEW: This code is dead, given the previous pattern *)
                              then mk_Valid app, encode_formula env' t 
                              else app, encode_typ env' t in 
        let g1 = close_vars vars g1 in
        let g = [Term.DeclFun(Term.freeV_sym ttok, [], Type_sort, Some (format1 "Typ_abbrev %s" (Print.sli lid)));
                 Term.Assume(mkForall([mk_Valid(app)], vars, mkEq(def, body)), None)] in (* REVIEW: Why include this if its not a logical abbrev *)
        g1@g, env

     | Sig_val_decl(lid, t, quals, _) -> 
        if not (quals |> Util.for_some (function Logic -> true | _ -> false)) (* REVIEW: replace this with a purity check on the codomain of t? *)
        then [], env
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
        
             let vname, vtok, env = gen_free_var env lid in 
             let formals, res = match Util.function_formals t with 
                | Some (args, comp) -> args, Util.comp_result comp 
                | None -> [], t in

             if !Options.z3_optimize_full_applications
             then (* Generate a token and a function symbol; equate the two, and use the function symbol for full applications *)
                  let guarded_vars, _, env', aux = encode_binders env formals in
                  let vars = List.map (function (x, y, _) -> (x,y)) guarded_vars in
                  let vtok_app = mk_ApplyE vtok vars in
                  let vapp = Term.mkApp(vname, List.map Term.mkBoundV vars) in
                  let vname_decl = Term.DeclFun(vname, formals |> List.map (function Inl _, _ -> Type_sort | _ -> Term_sort), Term_sort, None) in
                  let tok_decl, env = match formals with 
                    | [] -> [], push_free_var env lid vname (mkFreeV(vname, Term_sort))
                    | _ -> 
                      let vtok_decl = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, None) in
                      let name_tok_corr = Term.Assume(mkForall([vtok_app], vars, mkEq(vtok_app, vapp)), None) in
                      [vtok_decl;name_tok_corr], env in
                  let res, aux' = encode_typ env' res in
                  let typingAx = 
                    let guard = List.collect (fun (_, _, g) -> g) guarded_vars |> Term.mk_and_l in
                    Term.Assume(mkForall([vapp], vars, mkImp(guard, mk_HasType vapp res)), None) in
                  let g = aux@aux'@vname_decl::typingAx::(tok_decl@mk_disc_proj_axioms vapp vars@mk_prim lid (Inl vname)) in
                  g, env
             else (* Generate a token and use curried applications everywhere *)
                  let vapp, vars_rev = formals |> List.fold_left (fun (tm, vars) formal -> match formal with 
                    | Inl a, _ -> 
                        let aasym, aa, _ = gen_typ_var env a.v in 
                        (Term.mk_ApplyET tm aa, (aasym, Type_sort)::vars) 
                    | Inr x, _ -> 
                        let xxsym, xx = if is_null_binder formal
                                        then fresh_bvar "x" Term_sort
                                        else let xxsym, xx, _ = gen_term_var env x.v in xxsym, xx in 
                        (Term.mk_ApplyEE tm xx, (xxsym, Term_sort)::vars)) (vtok, []) in
                 let vars = List.rev vars_rev in
                 let typingAx = 
                    let tt, g1 = encode_typ env t in
                    g1@[Term.Assume(mk_HasType vtok tt, None)] in
                 let g = Term.DeclFun(Term.freeV_sym vtok, [], Term_sort, None)
                       ::(typingAx
                          @mk_disc_proj_axioms vapp vars
                          @mk_prim lid (Inr vtok)) in
                 g, env

     | Sig_assume(l, f, _, _) -> 
        let phi, g1 = encode_formula env f in 
        let g = [Term.Assume(phi, Some (format1 "Assumption: %s" (Print.sli l)))] in 
        g1@g, env
               
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
        let guarded_vars, _, env', aux = encode_binders env formals in 
        let vars = guarded_vars |> List.map (fun (x, y, _) -> x, y) in
        let guard = guarded_vars |> List.collect (fun (_, _, z) -> z) |> Term.mk_and_l in
        let res, aux' = encode_knd env' res in
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
        let kindingAx = Term.Assume(mkForall([tapp], vars, mkImp(guard, mk_HasKind tapp res)), Some "kinding") in
        let prims = primitive_type_axioms t tapp in
        let inversionAx = inversion_axioms tapp vars in
        let g = aux@aux'@decls@[kindingAx]
                @(primitive_type_axioms t tapp)
                @(inversion_axioms tapp vars)
                @(projection_axioms tapp vars) in
        g, env

    | Sig_datacon(d, t, _, quals, _) -> 
        let ddconstrsym, ddtok, env = gen_free_var env d in //Print.sli d in
        let formals, t_res = match Util.function_formals t with 
            | Some (f, c) -> f, Util.comp_result c
            | None -> [], t in
        let is_rec = quals |> Util.for_some (function RecordConstructor _ -> true | _ -> false) in
        let unmangle (x:bvdef<'a>) = 
            if is_rec then Util.mkbvd (Util.unmangle_field_name x.ppname, Util.unmangle_field_name x.realname)
            else x in 
        let projectors, vars, env, _ = formals |> List.fold_left (fun (p,v,env,i) formal -> match formal with 
        | Inl({v=a; sort=k}), _ ->
            let a = unmangle a in 
            let aasym, aa, env = gen_typ_var env a in
            (mk_typ_projector_name d a, Type_sort)::p, ((aasym, aa, Inl k), Type_sort)::v, env, i + 1
        | Inr({v=x; sort=t}), _ -> 
            let xxsym, xx, env = if is_null_binder formal
                                 then let xxsym, xx = fresh_bvar "x" Term_sort in xxsym, xx, env
                                 else let x = unmangle x in gen_term_var env x in
            (mk_term_projector_name d x, Term_sort)::p, ((xxsym, xx, Inr t), Term_sort)::v, env, i + 1) ([], [], env, 0) in
        let projectors = List.rev projectors in 
        let vars = List.rev vars in
        let datacons = (ddconstrsym, projectors, Term_sort, varops.next_id()) |> Term.constructor_to_decl in
   
        let app, args, sort = List.fold_left (fun (tm, args, sort) ((_, ax, _), s) -> match s with 
            | Type_sort -> Term.mk_ApplyET tm ax, ax::args, Arrow(s, sort)
            | Term_sort -> Term.mk_ApplyEE tm ax, ax::args, Arrow(s, sort)) (ddtok, [], Term_sort) vars in
   
        let guards, decls, vars = vars |> List.map (function
            | (aa, a, Inl k), s ->
                let kk, g = encode_knd env k in
                Term.mk_HasKind a kk, g, (aa,s,[])
            | (xx, x, Inr t), s ->  
                let tt, g = encode_typ env t in
                Term.mk_HasType x tt, g, (xx,s,[])) |> List.unzip3 in
        let guard = Term.mk_and_l guards in 
        let res_t, g = encode_typ env t_res in 
        let decls = close vars (List.flatten (g::decls)) in
        let dapp =  mkApp(ddconstrsym, List.rev args) in
        let g = [Term.DeclFun(Term.freeV_sym ddtok, [], Term_sort, Some (format1 "data constructor proxy: %s" (Print.sli d)));
                Term.Assume(mkForall([app], vars |> List.map (fun (x, s, _) -> (x,s)),
                                    mkEq(app, dapp)), Some "equality for proxy");
                Term.Assume(mkForall([mk_HasType dapp res_t], vars |> List.map (fun (x, s, _) -> (x,s)),
                                    mkImp(guard, mk_HasType dapp res_t)), Some "data constructor typing")] in
        datacons@decls@g, env

    | Sig_bundle(ses, _, _) -> 
      let g, env = encode_signature env ses in
      let g', inversions = g |> List.partition (function
        | Term.Assume(_, Some "inversion axiom") -> false
        | _ -> true) in
      g'@inversions, env

//    | Sig_let((false,[(Inr x, t, e)]), _) ->
//        let xxsym, xx, env = gen_free_var env x in 
//        let tt, g1 = encode_typ env t in 
//        let ee, g2 = encode_exp env e in
//        let g = [Term.DeclFun(xxsym, [], Term_sort, Some (Print.sli x));
//                Term.Assume(mk_HasType xx tt, None);
//                Term.Assume(mkEq(xx, ee), None)] in
//        g1@g2@g, env, [], []

    | Sig_let((_,lbs), _, _) -> //TODO 
        let msg = lbs |> List.map (fun (lb, _, _) -> Print.lbname_to_string lb) |> String.concat " and " in
        [], env

    | Sig_main _
    | Sig_monads _ -> [], env

and encode_signature env ses = 
    ses |> List.fold_left (fun (g, env) se ->            
      let g', env = encode_sigelt env se in 
      g@g', env) ([], env) 

let encode_env (env:env_t) (tcenv:Env.env) : (decls * env_t) = 
    let encode_binding (decls, env) = function
        | Env.Binding_var(x, t) -> 
            let tt, g = encode_typ env (norm_t env t) in
            let xxsym, xx, env' = gen_free_term_var env x in 
            let g' = [Term.DeclFun(xxsym, [], Term_sort, Some (Print.strBvd x));
                      Term.Assume(Term.mk_HasType xx tt, None)] in
            decls@g@g', env'
        | Env.Binding_typ(a, k) -> 
            let kk, g = encode_knd env (norm_k env k) in
            let aasym, aa, env' = gen_free_typ_var env a in 
            let g' = [Term.DeclFun(aasym, [], Type_sort, Some (Print.strBvd a));
                      Term.Assume(Term.mk_HasKind aa kk, None)] in
            decls@g@g', env'
        | Env.Binding_lid(x, t) -> 
            let tt, g = encode_typ env (norm_t env t) in
            let xxname, xxtok, env' = gen_free_var env x in 
            let g' = [Term.DeclFun(Term.freeV_sym xxtok, [], Term_sort, Some (Print.sli x));
                      Term.Assume(Term.mk_HasType xxtok tt, None)] in
            decls@g@g', env'
        | Env.Binding_sig se -> 
            let decls', env = encode_sigelt env se in decls@decls', env in
    Env.fold_env tcenv encode_binding ([], env)

(* caching encodings of the environment and the top-level API to the encoding *)
open Microsoft.FStar.Tc.Env
let seen_modules : ref<list<lident>> = Util.mk_ref []
let seen (m:modul) : bool = 
    if !seen_modules |> Util.for_some (fun l -> lid_equals m.name l)
    then (//Util.fprint1 ">>Skipping module %s\n" (Print.sli m.name); 
         true)
    else (//Util.fprint1 ">>Encoding module %s\n" (Print.sli m.name); 
          seen_modules := m.name::!seen_modules; false)

type cache_t = {
        prelude_env:Tc.Env.env -> env_t * list<decl>;
        cache_env:env_t -> unit
    }

let cache = 
    let last_env : ref<option<env_t>> = Util.mk_ref None in
    {prelude_env=(fun tcenv ->     
        match !last_env with 
            | None -> 
                let e = {bindings=[]; tcenv=tcenv} in
                last_env := Some e;
                e, [Term.DefPrelude]
            | Some e -> {e with tcenv=tcenv}, []);
     cache_env=(fun e -> last_env := Some e)} 

let smt_query (tcenv:Tc.Env.env) (q:typ) : bool = 
   let e, prelude = cache.prelude_env tcenv in
   let decls, env = tcenv.modules |> List.rev |> List.collect (fun m -> if seen m then [] else m.exports) |> encode_signature e in
   cache.cache_env env;
   varops.push();
   let env_decls, env = encode_env env tcenv in
   if debug tcenv Options.Low then Util.fprint1 "Encoding query formula: %s\n" (Print.formula_to_string q);
   let phi, phi_decls = encode_formula env q in
   let label_suffix = [] in  //labels |> List.fold_left (fun decls (lname, t) -> decls@[Echo lname; Eval t]) theory in
   let r = Caption (Range.string_of_range (Tc.Env.get_range tcenv)) in
   varops.pop();
   let decls = prelude@decls@(Term.Push::r::env_decls)@Term.Caption "<Query>"::phi_decls@[Term.Assume(mkNot phi, Some "query"); Term.Caption "</Query>"; Term.CheckSat]@label_suffix@[Term.Pop; Term.Echo "Done!"] in
   Z3.callZ3Exe (!Options.logQueries) decls

let is_trivial (tcenv:Tc.Env.env) (q:typ) : bool = 
   let e, prelude = cache.prelude_env tcenv in
   let f, _ = encode_formula e q in
   match f.tm with 
    | True -> true
    | _ -> false

let solver = {
    solve=smt_query;
}

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

type binding = 
    | Binding_var   of bvvdef * term
    | Binding_tvar  of btvdef * term
    | Binding_fvar  of lident * term
    | Binding_ftvar of lident * term
   
type env_t = {bindings:list<binding>;
              tcenv:Env.env}

let lookup_binding env f = 
    match env.bindings |> List.tryFind f with 
        | None -> None 
        | Some (Binding_var(_, s))
        | Some (Binding_tvar(_, s))
        | Some (Binding_fvar(_, s))
        | Some (Binding_ftvar(_, s)) -> Some s

type varops_t = {
    new_var:ident -> ident -> string;
    new_fvar:lident -> string;
    fresh:string -> string;
    string_const:string -> term * list<decl>
}
              
let escape (s:string) = s.Replace('\'', '_')

let varops = 
    let ctr = Util.mk_ref 0 in
    let names = Util.smap_create 100 in
    let string_constants = Util.smap_create 100 in
    let mk_unique y = 
        let y = match Util.smap_try_find names y with 
                  | None -> y 
                  | Some _ -> incr ctr; y ^ "__" ^ (string_of_int !ctr) in
        let y = escape y in
        Util.smap_add names y true; y in
    let new_var pp rn = mk_unique <| pp.idText ^ "__" ^ rn.idText in
    let new_fvar lid = mk_unique lid.str in
    let fresh sfx = incr ctr; let xsym = format2 "%s_%s" sfx (string_of_int !ctr) in xsym in
    let string_const s = match Util.smap_try_find string_constants s with
        | Some f -> f, []
        | None -> 
            let fsym = fresh "string" in
            let f = mkFreeV(fsym, Term_sort) in
            let g = [Term.DeclFun(fsym, [], String_sort, Some s);
                     Term.Assume(mkEq(f, mk_String_const !ctr), Some "String equality axiom")] in 
            Util.smap_add string_constants s f;
            f, g in
    {new_var=new_var;
     new_fvar=new_fvar;
     fresh=fresh;
     string_const=string_const}
let fresh_bvar x s = let xsym = varops.fresh x in xsym, mkBoundV(xsym, s)
let fresh_fvar x s = let xsym = varops.fresh x in xsym, mkFreeV(xsym, s)

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
    match lookup_binding env (function Binding_var(b, _) -> Util.bvd_eq b a.v | _ -> false) with
    | None -> failwith (format1 "Bound term variable not found: %s" (Print.strBvd a.v))
    | Some s -> s

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
   match lookup_binding env (function Binding_tvar(b, _) -> Util.bvd_eq b a.v | _ -> false) with 
    | None -> failwith (format1 "Bound type variable not found: %s" (Print.strBvd a.v))
    | Some s -> s

let gen_free_var (env:env_t) (x:lident) =
    let ysym = varops.new_fvar x in 
    let y = mkFreeV(ysym, Term_sort) in
    ysym, y, {env with bindings=Binding_fvar(x, y)::env.bindings}
let push_free_var (env:env_t) (x:lident) (t:term) = 
    {env with bindings=Binding_fvar(x, t)::env.bindings}
let lookup_lid env a = 
    match lookup_binding env (function Binding_fvar(b, _) -> lid_equals b a | _ -> false) with
    | None -> failwith (format1 "Name not found: %s" (Print.sli a))
    | Some s -> s
let lookup_free_var env a = lookup_lid env a.v

let gen_free_tvar (env:env_t) (x:lident) =
    let ysym = varops.new_fvar x in 
    let y = mkFreeV(ysym, Type_sort) in 
    ysym, y, {env with bindings=Binding_ftvar(x, y)::env.bindings}
let push_free_tvar (env:env_t) (x:lident) (t:term) = 
    {env with bindings=Binding_ftvar(x, t)::env.bindings}
let lookup_free_tvar env a = 
    match lookup_binding env (function Binding_ftvar(b, _) -> lid_equals b a.v | _ -> false) with
    | None -> failwith (format1 "Type name not found: %s" (Print.sli a.v))
    | Some s -> s

let mk_typ_projector_name lid (a:btvdef) = escape <| format2 "%s_%s" (Print.sli lid) a.ppname.idText
let mk_term_projector_name lid (a:bvvdef) = escape <| format2 "%s_%s" (Print.sli lid) a.ppname.idText
let mk_term_projector_name_by_pos lid (i:int) = escape <| format2 "%s_%s" (Print.sli lid) (string_of_int i)
let mk_typ_projector (lid:lident) (a:btvdef)  : term = 
    mkFreeV(mk_typ_projector_name lid a, Arrow(Term_sort, Type_sort))
let mk_term_projector (lid:lident) (a:bvvdef) : term = 
    mkFreeV(mk_term_projector_name lid a, Arrow(Term_sort, Term_sort))
let mk_term_projector_by_pos (lid:lident) (i:int) : term = 
    mkFreeV(mk_term_projector_name_by_pos lid i, Arrow(Term_sort, Term_sort))
let mk_data_tester env l x = Term.mk_tester Term_sort (Print.sli l) x
let close1 (binders:list<(string * sort * list<pat>)>) d : decl = match d with 
  | Assume(tm, c) -> 
    let fvs = freevars tm in
    let tm' = binders |> List.fold_left (fun tm (x,s,p) -> 
       if Util.for_some (fun (y, _) -> x=y) fvs
       then Term.mkForall(p, [(x,s)], tm)
       else tm) tm in
    Assume(tm', c)
  | _ -> d
let close (binders:list<(string * sort * list<pat>)>) ds : decls = 
    ds |> List.map (close1 binders)
let closure vars t = 
    List.fold_left (fun out (v, t) -> match t with 
        | Type_sort -> Term.mk_ApplyTT out (mkBoundV(v,t))
        | Term_sort -> Term.mk_ApplyTE out (mkBoundV(v,t))) t vars
(*---------------------------------------------------------------------------------*)
let norm_t env t = Tc.Normalize.normalize env.tcenv t
let norm_k env k = Tc.Normalize.normalize_kind env.tcenv k

type res = (
    term     (* the translation of a knd/typ/exp *)
  * decls    (* auxiliary top-level assertions in support of the term *)
 )

let trivial_post t = 
  withkind (Kind_dcon(None, t, Kind_type, false)) <| Typ_lam(Util.new_bvd None, t, Util.ftv Const.true_lid)
          
let rec encode_knd (env:env_t) (k:knd)  : res = 
    match Util.compress_kind k with 
        | Kind_type -> 
            Term.mk_Kind_type, []

        | Kind_dcon(xopt, t1, k2, _) ->
            let tt1, g1 = encode_typ env t1 in 
            let xxsym, xx, env' = match xopt with 
                | None -> withenv env <| fresh_bvar "x" Term_sort
                | Some x -> gen_term_var env x in 
            let kk2, g2 = encode_knd env' k2 in 
            let ksym, k = fresh_fvar "kind" Kind_sort in 
            let fsym, f = fresh_bvar "f" Type_sort in
            let g = [Term.DeclFun(ksym, [], Kind_sort, None);
                     Term.Assume(mk_tester Kind_sort "Kind_dcon" k, None);
                     Term.Assume(mkForall ([mk_HasKind f k], [(fsym,Type_sort)], 
                                           mkIff(mk_HasKind f k, 
                                             mkAnd(mk_tester Kind_sort "Kind_dcon" (mk_PreKind f), 
                                                 mkForall([mk_ApplyTE f xx], [(xxsym, Term_sort)], 
                                                          mkImp(mk_HasType xx tt1, 
                                                                mk_HasKind (mk_ApplyTE f xx) kk2))))), None)] in
            k, (g1@close [(xxsym, Term_sort, [mk_HasType xx tt1])] g2@g)
             
        | Kind_tcon(aopt, k1, k2, _) -> 
            let kk1, g1 = encode_knd env k1 in 
            let aasym, aa, env' = match aopt with 
                | None -> withenv env <| fresh_bvar "a" Type_sort
                | Some a -> gen_typ_var env a in 
            let kk2, g2 = encode_knd env' k2 in 
            let ksym, k = fresh_fvar "kind" Kind_sort in 
            let fsym, f = fresh_bvar "f" Type_sort in
            let g = [Term.DeclFun(ksym, [], Kind_sort, None);
                     Term.Assume(mk_tester Kind_sort "Kind_tcon" k, None);
                     Term.Assume(mkForall ([mk_HasKind f k], [(fsym,Type_sort)], 
                                         mkIff(mk_HasKind f k, 
                                             mkAnd(mk_tester Kind_sort "Kind_tcon" (mk_PreKind f), 
                                                 mkForall([mk_ApplyTT f aa], [(aasym, Type_sort)], 
                                                        mkImp(mk_HasKind aa kk1, 
                                                            mk_HasKind (mk_ApplyTT f aa) kk2))))), None)] in
            k, (g1@close [(aasym, Type_sort, [mk_HasKind aa kk1])] g2@g)
            
        | Kind_abbrev(_, k) -> 
            encode_knd env k

        | Kind_uvar uv -> 
            let ksym = format1 "Kind_uvar %d" (string_of_int <| Unionfind.uvar_id uv) in
            let g = [Term.DeclFun(ksym, [], Kind_sort, None)] in
            mkFreeV(ksym, Kind_sort), g

        | _ -> failwith (Util.format1 "Unknown kind: %s" (Print.kind_to_string k))

and encode_typ (env:env_t) (t:typ) : res = (* expects t to be in normal form already *)
    let t = Util.compress_typ t in
    match t.t with 
      | Typ_btvar a -> 
        lookup_typ_var env a, []

      | Typ_const fv -> 
        lookup_free_tvar env fv, []

      | Typ_refine(x, t, f) -> 
        let tt, g1 = encode_typ env t in 
        let xxsym, xx, env' = gen_term_var env x in
        let ff, g2 = encode_formula env' f in 
        let tsym, n = fresh_fvar "type" Type_sort in
        let t = closure (Term.sub_fv (Term.claim ff.freevars) [(xxsym, Term_sort)]) n in
        let g = [Term.DeclFun(tsym, [], Type_sort, None);
                 Term.Assume(mkForall([mk_HasType xx t], [(xxsym, Term_sort)], 
                                    mkIff(mk_HasType xx t, mkAnd(mk_HasType xx tt, ff))), None)] in 
        t, g1@close [(xxsym, Term_sort, [mk_HasType xx t])] g2@g
     
      | Typ_fun _ 
      | Typ_univ _ -> 
        let formals, res = Util.collect_formals t in
        if not <| Util.is_pure env.tcenv res 
        then let tsym, t = fresh_fvar "type" Type_sort in
             let fsym, f = fresh_bvar "f" Term_sort in 
             let g = [Term.DeclFun(tsym, [], Type_sort, None);
                      Term.Assume(mk_tester Type_sort "Typ_fun" t, None);
                      Term.Assume(mkForall([mk_HasType f t], [(fsym, Term_sort)], 
                                         mkImp(mk_HasType f t, mk_tester Type_sort "Typ_fun" (mk_PreType f))), None)] in
             t, g
        else 
          let vars, env = formals |> List.fold_left (fun (v,env) -> function
            | Inl(a, k) -> 
                let aasym, aa, env = gen_typ_var env a in
                ((aasym, aa, Inl k), Type_sort)::v, env
            | Inr(Some x, t, _) -> 
                let xxsym, xx, env = gen_term_var env x in
                ((xxsym, xx, Inr t), Term_sort)::v, env
            | Inr(None, t, _) -> 
                let xxsym, xx = fresh_bvar "x" Term_sort in 
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
          let t2, wp2, _ = Tc.Util.destruct_comp (Normalize.normalize_comp env.tcenv res) in
          let tt2, g2 = encode_typ env t2 in
          let wp2', g3 = encode_formula env (norm_t env <| (withkind Kind_type <| Typ_app(wp2, trivial_post t2, false))) in 
          let decls = close vars (List.flatten (g2::g3::decls)) in
          let vars = vars |> List.map (fun (x, s, _) -> (x,s)) in
          let g = [Term.DeclFun(tsym, [], Type_sort, None);
                   Term.Assume(mk_tester Type_sort "Typ_fun" t, None);
                   Term.Assume(mkForall([app], vars@[(fsym, Term_sort)], 
                                         mkImp(mk_HasType f t, 
                                               mkAnd(mk_tester Type_sort "Typ_fun" (mk_PreType f),
                                                     mkImp(mkAnd(guard, wp2'),
                                                            mk_HasType app tt2)))), None)] in
          t, decls@g

//      | Typ_fun(xopt, t1, c, _) -> 
//        let c = Comp <| Normalize.weak_norm_comp env.tcenv c in
//        if not <| Util.is_pure env.tcenv c 
//        then let tsym, t = fresh_fvar "type" Type_sort in
//             let fsym, f = fresh_bvar "f" Term_sort in 
//             let g = [Term.DeclFun(tsym, [], Type_sort, None);
//                      Term.Assume(mk_tester Type_sort "Typ_fun" t, None);
//                      Term.Assume(mkForall([mk_HasType f t], [(fsym, Term_sort)], 
//                                         mkImp(mk_HasType f t, mk_tester Type_sort "Typ_fun" (mk_PreType f))), None)] in
//             t, g
//        else let tt1, g1 = encode_typ env t1 in 
//             let xxsym, xx, env' = match xopt with 
//                | None -> withenv env <| fresh_bvar "x" Term_sort
//                | Some x -> gen_term_var env x in 
//             let t2, wp2, _ = Tc.Util.destruct_comp (Util.force_comp c) in
//             let tt2, g2 = encode_typ env' t2 in
//             let wp2', g3 = encode_formula env' (norm_t env' <| (withkind Kind_type <| Typ_app(wp2, trivial_post t2, false))) in 
//             let g23 = match xopt with 
//                | None -> g2@g3
//                | _ -> close [(xxsym, Term_sort, [mk_HasType xx tt1])] (g2@g3) in
//             let tsym, t = fresh_fvar "type" Type_sort in 
//             let fsym, f = fresh_bvar "f" Term_sort in 
//             let g = [Term.DeclFun(tsym, [], Type_sort, None);
//                      Term.Assume(mk_tester Type_sort "Typ_fun" t, None);
//                      Term.Assume(mkForall([mk_HasType f t], [(fsym, Term_sort)], 
//                                         mkIff(mk_HasType f t, 
//                                             mkAnd(mk_tester Type_sort "Typ_fun" (mk_PreType f),
//                                                 mkForall([mk_ApplyEE f xx], [(xxsym, Term_sort)], 
//                                                        mkImp(mkAnd(mk_HasType xx tt1, wp2'),
//                                                            mk_HasType (mk_ApplyEE f xx) tt2))))), None)] in
//            t, g1@g23@g
//
//      | Typ_univ(a, k, c) -> 
//        let c = Comp <| Normalize.weak_norm_comp env.tcenv c in
//        if not <| Util.is_pure env.tcenv c 
//        then let tsym, t = fresh_fvar "type" Type_sort in
//             let fsym, f = fresh_bvar "f" Term_sort in 
//             let g = [Term.DeclFun(tsym, [], Type_sort, None);
//                      Term.Assume(mk_tester Type_sort "Typ_univ" t, None);
//                      Term.Assume(mkForall([mk_HasType f t], [(fsym, Term_sort)], 
//                                         mkImp(mk_HasType f t, mk_tester Type_sort "Typ_univ" (mk_PreType f))), None)] in
//             f, g
//        else let kk, g1 = encode_knd env k in 
//             let aasym, aa, env' = gen_typ_var env a in
//             let t2, wp2, _ = Util.destruct_comp (Util.force_comp c) in
//             let tt2, g2 = encode_typ env' t2 in
//             let post = withkind kun <| Typ_lam(Util.new_bvd None, t2, Util.ftv Const.true_lid) in
//             let wp2', g3 = encode_formula env' (norm_t env' <| (withkind Kind_type <| Typ_app(wp2, post, false))) in 
//             let tsym, t = fresh_fvar "type" Type_sort in 
//             let fsym, f = fresh_bvar "f" Term_sort in 
//             let g = [Term.DeclFun(tsym, [], Type_sort, None);
//                      Term.Assume(mk_tester Type_sort "Typ_univ" t, None);
//                      Term.Assume(mkForall([mk_HasType f t], [(fsym, Term_sort)], 
//                                         mkIff(mk_HasType f t, 
//                                             mkAnd(mk_tester Type_sort "Typ_univ" (mk_PreType f),
//                                                 mkForall([mk_ApplyET f aa], [(aasym, Type_sort)], 
//                                                        mkImp(mkAnd(mk_HasKind aa kk, wp2'),
//                                                            mk_HasType (mk_ApplyET f aa) tt2))))), None)] in
//            t, g1@(close [(aasym, Type_sort, [mk_HasKind aa kk])] <| g2@g3)@g
//      
      | Typ_app(t1, t2, _) -> 
        let tt1, g1 = encode_typ env t1 in 
        let tt2, g2 = encode_typ env t2 in
        Term.mk_ApplyTT tt1 tt2, g1@g2

      | Typ_dep(t1, e2, _) -> 
        let tt1, g1 = encode_typ env t1 in 
        let ee2, g2 = encode_exp env e2 in
        Term.mk_ApplyTE tt1 ee2, g1@g2

      | Typ_lam(x, t1, t2) -> 
        let tt1, g1 = encode_typ env t1 in 
        let xxsym, xx, env' = gen_term_var env x in 
        let tt2, g2 = encode_typ env' t2 in 
        let tsym, t = fresh_fvar "type" Type_sort in
        let g = [Term.DeclFun(tsym, [], Type_sort, None);
                 Term.Assume(mkForall([mk_ApplyTE t xx], [(xxsym, Term_sort)], 
                                    mkImp(mk_HasType xx tt1, 
                                        mkEq(mk_ApplyTE t xx, tt2))), None)] in
        t, g1@close [(xxsym, Term_sort, [mk_HasType xx tt1])] g2@g

      | Typ_tlam(a, k1, t2) -> 
        let kk1, g1 = encode_knd env k1 in 
        let aasym, aa, env' = gen_typ_var env a in 
        let tt2, g2 = encode_typ env' t2 in 
        let tsym, t = fresh_fvar "type" Type_sort in
        let g = [Term.DeclFun(tsym, [], Type_sort, None);
                 Term.Assume(mkForall([mk_ApplyTT t aa], [(aasym, Type_sort)], 
                                    mkImp(mk_HasKind aa kk1,
                                        mkEq(mk_ApplyTT t aa, tt2))), None)] in
        t, g1@close [(aasym, Type_sort, [mk_HasKind aa kk1])] g2@g

      | Typ_ascribed(t, k) -> encode_typ env t
//        let tt, g1 = encode_typ env t in 
//        let kk, g2 = encode_knd env k in 
//        let g = [Term.Assume(mk_HasKind tt kk, None)] in
//        tt, g1@g2@g

      | Typ_uvar(uv, _) -> 
        let tsym = format1 "Typ_uvar_%s" (string_of_int <| Unionfind.uvar_id uv) in
        let g = [Term.DeclFun(tsym, [], Type_sort, None)] in 
        mkFreeV(tsym, Type_sort), g

      | Typ_meta _
      | Typ_delayed  _ 
      | Typ_unknown    -> failwith (format1 "Impossible: %s" (Print.tag_of_typ t))                 
       
and encode_exp (env:env_t) (e:exp) : res =
    let e = Visit.compress_exp_uvars e in 
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
    match e with 
      | Exp_delayed _ -> encode_exp env (Util.compress_exp e)
       
      | Exp_meta(Meta_info(Exp_abs(x, t, e), tfun, _)) -> 
        begin match (Util.compress_typ tfun).t with 
            | Typ_fun(_, _, c, _) -> 
                if not <| Util.is_pure env.tcenv c
                then let esym, e = fresh_fvar "impure_fun" Term_sort in
                     e, [Term.DeclFun(esym, [], Term_sort, None)]
                else let t2, wp2, _ = Tc.Util.destruct_comp (Util.force_comp c) in
                     let tt, g1 = encode_typ env t in
                     let xxsym, xx, env' = gen_term_var env x in
                     let tt2, g2 = encode_typ env' t2 in
                     let wp2', g3 = encode_formula env' (withkind Kind_type <| Typ_app(wp2, trivial_post t2, false)) in
                     let ee, g4 = encode_exp env' e in
                     let fsym, f = fresh_fvar "fun" Term_sort in
                     let g = [Term.DeclFun(fsym, [], Term_sort, None);
                              Term.Assume(mkForall([mk_ApplyEE f xx], [(xxsym, Term_sort)], 
                                                 mkImp(mkAnd(mk_HasType xx tt, wp2'),
                                                     mkAnd(mkEq(mk_ApplyEE f xx, ee),
                                                         mk_HasType ee tt2))), None)] in
                     f, g1@(close [(xxsym, Term_sort, [mk_HasType xx tt])] g2@g3@g4)@g
            | _ -> failwith "Impossible"
        end


      | Exp_meta(Meta_info(Exp_tabs(a, k, e), tfun, _)) -> 
        begin match (Util.compress_typ tfun).t with 
            | Typ_univ(_, _, c) -> 
                if not <| Util.is_pure env.tcenv c
                then let esym, e = fresh_fvar "impure_fun" Term_sort in
                     e, [Term.DeclFun(esym, [], Term_sort, None)]
                else let t2, wp2, _ = Tc.Util.destruct_comp (Util.force_comp c) in
                     let kk, g1 = encode_knd env k in
                     let aasym, aa, env' = gen_typ_var env a in
                     let tt2, g2 = encode_typ env' t2 in
                     let wp2', g3 = encode_formula env' (withkind Kind_type <| Typ_app(wp2, trivial_post t2, false)) in
                     let ee, g4 = encode_exp env' e in
                     let fsym, f = fresh_fvar "fun" Term_sort in
                     let g = [Term.DeclFun(fsym, [], Term_sort, None);
                              Term.Assume(mkForall([mk_ApplyET f aa], [(aasym, Type_sort)], 
                                                 mkImp(mkAnd(mk_HasKind aa kk, wp2'),
                                                     mkAnd(mkEq(mk_ApplyET f aa, ee),
                                                         mk_HasType ee tt2))), None)] in
                     f, g1@(close [(aasym, Type_sort, [mk_HasKind aa kk])] g2@g3@g4)@g
            | _ -> failwith "Impossible"
        end

      | Exp_meta(Meta_info(e, _, _))
      | Exp_meta(Meta_desugared(e, _)) -> encode_exp env e

      | Exp_bvar x -> 
        lookup_term_var env x, []

      | Exp_fvar(v, _) -> 
        lookup_free_var env v, []

      | Exp_constant c -> 
        encode_const c

      | Exp_app(e1, e2, _) -> 
        let ee1, g1 = encode_exp env e1 in 
        let ee2, g2 = encode_exp env e2 in 
        mk_ApplyEE ee1 ee2, g1@g2
        
      | Exp_tapp(e1, t2) -> 
        let ee1, g1 = encode_exp env e1 in 
        let tt2, g2 = encode_typ env t2 in 
        mk_ApplyET ee1 tt2, g1@g2
      
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
                  let args, _ =  Util.collect_formals <| Tc.Env.lookup_datacon env.tcenv lid in  
                  let guards, env, g, _ = List.fold_left2 (fun (guards, env, g, i) arg pat -> match arg with 
                    | Inl (a, k) -> 
                      let t = mk_typ_projector lid a in
                      let aa = Term.mk_ApplyTE t d in 
                      let guard, env, g' = mk_guard_env env aa pat in
                      (guard::guards, env, g@g', i+1)
                    | Inr (xopt, t, _) ->
                      let t = match xopt with 
                        | None -> mk_term_projector_by_pos lid i
                        | Some x -> mk_term_projector lid x in
                      let xx = Term.mk_ApplyTE t d in 
                      let guard, env, g' = mk_guard_env env xx pat in
                      (guard::guards, env, g@g', i+1))
                      ([], env, [], 0) args pats in
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
//        let ee, g1 = encode_exp env e in 
//        let tt, g2 = encode_typ env t in 
//        let g = [Term.Assume(mk_HasType ee tt, None)] in
//        ee, g1@g2@g
      
      | Exp_uvar(uv, _) ->
        let esym = format1 "Exp_uvar %d" (string_of_int <| Unionfind.uvar_id uv) in
        let g = [Term.DeclFun(esym, [], Term_sort, None)] in 
        mkFreeV(esym, Term_sort), g

      | Exp_abs _
      | Exp_tabs _
      | Exp_meta _ -> failwith "Impossible"

and encode_either_l env l = 
    let l, g'' = l |> List.fold_left (fun (pats, g) -> function 
        | Inl t -> let p, g' = encode_formula env t in p::pats, g@g'
        | Inr e -> let p, g' = encode_exp env e in p::pats, g@g') ([], []) in
    List.rev l, g''

and encode_formula (env:env_t) (phi:typ) : res = (* expects phi to be normalized *)
    let enc f l = let l, g = encode_either_l env l in f l, g in
    let const_op f _ = f, [] in
    let un_op f l = f <| List.hd l in
    let bin_op f = function 
        | [t1;t2] -> f(t1,t2)
        | _ -> failwith "Impossible" in
    let tri_op f = function
        | [t1;t2;t3] -> f(t1,t2,t3)
        | _ -> failwith "Impossible" in
    let eq_op f = function 
        | [_;_;e1;e2] -> bin_op f [e1;e2]
        | l -> bin_op f l in
    let unboxInt_l f l =  f (List.map Term.unboxInt l) in
    let connectives = [ 
                        (Const.true_lid, const_op mkTrue);
                        (Const.false_lid, const_op mkFalse);
                        (Const.and_lid,  enc <| bin_op mkAnd);
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
                    ] in

    let fallback phi =  
        let t, args = Util.flatten_typ_apps phi in
        let _ = printfn "Falling back on %s\n" (Print.typ_to_string phi) in
        let _ = printfn "Failed to destruct %s (%s) (%s)\n" (Print.typ_to_string t) (Print.tag_of_typ t) (args |> List.map (function Inl t -> Print.tag_of_typ t | Inr e -> Print.exp_to_string e) |> String.concat ", ") in
        let tt, g = encode_typ env phi in
        Term.mk_Valid tt, g in

    let encode_q_body env vars pats body = 
      let env, (vars, guard), g = vars |> List.fold_left (fun (env, (vars, guard), g) -> function 
            | Inl (a, k) -> 
              let kk, g' = encode_knd env k in 
              let aasym, aa, env = gen_typ_var env a in 
              (env, ((aasym, Type_sort)::vars, mkAnd(guard, mk_HasKind aa kk)), g@g')
            | Inr (x, t) ->
              let tt, g' = encode_typ env t in 
              let xxsym, xx, env = gen_term_var env x in 
              (env, ((xxsym, Term_sort)::vars, mkAnd(guard, mk_HasType xx tt)), g@g')) (env, ([], mkTrue), []) in
      let body, g' = encode_formula env body in 
      let pats, _ = encode_either_l env pats in
      List.rev vars, guard, List.rev pats, body, g@g' in
        
    match Util.destruct_typ_as_formula phi with
        | None -> fallback phi
        
        | Some (Util.BaseConn(op, arms)) -> 
          (match connectives |> List.tryFind (fun (l, _) -> lid_equals op l) with 
             | None -> fallback phi
             | Some (_, f) -> f arms)

        | Some (Util.QAll(vars, pats, body)) -> 
          let vars, guard, pats, body, g = encode_q_body env vars pats body in
          mkForall(pats, vars, mkImp(guard, body)), g

        | Some (Util.QEx(vars, pats, body)) -> 
          let vars, guard, pats, body, g = encode_q_body env vars pats body in
          mkForall(pats, vars, mkAnd(guard, body)), g

(* ----------------------------------------------------------------------------------------------- *)
let mk_prim, is_prim =
    let asym, a = fresh_bvar "a" Type_sort in 
    let bsym, b = fresh_bvar "b" Type_sort in 
    let xsym, x = fresh_bvar "x" Term_sort in 
    let ysym, y = fresh_bvar "y" Term_sort in 
    let eq_assumption vars t1 t2 = Term.Assume(mkForall([t1], vars, mkEq(t1,t2)), None) in
    let abxy_t v tm = 
        let vars = [(asym, Type_sort); (bsym, Type_sort); (xsym, Term_sort); (ysym, Term_sort)] in 
        eq_assumption vars (mk_ApplyEE (mk_ApplyEE (mk_ApplyET (mk_ApplyET v a) b) x) y) tm in 
    let xy_t v tm = 
        let vars = [(xsym, Term_sort); (ysym, Term_sort)] in 
        eq_assumption vars (mk_ApplyEE (mk_ApplyEE v x) y) tm in 
    let x_t v tm = 
        let vars = [(xsym, Term_sort)] in
        eq_assumption vars (mk_ApplyEE v x) tm in 
    let prims = [
        (Const.op_Eq,          (fun v -> abxy_t v (boxBool <| mkEq(x,y))));
        (Const.op_notEq,       (fun v -> abxy_t v (boxBool <| mkNot(mkEq(x,y)))));
        (Const.op_LT,          (fun v -> xy_t   v (boxBool <| mkLT(unboxInt x, unboxInt y))));
        (Const.op_LTE,         (fun v -> xy_t   v (boxBool <| mkLTE(unboxInt x, unboxInt y))));
        (Const.op_GT,          (fun v -> xy_t   v (boxBool <| mkGT(unboxInt x, unboxInt y))));
        (Const.op_GTE,         (fun v -> xy_t   v (boxBool <| mkGTE(unboxInt x, unboxInt y))));
        (Const.op_Subtraction, (fun v -> xy_t   v (boxInt  <| mkSub(unboxInt x, unboxInt y))));
        (Const.op_Minus,       (fun v -> x_t    v (boxInt  <| mkMinus(unboxInt x))));
        (Const.op_Addition,    (fun v -> xy_t   v (boxInt  <| mkAdd(unboxInt x, unboxInt y))));
        (Const.op_Multiply,    (fun v -> xy_t   v (boxInt  <| mkMul(unboxInt x, unboxInt y))));
        (Const.op_Division,    (fun v -> xy_t   v (boxInt  <| mkDiv(unboxInt x, unboxInt y))));
        (Const.op_Modulus,     (fun v -> xy_t   v (boxInt  <| mkMod(unboxInt x, unboxInt y))));
        (Const.op_And,         (fun v -> xy_t   v (boxBool <| mkAnd(unboxBool x, unboxBool y))));
        (Const.op_Or,          (fun v -> xy_t   v (boxBool <| mkOr(unboxBool x, unboxBool y))));
        (Const.op_Negation,    (fun v -> x_t    v (boxBool <| mkNot(unboxBool x))));
        ] in
    (fun l v -> prims |> List.filter (fun (l', _) -> lid_equals l l') |> List.map (fun (_, b) -> b v)), 
    (fun l -> prims |> Util.for_some (fun (l', _) -> lid_equals l l'))

 
let rec encode_sigelt (env:env_t) (se:sigelt) : (decls * env_t * typenames * datacons) = 
    let g, e, t, d = encode_sigelt' env se in 
    let nm = match Util.lid_of_sigelt se with 
        | None -> ""
        | Some l -> l.str in
    let g = Caption (format1 "<Start encoding %s>" nm)::g@[Caption (format1 "</end encoding %s>" nm)] in
    g, e, t, d
    
and encode_sigelt' (env:env_t) (se:sigelt) : (decls * env_t * typenames * datacons) = 
    let close_and_encode_knd env tt tps k =  
        let vars, env', tapp = tps |> List.fold_left (fun (vars, env, t) -> function
            | Tparam_typ(a, k') ->
                let aasym, aa, env = gen_typ_var env a in 
                let t = Term.mk_ApplyTT t aa in
                ((aasym, Type_sort)::vars, env, t)
            | Tparam_term(x, t') -> 
                let xxsym, xx, env = gen_term_var env x in 
                let t = Term.mk_ApplyTE t xx in
                ((xxsym, Term_sort)::vars, env, t)) ([], env, tt) in 
            let kk, g = encode_knd env' k in
            vars, tapp, kk, g@[Term.Assume(mkForall([tapp], List.rev vars, mk_HasKind tapp kk), None)] in
      if Tc.Env.debug env.tcenv
      then Util.print_string (format1 "Encoding %s\n" (Print.sigelt_to_string_short se));
      match se with
        | Sig_typ_abbrev(lid, tps, k, t, tags, _) -> 
          let tsym, tt, env = gen_free_tvar env lid in 
          let def, g1 = encode_typ env (Util.close_with_lam tps t) in 
          let _, _, _, g2 = close_and_encode_knd env tt tps k in
          let g = [Term.DeclFun(tsym, [], Type_sort, Some (format1 "Typ_abbrev %s" (Print.sli lid)));
                   Term.Assume(mkEq(tt, def), None)] in
          g1@g@g2, env, [], []
        
        | Sig_val_decl(lid, t, _, Some ltag, _) -> 
          let tt, g1 = encode_typ env t in 
          let vsym, v, env = gen_free_var env lid in 
          let args, _ = Util.collect_formals t in
          let vapp, vars = args |> List.fold_left (fun (tm, vars) arg -> match arg with 
            | Inl (a, _) -> let aasym, aa, _ = gen_typ_var env a in (Term.mk_ApplyET tm aa, (aasym, Type_sort)::vars) 
            | Inr (Some x, _, _) -> 
              let xxsym, xx, _ = gen_term_var env x in (Term.mk_ApplyEE tm xx, (xxsym, Term_sort)::vars) 
            | Inr _ -> 
              let xxsym, xx = fresh_bvar "x" Term_sort in (Term.mk_ApplyEE tm xx, (xxsym, Term_sort)::vars)) (v, []) in
          let xxsym, xx = fresh_bvar "x" Term_sort in 
          let vapp = mk_ApplyEE vapp xx in
          let eqAx = match ltag with 
            | Logic_discriminator d -> 
              [Term.Assume(mkForall([vapp], (List.rev <| ((xxsym, Term_sort)::vars)), 
                                    mkEq(vapp, Term.boxBool <| Term.mk_tester Term_sort (Print.sli d) xx)), None)]
            | Logic_projector(d, Inr f) -> 
              [Term.Assume(mkForall([vapp], (List.rev <| ((xxsym, Term_sort)::vars)), 
                                    mkEq(vapp, Term.mkApp(mk_term_projector_name d f, Arrow(Term_sort, Term_sort), [xx]))), None)]
            | _ -> [] in
          let g = [Term.DeclFun(vsym, [], Term_sort, Some (format1 "val %s" (Print.sli lid)));
                   Term.Assume(mk_HasType v tt, None)] in
          g1@g@eqAx@mk_prim lid v, env, [], []

        | Sig_val_decl(lid, t, _, _, _) -> 
          if is_prim lid 
          then 
              let vsym, v, env = gen_free_var env lid in 
              let tt, g1 = encode_typ env t in 
              let g = [Term.DeclFun(vsym, [], Term_sort, Some (format1 "val %s" (Print.sli lid)));
                       Term.Assume(mk_HasType v tt, None)] in
              g1@g@mk_prim lid v, env, [], []
           else [], env, [], []


        | Sig_assume(l, f, _, _, _) -> 
          let phi, g1 = encode_formula env f in 
          let g = [Term.Assume(phi, Some (format1 "Assumption: %s" (Print.sli l)))] in 
          g1@g, env, [], []
        
        | Sig_logic_function(l, t, tags, _) -> 
          let tt, g1 = encode_typ env t in 
          let fsym, f, env = gen_free_var env l in
          let g = [Term.DeclFun(fsym, [], Term_sort, Some (format1 "logic val %s" (Print.sli l)));
                   Term.Assume(mk_HasType f tt, Some (format1 "Typing assumption for logic val %s" (Print.sli l)))] in 
          g1@g, env, [], []
       
        | Sig_tycon(t, tps, k, _, datas, tags, _) -> 
          printfn "Encoding %s at kind %s\n" (Print.sli t) (Print.kind_to_string k);
          let ttsym, _, _ = gen_free_var env t in
          let tt = Term.mk_Typ_const ttsym in
          let env = push_free_tvar env t tt in 
          let vars, tapp, _, g1 = close_and_encode_knd env tt tps (Util.close_kind tps k) in
          let xxsym, xx = fresh_bvar "x" Term_sort in
          let eqAx = match tags with 
            | [Logic_projector(d, Inl a)] -> 
              let tapp = mk_ApplyTE tapp xx in
              [Term.Assume(mkForall([tapp], List.rev <| (xxsym, Term_sort)::vars, 
                                    mkEq(tapp, Term.mkApp(mk_typ_projector_name d a, Arrow(Term_sort, Type_sort), [xx]))), None)] 
            | _ -> [] in
          if List.length datas = 0 || tags |> Util.for_some (function Logic_type -> true | _ -> false) //uninterpreted types don't get data axioms
          then g1@eqAx, env, [ttsym], []
          else let data_ax = datas |> List.fold_left (fun out l -> mkOr(out, mk_data_tester env l xx)) mkFalse in
               let g = [Term.Assume(mkForall([tapp], vars,
                                     mkForall([mk_HasType xx tapp], [(xxsym, Term_sort)], 
                                          mkImp(mk_HasType xx tapp, data_ax))), None)] in
               g1@g@eqAx, env, [ttsym], []

        | Sig_datacon(d, t, _, _) -> 
//          let _, g1 = encode_typ env t in 
          let ddconstrsym = Print.sli d in
          let ddfunsym, ddfun = fresh_fvar (Print.sli d) Term_sort in
          let env = push_free_var env d ddfun in
          let formals, res = Util.collect_formals t in

          let projectors, vars, env, _ = formals |> List.fold_left (fun (p,v,env,i) -> function
            | Inl(a, k) -> 
                let aasym, aa, env = gen_typ_var env a in
                (mk_typ_projector_name d a, Type_sort)::p, ((aasym, aa, Inl k), Type_sort)::v, env, i + 1
            | Inr(Some x, t, _) -> 
                let xxsym, xx, env = gen_term_var env x in
                (mk_term_projector_name d x, Term_sort)::p, ((xxsym, xx, Inr t), Term_sort)::v, env, i + 1
            | Inr(None, t, _) -> 
                let xxsym, xx = fresh_bvar "x" Term_sort in 
                (mk_term_projector_name_by_pos d i, Term_sort)::p, ((xxsym, xx, Inr t), Term_sort)::v, env, i + 1) ([], [], env, 0) in
          let projectors = List.rev projectors in 
          let vars = List.rev vars in
          let datacons = [(ddconstrsym, projectors, Term_sort)] in
   
          let app, args, sort = List.fold_left (fun (tm, args, sort) ((_, ax, _), s) -> match s with 
            | Type_sort -> Term.mk_ApplyET tm ax, ax::args, Arrow(s, sort)
            | Term_sort -> Term.mk_ApplyEE tm ax, ax::args, Arrow(s, sort)) (ddfun, [], Term_sort) vars in
   
          let guards, decls, vars = vars |> List.map (function
            | (aa, a, Inl k), s ->
                let kk, g = encode_knd env k in
                Term.mk_HasKind a kk, g, (aa,s,[])
            | (xx, x, Inr t), s ->  
                let tt, g = encode_typ env t in
                Term.mk_HasType x tt, g, (xx,s,[])) |> List.unzip3 in
          let guard = Term.mk_and_l guards in 
          let res_t, g = encode_typ env (Util.comp_result res) in
          let decls = close vars (List.flatten (g::decls)) in
          let dapp =  mkApp(ddconstrsym, sort, List.rev args) in
          let g = [Term.DeclFun(ddfunsym, [], Term_sort, Some (format1 "data constructor proxy: %s" (Print.sli d)));
                   Term.Assume(mkForall([app], vars |> List.map (fun (x, s, _) -> (x,s)),
                                      mkEq(app, dapp)), Some "equality for proxy");
                   Term.Assume(mkForall([dapp], vars |> List.map (fun (x, s, _) -> (x,s)),
                                        mkImp(guard, mk_HasType dapp res_t)), Some "data constructor typing")] in
          decls@g, env, [], datacons

        | Sig_bundle(ses, _) -> 
          encode_signature env ses

        | Sig_let((false,[(Inr x, t, e)]), _) ->
          let xxsym, xx, env = gen_free_var env x in 
          let tt, g1 = encode_typ env t in 
          let ee, g2 = encode_exp env e in
          let g = [Term.DeclFun(xxsym, [], Term_sort, Some (Print.sli x));
                   Term.Assume(mk_HasType xx tt, None);
                   Term.Assume(mkEq(xx, ee), None)] in
          g1@g2@g, env, [], []

        | Sig_let((_,lbs), _) -> //TODO 
          let msg = lbs |> List.map (fun (lb, _, _) -> Print.lbname_to_string lb) |> String.concat " and " in
          let g = [Term.Caption(format1 "Skipping let rec %s" msg)] in
          g, env, [], []

        | Sig_main _
        | Sig_monads _ -> [], env, [], []

and encode_signature env ses = 
    ses |> List.fold_left (fun (g, env, tys, datas) se ->            
      let g', env, tys', datas' = encode_sigelt env se in 
      (g@g', env, tys@tys', datas@datas')) ([], env, [], []) 

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
            let xxsym, xx, env' = gen_free_var env x in 
            let g' = [Term.DeclFun(xxsym, [], Term_sort, Some (Print.sli x));
                      Term.Assume(Term.mk_HasType xx tt, None)] in
            decls@g@g', env'
        | Env.Binding_sig se -> 
            let decls, env, _, _ = encode_sigelt env se in decls, env in
    Env.fold_env tcenv encode_binding ([], env)

open Microsoft.FStar.Tc.Env

let formula_to_string tcenv q : string = 
   let e = {bindings=[]; tcenv=tcenv} in
   let f, _ = encode_formula e q in
   Term.termToSmt [] f

let smt_query (tcenv:Tc.Env.env) (q:typ) : bool = 
   let e = {bindings=[]; tcenv=tcenv} in
   if Tc.Env.debug tcenv then printfn "Encoding signature";
   let decls, env, tys, datas = tcenv.modules |> List.collect (fun m -> m.exports) |> encode_signature e in
   if Tc.Env.debug tcenv then printfn "Encoding environment";
   let decls', env = encode_env env tcenv in
   if Tc.Env.debug tcenv then printfn "Encoding query %s" (Print.formula_to_string q);
   let phi, decls'' = encode_formula env q in
   let decls = Term.DefPrelude(tys, datas)::decls@decls'@decls''@[Term.Assume(mkNot phi, Some "query"); Term.CheckSat] in
   if Tc.Env.debug tcenv then printfn "Calling Z3";
   Z3.callZ3Exe (Tc.Env.debug tcenv) decls [] 

let solver = {
    solve=smt_query;
    formula_to_string=formula_to_string
}
//let is_builtin lid = 
//    lid_equals lid Const.int_lid ||
//    lid_equals lid Const.bool_lid ||
//    lid_equals lid Const.string_lid ||
//    lid_equals lid Const.unit_lid //NS: ref?
//
//let is_lid_skippable = 
//  let skippables = [Const.forall_lid;
//                    Const.forallA_lid;
//                    Const.forallP_lid;
//                    Const.exists_lid;
//                    Const.existsA_lid;
//                    Const.existsP_lid;
//                    Const.ifthenelse_lid;
//                    Const.assume_lid;
//                    Const.eq_lid;
//                    Const.eq2_lid;
//                    Const.eqA_lid;
//                    Const.eqTyp_lid;
//                    Const.lt_lid;
//                    Const.gt_lid;
//                    Const.lte_lid;
//                    Const.gte_lid;
//                    Const.reln_lid;
//                    Const.doublesided_lid;
//                    Const.and_lid;
//                    Const.or_lid;
//                    Const.not_lid;
//                    Const.implies_lid;
//                    Const.iff_lid;
//                    Const.true_lid;
//                    Const.false_lid;
//                    Const.add_lid;
//                    Const.sub_lid;
//                    Const.mul_lid;
//                    Const.div_lid;
//                    Const.minus_lid;
//                    Const.modulo_lid;
//                    Const.op_And_lid;
//                    Const.op_Or_lid;
//                    Const.op_Not_lid;
//                    Const.op_Add_lid;
//                    Const.op_Subtraction_lid;
//                    Const.op_Division_lid;
//                    Const.op_Modulus_lid;
//                    Const.op_Multiply_lid;
//                    Const.op_GreaterThanOrEqual_lid;
//                    Const.op_Dereference_lid;
//                    Const.op_Eq;
//                    Const.unfold_lid] in
//    fun l -> List.exists (Sugar.lid_equals l) skippables 
//let isAtom tenv p = 
//  let pred, args = flatten_typ_apps p in 
//  match p.sort with 
//    | Kind_type -> 
//      (match pred.v with 
//        | Typ_const _
//        | Typ_btvar _ 
//        | Typ_uvar _ -> true
//        | _ -> false)
//    | _ -> false
//      

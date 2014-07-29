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
        | None -> failwith "Unbound variable"
        | Some (Binding_var(_, s))
        | Some (Binding_tvar(_, s))
        | Some (Binding_fvar(_, s))
        | Some (Binding_ftvar(_, s)) -> s

type varops_t = {
    new_var:ident -> ident -> string;
    new_fvar:lident -> string;
    fresh:string -> string * term;
    string_const:string -> term * list<decl>
}
              
let varops = 
    let ctr = Util.mk_ref 0 in
    let names = Util.smap_create 100 in
    let string_constants = Util.smap_create 100 in
    let mk_unique y = 
        let y = match Util.smap_try_find names y with 
                  | None -> y 
                  | Some _ -> incr ctr; y ^ "__" ^ (string_of_int !ctr) in
        Util.smap_add names y true; y in
    let new_var pp rn = mk_unique <| pp.idText ^ "__" ^ rn.idText in
    let new_fvar lid = mk_unique lid.str in
    let fresh sfx = incr ctr; let xsym = format2 "%s_%s" sfx (string_of_int !ctr) in xsym, Funsym xsym in
    let string_const s = match Util.smap_try_find string_constants s with
        | Some f -> f, []
        | None -> 
            let fsym, f = fresh "string" in
            let g = [Term.DeclFun(fsym, [], String_sort, Some s);
                     Term.Assume(Eq(f, mk_String_const !ctr), None)] in 
            Util.smap_add string_constants s f;
            f, g in
    {new_var=new_var;
     new_fvar=new_fvar;
     fresh=fresh;
     string_const=string_const}
let fresh x = varops.fresh x

let gen_term_var (env:env_t) (x:bvvdef) = 
    let ysym = varops.new_var x.ppname x.realname in 
    let y = Funsym ysym in 
    ysym, y, {env with bindings=Binding_var(x,y)::env.bindings}
let push_term_var (env:env_t) (x:bvvdef) (t:term) = 
    {env with bindings=Binding_var(x,t)::env.bindings}
let lookup_term_var env a = 
    lookup_binding env (function Binding_var(b, _) -> Util.bvd_eq b a.v | _ -> false)

let gen_typ_var (env:env_t) (x:btvdef) = 
    let ysym = varops.new_var x.ppname x.realname in 
    let y = Funsym ysym in
    ysym, y, {env with bindings=Binding_tvar(x,y)::env.bindings}
let push_typ_var (env:env_t) (x:btvdef) (t:term) = 
    {env with bindings=Binding_tvar(x,t)::env.bindings}
 let lookup_typ_var env a = 
    lookup_binding env (function Binding_tvar(b, _) -> Util.bvd_eq b a.v | _ -> false)

let gen_free_var (env:env_t) (x:lident) =
    let ysym = varops.new_fvar x in 
    let y = Funsym ysym in
    ysym, y, {env with bindings=Binding_fvar(x, y)::env.bindings}
let push_free_var (env:env_t) (x:lident) (t:term) = 
    {env with bindings=Binding_fvar(x, t)::env.bindings}
let lookup_free_var env a = 
    lookup_binding env (function Binding_fvar(b, _) -> lid_equals b a.v | _ -> false)
let lookup_lid env a = 
    lookup_binding env (function Binding_fvar(b, _) -> lid_equals b a | _ -> false)

let gen_free_tvar (env:env_t) (x:lident) =
    let ysym = varops.new_fvar x in 
    let y = Funsym ysym in 
    ysym, y, {env with bindings=Binding_ftvar(x, y)::env.bindings}
let push_free_tvar (env:env_t) (x:lident) (t:term) = 
    {env with bindings=Binding_ftvar(x, t)::env.bindings}
let lookup_free_tvar env a = 
    lookup_binding env (function Binding_ftvar(b, _) -> lid_equals b a.v | _ -> false)

let lookup_typ_projector (env:env_t) (lid:lident) (a:btvdef)  : term = failwith "NYI"
let lookup_term_projector (env:env_t) (lid:lident) (a:bvvdef) : term = failwith "NYI"
let lookup_term_projector_by_pos (env:env_t) (lid:lident) (i:int) : term = failwith "NYI"
let mk_data_tester env l = failwith "NYI"
let close (binders:list<(string * sort)>) d : decls = failwith "NYI"

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
                | None -> withenv env <| fresh "x"
                | Some x -> gen_term_var env x in 
            let kk2, g2 = encode_knd env' k2 in 
            let ksym, k = fresh "kind" in 
            let fsym, f = fresh "f" in
            let g = [Term.DeclFun(ksym, [], Kind_sort, None);
                     Term.Assume(mk_tester Kind_sort "Kind_dcon" k, None);
                     Term.Assume(Forall ([mk_HasKind f k], [(fsym,Type_sort)], 
                                         Iff(mk_HasKind f k, 
                                             And(mk_tester Kind_sort "Kind_dcon" (mk_PreKind f), 
                                                 Forall([mk_ApplyTE f xx], [(xxsym, Term_sort)], 
                                                        Imp(mk_HasType xx tt1, 
                                                            mk_HasKind (mk_ApplyTE f xx) kk2))))), None)] in
            k, (g1@close [(xxsym, Term_sort)] g2@g)
             
        | Kind_tcon(aopt, k1, k2, _) -> 
            let kk1, g1 = encode_knd env k1 in 
            let aasym, aa, env' = match aopt with 
                | None -> withenv env <| fresh "a"
                | Some a -> gen_typ_var env a in 
            let kk2, g2 = encode_knd env' k2 in 
            let ksym, k = fresh "kind" in 
            let fsym, f = fresh "f" in
            let g = [Term.DeclFun(ksym, [], Kind_sort, None);
                     Term.Assume(mk_tester Kind_sort "Kind_tcon" k, None);
                     Term.Assume(Forall ([mk_HasKind f k], [(fsym,Type_sort)], 
                                         Iff(mk_HasKind f k, 
                                             And(mk_tester Kind_sort "Kind_tcon" (mk_PreKind f), 
                                                 Forall([mk_ApplyTT f aa], [(aasym, Type_sort)], 
                                                        Imp(mk_HasKind aa kk1, 
                                                            mk_HasKind (mk_ApplyTT f aa) kk2))))), None)] in
            k, (g1@close [(aasym, Type_sort)] g2@g)
            
        | Kind_abbrev(_, k) -> 
            encode_knd env k

        | Kind_uvar uv -> 
            let ksym = format1 "Kind_uvar %d" (string_of_int <| Unionfind.uvar_id uv) in
            let g = [Term.DeclFun(ksym, [], Kind_sort, None)] in
            Term.Funsym ksym, g

        | _ -> failwith "Unknown kind"

and encode_typ (env:env_t) (t:typ) : res = (* expects t to be in normal form already *)
    match t.t with 
      | Typ_btvar a -> 
        lookup_typ_var env a, []

      | Typ_const fv -> 
        lookup_free_tvar env fv, []

      | Typ_refine(x, t, f) -> 
        let tt, g1 = encode_typ env t in 
        let xxsym, xx, env' = gen_term_var env x in
        let ff, g2 = encode_formula env' f in 
        let tsym, t = fresh "type" in
        let g = [Term.DeclFun(tsym, [], Type_sort, None);
                 Term.Assume(Forall([mk_HasType xx t], [(xxsym, Term_sort)], 
                                    Iff(mk_HasType xx t, And(mk_HasType xx tt, ff))), None)] in 
        t, g1@close [(xxsym, Term_sort)] g2@g
     
      | Typ_fun(xopt, t1, c, _) -> 
        if not <| Util.is_pure env.tcenv c 
        then let tsym, t = fresh "type" in
             let fsym, f = fresh "f" in 
             let g = [Term.DeclFun(tsym, [], Type_sort, None);
                      Term.Assume(mk_tester Type_sort "Typ_fun" t, None);
                      Term.Assume(Forall([mk_HasType f t], [(fsym, Term_sort)], 
                                         Imp(mk_HasType f t, mk_tester Type_sort "Typ_fun" (mk_PreType f))), None)] in
             f, g
        else let tt1, g1 = encode_typ env t1 in 
             let xxsym, xx, env' = match xopt with 
                | None -> withenv env <| fresh "x"
                | Some x -> gen_term_var env x in 
             let t2, wp2, _ = Tc.Util.destruct_comp (Util.force_comp c) in
             let tt2, g2 = encode_typ env' t2 in
             let g2 = match xopt with 
                | None -> g2
                | _ -> close [(xxsym, Term_sort)] g2 in
             let wp2', g3 = encode_formula env' (norm_t env' <| (withkind Kind_type <| Typ_app(wp2, trivial_post t2, false))) in 
             let tsym, t = fresh "type" in 
             let fsym, f = fresh "f" in 
             let g = [Term.DeclFun(tsym, [], Type_sort, None);
                      Term.Assume(mk_tester Type_sort "Typ_fun" t, None);
                      Term.Assume(Forall([mk_HasType f t], [(fsym, Term_sort)], 
                                         Iff(mk_HasType f t, 
                                             And(mk_tester Type_sort "Typ_fun" (mk_PreType f),
                                                 Forall([mk_ApplyEE f xx], [(xxsym, Term_sort)], 
                                                        Imp(And(mk_HasType xx tt1, wp2'),
                                                            mk_HasType (mk_ApplyEE f xx) tt2))))), None)] in
            t, g1@g2@g3@g

      | Typ_univ(a, k, c) -> 
        if not <| Util.is_pure env.tcenv c 
        then let tsym, t = fresh "type" in
             let fsym, f = fresh "f" in 
             let g = [Term.DeclFun(tsym, [], Type_sort, None);
                      Term.Assume(mk_tester Type_sort "Typ_univ" t, None);
                      Term.Assume(Forall([mk_HasType f t], [(fsym, Term_sort)], 
                                         Imp(mk_HasType f t, mk_tester Type_sort "Typ_univ" (mk_PreType f))), None)] in
             f, g
        else let kk, g1 = encode_knd env k in 
             let aasym, aa, env' = gen_typ_var env a in
             let t2, wp2, _ = Util.destruct_comp (Util.force_comp c) in 
             let tt2, g2 = encode_typ env' t2 in
             let post = withkind kun <| Typ_lam(Util.new_bvd None, t2, Util.ftv Const.true_lid) in
             let wp2', g3 = encode_formula env' (norm_t env' <| (withkind Kind_type <| Typ_app(wp2, post, false))) in 
             let tsym, t = fresh "type" in 
             let fsym, f = fresh "f" in 
             let f = Funsym fsym in 
             let g = [Term.DeclFun(tsym, [], Type_sort, None);
                      Term.Assume(mk_tester Type_sort "Typ_univ" t, None);
                      Term.Assume(Forall([mk_HasType f t], [(fsym, Term_sort)], 
                                         Iff(mk_HasType f t, 
                                             And(mk_tester Type_sort "Typ_univ" (mk_PreType f),
                                                 Forall([mk_ApplyET f aa], [(aasym, Type_sort)], 
                                                        Imp(And(mk_HasKind aa kk, wp2'),
                                                            mk_HasType (mk_ApplyET f aa) tt2))))), None)] in
            t, g1@(close [(aasym, Type_sort)] <| g2@g3)@g
      
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
        let tsym, t = fresh "type" in
        let g = [Term.DeclFun(tsym, [], Type_sort, None);
                 Term.Assume(Forall([mk_ApplyTE t xx], [(xxsym, Term_sort)], 
                                    Imp(mk_HasType xx tt1, 
                                        Eq(mk_ApplyTE t xx, tt2))), None)] in
        t, g1@close [(xxsym, Term_sort)] g2@g

      | Typ_tlam(a, k1, t2) -> 
        let kk1, g1 = encode_knd env k1 in 
        let aasym, aa, env' = gen_typ_var env a in 
        let tt2, g2 = encode_typ env' t2 in 
        let tsym, t = fresh "type" in
        let g = [Term.DeclFun(tsym, [], Type_sort, None);
                 Term.Assume(Forall([mk_ApplyTT t aa], [(aasym, Type_sort)], 
                                    Imp(mk_HasKind aa kk1,
                                        Eq(mk_ApplyTT t aa, tt2))), None)] in
        t, g1@close [(aasym, Type_sort)] g2@g

      | Typ_ascribed(t, k) -> 
        let tt, g1 = encode_typ env t in 
        let kk, g2 = encode_knd env k in 
        let g = [Term.Assume(mk_HasKind tt kk, None)] in
        tt, g1@g2@g

      | Typ_uvar(uv, _) -> 
        let tsym = format1 "Typ_uvar %d" (string_of_int <| Unionfind.uvar_id uv) in
        let g = [Term.DeclFun(tsym, [], Type_sort, None)] in 
        Term.Funsym tsym, g

      | Typ_meta _
      | Typ_delayed  _ 
      | Typ_unknown    -> failwith "Impossible"                 
       
and encode_exp (env:env_t) (e:exp) : res =
    let e = Visit.compress_exp_uvars e in 
    let encode_const = function 
        | Const_unit -> mk_Term_unit, []
        | Const_bool true -> boxBool True, []
        | Const_bool false -> boxBool False, []
        | Const_int32 i -> boxInt (Integer i), []
        | Const_string(bytes, _) -> varops.string_const (Util.string_of_bytes <| bytes)
        | c -> 
        let esym, e = fresh "const" in 
        let g = [Term.DeclFun(esym, [], Term_sort, Some (format1 "Constant: %s" <| Print.const_to_string c))] in 
        e, g in
    match e with 
      | Exp_delayed _ -> encode_exp env (Util.compress_exp e)
       
      | Exp_meta(Meta_info(Exp_abs(x, t, e), tfun, _)) -> 
        begin match (Util.compress_typ tfun).t with 
            | Typ_fun(_, _, c, _) -> 
                if not <| Util.is_pure env.tcenv c
                then let esym, e = fresh "impure_fun" in
                     e, [Term.DeclFun(esym, [], Term_sort, None)]
                else let t2, wp2, _ = Tc.Util.destruct_comp (Util.force_comp c) in
                     let tt, g1 = encode_typ env t in
                     let xxsym, xx, env' = gen_term_var env x in
                     let tt2, g2 = encode_typ env' t2 in
                     let wp2', g3 = encode_formula env' (withkind Kind_type <| Typ_app(wp2, trivial_post t2, false)) in
                     let ee, g4 = encode_exp env' e in
                     let fsym, f = fresh "fun" in
                     let g = [Term.DeclFun(fsym, [], Term_sort, None);
                              Term.Assume(Forall([mk_ApplyEE f xx], [(xxsym, Term_sort)], 
                                                 Imp(And(mk_HasType xx tt, wp2'),
                                                     And(Eq(mk_ApplyEE f xx, ee),
                                                         mk_HasType ee tt2))), None)] in
                     f, g1@(close [(xxsym, Term_sort)] g2@g3@g4)@g
            | _ -> failwith "Impossible"
        end


      | Exp_meta(Meta_info(Exp_tabs(a, k, e), tfun, _)) -> 
        begin match (Util.compress_typ tfun).t with 
            | Typ_univ(_, _, c) -> 
                if not <| Util.is_pure env.tcenv c
                then let esym, e = fresh "impure_fun" in
                     e, [Term.DeclFun(esym, [], Term_sort, None)]
                else let t2, wp2, _ = Tc.Util.destruct_comp (Util.force_comp c) in
                     let kk, g1 = encode_knd env k in
                     let aasym, aa, env' = gen_typ_var env a in
                     let tt2, g2 = encode_typ env' t2 in
                     let wp2', g3 = encode_formula env' (withkind Kind_type <| Typ_app(wp2, trivial_post t2, false)) in
                     let ee, g4 = encode_exp env' e in
                     let fsym, f = fresh "fun" in
                     let g = [Term.DeclFun(fsym, [], Term_sort, None);
                              Term.Assume(Forall([mk_ApplyET f aa], [(aasym, Type_sort)], 
                                                 Imp(And(mk_HasKind aa kk, wp2'),
                                                     And(Eq(mk_ApplyET f aa, ee),
                                                         mk_HasType ee tt2))), None)] in
                     f, g1@(close [(aasym, Type_sort)] g2@g3@g4)@g
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
                | Pat_var x -> True, push_term_var env x d, []     
                | Pat_tvar a -> True, push_typ_var env a d, [] 
                | Pat_wild
                | Pat_twild -> True, env, []
                | Pat_constant c -> 
                  let c, g = encode_const c in
                  Eq(d, c), env, g 
                | Pat_cons(lid, pats) -> 
                  let cname = lookup_lid env lid in 
                  let guard = match cname with 
                    | Funsym l -> Term.mk_tester Term_sort l d 
                    | _ -> True in //warn?
                  let args, _ =  Util.collect_formals <| Tc.Env.lookup_datacon env.tcenv lid in  
                  let guards, env, g, _ = List.fold_left2 (fun (guards, env, g, i) arg pat -> match arg with 
                    | Inl (a, k) -> 
                      let t = lookup_typ_projector env lid a in
                      let aa = Term.mk_ApplyTE t d in 
                      let guard, env, g' = mk_guard_env env aa pat in
                      (guard::guards, env, g@g', i+1)
                    | Inr (xopt, t, _) ->
                      let t = match xopt with 
                        | None -> lookup_term_projector_by_pos env lid i
                        | Some x -> lookup_term_projector env lid x in
                      let xx = Term.mk_ApplyTE t d in 
                      let guard, env, g' = mk_guard_env env xx pat in
                      (guard::guards, env, g@g', i+1))
                      ([], env, [], 0) args pats in
                  let guard = List.hd <| Term.mk_and_l (guard::guards) in 
                  guard, env, g in
            top_level_pats pat |> 
            List.map (mk_guard_env env ee) |>
            List.map (fun (guard, env, g) -> 
                let bb, g1 = encode_exp env b in
                let guard, g2 = match wopt with 
                    | None -> guard, []
                    | Some e -> 
                        let w, g = encode_exp env e in  
                        And(guard, Eq(w, boxBool True)), g in
                guard, bb, g@g1@g2) in

        let ee, g1 = encode_exp env e in 
        let branches, g = List.fold_right (fun (pat, wopt, b) (def, g) -> 
            let gbgs = encode_pat env ee pat wopt b in 
            List.fold_right (fun (guard, branch, g') (def, g) -> 
               Term.IfThenElse(guard, branch, def), g@g') gbgs (def, g))
            pats (Term.boxBool False, []) in
        branches, g@g1
      
      | Exp_ascribed(e, t) -> 
        let ee, g1 = encode_exp env e in 
        let tt, g2 = encode_typ env t in 
        let g = [Term.Assume(mk_HasType ee tt, None)] in
        ee, g1@g2@g
      
      | Exp_uvar(uv, _) ->
        let esym = format1 "Exp_uvar %d" (string_of_int <| Unionfind.uvar_id uv) in
        let g = [Term.DeclFun(esym, [], Term_sort, None)] in 
        Term.Funsym esym, g

      | Exp_abs _
      | Exp_tabs _
      | Exp_meta _ -> failwith "Impossible"

and encode_formula (env:env_t) (phi:typ) : res = (* expects phi to be normalized *)
    let destruct_connectives f = 
      let oneType    = [Type_sort] in
      let twoTypes   = [Type_sort;Type_sort] in
      let threeTys   = [Type_sort;Type_sort;Type_sort] in
      let twoTerms   = [Term_sort;Term_sort] in
      let un_op  f [t1] = f t1 in
      let bin_op f [t1;t2] = f(t1,t2) in
      let tri_op f [t1;t2;t3] = f(t1,t2,t3) in
      let quad_op f [_;_;t1;t2] = f(t1, t2) in
      let connectives = [(Const.and_lid, twoTypes, bin_op And);
                         (Const.or_lid,  twoTypes, bin_op Or);
                         (Const.imp_lid, twoTypes, bin_op Imp);
                         (Const.iff_lid, twoTypes, bin_op Iff);
                         (Const.ite_lid, threeTys, tri_op IfThenElse);
                         (Const.not_lid, oneType,  un_op Not);
                         (Const.lt_lid,  twoTerms, bin_op LT);
                         (Const.gt_lid,  twoTerms, bin_op GT);
                         (Const.gte_lid, twoTerms, bin_op GTE);
                         (Const.lte_lid, twoTerms, bin_op LTE);
                         (Const.eqT_lid, twoTypes, bin_op Eq);
                         (Const.eq_lid,  twoTerms@twoTypes, quad_op Eq);
                        ] in 
      let rec aux args f (lid, arity, b) =  match f.t, arity with
        | Typ_app(tc, arg, _), [t] 
          when (t=Type_sort) -> 
          if Util.is_constructor tc lid
          then Some (lid, Inl arg::args, b)
          else None
        | Typ_dep(tc, arg, _), [t] 
          when (t=Term_sort) ->
          if (Util.is_constructor tc lid)
          then Some (lid, Inr arg::args, b)
          else None
        | Typ_app(f, arg, _), t::farity 
          when (t=Type_sort) -> 
          aux (Inl arg::args) f (lid, farity, b)
        | Typ_dep(f, arg, _), t::farity 
          when (t=Term_sort) -> 
          aux (Inr arg::args) f (lid, farity, b)
        | _ -> None in
      Util.find_map connectives (aux [] f) in

    let collect_quants t = 
      let rec aux qopt out t = 
        match qopt, Util.flatten_typ_apps t with
          | Some q, ({t=Typ_const tc}, [Inl t1; Inl {t=Typ_lam(x, _, t2)}])  
            when (lid_equals tc.v q) -> 
            aux qopt (Inr(x, t1)::out) t2

          | None, ({t=Typ_const tc}, [Inl t1; Inl {t=Typ_lam(x, _, t2)}])  
            when (Util.is_qlid tc.v) -> 
            aux (Some tc.v) (Inr(x,t1)::out) t2
            
          | _ -> qopt, List.rev out, t
      in aux None [] t in


      match destruct_connectives phi with 
        | Some (_, args, b) -> 
          let args, g = List.fold_left (fun (args, g) -> function
            | Inl t -> let tt, g' = encode_typ env t in (tt::args, g@g')
            | Inr e -> let ee, g' = encode_exp env e in (ee::args, g@g')) ([], []) args in
          b args, g

        | None ->
          begin match collect_quants phi with 
            | Some q, args, body -> 
              let env, (vars, guard), g = args |> List.fold_left (fun (env, (vars, guard), g) -> function 
                | Inl (a, k) -> 
                  let kk, g' = encode_knd env k in 
                  let aasym, aa, env = gen_typ_var env a in 
                  (env, ((aasym, Type_sort)::vars, And(guard, mk_HasKind aa kk)), g@g')
                | Inr (x, t) ->
                  let tt, g' = encode_typ env t in 
                  let xxsym, xx, env = gen_term_var env x in 
                  (env, ((xxsym, Term_sort)::vars, And(guard, mk_HasType xx tt)), g@g')) (env, ([], True), []) in
              let body, g' = encode_formula env body in 
              let q = if Util.is_forall q then Term.Forall else Term.Exists in
              q([], List.rev vars, Imp(guard, body)), g@g'
                         
            | _ -> 
              let tt, g = encode_typ env phi in
              Term.mk_Valid tt, g
          end
let mk_prim =
    let asym, a = fresh "a" in 
    let bsym, b = fresh "b" in 
    let xsym, x = fresh "x" in 
    let ysym, y = fresh "y" in 
    let eq_assumption vars t1 t2 = Term.Assume(Forall([t1], vars, Eq(t1,t2)), None) in
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
        (Const.op_Eq,          (fun v -> abxy_t v (boxBool <| Eq(x,y))));
        (Const.op_notEq,       (fun v -> abxy_t v (boxBool <| Not(Eq(x,y)))));
        (Const.op_LT,          (fun v -> xy_t   v (boxBool <| LT(unboxInt x, unboxInt y))));
        (Const.op_LTE,         (fun v -> xy_t   v (boxBool <| LTE(unboxInt x, unboxInt y))));
        (Const.op_GT,          (fun v -> xy_t   v (boxBool <| GT(unboxInt x, unboxInt y))));
        (Const.op_GTE,         (fun v -> xy_t   v (boxBool <| GTE(unboxInt x, unboxInt y))));
        (Const.op_Subtraction, (fun v -> xy_t   v (boxBool <| Sub(unboxInt x, unboxInt y))));
        (Const.op_Minus,       (fun v -> x_t    v (boxInt  <| Minus(unboxInt x))));
        (Const.op_Addition,    (fun v -> xy_t   v (boxInt  <| Add(unboxInt x, unboxInt y))));
        (Const.op_Multiply,    (fun v -> xy_t   v (boxInt  <| Mul(unboxInt x, unboxInt y))));
        (Const.op_Division,    (fun v -> xy_t   v (boxInt  <| Div(unboxInt x, unboxInt y))));
        (Const.op_Modulus,     (fun v -> xy_t   v (boxInt  <| Mod(unboxInt x, unboxInt y))));
        (Const.op_And,         (fun v -> xy_t   v (boxBool <| And(unboxBool x, unboxBool y))));
        (Const.op_Or,          (fun v -> xy_t   v (boxBool <| Or(unboxBool x, unboxBool y))));
        (Const.op_Negation,    (fun v -> x_t    v (boxBool <| Not(unboxBool x))));
        ] in
    fun l v -> prims |> List.filter (fun (l', _) -> lid_equals l l') |> List.map (fun (_, b) -> b v)
 
let rec encode_sigelt (env:env_t) (se:sigelt) : (decls * env_t * typenames * datacons) = 
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
            vars, tapp, kk, g@[Term.Assume(Forall([tapp], List.rev vars, mk_HasKind tapp kk), None)] in
      match se with
        | Sig_typ_abbrev(lid, tps, k, t, tags, _) -> 
          let tsym, tt, env = gen_free_var env lid in 
          let def, g1 = encode_typ env (Util.close_with_lam tps t) in 
          let _, _, _, g2 = close_and_encode_knd env tt tps k in
          let g = [Term.DeclFun(tsym, [], Type_sort, Some (format1 "Typ_abbrev %s" (Print.sli lid)));
                   Term.Assume(Eq(tt, def), None)] in
          g1@g@g2, env, [], []
        
        | Sig_val_decl(lid, t, _, None, _) -> 
          let vsym, v, env = gen_free_var env lid in 
          let tt, g1 = encode_typ env t in 
          let g = [Term.DeclFun(vsym, [], Term_sort, Some (format1 "val %s" (Print.sli lid)));
                   Term.Assume(mk_HasType v tt, None)] in
          g1@g@mk_prim lid v, env, [], []

        | Sig_val_decl(lid, t, _, Some ltag, _) -> failwith "Handle val-decl ltags" 

        | Sig_assume(l, f, _, _, _) -> 
          let phi, g1 = encode_formula env f in 
          let g = [Term.Assume(phi, Some (format1 "Assumption: %s" (Print.sli l)))] in 
          g1@g, env, [], []
        
        | Sig_logic_function(l, t, tags, _) -> 
          let tt, g1 = encode_typ env t in 
          let fsym, f, env = gen_free_var env l in
          let g = [Term.DeclFun(fsym, [], Term_sort, Some (format1 "logic val %s" (Print.sli l)));
                   Term.Assume(mk_HasType f tt, None)] in 
          g1@g, env, [], []
        
        | Sig_tycon(t, tps, k, _, datas, tags, _) -> 
          let ttsym, _, _ = gen_free_var env t in
          let tt = Term.mk_Typ_const ttsym in
          let env = push_free_tvar env t tt in 
          let vars, tapp, _, g1 = close_and_encode_knd env tt tps (Util.close_kind tps k) in
          let xxsym, xx = fresh "x" in
          if tags |> Util.for_some (function tag -> tag=Logic_type) //uninterpreted types don't get data axioms
          then g1, env, [ttsym], []
          else let data_ax = datas |> List.fold_left (fun out l -> Or(out, mk_data_tester env l)) False in
               let g = [Term.Assume(Forall([tapp], vars@[(xxsym, Term_sort)], 
                                      Imp(mk_HasType xx tapp, data_ax)), None)] in
               g1@g, env, [ttsym], []

        | Sig_datacon(d, t, _, _) -> 
          let _, g1 = encode_typ env t in 
          let ddconstrsym = Print.sli d in
          let ddfunsym, ddfun = fresh (Print.sli d) in
          let env = push_free_var env d ddfun in
          let projectors, vars = Util.collect_formals t |> fst |> List.mapi (fun i -> function 
            | Inl(a, k) -> (format2 "%s_%s" ddconstrsym a.ppname.idText, Type_sort), (fresh "a", Type_sort)
            | Inr(Some x, t, _) -> (format2 "%s_%s" ddconstrsym x.ppname.idText, Term_sort), (fresh "x", Term_sort)
            | Inr(None, t, _) -> (format2 "%s_%s" ddconstrsym (string_of_int i), Term_sort), (fresh "x", Term_sort)) |> List.unzip in
          let datacons = [(ddconstrsym, projectors, Term_sort)] in
          let app, args, sort = List.fold_left (fun (tm, args, sort) ((_, ax), s) -> match s with 
            | Type_sort -> Term.mk_ApplyET tm ax, ax::args, Arrow(s, sort)
            | Term_sort -> Term.mk_ApplyEE tm ax, ax::args, Arrow(s, sort)) (ddfun, [], Term_sort) vars in
          let g = [Term.DeclFun(ddfunsym, [], Term_sort, Some (format1 "data constructor proxy: %s" (Print.sli d)));
                   Term.Assume(Forall([app], vars |> List.map (fun ((x, _), s) -> x,s), 
                                      Eq(app, Term.App(ddconstrsym, sort, List.rev args))), None)] in
          g1@g, env, [], datacons

        | Sig_bundle(ses, _) -> 
          encode_signature env ses

        | Sig_let((false,[(Inr x, t, e)]), _) ->
          let xxsym, xx, env = gen_free_var env x in 
          let tt, g1 = encode_typ env t in 
          let ee, g2 = encode_exp env e in
          let g = [Term.DeclFun(xxsym, [], Term_sort, Some (Print.sli x));
                   Term.Assume(mk_HasType xx tt, None);
                   Term.Assume(Eq(xx, ee), None)] in
          g1@g2@g, env, [], []

        | Sig_let((_,lbs), _) -> //TODO 
          let msg = lbs |> List.map (fun (lb, _, _) -> Print.lbname_to_string lb) |> String.concat " and " in
          let g = [Term.Comment(format1 "Skipping let rec %s" msg)] in
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
            let xxsym, xx, env' = gen_term_var env x in 
            let g' = [Term.DeclFun(xxsym, [], Term_sort, Some (Print.strBvd x));
                      Term.Assume(Term.mk_HasType xx tt, None)] in
            decls@g@g', env'
        | Env.Binding_typ(a, k) -> 
            let kk, g = encode_knd env (norm_k env k) in
            let aasym, aa, env' = gen_typ_var env a in 
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
let smt_query (tcenv:Tc.Env.env) (q:typ) : bool = 
   let e = {bindings=[]; tcenv=tcenv} in
   let decls, env, tys, datas = tcenv.modules |> List.collect (fun m -> m.exports) |> encode_signature e in
   let decls', env = encode_env env tcenv in
   let phi, decls'' = encode_formula env (norm_t env q) in
   let decls = Term.DefPrelude(tys, datas)::decls@decls'@decls''@[Term.Assume(Not phi, Some "query")] in
   Z3.callZ3Exe decls [] 

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

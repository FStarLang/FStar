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
open Term

type binding = 
    | Binding_var   of bvvdef * string
    | Binding_tvar  of btvdef * string
    | Binding_fvar  of lident * string
    | Binding_ftvar of lident * string
   
type env_t = {bindings:list<binding>;
              tcenv:Env.env}

let lookup_binding env f = 
    match env.bindings |> List.tryFind f with 
        | None -> failwith "Unbound variable"
        | Some (Binding_var(_, s))
        | Some (Binding_tvar(_, s))
        | Some (Binding_fvar(_, s))
        | Some (Binding_ftvar(_, s)) -> s
              
let new_var, new_fvar, fresh, string_const = 
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
    let fresh sfx = incr ctr; format2 "%s_%s" sfx (string_of_int !ctr) in
    let string_const s = match Util.smap_try_find string_constants s with
        | Some f -> f, []
        | None -> 
            let fsym = fresh "string" in
            let f = Funsym fsym in
            let g = [Term.DeclFun(fsym, [], String_sort, Some s);
                     Term.Assume(Eq(f, mk_String_const !ctr), None)] in 
            Util.smap_add string_constants s f;
            f, g in
    new_var, new_fvar, fresh, string_const
              
let gen_term_var (env:env_t) (x:bvvdef) = 
    let y = new_var x.ppname x.realname in 
    y, {env with bindings=Binding_var(x,y)::env.bindings}
let lookup_term_var env a = 
    lookup_binding env (function Binding_var(b, _) -> Util.bvd_eq b a.v | _ -> false)

let gen_typ_var (env:env_t) (x:btvdef) = 
    let y = new_var x.ppname x.realname in 
    y, {env with bindings=Binding_tvar(x,y)::env.bindings}
let lookup_typ_var env a = 
    lookup_binding env (function Binding_tvar(b, _) -> Util.bvd_eq b a.v | _ -> false)

let gen_free_var (env:env_t) (x:lident) =
    let y = new_fvar x in 
    y, {env with bindings=Binding_fvar(x, y)::env.bindings}
let lookup_free_var env a = 
    lookup_binding env (function Binding_fvar(b, _) -> lid_equals b a.v | _ -> false)

let gen_free_tvar (env:env_t) (x:lident) =
    let y = new_fvar x in 
    y, {env with bindings=Binding_ftvar(x, y)::env.bindings}
let lookup_free_tvar env a = 
    lookup_binding env (function Binding_ftvar(b, _) -> lid_equals b a.v | _ -> false)

let close (binders:list<(string * sort)>) d : decls = failwith "NYI"

(*---------------------------------------------------------------------------------*)
let norm_t env t = Tc.Normalize.normalize env.tcenv t
let norm_k env k = Tc.Normalize.normalize_kind env.tcenv k

type res = (
    term     (* the translation of a knd/typ/exp *)
  * decls    (* auxiliary top-level assertions in support of the term *)
 )

let rec encode_knd (env:env_t) (k:knd)  : res = 
    match Util.compress_kind k with 
        | Kind_type -> 
            Term.mk_Kind_type, []

        | Kind_dcon(xopt, t1, k2, _) ->
            let tt1, g1 = encode_typ env t1 in 
            let xxsym, env' = match xopt with 
                | None -> fresh "x", env 
                | Some x -> 
                    let xx, env = gen_term_var env x in 
                    xx, env in
            let kk2, g2 = encode_knd env k2 in 
            let ksym = fresh "kind" in 
            let k = Term.Funsym ksym in
            let fsym = fresh "f" in
            let f = Funsym fsym in 
            let xx = Funsym xxsym in 
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
            let aasym, env' = match aopt with 
                | None -> fresh "a", env 
                | Some a -> 
                    let aa, env = gen_typ_var env a in 
                    aa, env in
            let kk2, g2 = encode_knd env k2 in 
            let ksym = fresh "kind" in 
            let k = Term.Funsym ksym in
            let fsym = fresh "f" in
            let f = Funsym fsym in 
            let aa = Funsym aasym in 
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
        Funsym <| lookup_typ_var env a, []

      | Typ_const fv -> 
        Funsym <| lookup_free_tvar env fv, []

      | Typ_refine(x, t, f) -> 
        let tt, g1 = encode_typ env t in 
        let xxsym, env' = gen_term_var env x in
        let xx = Funsym xxsym in
        let ff, g2 = encode_formula env' f in 
        let tsym = fresh "type" in
        let t = Funsym tsym in 
        let g = [Term.DeclFun(tsym, [], Type_sort, None);
                 Term.Assume(Forall([mk_HasType xx t], [(xxsym, Term_sort)], 
                                    Iff(mk_HasType xx t, And(mk_HasType xx tt, ff))), None)] in 
        t, g1@close [(xxsym, Term_sort)] g2@g
     
      | Typ_fun(xopt, t1, c, _) -> 
        if not <| Util.is_pure env.tcenv c 
        then let tsym = fresh "type" in
             let t = Funsym tsym in 
             let fsym = fresh "f" in 
             let f = Funsym fsym in 
             let g = [Term.DeclFun(tsym, [], Type_sort, None);
                      Term.Assume(mk_tester Type_sort "Typ_fun" t, None);
                      Term.Assume(Forall([mk_HasType f t], [(fsym, Term_sort)], 
                                         Imp(mk_HasType f t, mk_tester Type_sort "Typ_fun" (mk_PreType f))), None)] in
             f, g
        else let tt1, g1 = encode_typ env t1 in 
             let xxsym, env' = match xopt with 
                | None -> fresh "x", env 
                | Some x -> gen_term_var env x in 
             let xx = Funsym xxsym in
             let t2, wp2, _ = Tc.Util.destruct_comp (Util.force_comp c) in
             let tt2, g2 = encode_typ env' t2 in
             let g2 = match xopt with 
                | None -> g2
                | _ -> close [(xxsym, Term_sort)] g2 in
             let post = withkind kun <| Typ_lam(Util.new_bvd None, t2, Util.ftv Const.true_lid) in
             let wp2', g3 = encode_formula env' (norm_t env' <| (withkind Kind_type <| Typ_app(wp2, post, false))) in 
             let tsym = fresh "type" in 
             let t = Funsym tsym in 
             let fsym = fresh "f" in 
             let f = Funsym fsym in 
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
        then let tsym = fresh "type" in
             let t = Funsym tsym in 
             let fsym = fresh "f" in 
             let f = Funsym fsym in 
             let g = [Term.DeclFun(tsym, [], Type_sort, None);
                      Term.Assume(mk_tester Type_sort "Typ_univ" t, None);
                      Term.Assume(Forall([mk_HasType f t], [(fsym, Term_sort)], 
                                         Imp(mk_HasType f t, mk_tester Type_sort "Typ_univ" (mk_PreType f))), None)] in
             f, g
        else let kk, g1 = encode_knd env k in 
             let aasym, env' = gen_typ_var env a in
             let aa = Funsym aasym in
             let t2, wp2, _ = Util.destruct_comp (Util.force_comp c) in 
             let tt2, g2 = encode_typ env' t2 in
             let post = withkind kun <| Typ_lam(Util.new_bvd None, t2, Util.ftv Const.true_lid) in
             let wp2', g3 = encode_formula env' (norm_t env' <| (withkind Kind_type <| Typ_app(wp2, post, false))) in 
             let tsym = fresh "type" in 
             let t = Funsym tsym in 
             let fsym = fresh "f" in 
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
        let xxsym, env' = gen_term_var env x in 
        let tt2, g2 = encode_typ env' t2 in 
        let xx = Funsym xxsym in 
        let tsym = fresh "type" in
        let t = Funsym tsym in 
        let g = [Term.DeclFun(tsym, [], Type_sort, None);
                 Term.Assume(Forall([mk_ApplyTE t xx], [(xxsym, Term_sort)], 
                                    Imp(mk_HasType xx tt1, 
                                        Eq(mk_ApplyTE t xx, tt2))), None)] in
        t, g1@close [(xxsym, Term_sort)] g2@g

      | Typ_tlam(a, k1, t2) -> 
        let kk1, g1 = encode_knd env k1 in 
        let aasym, env' = gen_typ_var env a in 
        let tt2, g2 = encode_typ env' t2 in 
        let aa = Funsym aasym in 
        let tsym = fresh "type" in
        let t = Funsym tsym in 
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
    match e with 
      | Exp_delayed _ -> encode_exp env (Util.compress_exp e)
       
      | Exp_meta(Meta_info(Exp_abs(x, t, e), t2, _)) -> ()
      | Exp_meta(Meta_info(Exp_tabs(a, k, e), t2, _)) -> ()

      | Exp_meta(Meta_desugared(e, _))
      | Exp_meta(Meta_info(e, _, _)) -> encode_exp env e 

      | Exp_bvar x -> 
        Funsym (lookup_term_var env x), []

      | Exp_fvar(v, _) -> 
        Funsym (lookup_free_var env v), []

      | Exp_constant c -> 
        (match c with
         | Const_unit -> mk_Term_unit, []
         | Const_bool true -> boxBool True, []
         | Const_bool false -> boxBool False, []
         | Const_int32 i -> boxInt (Integer i), []
         | Const_string(bytes, _) -> string_const (Util.string_of_bytes <| bytes)
         | _ -> 
           let esym = fresh "const" in 
           let e = Funsym esym in 
           let g = [Term.DeclFun(esym, [], Term_sort, Some (format1 "Constant: %s" <| Print.const_to_string c))] in 
           e, g)

      | Exp_primop(op, args) -> failwith "NYI"

      | Exp_app(e1, e2, _) -> 
        let ee1, g1 = encode_exp env e1 in 
        let ee2, g2 = encode_exp env e2 in 
        mk_ApplyEE ee1 ee2, g1@g2
        
      | Exp_tapp(e1, t2) -> 
        let ee1, g1 = encode_exp env e1 in 
        let tt2, g2 = encode_typ env t2 in 
        mk_ApplyET ee1 tt2, g1@g2
      
      
//      | Exp_match      of exp * list<(pat * option<exp> * exp)>      (* optional when clause in each equation *)
//      | Exp_let        of letbindings * exp                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
      
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

and encode_formula (env:env_t) (phi:typ) : res = 
    failwith "NYI"

let encode_sigelt (env:env_t) (se:sigelt) : (decls * env_t) = 
    failwith "NYI"

let encode_env (tcenv:Env.env) (env:env_t) : (decls * env_t) = 
    let encode_binding (decls, env) = function
        | Env.Binding_var(x, t) -> 
            let tt, g = encode_typ env (norm_t env t) in
            let xx, env' = gen_term_var env x in 
            let g' = [Term.DeclFun(xx, [], Term_sort, Some (Print.strBvd x));
                      Term.Assume(Term.mk_HasType (Term.Funsym(xx)) tt, None)] in
            decls@g@g', env'
        | Env.Binding_typ(a, k) -> 
            let kk, g = encode_knd env (norm_k env k) in
            let aa, env' = gen_typ_var env a in 
            let g' = [Term.DeclFun(aa, [], Type_sort, Some (Print.strBvd a));
                      Term.Assume(Term.mk_HasKind (Term.Funsym(aa)) kk, None)] in
            decls@g@g', env'
        | Env.Binding_lid(x, t) -> 
            let tt, g = encode_typ env (norm_t env t) in
            let xx, env' = gen_free_var env x in 
            let g' = [Term.DeclFun(xx, [], Term_sort, Some (Print.sli x));
                      Term.Assume(Term.mk_HasType (Term.Funsym(xx)) tt, None)] in
            decls@g@g', env'
        | Env.Binding_sig se -> 
            encode_sigelt env se in
    Env.fold_env tcenv encode_binding ([], env)


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
//
//let rec kind_to_sorts k = match Util.compress_kind k with
//  | Kind_tcon(_, _, k) -> Type_sort::kind_to_sorts k
//  | Kind_dcon(_, _, k) -> Term_sort::kind_to_sorts k
//  | Kind_abbrev(_, k) -> kind_to_sorts k
//  | Kind_type -> []
//    
//let rec typ_to_sorts t = match (Util.compress_typ t).t with 
//  | Typ_fun(_, _, t) -> Term_sort::typ_to_sorts t
//  | Typ_univ(_, _, t) -> Type_sort::typToSorts t
//  | _ -> Term_sort
//    
//let arrowSort sorts = 
//  sorts |> List.fold_right (fun k sopt -> match sopt with 
//    | None -> Some k 
//    | Some k' -> Some <| Arrow(k, k')) |> Util.must
//
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
//let getBvd = function 
//  | Some x -> x 
//  | None -> new_bvd None 
//
//(* ******************************************************************************** *)
//(* Encoding core language: kinds, types, terms, formulas                            *)
//(* ******************************************************************************** *)
//let destructConnectives f = 
//  let oneType = [Type_sort] in
//  let twoTypes = [Type_sort;Type_sort] in
//  let threeTypes = [Type_sort;Type_sort;Type_sort] in
//  let twoTerms = [Term_sort;Term_sort] in
//  let connectives = [(Const.and_lid,     twoTypes);
//                     (Const.or_lid,      twoTypes);
//                     (Const.implies_lid, twoTypes);
//                     (Const.iff_lid,     twoTypes);
//                     (Const.ifthenelse_lid, threeTypes);
//                     (Const.not_lid,     oneType);
//                     (Const.spec_only_lid, oneType);
//                     (Const.lt_lid,      twoTerms);
//                     (Const.gt_lid,      twoTerms);
//                     (Const.gte_lid,     twoTerms);
//                     (Const.lte_lid,     twoTerms);
//                     (Const.eqTyp_lid,   twoTypes);
//                     (Const.eq_lid,      twoTerms@[Type_sort]);
//                     (Const.eq2_lid,     twoTerms@twoTypes);
//                     (Const.eqA_lid,     twoTerms@[Type_sort]);
//                     (Const.reln_lid,    oneType)] in 
//  let rec aux args f lid arity =  match f.t, arity with
//    | Typ_app(tc, arg), [t] 
//      when (t=Type_sort && Util.is_constructor tc lid) -> 
//      Some (lid, Inl arg::args)
//    | Typ_dep(tc, arg), [t] 
//      when (t=Term_sort && Util.is_constructor tc lid) -> 
//      Some (lid, Inr arg::args)
//    | Typ_app(f, arg), t::farity 
//      when t=Type_sort -> 
//      aux (Inl arg::args) f lid farity
//    | Typ_dep(f, arg), t::farity 
//      when t=Term_sort -> 
//      aux (Inr arg::args) f lid farity
//    | _ -> None in
//  Util.find_map connectives (fun (lid, arity) -> aux [] f lid arity)
//    
//let collect_u_quants t = 
//  let rec aux out t = 
//    match Util.flattenTypAppsAndDeps t' with
//      | {v=Typ_const(tc,_)}, [Inl t1; Inl {v=Typ_lam(x, _, t2)}] 
//        when (Const.is_forall tc.v) -> 
//        aux ((x, t1)::out) t2
//      | _ -> List.rev out, t'
//  in aux [] t

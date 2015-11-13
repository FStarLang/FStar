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
// (c) Microsoft Corporation. All rights reserved
module FStar.Syntax.Util

open Prims
open FStar
open FStar.Util
open FStar.Ident
open FStar.Range
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Const

let handle_err warning ret e =
  match e with
    | Error(msg, r) ->
        Util.print_string (Util.format3 "%s : %s\n%s\n" (Range.string_of_range r) (if warning then "Warning" else "Error") msg);
        ret
    | NYI s ->
        Util.print_string (Util.format1 "Feature not yet implemented: %s" s);
        ret
    | Err s ->
        Util.print_string (Util.format1 "Error: %s" s)
    | _ -> raise e

let handleable = function
  | Error _
  | NYI _
  | Err _ -> true
  | _ -> false


(********************************************************************************)
(**************************Utilities for identifiers ****************************)
(********************************************************************************)

let mk_discriminator lid =
  lid_of_ids (lid.ns@[mk_ident("is_" ^ lid.ident.idText, lid.ident.idRange)])

let is_name (lid:lident) =
  let c = Util.char_at lid.ident.idText 0 in
  Util.is_upper c

let arg_of_non_null_binder (b, imp) = (bv_to_tm b, imp)

let args_of_non_null_binders (binders:binders) =
    binders |> List.collect (fun b ->
        if is_null_binder b then []
        else [arg_of_non_null_binder b])

let args_of_binders (binders:Syntax.binders) : (Syntax.binders * args) =
 binders |> List.map (fun b ->
    if is_null_binder b
    then let b = new_bv None (fst b).sort, snd b in
         b, arg_of_non_null_binder b
    else b, arg_of_non_null_binder b) |> List.unzip

let name_binders binders =
    binders |> List.mapi (fun i b ->
            if is_null_binder b
            then let a, imp = b in
                 let b = id_of_text ("_" ^ string_of_int i) in
                 let b = {ppname=b; index=0; sort=a.sort} in
                 b, imp
            else b)

let name_function_binders t = match t.n with
    | Tm_arrow(binders, comp) -> mk (Tm_arrow(name_binders binders, comp)) None t.pos
    | _ -> t

let null_binders_of_tks (tks:list<(typ * aqual)>) : binders =
    tks |> List.map (fun (t, imp) -> fst <| null_binder t, imp)

let binders_of_tks (tks:list<(typ * aqual)>) : binders =
    tks |> List.map (fun (t, imp) -> new_bv (Some t.pos) t, imp)

let binders_of_freevars fvs = Util.set_elements fvs |> List.map mk_binder

let mk_subst s = [s]

let subst_formal (f:binder) (a:arg) = DB(0, fst a)
let subst_of_list (formals:binders) (actuals:args) : subst =
    if (List.length formals = List.length actuals)
    then List.fold_right2 (fun f a (n, out) -> (n + 1, DB(n, fst a)::out)) formals actuals (0, [])
         |> snd
    else failwith "Ill-formed substitution"

open FStar.Syntax.Subst

let rec unmeta e =
    let e = compress e in
    match e.n with
        | Tm_meta(e, _) 
        | Tm_ascribed(e, _, _) -> unmeta e
        | _ -> e

(********************************************************************************)
(*********************** Utilities for computation types ************************)
(********************************************************************************)

let ml_comp t r =
  mk_Comp ({effect_name=set_lid_range Const.effect_ML_lid r;
         result_typ=t;
         effect_args=[];
         flags=[MLEFFECT]})

let total_comp t r = mk_Total t

let gtotal_comp t =
    mk_Comp ({
        effect_name=Const.effect_GTot_lid;
        result_typ=t;
        effect_args=[];
        flags=[SOMETRIVIAL]
   })

let comp_set_flags (c:comp) f = match c.n with
  | Total _ -> c
  | Comp ct -> {c with n=Comp ({ct with flags=f})}

let comp_flags c = match c.n with
  | Total _ -> [TOTAL]
  | Comp ct -> ct.flags

let comp_effect_name c = match c.n with
    | Comp c  -> c.effect_name
    | Total _ -> Const.effect_Tot_lid

let comp_to_comp_typ (c:comp) : comp_typ =
    match c.n with
    | Comp c -> c
    | Total t -> {effect_name=Const.effect_Tot_lid; result_typ=t; effect_args=[]; flags=[TOTAL]}

let is_total_comp c =
    comp_flags c |> Util.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_total_lcomp c = lid_equals c.eff_name Const.effect_Tot_lid || c.cflags |> Util.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_tot_or_gtot_lcomp c = lid_equals c.eff_name Const.effect_Tot_lid
                             || lid_equals c.eff_name Const.effect_GTot_lid
                             || c.cflags |> Util.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_partial_return c = comp_flags c |> Util.for_some (function RETURN | PARTIAL_RETURN -> true | _ -> false)

let is_lcomp_partial_return c = c.cflags |> Util.for_some (function RETURN | PARTIAL_RETURN -> true | _ -> false)

let is_tot_or_gtot_comp c =
    is_total_comp c
    || lid_equals Const.effect_GTot_lid (comp_effect_name c)

let is_pure_comp c = match c.n with
    | Total _ -> true
    | Comp ct -> is_tot_or_gtot_comp c
                 || lid_equals ct.effect_name Const.effect_PURE_lid
                 || lid_equals ct.effect_name Const.effect_Pure_lid
                 || ct.flags |> Util.for_some (function LEMMA -> true | _ -> false)

let is_ghost_effect l =
     lid_equals Const.effect_GTot_lid l
    || lid_equals Const.effect_GHOST_lid l
    || lid_equals Const.effect_Ghost_lid l

let is_pure_or_ghost_comp c = is_pure_comp c || is_ghost_effect (comp_effect_name c)

let is_pure_lcomp lc =
    is_total_lcomp lc
    || lid_equals lc.eff_name Const.effect_PURE_lid
    || lid_equals lc.eff_name Const.effect_Pure_lid
    || lc.cflags |> Util.for_some (function LEMMA -> true | _ -> false)

let is_pure_or_ghost_lcomp lc =
    is_pure_lcomp lc || is_ghost_effect lc.eff_name

let is_pure_or_ghost_function t = match (compress t).n with
    | Tm_arrow(_, c) -> is_pure_or_ghost_comp c
    | _ -> true

let is_lemma t =  match (compress t).n with
    | Tm_arrow(_, c) -> 
      begin match c.n with
        | Comp ct -> lid_equals ct.effect_name Const.effect_Lemma_lid
        | _ -> false
      end
    | _ -> false

let is_smt_lemma t = match (compress t).n with
    | Tm_arrow(_, c) -> 
      begin match c.n with
        | Comp ct when (lid_equals ct.effect_name Const.effect_Lemma_lid) ->
            begin match ct.effect_args with
                | _req::_ens::(pats, _)::_ ->
                  begin match (unmeta pats).n with
                    | Tm_app({n=Tm_fvar(fv, _)}, _) -> lid_equals fv.v Const.cons_lid
                    | _ -> false
                  end
                | _ -> false
            end
        | _ -> false
      end
    | _ -> false

let is_ml_comp c = match c.n with
  | Comp c -> lid_equals c.effect_name Const.effect_ML_lid
              || c.flags |> Util.for_some (function MLEFFECT -> true | _ -> false)

  | _ -> false

let comp_result c = match c.n with
  | Total t -> t
  | Comp ct -> ct.result_typ

let set_result_typ c t = match c.n with
  | Total _ -> mk_Total t
  | Comp ct -> mk_Comp({ct with result_typ=t})

let is_trivial_wp c =
  comp_flags c |> Util.for_some (function TOTAL | RETURN -> true | _ -> false)

(********************************************************************************)
(****************Simple utils on the local structure of a term ******************)
(********************************************************************************)
let primops =
  [Const.op_Eq;
   Const.op_notEq;
   Const.op_LT;
   Const.op_LTE;
   Const.op_GT;
   Const.op_GTE;
   Const.op_Subtraction;
   Const.op_Minus;
   Const.op_Addition;
   Const.op_Multiply;
   Const.op_Division;
   Const.op_Modulus;
   Const.op_And;
   Const.op_Or;
   Const.op_Negation;]

let is_primop f = match f.n with
  | Tm_fvar(fv,_) -> primops |> Util.for_some (lid_equals fv.v)
  | _ -> false

let rec unascribe e = match e.n with
  | Tm_ascribed (e, _, _) -> unascribe e
  | _ -> e

let rec ascribe t k = match t.n with
  | Tm_ascribed (t', _, _) -> ascribe t' k
  | _ -> mk (Tm_ascribed(t, k, None)) None t.pos

let rec unrefine t =
  let t = compress t in
  match t.n with
      | Tm_refine(x, _) -> unrefine x.sort
      | Tm_ascribed(t, _, _) -> unrefine t
      | _ -> t

let is_fun e = match (compress e).n with
  | Tm_abs _ -> true
  | _ -> false

let is_function_typ t = match (compress t).n with
  | Tm_arrow _ -> true
  | _ -> false

let rec pre_typ t =
    let t = compress t in
    match t.n with
      | Tm_refine(x, _) -> pre_typ x.sort
      | Tm_ascribed(t, _, _) -> pre_typ t
      | _ -> t

let destruct typ lid =
  let typ = compress typ in
  match typ.n with
    | Tm_app({n=Tm_fvar(tc, _)}, args) when lid_equals tc.v lid -> Some args
    | Tm_fvar (tc, _) when lid_equals tc.v lid -> Some []
    | _ -> None

let rec lids_of_sigelt se = match se with
  | Sig_let(_, _, lids, _)
  | Sig_bundle(_, _, lids, _) -> lids
  | Sig_tycon (lid, _, _,  _, _, _, _, _)
  | Sig_effect_abbrev(lid, _, _,  _, _)
  | Sig_datacon (lid, _, _, _, _, _, _)
  | Sig_val_decl (lid, _, _, _, _)
  | Sig_assume (lid, _, _, _) -> [lid]
  | Sig_new_effect(n, _) -> [n.mname]
  | Sig_sub_effect _
  | Sig_pragma _
  | Sig_main _ -> []

let lid_of_sigelt se : option<lident> = match lids_of_sigelt se with
  | [l] -> Some l
  | _ -> None

let range_of_sigelt x = match x with
  | Sig_bundle(_, _, _, r)
  | Sig_tycon (_, _, _,  _, _, _, _, r)
  | Sig_effect_abbrev  (_, _, _, _, r)
  | Sig_datacon (_, _, _, _, _, _, r)
  | Sig_val_decl (_, _, _, _, r)
  | Sig_assume (_, _, _, r)
  | Sig_let(_, r, _, _)
  | Sig_main(_, r)
  | Sig_pragma(_, r)
  | Sig_new_effect(_, r)
  | Sig_sub_effect(_, r) -> r

let range_of_lb = function
  | (Inl x, _, _) -> range_of_bv  x
  | (Inr l, _, _) -> range_of_lid l

let range_of_arg (hd, _) = hd.pos

let range_of_args args r =
   args |> List.fold_left (fun r a -> Range.union_ranges r (range_of_arg a)) r

let mk_app f args =
  let r = range_of_args args f.pos in
  mk (Tm_app(f, args)) None r

let mk_data l args =
  match args with
    | [] ->
      mk (Tm_meta(fvar (Some Data_ctor) l (range_of_lid l), Meta_desugared Data_app)) None (range_of_lid l)
    | _ ->
      let e = mk_app (fvar (Some Data_ctor) l (range_of_lid l)) args in
      mk (Tm_meta(e, Meta_desugared Data_app)) None e.pos

let mangle_field_name x = mk_ident("^fname^" ^ x.idText, x.idRange)
let unmangle_field_name x =
    if Util.starts_with x.idText "^fname^"
    then mk_ident(Util.substring_from x.idText 7, x.idRange)
    else x

let mk_field_projector_name lid (x:bv) i =
    let nm = if Syntax.is_null_bv x
             then mk_ident("_" ^ Util.string_of_int i, Syntax.range_of_bv x)
             else x.ppname in
    let y = {x with ppname=nm} in
    lid_of_ids (ids_of_lid lid @ [unmangle_field_name nm]), y

let unchecked_unify uv t =
  match Unionfind.find uv with
    | Fixed _ -> failwith (Util.format1 "Changing a fixed uvar! U%s\n" (Util.string_of_int <| Unionfind.uvar_id uv))
    | _ -> Unionfind.change uv (Fixed t) (* used to be an alpha-convert t here; but we now have an invariant that t is closed *)




(***********************************************************************************************)
(* closing types and terms *)
(***********************************************************************************************)
let rec arrow_formals k =
    let k = Subst.compress k in
    match k.n with
        | Tm_arrow(bs, c) ->
            let bs, c = Subst.open_comp bs c in
            if is_tot_or_gtot_comp c
            then let bs', k = arrow_formals (comp_result c) in
                 bs@bs', k
            else bs, comp_result c
        | _ -> [], k

let abs bs t = match bs with 
    | [] -> t
    | _ -> mk (Tm_abs(close_binders bs, Subst.close bs t)) None t.pos
let arrow bs c = mk (Tm_arrow(close_binders bs, Subst.close_comp bs c)) None c.pos
let refine b t = mk (Tm_refine(b, Subst.close [mk_binder b] t)) None (Range.union_ranges (range_of_bv b) t.pos)
let branch (p, wopt, e) =
    let bs = Syntax.pat_bvs p |> List.map mk_binder in 
    let wopt = match wopt with 
        | None -> None
        | Some e -> Some (Subst.close bs e) in
    let e = Subst.close bs e in 
    (p, wopt, e)

(********************************************************************************)
(*********************** Various tests on constants  ****************************)
(********************************************************************************)
let is_tuple_constructor (t:typ) = match t.n with
  | Tm_fvar (l, _) -> Util.starts_with l.v.str "Prims.Tuple"
  | _ -> false

let mk_tuple_lid n r =
  let t = Util.format1 "Tuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let mk_tuple_data_lid n r =
  let t = Util.format1 "MkTuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let is_tuple_data_lid f n =
  lid_equals f (mk_tuple_data_lid n dummyRange)

let is_dtuple_constructor (t:typ) = match t.n with
  | Tm_fvar (l, _) -> Util.starts_with l.v.str "Prims.DTuple"
  | _ -> false

let mk_dtuple_lid n r =
  let t = Util.format1 "DTuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let mk_dtuple_data_lid n r =
  let t = Util.format1 "MkDTuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let is_lid_equality x =
    lid_equals x Const.eq_lid  ||
    lid_equals x Const.eq2_lid ||
    lid_equals x Const.eqT_lid

let is_forall lid = lid_equals lid Const.forall_lid || lid_equals lid Const.allTyp_lid
let is_exists lid = lid_equals lid Const.exists_lid || lid_equals lid Const.exTyp_lid
let is_qlid lid   = is_forall lid || is_exists lid
let is_equality x = is_lid_equality x.v

let lid_is_connective =
  let lst = [Const.and_lid; Const.or_lid; Const.not_lid;
             Const.iff_lid; Const.imp_lid] in
  fun lid -> Util.for_some (lid_equals lid) lst

let is_constructor t lid =
  match (pre_typ t).n with
    | Tm_fvar (tc, _) -> lid_equals tc.v lid
    | _ -> false

let rec is_constructed_typ t lid = match (pre_typ t).n with
  | Tm_fvar _ -> is_constructor t lid
  | Tm_app(t, _) -> is_constructed_typ t lid
  | _ -> false

let rec get_tycon t =
  let t = pre_typ t in
  match t.n with
  | Tm_bvar _
  | Tm_name _
  | Tm_fvar _  -> Some t
  | Tm_app(t, _) -> get_tycon t
  | _ -> None

let sortByFieldName (fn_a_l:list<(fieldname * 'a)>) =
  fn_a_l |> List.sortWith
      (fun (fn1, _) (fn2, _) ->
        String.compare
          (text_of_lid fn1)
          (text_of_lid fn2))

let is_interpreted l =
  let theory_syms =
    [Const.op_Eq          ;
     Const.op_notEq       ;
     Const.op_LT          ;
     Const.op_LTE         ;
     Const.op_GT          ;
     Const.op_GTE         ;
     Const.op_Subtraction ;
     Const.op_Minus       ;
     Const.op_Addition    ;
     Const.op_Multiply    ;
     Const.op_Division    ;
     Const.op_Modulus     ;
     Const.op_And         ;
     Const.op_Or          ;
     Const.op_Negation] in
  Util.for_some (lid_equals l) theory_syms

(********************************************************************************)
(*********************** Constructors of common terms  **************************)
(********************************************************************************)

let ktype0 = mk (Tm_type(U_zero)) None dummyRange

let kt_kt = Const.kunary ktype0 ktype0
let kt_kt_kt = Const.kbin ktype0 ktype0 ktype0

let tand    = fvar None Const.and_lid dummyRange
let tor     = fvar None Const.or_lid dummyRange
let timp    = fvar None Const.imp_lid dummyRange
let tiff    = fvar None Const.iff_lid dummyRange
let t_bool :term = fvar None Const.bool_lid dummyRange
let t_false = fvar None Const.false_lid dummyRange
let t_true  = fvar None Const.true_lid dummyRange
let b2t_v   = fvar None Const.b2t_lid dummyRange
let t_not   = fvar None Const.not_lid dummyRange

let mk_conj_opt phi1 phi2 = match phi1 with
  | None -> Some phi2
  | Some phi1 -> Some (mk (Tm_app(tand, [arg phi1; arg phi2])) None (Range.union_ranges phi1.pos phi2.pos))
let mk_binop op_t phi1 phi2 = mk (Tm_app(op_t, [arg phi1; arg phi2])) None (Range.union_ranges phi1.pos phi2.pos)
let mk_neg phi = mk (Tm_app(t_not, [arg phi])) None phi.pos
let mk_conj phi1 phi2 = mk_binop tand phi1 phi2
let mk_conj_l phi = match phi with
    | [] -> fvar None Const.true_lid dummyRange
    | hd::tl -> List.fold_right mk_conj tl hd
let mk_disj phi1 phi2 = mk_binop tor phi1 phi2
let mk_disj_l phi = match phi with
    | [] -> t_false
    | hd::tl -> List.fold_right mk_disj tl hd
let mk_imp phi1 phi2  =
    match (compress phi1).n with
        | Tm_fvar (tc, _) when (lid_equals tc.v Const.false_lid) -> t_true
        | Tm_fvar (tc, _) when (lid_equals tc.v Const.true_lid) -> phi2
        | _ ->
            begin match (compress phi2).n with
                | Tm_fvar(tc, _) when (lid_equals tc.v Const.true_lid
                                    || lid_equals tc.v Const.false_lid) -> phi2
                | _ -> mk_binop timp phi1 phi2
            end
let mk_iff phi1 phi2  = mk_binop tiff phi1 phi2
let b2t e = mk (Tm_app(b2t_v, [arg e])) None e.pos//implicitly coerce a boolean to a type

let eq_pred_t : term =
    let a = new_bv None ktype0 in
    let atyp = bv_to_tm a in
    let b = new_bv None ktype0 in
    let btyp = bv_to_tm b in
    arrow [(a, Some Implicit); (b, Some Implicit); null_binder atyp; null_binder btyp]
          (mk_Total ktype0)

let teq = fvar None Const.eq2_lid dummyRange

let mk_eq t1 t2 e1 e2 = mk (Tm_app(teq, [arg e1; arg e2])) None (Range.union_ranges e1.pos e2.pos)
let eq_typ = fvar None Const.eqT_lid dummyRange
let mk_eq_typ t1 t2 = mk (Tm_app(eq_typ, [arg t1; arg t2])) None (Range.union_ranges t1.pos t2.pos)

let lex_t :term = fvar None Const.lex_t_lid dummyRange
let lex_top : term = fvar (Some Data_ctor) Const.lextop_lid dummyRange
let lex_pair : term = fvar (Some Data_ctor) Const.lexcons_lid dummyRange
let forall_t : term = 
    let a = new_bv None ktype0 in
    let atyp = bv_to_tm a in
    arrow [(a, Some Implicit); null_binder atyp] (mk_Total ktype0)
let tforall = fvar None Const.forall_lid dummyRange

let mk_forall (x:bv) (body:typ) : typ =
  mk (Tm_app(tforall, [arg (abs [mk_binder x] body)])) None dummyRange

let rec close_forall bs f =
  List.fold_right (fun b f -> if Syntax.is_null_binder b then f else mk_forall (fst b) f) bs f

let rec is_wild_pat p =
    match p.v with
    | Pat_wild _ -> true
    | _ -> false

let head_and_args t =
    let t = compress t in
    match t.n with
        | Tm_app(head, args) -> head, args
        | _ -> t, []
        
let if_then_else b t1 t2 =
    let then_branch = (withinfo (Pat_constant (Const_bool true)) tun.n t1.pos, None, t1) in
    let else_branch = (withinfo (Pat_constant (Const_bool false)) tun.n t2.pos, None, t2) in
    mk (Tm_match(b, [then_branch; else_branch])) None (Range.union_ranges b.pos (Range.union_ranges t1.pos t2.pos))

(**************************************************************************************)
(* Destructing a type as a formula *)
(**************************************************************************************)
type qpats = list<args>
type connective =
    | QAll of binders * qpats * typ
    | QEx of binders * qpats * typ
    | BaseConn of lident * args

let destruct_typ_as_formula f : option<connective> =
    let destruct_base_conn f =
        let connectives = [ (Const.true_lid,  0);
                            (Const.false_lid, 0);
                            (Const.and_lid,   2);
                            (Const.or_lid,    2);
                            (Const.imp_lid, 2);
                            (Const.iff_lid, 2);
                            (Const.ite_lid, 3);
                            (Const.not_lid, 1);
                            (Const.eqT_lid, 2);
                            (Const.eq2_lid, 2);
                            (Const.eq2_lid, 4);
                        ] in
        let rec aux f (lid, arity) =
            let t, args = head_and_args f in
            if is_constructor t lid
                && List.length args = arity
            then Some (BaseConn(lid, args))
            else None in
        Util.find_map connectives (aux f) in

    let patterns t =
        let t = compress t in
        match t.n with
            | Tm_meta(t, Meta_pattern pats) -> pats, compress t
            | _ -> [], compress t in

    let destruct_q_conn t =
        let is_q : bool -> lident -> Tot<bool> = fun fa l -> if fa then is_forall l else is_exists l in
        let flat t =
            let t, args = head_and_args t in
            t, args |> List.map (fun (t, imp) -> compress t, imp) in
        let rec aux qopt out t = match qopt, flat t with
            | Some fa, ({n=Tm_fvar (tc, _)}, [{n=Tm_abs([b], t2)}, _])
            | Some fa, ({n=Tm_fvar (tc, _)}, [_; ({n=Tm_abs([b], t2)}, _)])
                when (is_q fa tc.v) ->
              aux qopt (b::out) t2

            | None, ({n=Tm_fvar(tc, _)}, [({n=Tm_abs([b], t2)}, _)])
            | None, ({n=Tm_fvar(tc, _)}, [_; ({n=Tm_abs([b], t2)}, _)])
                when (is_qlid tc.v) ->
              aux (Some (is_forall tc.v)) (b::out) t2

            | Some true, _ ->
              let pats, body = patterns t in
              Some (QAll(List.rev out, pats, body))

            | Some false, _ ->
              let pats, body = patterns t in
              Some(QEx(List.rev out, pats, body))

            | _ -> None in
        aux None [] t in

    let phi = compress f in
        match destruct_base_conn phi with
        | Some b -> Some b
        | None -> destruct_q_conn phi

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
open FStar.Syntax
open FStar.Syntax.Syntax

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
type gensym_t = {
    gensym: unit -> string;
    reset:unit -> unit;
}
let gs =
  let ctr = mk_ref 0 in
  let n_resets = mk_ref 0 in
  {gensym =(fun () -> "_" ^ (Util.string_of_int !n_resets) ^ "_" ^ (Util.string_of_int (incr ctr; !ctr)));
   reset = (fun () -> ctr := 0; incr n_resets)}
let gensym () = gs.gensym()
let reset_gensym() = gs.reset()
let rec gensyms x = match x with
  | 0 -> []
  | n -> gensym ()::gensyms (n-1)

let genident : option<Range.range> -> ident = fun r ->
  let sym = gensym () in
  match r with
    | None -> mk_ident(sym, dummyRange)
    | Some r -> mk_ident(sym, r)

let mkbv x y t  = {ppname=x;index=y;sort=t}
let setsort w t = {v=w.v; sort=t; p=w.p}
let withinfo e s r = {v=e; sort=s; p=r}
let withsort e s   = withinfo e s dummyRange
let lbname_eq l1 l2 = match l1, l2 with
  | Inl x, Inl y -> bv_eq x y
  | Inr l, Inr m -> lid_equals l m
  | _ -> false
let fvar_eq fv1 fv2  = lid_equals fv1.v fv2.v
let new_bv ropt t = mkbv (genident ropt) 0 t
let bvd_of_str s = mkbv (id_of_text s) 0 
let set_bv_range bv r = {bv with ppname=mk_ident(bv.ppname.idText, r)}
let set_lid_range l r =
  let ids = (l.ns@[l.ident]) |> List.map (fun i -> mk_ident(i.idText, r)) in
  lid_of_ids ids
let fv l dc = withinfo l tun (range_of_lid l), dc
let fvar dc l r = mk (Tm_fvar(fv (set_lid_range l r) dc)) None r

let mk_discriminator lid =
  lid_of_ids (lid.ns@[Syntax.mk_ident("is_" ^ lid.ident.idText, lid.ident.idRange)])

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
                 let b = mkbv b 0 a.sort in
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
        | Tm_meta(e, Meta_desugared _) 
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
  | Sig_tycon (lid, _, _,  _, _, _, _)
  | Sig_effect_abbrev(lid, _, _,  _, _)
  | Sig_datacon (lid, _, _, _, _, _)
  | Sig_val_decl (lid, _, _, _)
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
  | Sig_tycon (_, _, _,  _, _, _, r)
  | Sig_effect_abbrev  (_, _, _, _, r)
  | Sig_datacon (_, _, _, _, _, r)
  | Sig_val_decl (_, _, _, r)
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
             then Syntax.mk_ident("_" ^ Util.string_of_int i, range_of_bv x)
             else x.ppname in
    let y = {x with ppname=nm} in
    lid_of_ids (ids_of_lid lid @ [unmangle_field_name nm]), y

let unchecked_unify uv t =
  match Unionfind.find uv with
    | Fixed _ -> failwith (Util.format1 "Changing a fixed uvar! U%s\n" (Util.string_of_int <| Unionfind.uvar_id uv))
    | _ -> Unionfind.change uv (Fixed t) (* used to be an alpha-convert t here; but we now have an invariant that t is closed *)


(********************************************************************************)
(************************* Free names and unif variables ************************)
(********************************************************************************)
let singleton_bv x = Util.set_add x (new_bv_set())
let singleton_uv x = Util.set_add x (new_uv_set())
let union_nm_uv (x1, y1) (x2, y2) = Util.set_union x1 x2, Util.set_union y1 y2
let rec free_names_and_uvars' tm =
    let aux_binders bs acc = 
        bs |> List.fold_left (fun n (x, _) -> union_nm_uv n (free_names_and_uvars x.sort)) acc in
    let t = Subst.compress tm in 
    match t.n with
      | Tm_delayed _ -> failwith "Impossible"

      | Tm_name x ->
        singleton_bv x, no_uvs

      | Tm_uvar (x, _) -> 
        no_names, singleton_uv x

      | Tm_bvar _
      | Tm_name _
      | Tm_fvar _ 
      | Tm_constant _
      | Tm_type _ 
      | Tm_unknown -> 
        no_names, no_uvs
        
      | Tm_uinst(t, _) -> 
        free_names_and_uvars t

      | Tm_abs(bs, t) -> 
        aux_binders bs (free_names_and_uvars t)

      | Tm_arrow (bs, c) -> 
        aux_binders bs (free_names_and_uvars_comp c)

      | Tm_refine(bv, t) -> 
        aux_binders [bv, None] (free_names_and_uvars t)
      
      | Tm_app(t, args) -> 
        free_names_and_uvars_args args (free_names_and_uvars t)

      | Tm_match(t, pats) -> 
        pats |> List.fold_left (fun n (p, wopt, t) -> 
            let n1 = match wopt with 
                | None -> no_names, no_uvs 
                | Some w -> free_names_and_uvars w in 
            let n2 = free_names_and_uvars t in
            let n = union_nm_uv n1 (union_nm_uv n2 n) in
            pat_bvs p |> List.fold_left (fun n x -> union_nm_uv n (free_names_and_uvars x.sort)) n)
            (free_names_and_uvars t)
      
      | Tm_ascribed(t1, t2, _) -> 
        union_nm_uv (free_names_and_uvars t1) (free_names_and_uvars t2)

      | Tm_let(lbs, t) -> 
        snd lbs |> List.fold_left (fun n lb -> 
          union_nm_uv n (union_nm_uv (free_names_and_uvars lb.lbtyp) (free_names_and_uvars lb.lbdef)))
          (free_names_and_uvars t)
          
      | Tm_meta(t, Meta_pattern args) -> 
        free_names_and_uvars_args args (free_names_and_uvars t)

      | Tm_meta(t, _) -> 
        free_names_and_uvars t

and free_names_and_uvars t = 
    let t = Subst.compress t in 
    match !t.vars with 
        | Some n -> n 
        | _ -> 
        let n = free_names_and_uvars' t in
        t.vars := Some n;
        n

and free_names_and_uvars_args args acc = 
        args |> List.fold_left (fun n (x, _) -> union_nm_uv n (free_names_and_uvars x)) acc
             
and free_names_and_uvars_comp c = 
    match !c.vars with 
        | Some n -> n
        | _ -> 
         let n = match c.n with 
            | Total t -> 
              free_names_and_uvars t
            | Comp ct -> 
              free_names_and_uvars_args ct.effect_args (free_names_and_uvars ct.result_typ) in
         c.vars := Some n;
         n
         
let freenames t = fst (free_names_and_uvars t)
let uvars t = snd (free_names_and_uvars t)

(***********************************************************************************************)
(* closing types and terms *)
(***********************************************************************************************)
let rec arrow_formals k =
    let k = Subst.compress k in
    match k.n with
        | Tm_arrow(bs, c) ->
            if is_tot_or_gtot_comp c
            then let bs', k = arrow_formals (comp_result c) in
                 bs@bs', k
            else bs, comp_result c
        | _ -> [], k

let abs bs t = mk (Tm_abs(bs, Subst.close bs t)) None t.pos
let arrow bs c = mk (Tm_arrow(bs, Subst.close_comp bs c)) None c.pos


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
  Syntax.lid_equals f (mk_tuple_data_lid n Syntax.dummyRange)

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

let ktype0 = mk (Tm_type(U_zero)) None dummyRange

let kt_kt = Const.kunary ktype0 ktype0
let kt_kt_kt = Const.kbin ktype0 ktype0 ktype0

let tand    = fvar None Const.and_lid dummyRange
let tor     = fvar None Const.or_lid dummyRange
let timp    = fvar None Const.imp_lid dummyRange
let tiff    = fvar None Const.iff_lid dummyRange
let t_bool  = fvar None Const.bool_lid dummyRange
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

let rec unmeta t =
    let t = compress t in
    match t.n with
        | Tm_ascribed(t, _, _)
        | Tm_meta(t, _) -> unmeta t
        | _ -> t


let eq_k =
    let a = bvd_to_bvar_s (new_bvd None) ktype in
    let atyp = btvar_to_typ a in
    let b = bvd_to_bvar_s (new_bvd None) ktype in
    let btyp = btvar_to_typ b in
    mk_Kind_arrow([(Inl a, Some Implicit); (Inl b, Some Implicit); null_v_binder atyp; null_v_binder btyp],
                  ktype) dummyRange

let teq = ftv Const.eq2_lid eq_k
let mk_eq t1 t2 e1 e2 = match t1.n, t2.n with
    | Typ_unknown, _
    | _, Typ_unknown -> failwith "DIE! mk_eq with tun"
    | _ -> mk_Typ_app(teq, [itarg t1; itarg t2; varg e1; varg e2]) None (Range.union_ranges e1.pos e2.pos)
let eq_typ = ftv Const.eqT_lid kun
let mk_eq_typ t1 t2 = mk_Typ_app(eq_typ, [targ t1; targ t2]) None (Range.union_ranges t1.pos t2.pos)

let lex_t = ftv Const.lex_t_lid ktype
let lex_top =
    let lexnil = withinfo Const.lextop_lid lex_t dummyRange in
    mk_Exp_fvar(lexnil, Some Data_ctor) None dummyRange
    g
let lex_pair =
    let a = gen_bvar ktype in
    let lexcons = withinfo Const.lexcons_lid (mk_Typ_fun([t_binder a; null_v_binder (btvar_to_typ a); null_v_binder lex_t], mk_Total lex_t) None dummyRange) dummyRange in
    mk_Exp_fvar(lexcons, Some Data_ctor) None dummyRange

let forall_kind =
  let a = bvd_to_bvar_s (new_bvd None) ktype in
  let atyp = btvar_to_typ a in
  mk_Kind_arrow([(Inl a, Some Implicit);
                 null_t_binder <| mk_Kind_arrow([null_v_binder atyp], ktype) dummyRange],
                ktype)
                dummyRange
let tforall = ftv Const.forall_lid forall_kind

let allT_k k = mk_Kind_arrow([null_t_binder <| mk_Kind_arrow([null_t_binder k], ktype) dummyRange], ktype) dummyRange
let eqT_k k = mk_Kind_arrow([null_t_binder <| k; null_t_binder k], ktype) dummyRange

let tforall_typ k = ftv Const.allTyp_lid (allT_k k)

let mk_forallT a b =
  mk_Typ_app(tforall_typ a.sort, [targ <| mk_Typ_lam([t_binder a], b) None b.pos]) None b.pos

let mk_forall (x:bvvar) (body:typ) : typ =
  let r = dummyRange in
  mk_Typ_app(tforall, [(targ <| mk_Typ_lam([v_binder x], body) None r)]) None r

let rec close_forall bs f =
  List.fold_right (fun b f ->
    if Syntax.is_null_binder b
    then f
    else let body = mk_Typ_lam([b], f) None f.pos in
         match fst b with
           | Inl a -> mk_Typ_app(tforall_typ a.sort, [targ body]) None f.pos
           | Inr x -> mk_Typ_app(tforall, [(Inl x.sort, Some Implicit); targ body]) None f.pos) bs f

let rec is_wild_pat p =
    match p.v with
    | Pat_wild _ -> true
    | _ -> false

let head_and_args t =
    let t = compress_typ t in
    match t.n with
        | Typ_app(head, args) -> head, args
        | _ -> t, []

let head_and_args_e e =
    let e = compress_exp e in
    match e.n with
        | Exp_app(head, args) -> head, args
        | _ -> e, []

let function_formals t =
    let t = compress_typ t in
    match t.n with
        | Typ_fun(bs, c) -> Some (bs, c)
        | _ -> None

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
        let type_sort, term_sort = true, false in
        let oneType    = [type_sort] in
        let twoTypes   = [type_sort;type_sort] in
        let threeTys   = [type_sort;type_sort;type_sort] in
        let twoTerms   = [term_sort;term_sort] in
        let connectives = [ (Const.true_lid, []);
                            (Const.false_lid, []);
                            (Const.and_lid, twoTypes);
                            (Const.or_lid,  twoTypes);
                            (Const.imp_lid, twoTypes);
                            (Const.iff_lid, twoTypes);
                            (Const.ite_lid, threeTys);
                            (Const.not_lid, oneType);
                            (Const.eqT_lid, twoTypes);
                            (Const.eq2_lid, twoTerms);
                            (Const.eq2_lid, twoTypes@twoTerms);
                        ] in
        let rec aux f (lid, arity) =
            let t, args = head_and_args f in
            if is_constructor t lid
                && List.length args = List.length arity
                && List.forall2 (fun arg flag -> match arg with
                | Inl _, _ -> flag=type_sort
                | Inr _, _ -> flag=term_sort) args arity
            then Some (BaseConn(lid, args))
            else None in
        Util.find_map connectives (aux f) in

    let patterns t =
        let t = compress_typ t in
        match t.n with
            | Typ_meta(Meta_pattern(t, pats)) -> pats, compress_typ t
            | _ -> [], compress_typ t in

    let destruct_q_conn t =
        let is_q : bool -> lident -> Tot<bool> = fun fa l -> if fa then is_forall l else is_exists l in
        let flat t =
            let t, args = head_and_args t in
            t, args |> List.map (function (Inl t, imp) -> Inl (compress_typ t), imp
                                        | (Inr e, imp) -> Inr (compress_exp e), imp) in
        let rec aux qopt out t = match qopt, flat t with
            | Some fa, ({n=Typ_const tc}, [(Inl {n=Typ_lam([b], t2)}, _)])
            | Some fa, ({n=Typ_const tc}, [_; (Inl {n=Typ_lam([b], t2)}, _)])
                when (is_q fa tc.v) ->
              aux qopt (b::out) t2

            | None, ({n=Typ_const tc}, [(Inl {n=Typ_lam([b], t2)}, _)])
            | None, ({n=Typ_const tc}, [_; (Inl {n=Typ_lam([b], t2)}, _)])
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

    let phi = compress_typ f in
        match destruct_base_conn phi with
        | Some b -> Some b
        | None -> destruct_q_conn phi

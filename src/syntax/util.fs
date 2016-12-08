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

(********************************************************************************)
(**************************Utilities for identifiers ****************************)
(********************************************************************************)

let qual_id lid id = set_lid_range (lid_of_ids (lid.ns @ [lid.ident;id])) id.idRange

let mk_discriminator lid =
  lid_of_ids (lid.ns@[mk_ident(Ident.reserved_prefix ^ "is_" ^ lid.ident.idText, lid.ident.idRange)])

let is_name (lid:lident) =
  let c = Util.char_at lid.ident.idText 0 in
  Util.is_upper c

let arg_of_non_null_binder (b, imp) = (bv_to_name b, imp)

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

let subst_of_list (formals:binders) (actuals:args) : subst_t =
    if (List.length formals = List.length actuals)
    then List.fold_right2 (fun f a out -> NT(fst f, fst a)::out) formals actuals []
    else failwith "Ill-formed substitution"

let rename_binders (replace_xs:binders) (with_ys:binders) : subst_t =
    if List.length replace_xs = List.length with_ys
    then List.map2 (fun (x, _) (y, _) -> NT(x, bv_to_name y)) replace_xs with_ys
    else failwith "Ill-formed substitution"

open FStar.Syntax.Subst

let rec unmeta e =
    let e = compress e in
    match e.n with
        | Tm_meta(e, _)
        | Tm_ascribed(e, _, _) -> unmeta e
        | _ -> e

(********************************************************************************)
(*************************** Utilities for universes ****************************)
(********************************************************************************)
(* kernel u = (k_u, n)
        where u is of the form S^n k_u
        i.e., k_u is the "kernel" and n is the offset *)
let rec univ_kernel u = match u with
    | U_unknown
    | U_name _
    | U_unif _
    | U_zero -> u, 0
    | U_succ u -> let k, n = univ_kernel u in k, n+1
    | U_max _  -> failwith "Imposible: univ_kernel (U_max _)"
    | U_bvar _ -> failwith "Imposible: univ_kernel (U_bvar _)"

//requires: kernel u = U_zero, n
//returns: n
let constant_univ_as_nat u = snd (univ_kernel u)

//ordering on universes:
//    constants come first, in order of their size
//    named universes come next, in lexical order of their kernels and their offsets
//    unification variables next, in lexical order of their kernels and their offsets
//    max terms come last
//e.g, [Z; S Z; S S Z; u1; S u1; u2; S u2; S S u2; ?v1; S ?v1; ?v2]
let rec compare_univs u1 u2 = match u1, u2 with
    | U_bvar _, _
    | _, U_bvar _  -> failwith "Impossible: compare_univs"

    | U_unknown, U_unknown -> 0
    | U_unknown, _ -> -1
    | _, U_unknown -> 1

    | U_zero, U_zero -> 0
    | U_zero, _ -> -1
    | _, U_zero -> 1

    | U_name u1 , U_name u2 -> String.compare u1.idText u2.idText
    | U_name _, U_unif _ -> -1
    | U_unif _, U_name _ -> 1

    | U_unif u1, U_unif u2 -> Unionfind.uvar_id u1 - Unionfind.uvar_id u2

    | U_max us1, U_max us2 ->
      let n1 = List.length us1 in
      let n2 = List.length us2 in
      if n1 <> n2
      then n1 - n2
      else let copt = Util.find_map (List.zip us1 us2) (fun (u1, u2) ->
                let c = compare_univs u1 u2 in
                if c<>0 then Some c
                else None) in
           begin match copt with
            | None -> 0
            | Some c -> c
           end

    | U_max _, _ -> -1

    | _, U_max _ -> 1

    | _ ->
        let k1, n1 = univ_kernel u1 in
        let k2, n2 = univ_kernel u2 in
        let r = compare_univs k1 k2 in
        if r=0
        then n1 - n2
        else r

let eq_univs u1 u2 = compare_univs u1 u2 = 0

(********************************************************************************)
(*********************** Utilities for computation types ************************)
(********************************************************************************)

let ml_comp t r =
  mk_Comp ({comp_univs=[U_unknown];
            effect_name=set_lid_range Const.effect_ML_lid r;
            result_typ=t;
            effect_args=[];
            flags=[MLEFFECT]})

let comp_effect_name c = match c.n with
    | Comp c  -> c.effect_name
    | Total _ -> Const.effect_Tot_lid
    | GTotal _ -> Const.effect_GTot_lid

let comp_flags c = match c.n with
    | Total _ -> [TOTAL]
    | GTotal _ -> [SOMETRIVIAL]
    | Comp ct -> ct.flags

let comp_set_flags (c:comp) f =
    (* Duplicate of the function below not failing when universe is not provided *)
    let comp_to_comp_typ (c:comp) : comp_typ =
        match c.n with
            | Comp c -> c
            | Total (t, u_opt)
            | GTotal(t, u_opt) ->
                {comp_univs=dflt [] (map_opt u_opt (fun x -> [x]));
                 effect_name=comp_effect_name c;
                 result_typ=t;
                 effect_args=[];
                 flags=comp_flags c}
    in
    {c with n=Comp ({comp_to_comp_typ c with flags=f})}

let comp_to_comp_typ (c:comp) : comp_typ =
    match c.n with
    | Comp c -> c
    | Total (t, Some u)
    | GTotal(t, Some u) ->
      {comp_univs=[u];
       effect_name=comp_effect_name c;
       result_typ=t;
       effect_args=[];
       flags=comp_flags c}
    | _ -> failwith "Assertion failed: Computation type without universe"

let is_named_tot c =
    match c.n with
        | Comp c -> lid_equals c.effect_name Const.effect_Tot_lid
        | Total _ -> true
        | GTotal _ -> false

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

let is_pure_effect l =
     lid_equals l Const.effect_Tot_lid
     || lid_equals l Const.effect_PURE_lid
     || lid_equals l Const.effect_Pure_lid

let is_pure_comp c = match c.n with
    | Total _ -> true
    | GTotal _ -> false
    | Comp ct -> is_total_comp c
                 || is_pure_effect ct.effect_name
                 || ct.flags |> Util.for_some (function LEMMA -> true | _ -> false)

let is_ghost_effect l =
       lid_equals Const.effect_GTot_lid l
    || lid_equals Const.effect_GHOST_lid l
    || lid_equals Const.effect_Ghost_lid l

let is_pure_or_ghost_comp c = is_pure_comp c || is_ghost_effect (comp_effect_name c)

let is_pure_lcomp lc =
    is_total_lcomp lc
    || is_pure_effect lc.eff_name
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


let head_and_args t =
    let t = compress t in
    match t.n with
        | Tm_app(head, args) -> head, args
        | _ -> t, []

 let un_uinst t =
    let t = Subst.compress t in
    match t.n with
        | Tm_uinst(t, _) -> Subst.compress t
        | _ -> t

let is_smt_lemma t = match (compress t).n with
    | Tm_arrow(_, c) ->
      begin match c.n with
        | Comp ct when lid_equals ct.effect_name Const.effect_Lemma_lid ->
            begin match ct.effect_args with
                | _req::_ens::(pats, _)::_ ->
                  let pats' = unmeta pats in
                  let head, _ = head_and_args pats' in
                  begin match (un_uinst head).n with
                    | Tm_fvar fv -> fv_eq_lid fv Const.cons_lid
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
  | Total (t, _)
  | GTotal (t, _) -> t
  | Comp ct -> ct.result_typ

let set_result_typ c t = match c.n with
  | Total _ -> mk_Total t
  | GTotal _ -> mk_GTotal t
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
let is_primop_lid l = primops |> Util.for_some (lid_equals l)

let is_primop f = match f.n with
  | Tm_fvar fv -> is_primop_lid fv.fv_name.v
  | _ -> false

let rec unascribe e =
    let e = Subst.compress e in
    match e.n with
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

let rec is_unit t =
    match (unrefine t).n with
    | Tm_type _ -> true
    | Tm_fvar fv ->
      fv_eq_lid fv Const.unit_lid
      || fv_eq_lid fv Const.squash_lid
    | Tm_uinst (t, _) -> is_unit t
    | _ -> false

let rec non_informative t =
    match (unrefine t).n with
    | Tm_type _ -> true
    | Tm_fvar fv ->
      fv_eq_lid fv Const.unit_lid
      || fv_eq_lid fv Const.squash_lid
      || fv_eq_lid fv Const.erased_lid
    | Tm_app(head, _) -> non_informative head
    | Tm_uinst (t, _) -> non_informative t
    | Tm_arrow(_, c) ->
      is_tot_or_gtot_comp c
      && non_informative (comp_result c)
    | _ -> false

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
  match (un_uinst typ).n with
    | Tm_app(head, args) ->
      let head = un_uinst head in
      begin match head.n with
              | Tm_fvar tc when fv_eq_lid tc lid -> Some args
              | _ -> None
      end
    | Tm_fvar tc when fv_eq_lid tc lid -> Some []
    | _ -> None

let rec lids_of_sigelt se = match se with
  | Sig_let(_, _, lids, _)
  | Sig_bundle(_, _, lids, _) -> lids
  | Sig_inductive_typ (lid, _, _,  _, _, _, _, _)
  | Sig_effect_abbrev(lid, _, _, _,  _, _, _)
  | Sig_datacon (lid, _, _, _, _, _, _, _)
  | Sig_declare_typ (lid, _, _, _, _)
  | Sig_assume (lid, _, _, _) -> [lid]
  | Sig_new_effect_for_free(n, _)
  | Sig_new_effect(n, _) -> [n.mname]
  | Sig_sub_effect _
  | Sig_pragma _
  | Sig_main _ -> []

let lid_of_sigelt se : option<lident> = match lids_of_sigelt se with
  | [l] -> Some l
  | _ -> None

let quals_of_sigelt x = match x with
  | Sig_bundle(_, quals, _, _)
  | Sig_inductive_typ (_, _, _,  _, _, _, quals, _)
  | Sig_effect_abbrev  (_, _, _, _, quals, _, _)
  | Sig_datacon (_, _, _, _, _, quals, _, _)
  | Sig_declare_typ (_, _, _, quals, _)
  | Sig_assume (_, _, quals, _)
  | Sig_let(_, _, _, quals)
  | Sig_new_effect({qualifiers=quals}, _)
  | Sig_new_effect_for_free({qualifiers=quals}, _) ->
    quals
  | Sig_sub_effect(_, _)
  | Sig_pragma(_, _)
  | Sig_main(_, _) -> []

let range_of_sigelt x = match x with
  | Sig_bundle(_, _, _, r)
  | Sig_inductive_typ (_, _, _,  _, _, _, _, r)
  | Sig_effect_abbrev  (_, _, _, _, _, _, r)
  | Sig_datacon (_, _, _, _, _, _, _, r)
  | Sig_declare_typ (_, _, _, _, r)
  | Sig_assume (_, _, _, r)
  | Sig_let(_, r, _, _)
  | Sig_main(_, r)
  | Sig_pragma(_, r)
  | Sig_new_effect(_, r)
  | Sig_new_effect_for_free(_, r)
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
      mk (Tm_meta(fvar l Delta_constant (Some Data_ctor), Meta_desugared Data_app)) None (range_of_lid l)
    | _ ->
      let e = mk_app (fvar l Delta_constant (Some Data_ctor)) args in
      mk (Tm_meta(e, Meta_desugared Data_app)) None e.pos

let mangle_field_name x = mk_ident("^fname^" ^ x.idText, x.idRange)
let unmangle_field_name x =
    if Util.starts_with x.idText "^fname^"
    then mk_ident(Util.substring_from x.idText 7, x.idRange)
    else x

(***********************************************************************************************)
(* Combining an effect name with the name of one of its actions, or a
   data constructor name with the name of one of its formal parameters

   NOTE: the conventions defined here must be in sync with manually
   linked ML files, such as ulib/ml/prims.ml
 *)
(***********************************************************************************************)

let field_projector_prefix = "__proj__"

(* NOTE: the following would have been desirable:

<<
let field_projector_prefix = Ident.reserved_prefix ^ "proj__"
>>

   but it DOES NOT work with --use_hints on
   examples/preorders/MRefHeap.fst (even after regenerating hints), it
   will produce the following error:

   fstar.exe  --use_hints --verify_module MRefHeap MRefHeap.fst
   ./MRefHeap.fst(55,51-58,27): (Error) Unknown assertion failed
   Verified module: MRefHeap (2150 milliseconds)
   1 error was reported (see above)

   In fact, any naming convention that DOES NOT start with
   Ident.reserved_prefix seems to work.
*)

let field_projector_sep = "__item__"

let field_projector_contains_constructor s = Util.starts_with s field_projector_prefix

let mk_field_projector_name_from_string constr field =
    field_projector_prefix ^ constr ^ field_projector_sep ^ field

let mk_field_projector_name_from_ident lid (i : ident) =
    let j = unmangle_field_name i in
    let jtext = j.idText in
    let newi =
        if field_projector_contains_constructor jtext
        then j
        else mk_ident (mk_field_projector_name_from_string lid.ident.idText jtext, i.idRange)
    in
    lid_of_ids (lid.ns @ [newi])

let mk_field_projector_name lid (x:bv) i =
    let nm = if Syntax.is_null_bv x
             then mk_ident("_" ^ Util.string_of_int i, Syntax.range_of_bv x)
             else x.ppname in
    let y = {x with ppname=nm} in
    mk_field_projector_name_from_ident lid nm, y

let set_uvar uv t =
  match Unionfind.find uv with
    | Fixed _ -> failwith (Util.format1 "Changing a fixed uvar! ?%s\n" (Util.string_of_int <| Unionfind.uvar_id uv))
    | _ -> Unionfind.change uv (Fixed t)

let qualifier_equal q1 q2 = match q1, q2 with
  | Discriminator l1, Discriminator l2 -> lid_equals l1 l2
  | Projector (l1a, l1b), Projector (l2a, l2b) -> lid_equals l1a l2a && l1b.idText=l2b.idText
  | RecordType (ns1, f1), RecordType (ns2, f2) 
  | RecordConstructor (ns1, f1), RecordConstructor (ns2, f2) ->
      List.length ns1 = List.length ns2 && List.forall2 (fun x1 x2 -> x1.idText = x2.idText) f1 f2 &&
      List.length f1 = List.length f2 && List.forall2 (fun x1 x2 -> x1.idText = x2.idText) f1 f2
  | _ -> q1=q2


(***********************************************************************************************)
(* closing types and terms *)
(***********************************************************************************************)
let abs bs t lopt =
  if List.length bs = 0 then
    t
  else
    let close_lopt lopt = match lopt with
        | None
        | Some (Inr _) -> lopt
        | Some (Inl lc) ->
            Some (Inl (close_lcomp bs lc))
    in
    match bs with
    | [] -> t
    | _ ->
    let body = compress (Subst.close bs t) in
    match body.n, lopt with
        | Tm_abs(bs', t, lopt'), None ->
          mk (Tm_abs(close_binders bs@bs', t, close_lopt lopt')) None t.pos
        | _ ->
          mk (Tm_abs(close_binders bs, body, close_lopt lopt)) None t.pos

let arrow bs c = match bs with
  | [] -> comp_result c
  | _ -> mk (Tm_arrow(close_binders bs, Subst.close_comp bs c)) None c.pos

let flat_arrow bs c =
  let t = arrow bs c in
  match (Subst.compress t).n with
  | Tm_arrow(bs, c) ->
    begin match c.n with
        | Total (tres, _) ->
          begin match (Subst.compress tres).n with
               | Tm_arrow(bs', c') -> mk (Tm_arrow(bs@bs', c')) (!t.tk) t.pos
               | _ -> t
          end
        | _ -> t
    end
  | _ -> t

let refine b t = mk (Tm_refine(b, Subst.close [mk_binder b] t)) !b.sort.tk (Range.union_ranges (range_of_bv b) t.pos)
let branch b = Subst.close_branch b


let rec arrow_formals_comp k =
    let k = Subst.compress k in
    match k.n with
        | Tm_arrow(bs, c) ->
            let bs, c = Subst.open_comp bs c in
            if is_tot_or_gtot_comp c
            then let bs', k = arrow_formals_comp (comp_result c) in
                bs@bs', k
            else bs, c
        | _ -> [], Syntax.mk_Total k

let rec arrow_formals k =
    let bs, c = arrow_formals_comp k in
    bs, comp_result c

let abs_formals t =
    let rec aux t what =
        match (unascribe <| Subst.compress t).n with
        | Tm_abs(bs, t, what) ->
            let bs',t, what = aux t what in
            bs@bs', t, what
        | _ -> [], t, what
    in
    let bs, t, what = aux t None in
    (* TODO : what should be open, no ? *)
    (*let what = match what with
        | Some (Inr lc) -> Subst.open_lc bs what
        | _ -> what
    in*)
    let bs, t = Subst.open_term bs t in
    bs, t, what

let mk_letbinding lbname univ_vars typ eff def =
    {lbname=lbname;
     lbunivs=univ_vars;
     lbtyp=typ;
     lbeff=eff;
     lbdef=def}

let close_univs_and_mk_letbinding recs lbname univ_vars typ eff def =
    let def = match recs, univ_vars with
        | None, _
        | _, [] -> def
        | Some fvs, _ ->
          let universes = univ_vars |> List.map U_name in
          let inst = fvs |> List.map (fun fv -> fv.fv_name.v, universes) in
          FStar.Syntax.InstFV.instantiate inst def in
    let typ = Subst.close_univ_vars univ_vars typ in
    let def = Subst.close_univ_vars univ_vars def in
    mk_letbinding lbname univ_vars typ eff def

let open_univ_vars_binders_and_comp uvs binders c =
    match binders with
        | [] ->
          let uvs, c = Subst.open_univ_vars_comp uvs c in
          uvs, [], c
        | _ ->
          let t' = arrow binders c in
          let uvs, t' = Subst.open_univ_vars uvs t' in
          match (Subst.compress t').n with
            | Tm_arrow(binders, c) -> uvs, binders, c
            | _ -> failwith "Impossible"

(********************************************************************************)
(*********************** Various tests on constants  ****************************)
(********************************************************************************)
let is_tuple_constructor (t:typ) = match t.n with
  | Tm_fvar fv -> Util.starts_with fv.fv_name.v.str "Prims.tuple"
  | _ -> false

let mk_tuple_lid n r =
  let t = Util.format1 "tuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let mk_tuple_data_lid n r =
  let t = Util.format1 "Mktuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let is_tuple_data_lid f n =
  lid_equals f (mk_tuple_data_lid n dummyRange)

let is_dtuple_constructor (t:typ) = match t.n with
  | Tm_fvar fv -> Util.starts_with fv.fv_name.v.str "Prims.dtuple"
  | _ -> false

let mk_dtuple_lid n r =
  let t = Util.format1 "dtuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let mk_dtuple_data_lid n r =
  let t = Util.format1 "Mkdtuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let is_lid_equality x = lid_equals x Const.eq2_lid

let is_forall lid = lid_equals lid Const.forall_lid
let is_exists lid = lid_equals lid Const.exists_lid
let is_qlid lid   = is_forall lid || is_exists lid
let is_equality x = is_lid_equality x.v

let lid_is_connective =
  let lst = [Const.and_lid; Const.or_lid; Const.not_lid;
             Const.iff_lid; Const.imp_lid] in
  fun lid -> Util.for_some (lid_equals lid) lst

let is_constructor t lid =
  match (pre_typ t).n with
    | Tm_fvar tc -> lid_equals tc.fv_name.v lid
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

let ktype  : term = mk (Tm_type(U_unknown)) None dummyRange
let ktype0 : term = mk (Tm_type(U_zero)) None dummyRange

//Type(u), where u is a new universe unification variable
let type_u () : typ * universe =
    let u = U_unif <| Unionfind.fresh None in
    mk (Tm_type u) None Range.dummyRange, u

let kt_kt = Const.kunary ktype0 ktype0
let kt_kt_kt = Const.kbin ktype0 ktype0 ktype0

let fvar_const l = fvar l Delta_constant None
let tand    = fvar_const Const.and_lid
let tor     = fvar_const Const.or_lid
let timp    = fvar_const Const.imp_lid
let tiff    = fvar_const Const.iff_lid
let t_bool  = fvar_const Const.bool_lid
let t_false = fvar_const Const.false_lid
let t_true  = fvar_const Const.true_lid
let b2t_v   = fvar_const Const.b2t_lid
let t_not   = fvar_const Const.not_lid

let mk_conj_opt phi1 phi2 = match phi1 with
  | None -> Some phi2
  | Some phi1 -> Some (mk (Tm_app(tand, [as_arg phi1; as_arg phi2])) None (Range.union_ranges phi1.pos phi2.pos))
let mk_binop op_t phi1 phi2 = mk (Tm_app(op_t, [as_arg phi1; as_arg phi2])) None (Range.union_ranges phi1.pos phi2.pos)
let mk_neg phi = mk (Tm_app(t_not, [as_arg phi])) None phi.pos
let mk_conj phi1 phi2 = mk_binop tand phi1 phi2
let mk_conj_l phi = match phi with
    | [] -> fvar Const.true_lid Delta_constant None
    | hd::tl -> List.fold_right mk_conj tl hd
let mk_disj phi1 phi2 = mk_binop tor phi1 phi2
let mk_disj_l phi = match phi with
    | [] -> t_false
    | hd::tl -> List.fold_right mk_disj tl hd
let mk_imp phi1 phi2  =
    match (compress phi1).n with
        | Tm_fvar tc when fv_eq_lid tc Const.false_lid -> t_true
        | Tm_fvar tc when fv_eq_lid tc Const.true_lid  -> phi2
        | _ ->
            begin match (compress phi2).n with
                | Tm_fvar tc when (fv_eq_lid tc Const.true_lid
                                || fv_eq_lid tc Const.false_lid) -> phi2
                | _ -> mk_binop timp phi1 phi2
            end
let mk_iff phi1 phi2  = mk_binop tiff phi1 phi2
let b2t e = mk (Tm_app(b2t_v, [as_arg e])) None e.pos//implicitly coerce a boolean to a type

let teq = fvar_const Const.eq2_lid

let mk_eq t1 t2 e1 e2 = mk (Tm_app(teq, [as_arg e1; as_arg e2])) None (Range.union_ranges e1.pos e2.pos)

let mk_has_type t x t' =
    let t_has_type = fvar_const Const.has_type_lid in //TODO: Fix the U_zeroes below!
    let t_has_type = mk (Tm_uinst(t_has_type, [U_zero; U_zero])) None dummyRange in
    mk (Tm_app(t_has_type, [iarg t; as_arg x; as_arg t'])) None dummyRange

let lex_t    = fvar_const Const.lex_t_lid
let lex_top  = fvar Const.lextop_lid Delta_constant (Some Data_ctor)
let lex_pair = fvar Const.lexcons_lid Delta_constant (Some Data_ctor)
let tforall  = fvar Const.forall_lid (Delta_defined_at_level 1) None
let t_haseq   = fvar Const.haseq_lid Delta_constant None

let lcomp_of_comp c0 =
    let eff_name, flags =
        match c0.n with
        | Total _ -> Const.effect_Tot_lid, [TOTAL]
        | GTotal _ -> Const.effect_GTot_lid, [SOMETRIVIAL]
        | Comp c -> c.effect_name, c.flags in
    {eff_name = eff_name;
     res_typ = comp_result c0;
     cflags = flags;
     comp = fun() -> c0}

let mk_forall (x:bv) (body:typ) : typ =
  mk (Tm_app(tforall, [ iarg (x.sort);
                        as_arg (abs [mk_binder x] body (Some (Inl (lcomp_of_comp <| mk_Total ktype0))))])) None dummyRange

let rec close_forall bs f =
  List.fold_right (fun b f -> if Syntax.is_null_binder b then f else mk_forall (fst b) f) bs f

let rec is_wild_pat p =
    match p.v with
    | Pat_wild _ -> true
    | _ -> false

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
    let rec unmeta_monadic f =
      let f = Subst.compress f in
      match f.n with
      | Tm_meta(t, Meta_monadic _)
      | Tm_meta(t, Meta_monadic_lift _) -> unmeta_monadic t
      | _ -> f in
    let destruct_base_conn f =
        let connectives = [ (Const.true_lid,  0);
                            (Const.false_lid, 0);
                            (Const.and_lid,   2);
                            (Const.or_lid,    2);
                            (Const.imp_lid, 2);
                            (Const.iff_lid, 2);
                            (Const.ite_lid, 3);
                            (Const.not_lid, 1);
                            (Const.eq2_lid, 3);
                            (Const.eq2_lid, 2);
                            (Const.eq3_lid, 4);
                            (Const.eq3_lid, 2)
                        ] in
        let rec aux f (lid, arity) =
            let t, args = head_and_args (unmeta_monadic f) in
            let t = un_uinst t in
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
        let is_q : bool -> fv -> Tot<bool> = fun fa fv -> if fa then is_forall fv.fv_name.v else is_exists fv.fv_name.v in
        let flat t =
            let t, args = head_and_args t in
            un_uinst t, args |> List.map (fun (t, imp) -> unascribe t, imp) in
        let rec aux qopt out t = match qopt, flat t with
            | Some fa, ({n=Tm_fvar tc}, [({n=Tm_abs([b], t2, _)}, _)])
            | Some fa, ({n=Tm_fvar tc}, [_; ({n=Tm_abs([b], t2, _)}, _)])
                when (is_q fa tc) ->
              aux qopt (b::out) t2

            | None, ({n=Tm_fvar tc}, [({n=Tm_abs([b], t2, _)}, _)])
            | None, ({n=Tm_fvar tc}, [_; ({n=Tm_abs([b], t2, _)}, _)])
                when (is_qlid tc.fv_name.v) ->
              aux (Some (is_forall tc.fv_name.v)) (b::out) t2

            | Some b, _ ->
              let bs = List.rev out in
              let bs, t = Subst.open_term bs t in
              let pats, body = patterns t in
              if b
              then Some (QAll(bs, pats, body))
              else Some  (QEx(bs, pats, body))

            | _ -> None in
        aux None [] t in

    let phi = unmeta_monadic f in
        match destruct_base_conn phi with
        | Some b -> Some b
        | None -> destruct_q_conn phi


  let action_as_lb a =
    let lb = close_univs_and_mk_letbinding
                None
                (Inr (lid_as_fv a.action_name Delta_equational None))
                a.action_univs
                a.action_typ
                Const.effect_Tot_lid
                a.action_defn in
    Sig_let((false, [lb]), a.action_defn.pos, [a.action_name], [])

(* Some reification utilities *)
let mk_reify t =
    let reify_ = mk (Tm_constant(FStar.Const.Const_reify)) None t.pos in
    mk (Tm_app(reify_, [as_arg t])) None t.pos

(* Some utilities for clients who wish to build top-level bindings and keep
 * their delta-qualifiers correct (e.g. dmff). *)

let rec delta_qualifier t =
    let t = Subst.compress t in
    match t.n with
        | Tm_delayed _ -> failwith "Impossible"
        | Tm_fvar fv -> fv.fv_delta
        | Tm_bvar _
        | Tm_name _
        | Tm_match _
        | Tm_uvar _
        | Tm_unknown -> Delta_equational
        | Tm_type _
        | Tm_constant _
        | Tm_arrow _ -> Delta_constant
        | Tm_uinst(t, _)
        | Tm_refine({sort=t}, _)
        | Tm_meta(t, _)
        | Tm_ascribed(t, _, _)
        | Tm_app(t, _)
        | Tm_abs(_, t, _)
        | Tm_let(_, t) -> delta_qualifier t

let incr_delta_qualifier t =
    let d = delta_qualifier t in
    let rec aux d = match d with
        | Delta_equational -> d
        | Delta_constant -> Delta_defined_at_level 1
        | Delta_defined_at_level i -> Delta_defined_at_level (i + 1)
        | Delta_abstract d -> aux d in
    aux d

let is_unknown t = match (Subst.compress t).n with | Tm_unknown -> true | _ -> false

let rec list_elements (e:term) : option<list<term>> =
  let head, args = head_and_args (unmeta e) in
  match (un_uinst head).n, args with
  | Tm_fvar fv, _ when fv_eq_lid fv Const.nil_lid ->
      Some []
  | Tm_fvar fv, [_; (hd, _); (tl, _)] when fv_eq_lid fv Const.cons_lid ->
      Some (hd::must (list_elements tl))
  | _ ->
      None

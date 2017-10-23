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
open FStar.ST
open FStar.All

open Prims
open FStar
open FStar.Util
open FStar.Ident
open FStar.Range
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Const
open FStar.Dyn
module U = FStar.Util
module List = FStar.List
module PC = FStar.Parser.Const
(********************************************************************************)
(**************************Utilities for identifiers ****************************)
(********************************************************************************)

let qual_id lid id = set_lid_range (lid_of_ids (lid.ns @ [lid.ident;id])) id.idRange

let mk_discriminator lid =
  lid_of_ids (lid.ns@[mk_ident(Ident.reserved_prefix ^ "is_" ^ lid.ident.idText, lid.ident.idRange)])

let is_name (lid:lident) =
  let c = U.char_at lid.ident.idText 0 in
  U.is_upper c

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

let binders_of_freevars fvs = U.set_elements fvs |> List.map mk_binder

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

let rec unmeta_safe e =
    let e = compress e in
    match e.n with
        | Tm_meta(e', m) ->
            begin match m with
            | Meta_monadic _
            | Meta_monadic_lift _
            | Meta_alien _ ->
              e // don't remove the metas that really matter
            | _ -> unmeta_safe e'
            end
        | Tm_ascribed(e, _, _) -> unmeta_safe e
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

    | U_unif u1, U_unif u2 -> Unionfind.univ_uvar_id u1 - Unionfind.univ_uvar_id u2

    | U_max us1, U_max us2 ->
      let n1 = List.length us1 in
      let n2 = List.length us2 in
      if n1 <> n2
      then n1 - n2
      else let copt = U.find_map (List.zip us1 us2) (fun (u1, u2) ->
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
  mk_Comp ({comp_univs=[U_zero];
            effect_name=set_lid_range PC.effect_ML_lid r;
            result_typ=t;
            effect_args=[];
            flags=[MLEFFECT]})

let comp_effect_name c = match c.n with
    | Comp c  -> c.effect_name
    | Total _ -> PC.effect_Tot_lid
    | GTotal _ -> PC.effect_GTot_lid

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
        | Comp c -> lid_equals c.effect_name PC.effect_Tot_lid
        | Total _ -> true
        | GTotal _ -> false

let is_total_comp c =
    lid_equals (comp_effect_name c) PC.effect_Tot_lid
    || comp_flags c |> U.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_total_lcomp c = lid_equals c.eff_name PC.effect_Tot_lid || c.cflags |> U.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_tot_or_gtot_lcomp c = lid_equals c.eff_name PC.effect_Tot_lid
                             || lid_equals c.eff_name PC.effect_GTot_lid
                             || c.cflags |> U.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_partial_return c = comp_flags c |> U.for_some (function RETURN | PARTIAL_RETURN -> true | _ -> false)

let is_lcomp_partial_return c = c.cflags |> U.for_some (function RETURN | PARTIAL_RETURN -> true | _ -> false)

let is_tot_or_gtot_comp c =
    is_total_comp c
    || lid_equals PC.effect_GTot_lid (comp_effect_name c)

let is_pure_effect l =
     lid_equals l PC.effect_Tot_lid
     || lid_equals l PC.effect_PURE_lid
     || lid_equals l PC.effect_Pure_lid

let is_pure_comp c = match c.n with
    | Total _ -> true
    | GTotal _ -> false
    | Comp ct -> is_total_comp c
                 || is_pure_effect ct.effect_name
                 || ct.flags |> U.for_some (function LEMMA -> true | _ -> false)

let is_ghost_effect l =
       lid_equals PC.effect_GTot_lid l
    || lid_equals PC.effect_GHOST_lid l
    || lid_equals PC.effect_Ghost_lid l

let is_pure_or_ghost_comp c = is_pure_comp c || is_ghost_effect (comp_effect_name c)

let is_pure_lcomp lc =
    is_total_lcomp lc
    || is_pure_effect lc.eff_name
    || lc.cflags |> U.for_some (function LEMMA -> true | _ -> false)

let is_pure_or_ghost_lcomp lc =
    is_pure_lcomp lc || is_ghost_effect lc.eff_name

let is_pure_or_ghost_function t = match (compress t).n with
    | Tm_arrow(_, c) -> is_pure_or_ghost_comp c
    | _ -> true

let is_lemma_comp c =
    match c.n with
    | Comp ct -> lid_equals ct.effect_name PC.effect_Lemma_lid
    | _ -> false

let is_lemma t =
    match (compress t).n with
    | Tm_arrow(_, c) -> is_lemma_comp c
    | _ -> false

let head_and_args t =
    let t = compress t in
    match t.n with
        | Tm_app(head, args) -> head, args
        | _ -> t, []

let rec head_and_args' t =
    let t = compress t in
    match t.n with
        | Tm_app(head, args) ->
            let (head, args') = head_and_args' head
            in (head, args'@args)
        | _ -> t, []

 let un_uinst t =
    let t = Subst.compress t in
    match t.n with
        | Tm_uinst(t, _) -> Subst.compress t
        | _ -> t

let is_smt_lemma t = match (compress t).n with
    | Tm_arrow(_, c) ->
      begin match c.n with
        | Comp ct when lid_equals ct.effect_name PC.effect_Lemma_lid ->
            begin match ct.effect_args with
                | _req::_ens::(pats, _)::_ ->
                  let pats' = unmeta pats in
                  let head, _ = head_and_args pats' in
                  begin match (un_uinst head).n with
                    | Tm_fvar fv -> fv_eq_lid fv PC.cons_lid
                    | _ -> false
                  end
                | _ -> false
            end
        | _ -> false
      end
    | _ -> false

let is_ml_comp c = match c.n with
  | Comp c -> lid_equals c.effect_name PC.effect_ML_lid
              || c.flags |> U.for_some (function MLEFFECT -> true | _ -> false)

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
  comp_flags c |> U.for_some (function TOTAL | RETURN -> true | _ -> false)

(********************************************************************************)
(*               Simple utils on the structure of a term                        *)
(********************************************************************************)
let primops =
  [PC.op_Eq;
   PC.op_notEq;
   PC.op_LT;
   PC.op_LTE;
   PC.op_GT;
   PC.op_GTE;
   PC.op_Subtraction;
   PC.op_Minus;
   PC.op_Addition;
   PC.op_Multiply;
   PC.op_Division;
   PC.op_Modulus;
   PC.op_And;
   PC.op_Or;
   PC.op_Negation;]
let is_primop_lid l = primops |> U.for_some (lid_equals l)

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

(* ---------------------------------------------------------------------- *)
(* <eq_tm> Syntactic equality of zero-order terms                         *)
(* ---------------------------------------------------------------------- *)
type eq_result =
    | Equal
    | NotEqual
    | Unknown

let rec eq_tm (t1:term) (t2:term) : eq_result =
    let canon_app t =
        let hd, args = head_and_args' (unascribe t) in
        mk_Tm_app hd args None t.pos
    in
    let t1 = canon_app t1 in
    let t2 = canon_app t2 in
    let equal_if = function
        | true -> Equal
        | _ -> Unknown
    in
    let equal_iff = function
        | true -> Equal
        | _ -> NotEqual
    in
    let eq_and f g =
      match f with
      | Equal -> g()
      | _ -> Unknown
    in
    let eq_inj f g =
      match f, g with
      | Equal, Equal -> Equal
      | NotEqual, _
      | _, NotEqual -> NotEqual
      | Unknown, _
      | _, Unknown -> Unknown
    in
    let equal_data f1 args1 f2 args2 =
        // we got constructors! we know they are injective and disjoint, so we can do some
        // good analysis on them
        if fv_eq f1 f2
        then (
            assert (List.length args1 = List.length args2);
            List.fold_left (fun acc ((a1, q1), (a2, q2)) ->
                                assert (q1 = q2);
                                eq_inj acc (eq_tm a1 a2)) Equal <| List.zip args1 args2
        ) else NotEqual
    in
    match t1.n, t2.n with
    | Tm_name a, Tm_name b ->
      equal_if (bv_eq a b)

    | Tm_fvar f, Tm_fvar g ->
      if f.fv_qual = Some Data_ctor && g.fv_qual = Some Data_ctor
      then equal_data f [] g []
      else equal_if (fv_eq f g)

    | Tm_uinst(f, us), Tm_uinst(g, vs) ->
      eq_and (eq_tm f g) (fun () -> equal_if (eq_univs_list us vs))

    // Ranges should be opaque, even to the normalizer. c.f. #1312
    | Tm_constant (Const_range _), _
    | _, Tm_constant (Const_range _) ->
      Unknown

    | Tm_constant c, Tm_constant d ->
      equal_iff (eq_const c d)

    | Tm_uvar (u1, _), Tm_uvar (u2, _) ->
      equal_if (Unionfind.equiv u1 u2)

    | Tm_app (h1, args1), Tm_app (h2, args2) ->
      begin match (un_uinst h1).n, (un_uinst h2).n with
      | Tm_fvar f1, Tm_fvar f2 when f1.fv_qual = Some Data_ctor && f2.fv_qual = Some Data_ctor ->
        equal_data f1 args1 f2 args2
      | _ -> // can only they're equal if they syntactically match, nothing else
        eq_and (eq_tm h1 h2) (fun () -> eq_args args1 args2)
      end

    | Tm_type u, Tm_type v ->
      equal_if (eq_univs u v)

    | Tm_meta(t1, _), _ ->
      eq_tm t1 t2

    | _, Tm_meta(t2, _) ->
      eq_tm t1 t2

    | _ -> Unknown

and eq_args (a1:args) (a2:args) : eq_result =
    match a1, a2 with
    | [], [] -> Equal
    | (a, _)::a1, (b, _)::b1 ->
      (match eq_tm a b with
       | Equal -> eq_args a1 b1
       | _ -> Unknown)
    | _ -> Unknown

and eq_univs_list (us:universes) (vs:universes) : bool =
    List.length us = List.length vs
    && List.forall2 eq_univs us vs

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
      fv_eq_lid fv PC.unit_lid
      || fv_eq_lid fv PC.squash_lid
    | Tm_uinst (t, _) -> is_unit t
    | _ -> false

let rec non_informative t =
    match (unrefine t).n with
    | Tm_type _ -> true
    | Tm_fvar fv ->
      fv_eq_lid fv PC.unit_lid
      || fv_eq_lid fv PC.squash_lid
      || fv_eq_lid fv PC.erased_lid
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

let lids_of_sigelt (se: sigelt) = match se.sigel with
  | Sig_let(_, lids)
  | Sig_bundle(_, lids) -> lids
  | Sig_inductive_typ (lid, _,  _, _, _, _)
  | Sig_effect_abbrev(lid, _, _,  _, _)
  | Sig_datacon (lid, _, _, _, _, _)
  | Sig_declare_typ (lid, _, _)
  | Sig_assume (lid, _, _) -> [lid]
  | Sig_new_effect_for_free(n)
  | Sig_new_effect(n) -> [n.mname]
  | Sig_sub_effect _
  | Sig_pragma _
  | Sig_main _ -> []

let lid_of_sigelt se : option<lident> = match lids_of_sigelt se with
  | [l] -> Some l
  | _ -> None

let quals_of_sigelt (x: sigelt) = x.sigquals

let range_of_sigelt (x: sigelt) = x.sigrng

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

let mangle_field_name x = mk_ident("__fname__" ^ x.idText, x.idRange)
let unmangle_field_name x =
    if U.starts_with x.idText "__fname__"
    then mk_ident(U.substring_from x.idText 9, x.idRange)
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

let field_projector_contains_constructor s = U.starts_with s field_projector_prefix

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
             then mk_ident("_" ^ U.string_of_int i, Syntax.range_of_bv x)
             else x.ppname in
    let y = {x with ppname=nm} in
    mk_field_projector_name_from_ident lid nm, y

let set_uvar uv t =
  match Unionfind.find uv with
    | Some _ -> failwith (U.format1 "Changing a fixed uvar! ?%s\n" (U.string_of_int <| Unionfind.uvar_id uv))
    | _ -> Unionfind.change uv t

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
  let close_lopt lopt = match lopt with
      | None -> None
      | Some rc -> Some ({rc with residual_typ=FStar.Util.map_opt rc.residual_typ (close bs)})
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
               | Tm_arrow(bs', c') -> mk (Tm_arrow(bs@bs', c')) None t.pos
               | _ -> t
          end
        | _ -> t
    end
  | _ -> t

let refine b t = mk (Tm_refine(b, Subst.close [mk_binder b] t)) None (Range.union_ranges (range_of_bv b) t.pos)
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
    let subst_lcomp_opt s l = match l with
        | Some rc ->
          Some ({rc with residual_typ=FStar.Util.map_opt rc.residual_typ (Subst.subst s)})
        | _ -> l
    in
    let rec aux t abs_body_lcomp =
        match (unascribe <| Subst.compress t).n with
        | Tm_abs(bs, t, what) ->
            let bs',t, what = aux t what in
            bs@bs', t, what
        | _ -> [], t, abs_body_lcomp
    in
    let bs, t, abs_body_lcomp = aux t None in
    let bs, t, opening = Subst.open_term' bs t in
    let abs_body_lcomp = subst_lcomp_opt opening abs_body_lcomp in
    bs, t, abs_body_lcomp

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
          FStar.Syntax.InstFV.instantiate inst def
    in
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
  | Tm_fvar fv -> PC.is_tuple_constructor_string fv.fv_name.v.str
  | _ -> false

let is_dtuple_constructor (t:typ) = match t.n with
  | Tm_fvar fv -> PC.is_dtuple_constructor_lid fv.fv_name.v
  | _ -> false

let is_lid_equality x = lid_equals x PC.eq2_lid

let is_forall lid = lid_equals lid PC.forall_lid
let is_exists lid = lid_equals lid PC.exists_lid
let is_qlid lid   = is_forall lid || is_exists lid
let is_equality x = is_lid_equality x.v

let lid_is_connective =
  let lst = [PC.and_lid; PC.or_lid; PC.not_lid;
             PC.iff_lid; PC.imp_lid] in
  fun lid -> U.for_some (lid_equals lid) lst

let is_constructor t lid =
  match (pre_typ t).n with
    | Tm_fvar tc -> lid_equals tc.fv_name.v lid
    | _ -> false

let rec is_constructed_typ t lid =
  match (pre_typ t).n with
  | Tm_fvar _ -> is_constructor t lid
  | Tm_app(t, _)
  | Tm_uinst(t, _) -> is_constructed_typ t lid
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
    [PC.op_Eq          ;
     PC.op_notEq       ;
     PC.op_LT          ;
     PC.op_LTE         ;
     PC.op_GT          ;
     PC.op_GTE         ;
     PC.op_Subtraction ;
     PC.op_Minus       ;
     PC.op_Addition    ;
     PC.op_Multiply    ;
     PC.op_Division    ;
     PC.op_Modulus     ;
     PC.op_And         ;
     PC.op_Or          ;
     PC.op_Negation] in
  U.for_some (lid_equals l) theory_syms

let is_fstar_tactics_embed t =
    match (un_uinst t).n with
    | Tm_fvar fv -> fv_eq_lid fv PC.fstar_refl_embed_lid
    | _ -> false

let is_fstar_tactics_quote t =
    match (un_uinst t).n with
    | Tm_fvar fv -> fv_eq_lid fv PC.quote_lid
    | _ -> false

let is_fstar_tactics_by_tactic t =
    match (un_uinst t).n with
    | Tm_fvar fv -> fv_eq_lid fv PC.by_tactic_lid
    | _ -> false

(********************************************************************************)
(*********************** Constructors of common terms  **************************)
(********************************************************************************)

let ktype  : term = mk (Tm_type(U_unknown)) None dummyRange
let ktype0 : term = mk (Tm_type(U_zero)) None dummyRange

//Type(u), where u is a new universe unification variable
let type_u () : typ * universe =
    let u = U_unif <| Unionfind.univ_fresh () in
    mk (Tm_type u) None dummyRange, u

let attr_substitute =
mk (Tm_fvar (lid_as_fv (lid_of_path ["FStar"; "Pervasives"; "Substitute"] Range.dummyRange) Delta_constant None)) None Range.dummyRange

let exp_true_bool : term = mk (Tm_constant (Const_bool true)) None dummyRange
let exp_false_bool : term = mk (Tm_constant (Const_bool false)) None dummyRange
let exp_unit : term = mk (Tm_constant (Const_unit)) None dummyRange
(* Makes an (unbounded) integer from its string repr. *)
let exp_int s : term = mk (Tm_constant (Const_int (s,None))) None dummyRange
let exp_char c : term = mk (Tm_constant (Const_char c)) None dummyRange
let exp_string s : term = mk (Tm_constant (Const_string (s, dummyRange))) None dummyRange

let fvar_const l = fvar l Delta_constant None
let tand    = fvar_const PC.and_lid
let tor     = fvar_const PC.or_lid
let timp    = fvar PC.imp_lid (Delta_defined_at_level 1) None
let tiff    = fvar PC.iff_lid (Delta_defined_at_level 2) None
let t_bool  = fvar_const PC.bool_lid
let t_false = fvar_const PC.false_lid
let t_true  = fvar_const PC.true_lid
let b2t_v   = fvar_const PC.b2t_lid
let t_not   = fvar_const PC.not_lid

let mk_conj_opt phi1 phi2 = match phi1 with
  | None -> Some phi2
  | Some phi1 -> Some (mk (Tm_app(tand, [as_arg phi1; as_arg phi2])) None (Range.union_ranges phi1.pos phi2.pos))
let mk_binop op_t phi1 phi2 = mk (Tm_app(op_t, [as_arg phi1; as_arg phi2])) None (Range.union_ranges phi1.pos phi2.pos)
let mk_neg phi = mk (Tm_app(t_not, [as_arg phi])) None phi.pos
let mk_conj phi1 phi2 = mk_binop tand phi1 phi2
let mk_conj_l phi = match phi with
    | [] -> fvar PC.true_lid Delta_constant None
    | hd::tl -> List.fold_right mk_conj tl hd
let mk_disj phi1 phi2 = mk_binop tor phi1 phi2
let mk_disj_l phi = match phi with
    | [] -> t_false
    | hd::tl -> List.fold_right mk_disj tl hd
let mk_imp phi1 phi2 : term = mk_binop timp phi1 phi2
let mk_iff phi1 phi2 : term = mk_binop tiff phi1 phi2
let b2t e = mk (Tm_app(b2t_v, [as_arg e])) None e.pos//implicitly coerce a boolean to a type

let teq = fvar_const PC.eq2_lid
let mk_untyped_eq2 e1 e2 = mk (Tm_app(teq, [as_arg e1; as_arg e2])) None (Range.union_ranges e1.pos e2.pos)
let mk_eq2 (u:universe) (t:typ) (e1:term) (e2:term) : term =
    let eq_inst = mk_Tm_uinst teq [u] in
    mk (Tm_app(eq_inst, [iarg t; as_arg e1; as_arg e2])) None (Range.union_ranges e1.pos e2.pos)

let mk_has_type t x t' =
    let t_has_type = fvar_const PC.has_type_lid in //TODO: Fix the U_zeroes below!
    let t_has_type = mk (Tm_uinst(t_has_type, [U_zero; U_zero])) None dummyRange in
    mk (Tm_app(t_has_type, [iarg t; as_arg x; as_arg t'])) None dummyRange

let lex_t    = fvar_const PC.lex_t_lid
let lex_top :term = mk (Tm_uinst (fvar PC.lextop_lid Delta_constant (Some Data_ctor), [U_zero])) None dummyRange
let lex_pair = fvar PC.lexcons_lid Delta_constant (Some Data_ctor)
let tforall  = fvar PC.forall_lid (Delta_defined_at_level 1) None
let t_haseq   = fvar PC.haseq_lid Delta_constant None

let lcomp_of_comp c0 =
    let eff_name, flags =
        match c0.n with
        | Total _ -> PC.effect_Tot_lid, [TOTAL]
        | GTotal _ -> PC.effect_GTot_lid, [SOMETRIVIAL]
        | Comp c -> c.effect_name, c.flags in
    {eff_name = eff_name;
     res_typ = comp_result c0;
     cflags = flags;
     comp = fun() -> c0}

let mk_residual_comp l t f = {
    residual_effect=l;
    residual_typ=t;
    residual_flags=f
  }
let residual_tot t = {
    residual_effect=PC.effect_Tot_lid;
    residual_typ=Some t;
    residual_flags=[TOTAL]
  }
let residual_comp_of_comp (c:comp) = {
    residual_effect=comp_effect_name c;
    residual_typ=Some (comp_result c);
    residual_flags=comp_flags c;
  }
let residual_comp_of_lcomp (lc:lcomp) = {
    residual_effect=lc.eff_name;
    residual_typ=Some (lc.res_typ);
    residual_flags=lc.cflags
  }


let mk_forall_aux fa x body =
  mk (Tm_app(fa, [ iarg (x.sort);
                   as_arg (abs [mk_binder x] body (Some (residual_tot ktype0)))])) None dummyRange

let mk_forall_no_univ (x:bv) (body:typ) : typ =
  mk_forall_aux tforall x body

let mk_forall (u:universe) (x:bv) (body:typ) : typ =
  let tforall = mk_Tm_uinst tforall [u] in
  mk_forall_aux tforall x body

let close_forall_no_univs bs f =
  List.fold_right (fun b f -> if Syntax.is_null_binder b then f else mk_forall_no_univ (fst b) f) bs f

let rec is_wild_pat p =
    match p.v with
    | Pat_wild _ -> true
    | _ -> false

let if_then_else b t1 t2 =
    let then_branch = (withinfo (Pat_constant (Const_bool true)) t1.pos, None, t1) in
    let else_branch = (withinfo (Pat_constant (Const_bool false)) t2.pos, None, t2) in
    mk (Tm_match(b, [then_branch; else_branch])) None (Range.union_ranges b.pos (Range.union_ranges t1.pos t2.pos))


let mk_squash p =
    let sq = fvar PC.squash_lid (Delta_defined_at_level 1) None in
    mk_app (mk_Tm_uinst sq [U_zero]) [as_arg p]

let un_squash t =
    let head, args = head_and_args t in
    match (un_uinst head).n, args with
    | Tm_fvar fv, [(p, _)]
        when fv_eq_lid fv PC.squash_lid ->
      Some p
    | Tm_refine (b, p), [] ->
        begin match b.sort.n with
        | Tm_fvar fv when fv_eq_lid fv PC.unit_lid ->
            let bs, p = Subst.open_term [mk_binder b] p in
            let b = match bs with
                    | [b] -> b
                    | _ -> failwith "impossible"
            in
            // A bit paranoid, but need this check for terms like `u:unit{u == ()}`
            if set_mem (fst b) (Free.names p)
            then None
            else Some p
        | _ -> None
        end
    | _ ->
      None

let arrow_one (t:typ) : option<(binder * comp)> =
    bind_opt (match (compress t).n with
              | Tm_arrow ([], c) ->
                  failwith "fatal: empty binders on arrow?"
              | Tm_arrow ([b], c) ->
                  Some (b, c)
              | Tm_arrow (b::bs, c) ->
                  Some (b, mk_Total (arrow bs c))
              | _ ->
                  None) (fun (b, c) ->
    let bs, c = Subst.open_comp [b] c in
    let b = match bs with
            | [b] -> b
            | _ -> failwith "impossible: open_comp returned different amount of binders"
    in
    Some (b, c))

let is_free_in (bv:bv) (t:term) : bool =
    U.set_mem bv (FStar.Syntax.Free.names t)

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
        let connectives = [ (PC.true_lid,  0);
                            (PC.false_lid, 0);
                            (PC.and_lid,   2);
                            (PC.or_lid,    2);
                            (PC.imp_lid, 2);
                            (PC.iff_lid, 2);
                            (PC.ite_lid, 3);
                            (PC.not_lid, 1);
                            (PC.eq2_lid, 3);
                            (PC.eq2_lid, 2);
                            (PC.eq3_lid, 4);
                            (PC.eq3_lid, 2)
                        ]
        in

        let aux f (lid, arity) =
            let t, args = head_and_args (unmeta_monadic f) in
            let t = un_uinst t in
            if is_constructor t lid
            && List.length args = arity
            then Some (BaseConn(lid, args))
            else None in
        U.find_map connectives (aux f) in

    let patterns t =
        let t = compress t in
        match t.n with
            | Tm_meta(t, Meta_pattern pats) -> pats, compress t
            | _ -> [], t in

    let destruct_q_conn t =
        let is_q (fa:bool) (fv:fv) : bool =
            if fa
            then is_forall fv.fv_name.v
            else is_exists fv.fv_name.v
        in
        let flat t =
            let t, args = head_and_args t in
            un_uinst t, args |> List.map (fun (t, imp) -> unascribe t, imp)
        in
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

    // Unfolded connectives
    let u_connectives =
        [ (PC.true_lid,  PC.c_true_lid, 0);
          (PC.false_lid, PC.c_false_lid, 0);
          (PC.and_lid,   PC.c_and_lid, 2);
          (PC.or_lid,    PC.c_or_lid, 2);
        ]
    in
    let destruct_sq_base_conn t =
        bind_opt (un_squash t) (fun t ->
        let hd, args = head_and_args' t in
        match (un_uinst hd).n, List.length args with
        | Tm_fvar fv, 2
            when fv_eq_lid fv PC.c_and_lid ->
                Some (BaseConn (PC.and_lid, args))
        | Tm_fvar fv, 2
            when fv_eq_lid fv PC.c_or_lid ->
                Some (BaseConn (PC.or_lid, args))

        // eq2 can have 2 args or 3
        | Tm_fvar fv, 2
            when fv_eq_lid fv PC.c_eq2_lid ->
                Some (BaseConn (PC.eq2_lid, args))
        | Tm_fvar fv, 3
            when fv_eq_lid fv PC.c_eq2_lid ->
                Some (BaseConn (PC.eq2_lid, args))

        // eq3 can have 2 args or 4
        | Tm_fvar fv, 2
            when fv_eq_lid fv PC.c_eq3_lid ->
                Some (BaseConn (PC.eq3_lid, args))
        | Tm_fvar fv, 4
            when fv_eq_lid fv PC.c_eq3_lid ->
                Some (BaseConn (PC.eq3_lid, args))

        | Tm_fvar fv, 0
            when fv_eq_lid fv PC.c_true_lid ->
                Some (BaseConn (PC.true_lid, args))
        | Tm_fvar fv, 0
            when fv_eq_lid fv PC.c_false_lid ->
                Some (BaseConn (PC.false_lid, args))

        | _ ->
            None
        )
    in
    let rec destruct_sq_forall t =
        bind_opt (un_squash t) (fun t ->
        match arrow_one t with
        | Some (b, c) ->
            if not (is_tot_or_gtot_comp c)
            then None
            else
                let q = (comp_to_comp_typ c).result_typ in
                if is_free_in (fst b) q
                then (
                    let pats, q = patterns q in
                    maybe_collect <| Some (QAll([b], pats, q))
                ) else (
                    // Since we know it's not free, we can just open and discard the binder
                    Some (BaseConn (PC.imp_lid, [as_arg (fst b).sort; as_arg q]))
                )
        | _ -> None)
    and destruct_sq_exists t =
        bind_opt (un_squash t) (fun t ->
        let hd, args = head_and_args' t in
        match (un_uinst hd).n, args with
        | Tm_fvar fv, [(a1, _); (a2, _)]
            when fv_eq_lid fv PC.dtuple2_lid ->
                begin match (compress a2).n with
                | Tm_abs ([b], q, _) ->
                    let bs, q = open_term [b] q in
                    let b = match bs with // coverage...
                            | [b] -> b
                            | _ -> failwith "impossible"
                    in
                    let pats, q = patterns q in
                    maybe_collect <| Some (QEx ([b], pats, q))
                | _ -> None
                end
        | _ -> None)
    and maybe_collect f =
        match f with
        | Some (QAll (bs, pats, phi)) ->
            begin match destruct_sq_forall phi with
            | Some (QAll (bs', pats', psi)) -> Some <| QAll(bs@bs', pats@pats', psi)
            | _ -> f
            end
        | Some (QEx (bs, pats, phi)) ->
            begin match destruct_sq_exists phi with
            | Some (QEx (bs', pats', psi)) -> Some <| QEx(bs@bs', pats@pats', psi)
            | _ -> f
            end
        | _ -> f
    in

    let phi = unmeta_monadic f in
        // Try all possibilities, stopping at the first
        catch_opt (destruct_base_conn phi) (fun () ->
        catch_opt (destruct_q_conn phi) (fun () ->
        catch_opt (destruct_sq_base_conn phi) (fun () ->
        catch_opt (destruct_sq_forall phi) (fun () ->
        catch_opt (destruct_sq_exists phi) (fun () ->
                   None)))))

let unthunk_lemma_post t =
    match (compress t).n with
    | Tm_abs ([b], e, _) ->
        let bs, e = open_term [b] e in
        let b = List.hd bs in
        if is_free_in (fst b) e
        then mk_app t [as_arg exp_unit]
        else e
    | _ ->
        mk_app t [as_arg exp_unit]

let action_as_lb eff_lid a =
  let lb =
    close_univs_and_mk_letbinding
      None
      (* Actions are set to Delta_constant since they need an explicit reify to be unfolded *)
      (Inr (lid_as_fv a.action_name Delta_equational None))
      a.action_univs
      (arrow a.action_params (mk_Total a.action_typ))
      PC.effect_Tot_lid
      (abs a.action_params a.action_defn None)
  in
  { sigel = Sig_let((false, [lb]), [a.action_name]);
    sigrng = a.action_defn.pos;
    sigquals = [Visible_default ; Action eff_lid];
    sigmeta = default_sigmeta;
    sigattrs = [] }

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

let rec incr_delta_depth d =
    match d with
    | Delta_equational -> d
    | Delta_constant -> Delta_defined_at_level 1
    | Delta_defined_at_level i -> Delta_defined_at_level (i + 1)
    | Delta_abstract d -> incr_delta_depth d

let incr_delta_qualifier t =
    incr_delta_depth (delta_qualifier t)

let is_unknown t = match (Subst.compress t).n with | Tm_unknown -> true | _ -> false

let rec list_elements (e:term) : option<list<term>> =
  let head, args = head_and_args (unmeta e) in
  match (un_uinst head).n, args with
  | Tm_fvar fv, _ when fv_eq_lid fv PC.nil_lid ->
      Some []
  | Tm_fvar fv, [_; (hd, _); (tl, _)] when fv_eq_lid fv PC.cons_lid ->
      Some (hd::must (list_elements tl))
  | _ ->
      None


let rec apply_last f l = match l with
   | [] -> failwith "apply_last: got empty list"
   | [a] -> [f a]
   | (x::xs) -> x :: (apply_last f xs)

let dm4f_lid ed name : lident =
    let p = path_of_lid ed.mname in
    let p' = apply_last (fun s -> "_dm4f_" ^ s ^ "_" ^ name) p in
    lid_of_path p' Range.dummyRange

let rec mk_list (typ:term) (rng:range) (l:list<term>) : term =
    let ctor l = mk (Tm_fvar (lid_as_fv l Delta_constant (Some Data_ctor))) None rng in
    let cons args pos = mk_Tm_app (mk_Tm_uinst (ctor PC.cons_lid) [U_zero]) args None pos in
    let nil  args pos = mk_Tm_app (mk_Tm_uinst (ctor PC.nil_lid)  [U_zero]) args None pos in
    List.fold_right (fun t a -> cons [iarg typ; as_arg t; as_arg a] t.pos) l (nil [iarg typ] rng)

let uvar_from_id (id : int) (t : typ)=
    mk (Tm_uvar (Unionfind.from_id id, t)) None Range.dummyRange

// Some generic equalities
let rec eqlist (eq : 'a -> 'a -> bool) (xs : list<'a>) (ys : list<'a>) : bool =
    match xs, ys with
    | [], [] -> true
    | x::xs, y::ys -> eq x y && eqlist eq xs ys
    | _ -> false

let eqsum (e1 : 'a -> 'a -> bool) (e2 : 'b -> 'b -> bool) (x : either<'a,'b>) (y : either<'a,'b>) : bool =
    match x, y with
    | Inl x, Inl y -> e1 x y
    | Inr x, Inr y -> e2 x y
    | _ -> false

let eqprod (e1 : 'a -> 'a -> bool) (e2 : 'b -> 'b -> bool) (x : 'a * 'b) (y : 'a * 'b) : bool =
    match x, y with
    | (x1,x2), (y1,y2) -> e1 x1 y1 && e2 x2 y2

let eqopt (e : 'a -> 'a -> bool) (x : option<'a>) (y : option<'a>) : bool =
    match x, y with
    | Some x, Some y -> e x y
    | _ -> false

// Checks for syntactic equality. A returned false doesn't guarantee anything.
// We DO NOT OPEN TERMS as we descend on them, and just compare their bound variable
// indices.
// TODO: GM: be smarter about lcomps, for now we just ignore them and I'm not sure that's ok.
let rec term_eq t1 t2 =
  let canon_app t =
    match t.n with
    | Tm_app _ -> let (hd, args) = head_and_args' t in
                  { t with n = Tm_app (hd, args) }
    | _ -> t
  in
  let t1 = canon_app (unmeta_safe t1) in
  let t2 = canon_app (unmeta_safe t2) in
  match t1.n, t2.n with
  | Tm_bvar x, Tm_bvar y -> x.index = y.index
  | Tm_name x, Tm_name y -> bv_eq x y
  | Tm_fvar x, Tm_fvar y -> fv_eq x y
  | Tm_uinst (t1, us1), Tm_uinst (t2, us2) ->
        eqlist eq_univs us1 us2 && term_eq t1 t2
  | Tm_constant c1, Tm_constant c2 -> eq_const c1 c2
  | Tm_type x, Tm_type y -> x = y
  | Tm_abs (b1,t1,k1), Tm_abs (b2,t2,k2) -> eqlist binder_eq b1 b2 && term_eq t1 t2 //&& eqopt (eqsum lcomp_eq residual_eq) k1 k2
  | Tm_app (f1,a1), Tm_app (f2,a2) -> term_eq f1 f2 && eqlist arg_eq a1 a2
  | Tm_arrow (b1,c1), Tm_arrow (b2,c2) -> eqlist binder_eq b1 b2 && comp_eq c1 c2
  | Tm_refine (b1,t1), Tm_refine (b2,t2) -> bv_eq b1 b2 && term_eq t1 t2
  | Tm_match (t1,bs1), Tm_match (t2,bs2) -> term_eq t1 t2 && eqlist branch_eq bs1 bs2
  | _, _ -> false // TODO missing cases
and arg_eq a1 a2 = eqprod term_eq (fun q1 q2 -> q1 = q2) a1 a2
and binder_eq b1 b2 = eqprod (fun b1 b2 -> term_eq b1.sort b2.sort) (fun q1 q2 -> q1 = q2) b1 b2
and lcomp_eq (c1:lcomp) (c2:lcomp) = false// TODO
and residual_eq (r1:residual_comp) (r2:residual_comp) = false// TODO
and comp_eq c1 c2 = match c1.n, c2.n with
  | Total (t1, u1), Total (t2, u2) -> term_eq t1 t2 // TODO what are the u's for? isn't the universe on t?
  | GTotal (t1, u1), GTotal (t2, u2) -> term_eq t1 t2
  | Comp c1, Comp c2 -> c1.comp_univs = c2.comp_univs &&
                        c1.effect_name = c2.effect_name &&
                        term_eq c1.result_typ c2.result_typ &&
                        eqlist arg_eq c1.effect_args c2.effect_args &&
                        eq_flags c1.flags c2.flags
  | _, _ -> false
and eq_flags f1 f2 = false // TODO
and branch_eq (p1,w1,t1) (p2,w2,t2) = false // TODO

let rec bottom_fold (f : term -> term) (t : term) : term =
    let ff = bottom_fold f in
    let tn = (compress t).n in
    let tn = match tn with
             | Tm_app (f, args) -> Tm_app (ff f, List.map (fun (a,q) -> (ff a, q)) args)
             // TODO: We ignore the types. Bug or feature?
             | Tm_abs (bs, t, k) -> let bs, t' = open_term bs t in
                                    let t'' = ff t' in
                                    Tm_abs (bs, close bs t'', k)
             | Tm_arrow (bs, k) -> tn //TODO
             | Tm_uinst (t, us) ->
                Tm_uinst (ff t, us)
             | _ -> tn in
    f ({ t with n = tn })

// An estimation of the size of a term, only for debugging
let rec sizeof (t:term) : int =
    match t.n with
    | Tm_delayed _ -> 1 + sizeof (compress t)
    | Tm_bvar bv
    | Tm_name bv -> 1 + sizeof bv.sort
    | Tm_uinst (t,us) -> List.length us + sizeof t
    | Tm_abs (bs, t, _) -> sizeof t  + List.fold_left (fun acc (bv, _) -> acc + sizeof bv.sort) 0 bs
    | Tm_app (hd, args) -> sizeof hd + List.fold_left (fun acc (arg, _) -> acc + sizeof arg) 0 args
    // TODO: obviously want much more
    | _ -> 1

let is_fvar lid t =
    match (un_uinst t).n with
    | Tm_fvar fv -> fv_eq_lid fv lid
    | _ -> false

let is_synth_by_tactic t =
    is_fvar PC.synth_lid t

(* Spooky behaviours are possible with this, proceed with caution *)

let mk_alien (ty : typ) (b : 'a) (s : string) (r : option<range>) : term =
    mk (Tm_meta (tun, Meta_alien (mkdyn b, s, ty))) None (match r with | Some r -> r | None -> dummyRange)

let un_alien (t : term) : dyn =
    let t = Subst.compress t in
    match t.n with
    | Tm_meta (_, Meta_alien (blob, _, _)) -> blob
    | _ -> failwith "unexpected: term was not an alien embedding"

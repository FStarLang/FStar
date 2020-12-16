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

(* A hook into FStar.Syntax.Print, only for debugging.
 * The reference is set in FStar.Main *)
let tts_f : ref<option<(term -> string)>> = U.mk_ref None
let tts t : string =
    match !tts_f with
    | None -> "<<hook unset>>"
    | Some f -> f t

let mk_discriminator lid =
  lid_of_ids (ns_of_lid lid
              @ [mk_ident (Ident.reserved_prefix ^ "is_" ^ (string_of_id (ident_of_lid lid)),
                           range_of_lid lid)])

let is_name (lid:lident) =
  let c = U.char_at (string_of_id (ident_of_lid lid)) 0 in
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
    | Tm_arrow(binders, comp) -> mk (Tm_arrow(name_binders binders, comp)) t.pos
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
            | Meta_monadic_lift _ ->
              e // don't remove the metas that really matter
            | _ -> unmeta_safe e'
            end
        | Tm_ascribed(e, _, _) -> unmeta_safe e
        | _ -> e

let unmeta_lift (t:term) : term =
  match (compress t).n with
  | Tm_meta (t, Meta_monadic_lift _) -> t
  | _ -> t

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
    | U_max _
    | U_zero -> u, 0
    | U_succ u -> let k, n = univ_kernel u in k, n+1
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
let rec compare_univs (u1:universe) (u2:universe) : int =
  let rec compare_kernel (uk1:universe) (uk2:universe) : int =
    match uk1, uk2 with
    | U_bvar _, _
    | _, U_bvar _  -> failwith "Impossible: compare_kernel bvar"

    | U_succ _, _
    | _, U_succ _  -> failwith "Impossible: compare_kernel succ"

    | U_unknown, U_unknown -> 0
    | U_unknown, _ -> -1
    | _, U_unknown ->  1

    | U_zero, U_zero -> 0
    | U_zero, _ -> -1
    | _, U_zero ->  1

    | U_name u1 , U_name u2 -> String.compare (string_of_id u1) (string_of_id u2)
    | U_name _, _ -> -1
    | _, U_name _ ->  1

    | U_unif u1, U_unif u2 -> Unionfind.univ_uvar_id u1 - Unionfind.univ_uvar_id u2
    | U_unif _, _ -> -1
    | _, U_unif _ ->  1

    (* Only remaining case *)
    | U_max us1, U_max us2 ->
      let n1 = List.length us1 in
      let n2 = List.length us2 in
      if n1 <> n2
      then n1 - n2 (* first order by increasing length *)
      else
        (* for same length, order lexicographically *)
        let copt = U.find_map (List.zip us1 us2) (fun (u1, u2) ->
             let c = compare_univs u1 u2 in
             if c<>0 then Some c
             else None) in
        begin match copt with
         | None -> 0
         | Some c -> c
        end
  in
  let uk1, n1 = univ_kernel u1 in
  let uk2, n2 = univ_kernel u2 in
  match compare_kernel uk1 uk2 with
  | 0 -> n1 - n2
  | n -> n

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

(* Duplicate of the function below not failing when universe is not provided *)
let comp_to_comp_typ_nouniv (c:comp) : comp_typ =
    match c.n with
        | Comp c -> c
        | Total (t, u_opt)
        | GTotal(t, u_opt) ->
            {comp_univs=dflt [] (map_opt u_opt (fun x -> [x]));
             effect_name=comp_effect_name c;
             result_typ=t;
             effect_args=[];
             flags=comp_flags c}

let comp_set_flags (c:comp) f =
    {c with n=Comp ({comp_to_comp_typ_nouniv c with flags=f})}

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


(*
 * For layered effects, given a (repr a is), return is
 * For wp effects, given a (unit -> M a wp), return wp
 *
 * The pattern matching is very syntactic inside this function
 * It is called from the computation types in the layered effect combinators
 *   e.g. f and g in bind
 * Layered effects typechecking code already makes sure that those types
 *   have this exact shape
 *)
let effect_indices_from_repr (repr:term) (is_layered:bool) (r:Range.range) (err:string)
: list<term> =
  let err () = Errors.raise_error (Errors.Fatal_UnexpectedEffect, err) r in
  let repr = compress repr in
  if is_layered
  then match repr.n with
       | Tm_app (_, _::is) -> is |> List.map fst
       | _ -> err ()
  else match repr.n with 
       | Tm_arrow (_, c) -> c |> comp_to_comp_typ |> (fun ct -> ct.effect_args |> List.map fst)
       | _ -> err ()

let destruct_comp c : (universe * typ * typ) =
  let wp = match c.effect_args with
    | [(wp, _)] -> wp
    | _ ->
      failwith (U.format2
        "Impossible: Got a computation %s with %s effect args"
        (string_of_lid c.effect_name)
        (c.effect_args |> List.length |> string_of_int)) in
  List.hd c.comp_univs, c.result_typ, wp

let is_named_tot c =
    match c.n with
        | Comp c -> lid_equals c.effect_name PC.effect_Tot_lid
        | Total _ -> true
        | GTotal _ -> false

let is_total_comp c =
    lid_equals (comp_effect_name c) PC.effect_Tot_lid
    || comp_flags c |> U.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_partial_return c = comp_flags c |> U.for_some (function RETURN | PARTIAL_RETURN -> true | _ -> false)

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

let is_div_effect l =
     lid_equals l PC.effect_DIV_lid
     || lid_equals l PC.effect_Div_lid
     || lid_equals l PC.effect_Dv_lid

let is_pure_or_ghost_comp c = is_pure_comp c || is_ghost_effect (comp_effect_name c)

let is_pure_or_ghost_effect l = is_pure_effect l || is_ghost_effect l

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

let rec head_of (t : term) : term =
    match (compress t).n with
    | Tm_app (t, _)
    | Tm_match (t, _)
    | Tm_abs (_, t, _)
    | Tm_ascribed (t, _, _)
    | Tm_meta (t, _) -> head_of t
    | _ -> t

let head_and_args t =
    let t = compress t in
    match t.n with
        | Tm_app(head, args) -> head, args
        | _ -> t, []

let rec head_and_args_full t =
    let t = compress t in
    match t.n with
        | Tm_app(head, args) ->
            let (head, args') = head_and_args_full head
            in (head, args'@args)
        | _ -> t, []

let un_uinst t =
    let t = Subst.compress t in
    match t.n with
        | Tm_uinst(t, _) -> Subst.compress t
        | _ -> t

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

let comp_effect_args (c:comp) :args =
  match c.n with
  | Total _
  | GTotal _ -> []
  | Comp ct -> ct.effect_args

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
  | _ -> mk (Tm_ascribed(t, k, None)) t.pos

let unfold_lazy i = must !lazy_chooser i.lkind i

let rec unlazy t =
    match (compress t).n with
    | Tm_lazy i -> unlazy <| unfold_lazy i
    | _ -> t

let unlazy_emb t =
    match (compress t).n with
    | Tm_lazy i ->
        begin match i.lkind with
        | Lazy_embedding _ -> unlazy <| unfold_lazy i
        | _ -> t
        end
    | _ -> t

let eq_lazy_kind k k' =
    match k, k' with
     | BadLazy, BadLazy
     | Lazy_bv, Lazy_bv
     | Lazy_binder, Lazy_binder
     | Lazy_optionstate, Lazy_optionstate
     | Lazy_fvar, Lazy_fvar
     | Lazy_comp, Lazy_comp
     | Lazy_env, Lazy_env
     | Lazy_proofstate, Lazy_proofstate
     | Lazy_goal, Lazy_goal
     | Lazy_sigelt, Lazy_sigelt
     | Lazy_uvar, Lazy_uvar -> true
     | _ -> false

let unlazy_as_t k t =
    match (compress t).n with
    | Tm_lazy ({lkind=k'; blob=v})
        when eq_lazy_kind k k' ->
      FStar.Dyn.undyn v
    | _ ->
      failwith "Not a Tm_lazy of the expected kind"

let mk_lazy (t : 'a) (typ : typ) (k : lazy_kind) (r : option<range>) : term =
    let rng = (match r with | Some r -> r | None -> dummyRange) in
    let i = {
        lkind = k;
        blob  = mkdyn t;
        ltyp   = typ;
        rng   = rng;
      } in
    mk (Tm_lazy i) rng

let canon_app t =
    let hd, args = head_and_args_full (unascribe t) in
    mk_Tm_app hd args t.pos

(* ---------------------------------------------------------------------- *)
(* <eq_tm> Syntactic equality of zero-order terms                         *)
(* ---------------------------------------------------------------------- *)
type eq_result =
    | Equal
    | NotEqual
    | Unknown

// Functions that we specially treat as injective, to make normalization
// (particularly of decidable equality) better. We should make sure they
// are actually proved to be injective.
let injectives =
    ["FStar.Int8.int_to_t";
     "FStar.Int16.int_to_t";
     "FStar.Int32.int_to_t";
     "FStar.Int64.int_to_t";
     "FStar.UInt8.uint_to_t";
     "FStar.UInt16.uint_to_t";
     "FStar.UInt32.uint_to_t";
     "FStar.UInt64.uint_to_t";
     "FStar.Int8.__int_to_t";
     "FStar.Int16.__int_to_t";
     "FStar.Int32.__int_to_t";
     "FStar.Int64.__int_to_t";
     "FStar.UInt8.__uint_to_t";
     "FStar.UInt16.__uint_to_t";
     "FStar.UInt32.__uint_to_t";
     "FStar.UInt64.__uint_to_t"]

let eq_inj f g =
     match f, g with
     | Equal, Equal -> Equal
     | NotEqual, _
     | _, NotEqual -> NotEqual
     | Unknown, _
     | _, Unknown -> Unknown

(* Precondition: terms are well-typed in a common environment, or this can return false positives *)
let rec eq_tm (t1:term) (t2:term) : eq_result =
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
    let equal_data (f1:fv) (args1:Syntax.args) (f2:fv) (args2:Syntax.args) =
        // we got constructors! we know they are injective and disjoint, so we can do some
        // good analysis on them
        if fv_eq f1 f2
        then (
            assert (List.length args1 = List.length args2);
            List.fold_left (fun acc ((a1, q1), (a2, q2)) ->
                                //if q1 <> q2
                                //then failwith (U.format1 "Arguments of %s mismatch on implicit qualifier\n"
                                //                (Ident.string_of_lid f1.fv_name.v));
                                //NS: 05/06/2018 ...this does not always hold
                                //    it's been succeeding because the assert is disabled in the non-debug builds
                                //assert (q1 = q2);
                                eq_inj acc (eq_tm a1 a2)) Equal <| List.zip args1 args2
        ) else NotEqual
    in
    let qual_is_inj = function
      | Some Data_ctor
      | Some (Record_ctor _) -> true
      | _ -> false
    in
    let heads_and_args_in_case_both_data :option<(fv * args * fv * args)> =
      let head1, args1 = t1 |> unmeta |> head_and_args in
      let head2, args2 = t2 |> unmeta |> head_and_args in
      match (un_uinst head1).n, (un_uinst head2).n with
      | Tm_fvar f, Tm_fvar g when qual_is_inj f.fv_qual &&
                                  qual_is_inj g.fv_qual -> Some (f, args1, g, args2)
      | _ -> None
    in
    let t1 = unmeta t1 in
    let t2 = unmeta t2 in
    match t1.n, t2.n with
    // We sometimes compare open terms, as we get alpha-equivalence
    // for free.
    | Tm_bvar bv1, Tm_bvar bv2 ->
      equal_if (bv1.index = bv2.index)

    | Tm_lazy _, _ -> eq_tm (unlazy t1) t2
    | _, Tm_lazy _ -> eq_tm t1 (unlazy t2)

    | Tm_name a, Tm_name b ->
      equal_if (bv_eq a b)

    | _ when heads_and_args_in_case_both_data |> is_some ->  //matches only when both are data constructors
      heads_and_args_in_case_both_data |> must |> (fun (f, args1, g, args2) ->
        equal_data f args1 g args2
      )

    | Tm_fvar f, Tm_fvar g -> equal_if (fv_eq f g)

    | Tm_uinst(f, us), Tm_uinst(g, vs) ->
      eq_and (eq_tm f g) (fun () -> equal_if (eq_univs_list us vs))

    // Ranges should be opaque, even to the normalizer. c.f. #1312
    | Tm_constant (Const_range _), _
    | _, Tm_constant (Const_range _) ->
      Unknown

    | Tm_constant c, Tm_constant d ->
      equal_iff (eq_const c d)

    | Tm_uvar (u1, ([], _)), Tm_uvar (u2, ([], _)) ->
      equal_if (Unionfind.equiv u1.ctx_uvar_head u2.ctx_uvar_head)

    | Tm_app (h1, args1), Tm_app (h2, args2) ->
      begin match (un_uinst h1).n, (un_uinst h2).n with
      | Tm_fvar f1, Tm_fvar f2 when fv_eq f1 f2 && List.mem (string_of_lid (lid_of_fv f1)) injectives ->
        equal_data f1 args1 f2 args2

      | _ -> // can only assert they're equal if they syntactically match, nothing else
        eq_and (eq_tm h1 h2) (fun () -> eq_args args1 args2)
      end

    | Tm_match (t1, bs1), Tm_match (t2, bs2) ->
        if List.length bs1 = List.length bs2
        then List.fold_right (fun (b1, b2) a -> eq_and a (fun () -> branch_matches b1 b2))
                             (List.zip bs1 bs2)
                             (eq_tm t1 t2)
        else Unknown

    | Tm_type u, Tm_type v ->
      equal_if (eq_univs u v)

    | Tm_quoted (t1, q1), Tm_quoted (t2, q2) ->
      eq_and (eq_quoteinfo q1 q2) (fun () -> eq_tm t1 t2)

    | Tm_refine (t1, phi1), Tm_refine (t2, phi2) ->
      eq_and (eq_tm t1.sort t2.sort) (fun () -> eq_tm phi1 phi2)

    | _ -> Unknown

and eq_quoteinfo q1 q2 =
    if q1.qkind <> q2.qkind
    then NotEqual
    else eq_antiquotes q1.antiquotes q2.antiquotes

and eq_antiquotes a1 a2 =
    match a1, a2 with
    | [], [] -> Equal
    | [], _
    | _, [] -> NotEqual
    | (x1, t1)::a1, (x2, t2)::a2 ->
      if not (bv_eq x1 x2)
      then NotEqual
      else match eq_tm t1 t2 with
           | NotEqual -> NotEqual
           | Unknown ->
             (match eq_antiquotes a1 a2 with
              | NotEqual -> NotEqual
              | _ -> Unknown)
            | Equal -> eq_antiquotes a1 a2

and branch_matches b1 b2 =
    let related_by f o1 o2 =
        match o1, o2 with
        | None, None -> true
        | Some x, Some y -> f x y
        | _, _ -> false
    in
    let (p1, w1, t1) = b1 in
    let (p2, w2, t2) = b2 in
    if eq_pat p1 p2
    then begin
         // We check the `when` branches too, even if unsupported for now
         if eq_tm t1 t2 = Equal && related_by (fun t1 t2 -> eq_tm t1 t2 = Equal) w1 w2
         then Equal
         else Unknown
         end
    else Unknown

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

let eq_aqual a1 a2 =
    match a1, a2 with
    | None, None -> Equal
    | None, _
    | _, None -> NotEqual
    | Some (Implicit b1), Some (Implicit b2) when b1=b2 -> Equal
    | Some (Meta (Arg_qualifier_meta_tac t1)), Some (Meta (Arg_qualifier_meta_tac t2))
    | Some (Meta (Arg_qualifier_meta_attr t1)), Some (Meta (Arg_qualifier_meta_attr t2)) -> eq_tm t1 t2
    | Some Equality, Some Equality -> Equal
    | _ -> NotEqual

let rec unrefine t =
  let t = compress t in
  match t.n with
  | Tm_refine(x, _) -> unrefine x.sort
  | Tm_ascribed(t, _, _) -> unrefine t
  | _ -> t

let rec is_uvar t =
  match (compress t).n with
  | Tm_uvar _ -> true
  | Tm_uinst (t, _) -> is_uvar t
  | Tm_app _ -> t |> head_and_args |> fst |> is_uvar
  | Tm_ascribed (t, _, _) -> is_uvar t
  | _ -> false

let rec is_unit t =
    match (unrefine t).n with
    | Tm_fvar fv ->
      fv_eq_lid fv PC.unit_lid
      || fv_eq_lid fv PC.squash_lid
      || fv_eq_lid fv PC.auto_squash_lid
    | Tm_app (head, _) -> is_unit head
    | Tm_uinst (t, _) -> is_unit t
    | _ -> false

let is_eqtype_no_unrefine (t:term) =
  match (Subst.compress t).n with
  | Tm_fvar fv -> fv_eq_lid fv PC.eqtype_lid
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
  | Sig_splice(lids, _)
  | Sig_bundle(_, lids) -> lids
  | Sig_inductive_typ (lid, _,  _, _, _, _)
  | Sig_effect_abbrev(lid, _, _,  _, _)
  | Sig_datacon (lid, _, _, _, _, _)
  | Sig_declare_typ (lid, _, _)
  | Sig_assume (lid, _, _) -> [lid]
  | Sig_new_effect(n) -> [n.mname]
  | Sig_sub_effect _
  | Sig_pragma _
  | Sig_fail _
  | Sig_polymonadic_bind _ -> []
  | Sig_polymonadic_subcomp _ -> []

let lid_of_sigelt se : option<lident> = match lids_of_sigelt se with
  | [l] -> Some l
  | _ -> None

let quals_of_sigelt (x: sigelt) = x.sigquals

let range_of_sigelt (x: sigelt) = x.sigrng

let range_of_lbname = function
  | Inl x -> range_of_bv  x
  | Inr fv -> range_of_lid fv.fv_name.v

let range_of_arg (hd, _) = hd.pos

let range_of_args args r =
   args |> List.fold_left (fun r a -> Range.union_ranges r (range_of_arg a)) r

let mk_app f args =
  match args with
  | [] -> f
  | _ ->
      let r = range_of_args args f.pos in
      mk (Tm_app(f, args)) r

let mk_app_binders f bs =
    mk_app f (List.map (fun (bv, aq) -> (bv_to_name bv, aq)) bs)

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

   fstar.exe  --use_hints MRefHeap.fst
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
    let itext = (string_of_id i) in
    let newi =
        if field_projector_contains_constructor itext
        then i
        else mk_ident (mk_field_projector_name_from_string (string_of_id (ident_of_lid lid)) itext, range_of_id i)
    in
    lid_of_ids (ns_of_lid lid @ [newi])

let mk_field_projector_name lid (x:bv) i =
    let nm = if Syntax.is_null_bv x
             then mk_ident("_" ^ U.string_of_int i, Syntax.range_of_bv x)
             else x.ppname in
    mk_field_projector_name_from_ident lid nm

let ses_of_sigbundle (se:sigelt) :list<sigelt> =
  match se.sigel with
  | Sig_bundle (ses, _) -> ses
  | _                   -> failwith "ses_of_sigbundle: not a Sig_bundle"

let set_uvar uv t =
  match Unionfind.find uv with
    | Some _ -> failwith (U.format1 "Changing a fixed uvar! ?%s\n" (U.string_of_int <| Unionfind.uvar_id uv))
    | _ -> Unionfind.change uv t

let qualifier_equal q1 q2 = match q1, q2 with
  | Discriminator l1, Discriminator l2 -> lid_equals l1 l2
  | Projector (l1a, l1b), Projector (l2a, l2b) -> lid_equals l1a l2a && (string_of_id l1b = string_of_id l2b)
  | RecordType (ns1, f1), RecordType (ns2, f2)
  | RecordConstructor (ns1, f1), RecordConstructor (ns2, f2) ->
      List.length ns1 = List.length ns2 && List.forall2 (fun x1 x2 -> (string_of_id x1) = (string_of_id x2)) f1 f2 &&
      List.length f1 = List.length f2 && List.forall2 (fun x1 x2 -> (string_of_id x1) = (string_of_id x2)) f1 f2
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
    match body.n with
        | Tm_abs(bs', t, lopt') ->  //AR: if the body is an Tm_abs, we can combine the binders and use lopt', ignoring lopt, since lopt will be Tot (non-informative anyway)
          mk (Tm_abs(close_binders bs@bs', t, close_lopt lopt')) t.pos
        | _ ->
          mk (Tm_abs(close_binders bs, body, close_lopt lopt)) t.pos

let arrow bs c = match bs with
  | [] -> comp_result c
  | _ -> mk (Tm_arrow(close_binders bs, Subst.close_comp bs c)) c.pos

let flat_arrow bs c =
  let t = arrow bs c in
  match (Subst.compress t).n with
  | Tm_arrow(bs, c) ->
    begin match c.n with
        | Total (tres, _) ->
          begin match (Subst.compress tres).n with
               | Tm_arrow(bs', c') -> mk (Tm_arrow(bs@bs', c')) t.pos
               | _ -> t
          end
        | _ -> t
    end
  | _ -> t

let rec canon_arrow t =
  match (compress t).n with
  | Tm_arrow (bs, c) ->
      let cn = match c.n with
               | Total (t, u) -> Total (canon_arrow t, u)
               | _ -> c.n
      in
      let c = { c with n = cn } in
      flat_arrow bs c
  | _ -> t

let refine b t = mk (Tm_refine(b, Subst.close [mk_binder b] t)) (Range.union_ranges (range_of_bv b) t.pos)
let branch b = Subst.close_branch b

let has_decreases (c:comp) : bool =
  match c.n with
  | Comp ct ->
    begin match ct.flags |> U.find_opt (function DECREASES _ -> true | _ -> false) with
    | Some (DECREASES d) -> true
    | _ -> false
    end
  | _ -> false

(*
 * AR: this function returns the binders and comp result type of an arrow type,
 *     flattening arrows of the form t -> Tot (t1 -> C), so that it returns two binders in this example
 *     the function also descends under the refinements (e.g. t -> Tot (f:(t1 -> C){phi}))
 *)
let rec arrow_formals_comp_ln k =
    let k = Subst.compress k in
    match k.n with
        | Tm_arrow(bs, c) ->
            if is_total_comp c && not (has_decreases c)
            then let bs', k = arrow_formals_comp_ln (comp_result c) in
                 bs@bs', k
            else bs, c
        | Tm_refine ({ sort = s }, _) ->
          (*
           * AR: start descending into s, but if s does not turn out to be an arrow later, we want to return k itself
           *)
          let rec aux (s:term) (k:term) =
            match (Subst.compress s).n with
            | Tm_arrow _ -> arrow_formals_comp_ln s  //found an arrow, go to the main function
            | Tm_refine ({ sort = s }, _) -> aux s k  //another refinement, descend into it, but with the same def
            | _ -> [], Syntax.mk_Total k  //return def
          in
          aux s k
        | _ -> [], Syntax.mk_Total k

let arrow_formals_comp k =
    let bs, c = arrow_formals_comp_ln k in
    Subst.open_comp bs c

let arrow_formals_ln k =
    let bs, c = arrow_formals_comp_ln k in
    bs, comp_result c

let arrow_formals k =
    let bs, c = arrow_formals_comp k in
    bs, comp_result c

(* let_rec_arity e f:
    if `f` is a let-rec bound name in e
    then this function returns
        1. f's type
        2. the natural arity of f, i.e., the number of arguments including universes on which the let rec is defined
        3. a list of booleans, one for each argument above, where the boolean is true iff the variable appears in the f's decreases clause
    This is used by NBE for detecting potential non-terminating loops
*)
let let_rec_arity (lb:letbinding) : int * option<(list<bool>)> =
    let rec arrow_until_decreases k =
        let k = Subst.compress k in
        match k.n with
        | Tm_arrow(bs, c) ->
            let bs, c = Subst.open_comp bs c in
            let ct = comp_to_comp_typ c in
           (match
                ct.flags |> U.find_opt (function DECREASES _ -> true | _ -> false)
            with
            | Some (DECREASES d) ->
                bs, Some d
            | _ ->
                if is_total_comp c
                then let bs', d = arrow_until_decreases (comp_result c) in
                      bs@bs', d
                else bs, None)

        | Tm_refine ({ sort = k }, _) ->
            arrow_until_decreases k

        | _ -> [], None
    in
    let bs, dopt = arrow_until_decreases lb.lbtyp in
    let n_univs = List.length lb.lbunivs in
    n_univs + List.length bs,
    U.map_opt dopt (fun d ->
       let d_bvs = FStar.Syntax.Free.names d in
       Common.tabulate n_univs (fun _ -> false)
       @ (bs |> List.map (fun (x, _) -> U.set_mem x d_bvs)))


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

let remove_inacc (t:term) : term =
    let no_acc ((b, aq) : binder) : binder =
      let aq =
        match aq with
        | Some (Implicit true) -> Some (Implicit false)
        | _ -> aq
      in
      (b, aq)
    in
    let bs, c = arrow_formals_comp_ln t in
    match bs with
    | [] -> t
    | _ -> mk (Tm_arrow (List.map no_acc bs, c)) t.pos

let mk_letbinding (lbname : either<bv,fv>) univ_vars typ eff def lbattrs pos =
    {lbname=lbname;
     lbunivs=univ_vars;
     lbtyp=typ;
     lbeff=eff;
     lbdef=def;
     lbattrs=lbattrs;
     lbpos=pos;
    }


let close_univs_and_mk_letbinding recs lbname univ_vars typ eff def attrs pos =
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
    mk_letbinding lbname univ_vars typ eff def attrs pos

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
  | Tm_fvar fv -> PC.is_tuple_constructor_string (string_of_lid fv.fv_name.v)
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

let is_fstar_tactics_by_tactic t =
    match (un_uinst t).n with
    | Tm_fvar fv -> fv_eq_lid fv PC.by_tactic_lid
    | _ -> false

let is_builtin_tactic md =
  let path = Ident.path_of_lid md in
  if List.length(path) > 2 then
    match fst (List.splitAt 2 path) with
    | ["FStar"; "Tactics"]
    | ["FStar"; "Reflection"] -> true
    | _ -> false
  else false

(********************************************************************************)
(*********************** Constructors of common terms  **************************)
(********************************************************************************)

let ktype  : term = mk (Tm_type(U_unknown)) dummyRange
let ktype0 : term = mk (Tm_type(U_zero)) dummyRange

//Type(u), where u is a new universe unification variable
let type_u () : typ * universe =
    let u = U_unif <| Unionfind.univ_fresh Range.dummyRange in
    mk (Tm_type u) dummyRange, u

// works on anything, really
let attr_eq a a' =
   match eq_tm a a' with
   | Equal -> true
   | _ -> false

let attr_substitute =
    mk (Tm_fvar (lid_as_fv (lid_of_path ["FStar"; "Pervasives"; "Substitute"] Range.dummyRange)
                           delta_constant
                           None))
       Range.dummyRange

let exp_true_bool : term = mk (Tm_constant (Const_bool true)) dummyRange
let exp_false_bool : term = mk (Tm_constant (Const_bool false)) dummyRange
let exp_unit : term = mk (Tm_constant (Const_unit)) dummyRange
(* Makes an (unbounded) integer from its string repr. *)
let exp_int s : term = mk (Tm_constant (Const_int (s,None))) dummyRange
let exp_char c : term = mk (Tm_constant (Const_char c)) dummyRange
let exp_string s : term = mk (Tm_constant (Const_string (s, dummyRange))) dummyRange

let fvar_const l = fvar l delta_constant None
let tand    = fvar_const PC.and_lid
let tor     = fvar_const PC.or_lid
let timp    = fvar PC.imp_lid (Delta_constant_at_level 1) None //NS delta: wrong? level 2
let tiff    = fvar PC.iff_lid (Delta_constant_at_level 2) None //NS delta: wrong? level 3
let t_bool  = fvar_const PC.bool_lid
let b2t_v   = fvar_const PC.b2t_lid
let t_not   = fvar_const PC.not_lid
// These are `True` and `False`, not the booleans
let t_false = fvar_const PC.false_lid //NS delta: wrong? should be Delta_constant_at_level 2
let t_true  = fvar_const PC.true_lid  //NS delta: wrong? should be Delta_constant_at_level 2
let tac_opaque_attr = exp_string "tac_opaque"
let dm4f_bind_range_attr = fvar_const PC.dm4f_bind_range_attr
let tcdecltime_attr = fvar_const PC.tcdecltime_attr
let inline_let_attr = fvar_const PC.inline_let_attr
let rename_let_attr = fvar_const PC.rename_let_attr

let t_ctx_uvar_and_sust = fvar_const PC.ctx_uvar_and_subst_lid

let mk_conj_opt phi1 phi2 = match phi1 with
  | None -> Some phi2
  | Some phi1 -> Some (mk (Tm_app(tand, [as_arg phi1; as_arg phi2])) (Range.union_ranges phi1.pos phi2.pos))
let mk_binop op_t phi1 phi2 = mk (Tm_app(op_t, [as_arg phi1; as_arg phi2])) (Range.union_ranges phi1.pos phi2.pos)
let mk_neg phi = mk (Tm_app(t_not, [as_arg phi])) phi.pos
let mk_conj phi1 phi2 = mk_binop tand phi1 phi2
let mk_conj_l phi = match phi with
    | [] -> fvar PC.true_lid delta_constant None //NS delta: wrong, see a t_true
    | hd::tl -> List.fold_right mk_conj tl hd
let mk_disj phi1 phi2 = mk_binop tor phi1 phi2
let mk_disj_l phi = match phi with
    | [] -> t_false
    | hd::tl -> List.fold_right mk_disj tl hd
let mk_imp phi1 phi2 : term = mk_binop timp phi1 phi2
let mk_iff phi1 phi2 : term = mk_binop tiff phi1 phi2
let b2t e = mk (Tm_app(b2t_v, [as_arg e])) e.pos//implicitly coerce a boolean to a type
let unb2t (e:term) : option<term> =
    let hd, args = head_and_args e in
    match (compress hd).n, args with
    | Tm_fvar fv, [(e, _)] when fv_eq_lid fv PC.b2t_lid -> Some e
    | _ -> None

let is_t_true t =
     match (unmeta t).n with
     | Tm_fvar fv -> fv_eq_lid fv PC.true_lid
     | _ -> false
let mk_conj_simp t1 t2 =
    if is_t_true t1 then t2
    else if is_t_true t2 then t1
    else mk_conj t1 t2
let mk_disj_simp t1 t2 =
    if is_t_true t1 then t_true
    else if is_t_true t2 then t_true
    else mk_disj t1 t2

let teq = fvar_const PC.eq2_lid
let mk_untyped_eq2 e1 e2 = mk (Tm_app(teq, [as_arg e1; as_arg e2])) (Range.union_ranges e1.pos e2.pos)
let mk_eq2 (u:universe) (t:typ) (e1:term) (e2:term) : term =
    let eq_inst = mk_Tm_uinst teq [u] in
    mk (Tm_app(eq_inst, [iarg t; as_arg e1; as_arg e2])) (Range.union_ranges e1.pos e2.pos)

let mk_has_type t x t' =
    let t_has_type = fvar_const PC.has_type_lid in //TODO: Fix the U_zeroes below!
    let t_has_type = mk (Tm_uinst(t_has_type, [U_zero; U_zero])) dummyRange in
    mk (Tm_app(t_has_type, [iarg t; as_arg x; as_arg t'])) dummyRange

let mk_with_type u t e =
    let t_with_type = fvar PC.with_type_lid delta_equational None in
    let t_with_type = mk (Tm_uinst(t_with_type, [u])) dummyRange in
    mk (Tm_app(t_with_type, [iarg t; as_arg e])) dummyRange

let lex_t    = fvar_const PC.lex_t_lid
let lex_top :term = fvar PC.lextop_lid delta_constant (Some Data_ctor) //NS delta: ok
let lex_pair = fvar PC.lexcons_lid delta_constant (Some Data_ctor) //NS delta: ok
let tforall  = fvar PC.forall_lid (Delta_constant_at_level 1) None //NS delta: wrong level 2
let t_haseq   = fvar PC.haseq_lid delta_constant None //NS delta: wrong Delta_abstract (Delta_constant_at_level 0)?

let decidable_eq = fvar_const PC.op_Eq
let mk_decidable_eq t e1 e2 = 
  mk (Tm_app (decidable_eq, [iarg t; as_arg e1; as_arg e2])) (Range.union_ranges e1.pos e2.pos)
let b_and = fvar_const PC.op_And
let mk_and e1 e2 =
  mk (Tm_app (b_and, [as_arg e1; as_arg e2])) (Range.union_ranges e1.pos e2.pos)
let mk_and_l l = match l with
    | [] -> exp_true_bool
    | hd::tl -> List.fold_left mk_and hd tl

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

let mk_forall_aux fa x body =
  mk (Tm_app(fa, [ iarg (x.sort);
                   as_arg (abs [mk_binder x] body (Some (residual_tot ktype0)))])) dummyRange

let mk_forall_no_univ (x:bv) (body:typ) : typ =
  mk_forall_aux tforall x body

let mk_forall (u:universe) (x:bv) (body:typ) : typ =
  let tforall = mk_Tm_uinst tforall [u] in
  mk_forall_aux tforall x body

let close_forall_no_univs bs f =
  List.fold_right (fun b f -> if Syntax.is_null_binder b then f else mk_forall_no_univ (fst b) f) bs f

let is_wild_pat p =
    match p.v with
    | Pat_wild _ -> true
    | _ -> false

let if_then_else b t1 t2 =
    let then_branch = (withinfo (Pat_constant (Const_bool true)) t1.pos, None, t1) in
    let else_branch = (withinfo (Pat_constant (Const_bool false)) t2.pos, None, t2) in
    mk (Tm_match(b, [then_branch; else_branch])) (Range.union_ranges b.pos (Range.union_ranges t1.pos t2.pos))

//////////////////////////////////////////////////////////////////////////////////////
// Operations on squashed and other irrelevant/sub-singleton types
//////////////////////////////////////////////////////////////////////////////////////
let mk_squash u p =
    let sq = fvar PC.squash_lid (Delta_constant_at_level 1) None in //NS delta: ok
    mk_app (mk_Tm_uinst sq [u]) [as_arg p]

let mk_auto_squash u p =
    let sq = fvar PC.auto_squash_lid (Delta_constant_at_level 2) None in //NS delta: ok
    mk_app (mk_Tm_uinst sq [u]) [as_arg p]

let un_squash t =
    let head, args = head_and_args t in
    let head = unascribe head in
    let head = un_uinst head in
    match (compress head).n, args with
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

let is_squash t =
    let head, args = head_and_args t in
    match (Subst.compress head).n, args with
    | Tm_uinst({n=Tm_fvar fv}, [u]), [(t, _)]
        when Syntax.fv_eq_lid fv PC.squash_lid ->
        Some (u, t)
    | _ -> None


let is_auto_squash t =
    let head, args = head_and_args t in
    match (Subst.compress head).n, args with
    | Tm_uinst({n=Tm_fvar fv}, [u]), [(t, _)]
        when Syntax.fv_eq_lid fv PC.auto_squash_lid ->
        Some (u, t)
    | _ -> None

let is_sub_singleton t =
    let head, _ = head_and_args (unmeta t) in
    match (un_uinst head).n with
    | Tm_fvar fv ->
          Syntax.fv_eq_lid fv PC.squash_lid
        || Syntax.fv_eq_lid fv PC.auto_squash_lid
        || Syntax.fv_eq_lid fv PC.and_lid
        || Syntax.fv_eq_lid fv PC.or_lid
        || Syntax.fv_eq_lid fv PC.not_lid
        || Syntax.fv_eq_lid fv PC.imp_lid
        || Syntax.fv_eq_lid fv PC.iff_lid
        || Syntax.fv_eq_lid fv PC.ite_lid
        || Syntax.fv_eq_lid fv PC.exists_lid
        || Syntax.fv_eq_lid fv PC.forall_lid
        || Syntax.fv_eq_lid fv PC.true_lid
        || Syntax.fv_eq_lid fv PC.false_lid
        || Syntax.fv_eq_lid fv PC.eq2_lid
        || Syntax.fv_eq_lid fv PC.eq3_lid
        || Syntax.fv_eq_lid fv PC.b2t_lid
        //these are an uninterpreted predicates
        //which we are better off treating as sub-singleton
        || Syntax.fv_eq_lid fv PC.haseq_lid
        || Syntax.fv_eq_lid fv PC.has_type_lid
        || Syntax.fv_eq_lid fv PC.precedes_lid
    | _ -> false

let arrow_one_ln (t:typ) : option<(binder * comp)> =
    match (compress t).n with
    | Tm_arrow ([], c) ->
        failwith "fatal: empty binders on arrow?"
    | Tm_arrow ([b], c) ->
        Some (b, c)
    | Tm_arrow (b::bs, c) ->
        Some (b, mk_Total (arrow bs c))
    | _ ->
        None

let arrow_one (t:typ) : option<(binder * comp)> =
    bind_opt (arrow_one_ln t) (fun (b, c) ->
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

(* destruct_typ_as_formula can be hot; these tables are defined
   here to ensure they are constructed only once in the executing
   binary

   the tables encode arity -> match_lid -> output_lid
   *)
let destruct_base_table =
  let f x = (x,x) in
  [ (0, [f PC.true_lid; f PC.false_lid]);
    (2, [f PC.and_lid; f PC.or_lid; f PC.imp_lid; f PC.iff_lid; f PC.eq2_lid; f PC.eq3_lid]);
    (1, [f PC.not_lid]);
    (3, [f PC.ite_lid; f PC.eq2_lid]);
    (4, [f PC.eq3_lid])
  ]

let destruct_sq_base_table =
  [ (2, [(PC.c_and_lid, PC.and_lid); (PC.c_or_lid, PC.or_lid);
         (PC.c_eq2_lid, PC.c_eq2_lid); (PC.c_eq3_lid, PC.c_eq3_lid)]);
    (3, [(PC.c_eq2_lid, PC.c_eq2_lid)]);
    (4, [(PC.c_eq3_lid, PC.c_eq3_lid)]);
    (0, [(PC.c_true_lid, PC.true_lid); (PC.c_false_lid, PC.false_lid)])
  ]

let destruct_typ_as_formula f : option<connective> =
    let rec unmeta_monadic f =
      let f = Subst.compress f in
      match f.n with
      | Tm_meta(t, Meta_monadic _)
      | Tm_meta(t, Meta_monadic_lift _) -> unmeta_monadic t
      | _ -> f in
    let lookup_arity_lid table target_lid args =
        let arg_len = List.length args in
        let aux (arity, lids) =
            if arg_len = arity
            then U.find_map lids
                (fun (lid, out_lid) ->
                  if lid_equals target_lid lid
                  then Some (BaseConn (out_lid, args))
                  else None)
            else None
        in
        U.find_map table aux
    in
    let destruct_base_conn t =
        let hd, args = head_and_args t in
        match (un_uinst hd).n with
        | Tm_fvar fv -> lookup_arity_lid destruct_base_table fv.fv_name.v args
        | _ -> None
    in
    let destruct_sq_base_conn t =
        bind_opt (un_squash t) (fun t ->
        let hd, args = head_and_args_full t in
        match (un_uinst hd).n with
        | Tm_fvar fv -> lookup_arity_lid destruct_sq_base_table fv.fv_name.v args
        | _ -> None
        )
    in
    let patterns t =
        let t = compress t in
        match t.n with
            | Tm_meta(t, Meta_pattern (_, pats)) -> pats, compress t
            | _ -> [], t
    in
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
    let rec destruct_sq_forall t =
        bind_opt (un_squash t) (fun t ->
        match arrow_one t with
        | Some (b, c) ->
            if not (is_tot_or_gtot_comp c)
            then None
            else
                let q = (comp_to_comp_typ_nouniv c).result_typ in
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
        let hd, args = head_and_args_full t in
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

let action_as_lb eff_lid a pos =
  let lb =
    close_univs_and_mk_letbinding None
      (* Actions are set to Delta_constant since they need an explicit reify to be unfolded *)
      (Inr (lid_as_fv a.action_name delta_equational None))
      a.action_univs
      (arrow a.action_params (mk_Total a.action_typ))
      PC.effect_Tot_lid
      (abs a.action_params a.action_defn None)
      []
      pos
  in
  { sigel = Sig_let((false, [lb]), [a.action_name]);
    sigrng = a.action_defn.pos;
    sigquals = [Visible_default ; Action eff_lid];
    sigmeta = default_sigmeta;
    sigattrs = [];
    sigopts = None; }

(* Some reification utilities *)
let mk_reify t =
    let reify_ = mk (Tm_constant(FStar.Const.Const_reify)) t.pos in
    mk (Tm_app(reify_, [as_arg t])) t.pos

let mk_reflect t =
    let reflect_ = mk (Tm_constant(FStar.Const.Const_reflect (Ident.lid_of_str "Bogus.Effect"))) t.pos in
    mk (Tm_app(reflect_, [as_arg t])) t.pos

(* Some utilities for clients who wish to build top-level bindings and keep
 * their delta-qualifiers correct (e.g. dmff). *)

let rec delta_qualifier t =
    let t = Subst.compress t in
    match t.n with
        | Tm_delayed _ -> failwith "Impossible"
        | Tm_lazy i -> delta_qualifier (unfold_lazy i)
        | Tm_fvar fv -> fv.fv_delta
        | Tm_bvar _
        | Tm_name _
        | Tm_match _
        | Tm_uvar _
        | Tm_unknown -> delta_equational
        | Tm_type _
        | Tm_quoted _
        | Tm_constant _
        | Tm_arrow _ -> delta_constant
        | Tm_uinst(t, _)
        | Tm_refine({sort=t}, _)
        | Tm_meta(t, _)
        | Tm_ascribed(t, _, _)
        | Tm_app(t, _)
        | Tm_abs(_, t, _)
        | Tm_let(_, t) -> delta_qualifier t

let rec incr_delta_depth d =
    match d with
    | Delta_constant_at_level i   -> Delta_constant_at_level (i + 1)
    | Delta_equational_at_level i -> Delta_equational_at_level (i + 1)
    | Delta_abstract d            -> incr_delta_depth d

let incr_delta_qualifier t =
    incr_delta_depth (delta_qualifier t)

let is_unknown t = match (Subst.compress t).n with | Tm_unknown -> true | _ -> false

let rec apply_last f l = match l with
   | [] -> failwith "apply_last: got empty list"
   | [a] -> [f a]
   | (x::xs) -> x :: (apply_last f xs)

let dm4f_lid ed name : lident =
    let p = path_of_lid ed.mname in
    let p' = apply_last (fun s -> "_dm4f_" ^ s ^ "_" ^ name) p in
    lid_of_path p' Range.dummyRange

let mk_list (typ:term) (rng:range) (l:list<term>) : term =
    let ctor l = mk (Tm_fvar (lid_as_fv l delta_constant (Some Data_ctor))) rng in
    let cons args pos = mk_Tm_app (mk_Tm_uinst (ctor PC.cons_lid) [U_zero]) args pos in
    let nil  args pos = mk_Tm_app (mk_Tm_uinst (ctor PC.nil_lid)  [U_zero]) args pos in
    List.fold_right (fun t a -> cons [iarg typ; as_arg t; as_arg a] t.pos) l (nil [iarg typ] rng)

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
// indices. We also ignore some parts of the syntax such universes and most annotations.

// Setting this ref to `true` causes messages to appear when
// some discrepancy was found. This is useful when trying to debug
// why term_eq is returning `false`. This reference is `one shot`,
// it will disable itself when term_eq returns, but in that single run
// it will provide a (backwards) trace of where the discrepancy apperared.
//
// Use at your own peril, and please keep it if there's no good
// reason against it, so I don't have to go crazy again.
let debug_term_eq = U.mk_ref false

let check msg cond =
  if cond
  then true
  else (if !debug_term_eq then U.print1 ">>> term_eq failing: %s\n" msg; false)

let fail msg = check msg false

let rec term_eq_dbg (dbg : bool) t1 t2 =
  let t1 = canon_app (unmeta_safe t1) in
  let t2 = canon_app (unmeta_safe t2) in
  match (compress (un_uinst t1)).n, (compress (un_uinst t2)).n with
  | Tm_uinst _, _
  | _, Tm_uinst _
        (* -> eqlist eq_univs us1 us2 && term_eq_dbg dbg t1 t2 *)
  | Tm_delayed _, _
  | _, Tm_delayed _
  | Tm_ascribed _, _
  | _, Tm_ascribed _ ->
    failwith "term_eq: impossible, should have been removed"

  | Tm_bvar x      , Tm_bvar y      -> check "bvar"  (x.index = y.index)
  | Tm_name x      , Tm_name y      -> check "name"  (x.index = y.index)
  | Tm_fvar x      , Tm_fvar y      -> check "fvar"  (fv_eq x y)
  | Tm_constant c1 , Tm_constant c2 -> check "const" (eq_const c1 c2)
  | Tm_type _, Tm_type _ -> true // x = y

  | Tm_abs (b1,t1,k1), Tm_abs (b2,t2,k2) ->
    (check "abs binders"  (eqlist (binder_eq_dbg dbg) b1 b2)) &&
    (check "abs bodies"   (term_eq_dbg dbg t1 t2))
    //&& eqopt (eqsum lcomp_eq_dbg dbg residual_eq) k1 k2

  | Tm_arrow (b1,c1), Tm_arrow (b2,c2) ->
    (check "arrow binders" (eqlist (binder_eq_dbg dbg) b1 b2)) &&
    (check "arrow comp"    (comp_eq_dbg dbg c1 c2))

  | Tm_refine (b1,t1), Tm_refine (b2,t2) ->
    (check "refine bv sort" (term_eq_dbg dbg b1.sort b2.sort)) &&
    (check "refine formula" (term_eq_dbg dbg t1 t2))

  | Tm_app (f1, a1), Tm_app (f2, a2) ->
    (check "app head"  (term_eq_dbg dbg f1 f2)) &&
    (check "app args"  (eqlist (arg_eq_dbg dbg) a1 a2))

  | Tm_match (t1,bs1), Tm_match (t2,bs2) ->
    (check "match head"     (term_eq_dbg dbg t1 t2)) &&
    (check "match branches" (eqlist (branch_eq_dbg dbg) bs1 bs2))

  | Tm_lazy _, _ -> check "lazy_l" (term_eq_dbg dbg (unlazy t1) t2)
  | _, Tm_lazy _ -> check "lazy_r" (term_eq_dbg dbg t1 (unlazy t2))

  | Tm_let ((b1, lbs1), t1), Tm_let ((b2, lbs2), t2) ->
    (check "let flag"  (b1 = b2)) &&
    (check "let lbs"   (eqlist (letbinding_eq_dbg dbg) lbs1 lbs2)) &&
    (check "let body"  (term_eq_dbg dbg t1 t2))

  | Tm_uvar (u1, _), Tm_uvar (u2, _) ->
    (* These must have alreade been resolved, so we check that
     * they are indeed the same uvar *)
    check "uvar" (u1.ctx_uvar_head = u2.ctx_uvar_head)

  | Tm_quoted (qt1, qi1), Tm_quoted (qt2, qi2) ->
    (check "tm_quoted qi"      (eq_quoteinfo qi1 qi2 = Equal)) &&
    (check "tm_quoted payload" (term_eq_dbg dbg qt1 qt2))

  | Tm_meta (t1, m1), Tm_meta (t2, m2) ->
    begin match m1, m2 with
    | Meta_monadic (n1, ty1), Meta_monadic (n2, ty2) ->
        (check "meta_monadic lid"   (lid_equals n1 n2)) &&
        (check "meta_monadic type"  (term_eq_dbg dbg ty1 ty2))

    | Meta_monadic_lift (s1, t1, ty1), Meta_monadic_lift (s2, t2, ty2) ->
        (check "meta_monadic_lift src"   (lid_equals s1 s2)) &&
        (check "meta_monadic_lift tgt"   (lid_equals t1 t2)) &&
        (check "meta_monadic_lift type"  (term_eq_dbg dbg ty1 ty2))

    | _ -> fail "metas"
    end

  // ?
  | Tm_unknown, _
  | _, Tm_unknown -> fail "unk"

  | Tm_bvar _, _
  | Tm_name _, _
  | Tm_fvar _, _
  | Tm_constant _, _
  | Tm_type _, _
  | Tm_abs _, _
  | Tm_arrow _, _
  | Tm_refine _, _
  | Tm_app _, _
  | Tm_match _, _
  | Tm_let _, _
  | Tm_uvar _, _
  | Tm_meta _, _
  | _, Tm_bvar _
  | _, Tm_name _
  | _, Tm_fvar _
  | _, Tm_constant _
  | _, Tm_type _
  | _, Tm_abs _
  | _, Tm_arrow _
  | _, Tm_refine _
  | _, Tm_app _
  | _, Tm_match _
  | _, Tm_let _
  | _, Tm_uvar _
  | _, Tm_meta _     -> fail "bottom"

and arg_eq_dbg (dbg : bool) a1 a2 =
    eqprod (fun t1 t2 -> check "arg tm" (term_eq_dbg dbg t1 t2))
           (fun q1 q2 -> check "arg qual"  (eq_aqual q1 q2 = Equal))
           a1 a2
and binder_eq_dbg (dbg : bool) b1 b2 =
    eqprod (fun b1 b2 -> check "binder sort"  (term_eq_dbg dbg b1.sort b2.sort))
           (fun q1 q2 -> check "binder qual"  (eq_aqual q1 q2 = Equal))
           b1 b2
and comp_eq_dbg (dbg : bool) c1 c2 =
    let c1 = comp_to_comp_typ_nouniv c1 in
    let c2 = comp_to_comp_typ_nouniv c2 in
    (check "comp eff"  (lid_equals c1.effect_name c2.effect_name)) &&
    //(check "comp univs"  (c1.comp_univs = c2.comp_univs)) &&
    (check "comp result typ"  (term_eq_dbg dbg c1.result_typ c2.result_typ)) &&
    (* (check "comp args"  (eqlist arg_eq_dbg dbg c1.effect_args c2.effect_args)) && *)
    true //eq_flags c1.flags c2.flags
and branch_eq_dbg (dbg : bool) (p1,w1,t1) (p2,w2,t2) =
    (check "branch pat"  (eq_pat p1 p2)) &&
    (check "branch body"  (term_eq_dbg dbg t1 t2))
    && (check "branch when" (
        match w1, w2 with
        | Some x, Some y -> term_eq_dbg dbg x y
        | None, None -> true
        | _ -> false))

and letbinding_eq_dbg (dbg : bool) (lb1 : letbinding) lb2 =
    // bvars have no meaning here, so we just check they have the same name
    (check "lb bv"   (eqsum (fun bv1 bv2 -> true) fv_eq lb1.lbname lb2.lbname)) &&
    (* (check "lb univs"  (lb1.lbunivs = lb2.lbunivs)) *)
    (check "lb typ"  (term_eq_dbg dbg lb1.lbtyp lb2.lbtyp)) &&
    (check "lb def"  (term_eq_dbg dbg lb1.lbdef lb2.lbdef))
    // Ignoring eff and attrs..

let term_eq t1 t2 =
    let r = term_eq_dbg !debug_term_eq t1 t2 in
    debug_term_eq := false;
    r

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

let has_attribute (attrs:list<Syntax.attribute>) (attr:lident) =
     FStar.Util.for_some (is_fvar attr) attrs

(* Checks whether the list of attrs contains an application of `attr`, and
 * returns the arguments if so. If there's more than one, the first one
 * takes precedence. *)
let get_attribute (attr : lident) (attrs:list<Syntax.attribute>) : option<args> =
    List.tryPick (fun t ->
        let head, args = head_and_args t in
        match (Subst.compress head).n with
        | Tm_fvar fv when fv_eq_lid fv attr -> Some args
        | _ -> None) attrs

let remove_attr (attr : lident) (attrs:list<attribute>) : list<attribute> =
    List.filter (fun a -> not (is_fvar attr a)) attrs

///////////////////////////////////////////
// Setting pragmas
///////////////////////////////////////////
let process_pragma p r =
    FStar.Errors.set_option_warning_callback_range (Some r);
    let set_options s =
      match Options.set_options s with
      | Getopt.Success -> ()
      | Getopt.Help  ->
        Errors.raise_error
                (Errors.Fatal_FailToProcessPragma,
                 "Failed to process pragma: use 'fstar --help' to see which options are available")
                r
      | Getopt.Error s ->
        Errors.raise_error
                (Errors.Fatal_FailToProcessPragma, "Failed to process pragma: " ^ s) r
    in
    match p with
    | LightOff ->
      Options.set_ml_ish()

    | SetOptions o ->
      set_options o

    | ResetOptions sopt ->
      Options.restore_cmd_line_options false |> ignore;
      begin match sopt with
      | None -> ()
      | Some s -> set_options s
      end

    | PushOptions sopt ->
      Options.internal_push ();
      begin match sopt with
      | None -> ()
      | Some s -> set_options s
      end

    | RestartSolver ->
      ()

    | PopOptions ->
      if Options.internal_pop ()
      then ()
      else Errors.raise_error (Errors.Fatal_FailToProcessPragma, "Cannot #pop-options, stack would become empty") r

///////////////////////////////////////////////////////////////////////////////////////////////
let rec unbound_variables tm :  list<bv> =
    let t = Subst.compress tm in
    match t.n with
      | Tm_delayed _ -> failwith "Impossible"

      | Tm_name x ->
        []

      | Tm_uvar _ ->
        []

      | Tm_type u ->
        []

      | Tm_bvar x ->
        [x]

      | Tm_fvar _
      | Tm_constant _
      | Tm_lazy _
      | Tm_unknown ->
        []

      | Tm_uinst(t, us) ->
        unbound_variables t

      | Tm_abs(bs, t, _) ->
        let bs, t = Subst.open_term bs t in
        List.collect (fun (b, _) -> unbound_variables b.sort) bs
        @ unbound_variables t

      | Tm_arrow (bs, c) ->
        let bs, c = Subst.open_comp bs c in
        List.collect (fun (b, _) -> unbound_variables b.sort) bs
        @ unbound_variables_comp c

      | Tm_refine(b, t) ->
        let bs, t = Subst.open_term [b, None] t in
        List.collect (fun (b, _) -> unbound_variables b.sort) bs
        @ unbound_variables t

      | Tm_app(t, args) ->
        List.collect (fun (x, _) -> unbound_variables x) args
        @ unbound_variables t

      | Tm_match(t, pats) ->
        unbound_variables t
        @ (pats |> List.collect (fun br ->
                 let p, wopt, t = Subst.open_branch br in
                 unbound_variables t
                 @ (match wopt with None -> [] | Some t -> unbound_variables t)))

      | Tm_ascribed(t1, asc, _) ->
        unbound_variables t1
        @ (match fst asc with
           | Inl t2 -> unbound_variables t2
           | Inr c2 -> unbound_variables_comp c2)
        @ (match snd asc with
           | None -> []
           | Some tac -> unbound_variables tac)

      | Tm_let ((false, [lb]), t) ->
        unbound_variables lb.lbtyp
        @ unbound_variables lb.lbdef
        @ (match lb.lbname with
           | Inr _ -> unbound_variables t
           | Inl bv -> let _, t= Subst.open_term [bv, None] t in
                       unbound_variables t)

      | Tm_let ((_, lbs), t) ->
        let lbs, t = Subst.open_let_rec lbs t in
        unbound_variables t
        @ List.collect (fun lb -> unbound_variables lb.lbtyp @ unbound_variables lb.lbdef) lbs

      | Tm_quoted (tm, qi) ->
        begin match qi.qkind with
        | Quote_static  -> []
        | Quote_dynamic -> unbound_variables tm
        end

      | Tm_meta(t, m) ->
        unbound_variables t
        @ (match m with
           | Meta_pattern (_, args) ->
             List.collect (List.collect (fun (a, _) -> unbound_variables a)) args

           | Meta_monadic_lift(_, _, t')
           | Meta_monadic(_, t') ->
             unbound_variables t'

           | Meta_labeled _
           | Meta_desugared _
           | Meta_named _ -> [])


and unbound_variables_comp c =
    match c.n with
    | GTotal (t, _)
    | Total (t, _) ->
      unbound_variables t

    | Comp ct ->
      unbound_variables ct.result_typ
      @ List.collect (fun (a, _) -> unbound_variables a) ct.effect_args

let extract_attr' (attr_lid:lid) (attrs:list<term>) : option<(list<term> * args)> =
    let rec aux acc attrs =
        match attrs with
        | [] -> None
        | h::t ->
            let head, args = head_and_args h in
            begin match (compress head).n with
            | Tm_fvar fv when fv_eq_lid fv attr_lid ->
                let attrs' = List.rev_acc acc t in
                Some (attrs', args)
            | _ ->
                aux (h::acc) t
            end
    in
    aux [] attrs

let extract_attr (attr_lid:lid) (se:sigelt) : option<(sigelt * args)> =
    match extract_attr' attr_lid se.sigattrs with
    | None -> None
    | Some (attrs', t) -> Some ({ se with sigattrs = attrs' }, t)

(* Utilities for working with Lemma's decorated with SMTPat *)
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

let rec list_elements (e:term) : option<list<term>> =
  let head, args = head_and_args (unmeta e) in
  match (un_uinst head).n, args with
  | Tm_fvar fv, _ when fv_eq_lid fv PC.nil_lid ->
      Some []
  | Tm_fvar fv, [_; (hd, _); (tl, _)] when fv_eq_lid fv PC.cons_lid ->
      Some (hd::must (list_elements tl))
  | _ ->
      None

(* Takes a term of shape `fun x -> e` and returns `e` when
`x` is not free in it. If it is free or the term
has some other shape just apply it to `()`. *)
let unthunk (t:term) : term =
    match (compress t).n with
    | Tm_abs ([b], e, _) ->
        let bs, e = open_term [b] e in
        let b = List.hd bs in
        if is_free_in (fst b) e
        then mk_app t [as_arg exp_unit]
        else e
    | _ ->
        mk_app t [as_arg exp_unit]

let unthunk_lemma_post t =
    unthunk t

let smt_lemma_as_forall (t:term) (universe_of_binders: binders -> list<universe>)
   : term
   =
    let list_elements (e:term) : list<term> =
      match list_elements e with
      | Some l -> l
      | None ->
        Errors.log_issue e.pos
          (Errors.Warning_NonListLiteralSMTPattern,
            "SMT pattern is not a list literal; ignoring the pattern");
        []
    in

    let one_pat p =
        let head, args = unmeta p |> head_and_args in
        match (un_uinst head).n, args with
        | Tm_fvar fv, [(_, _); arg]
            when fv_eq_lid fv PC.smtpat_lid ->
          arg
        | _ ->
            Errors.raise_error (Errors.Error_IllSMTPat,
                                U.format1 "Not an atomic SMT pattern: %s; \
                                           patterns on lemmas must be a list of simple SMTPat's \
                                           or a single SMTPatOr containing a list \
                                           of lists of patterns" (tts p))
                               p.pos
    in

    let lemma_pats p =
        let elts = list_elements p in
        let smt_pat_or t =
            let head, args = unmeta t |> head_and_args in
            match (un_uinst head).n, args with
                | Tm_fvar fv, [(e, _)]
                    when fv_eq_lid fv PC.smtpatOr_lid ->
                  Some e
                | _ -> None in
        match elts with
            | [t] ->
             begin match smt_pat_or t with
                | Some e ->
                  list_elements e |>  List.map (fun branch -> (list_elements branch) |> List.map one_pat)
                | _ -> [elts |> List.map one_pat]
              end
            | _ -> [elts |> List.map one_pat]
    in

    let binders, pre, post, patterns =
        match (Subst.compress t).n with
        | Tm_arrow(binders, c) ->
          let binders, c = Subst.open_comp binders c in
          begin match c.n with
            | Comp ({effect_args=[(pre, _); (post, _); (pats, _)]}) ->
              binders, pre, post, lemma_pats pats
            | _ -> failwith "impos"
          end

        | _ -> failwith "Impos"
    in
    (* Postcondition is thunked, c.f. #57 *)
    let post = unthunk_lemma_post post in
    let body = mk (Tm_meta (mk_imp pre post, Meta_pattern (binders_to_names binders, patterns))) t.pos in
    let quant =
      List.fold_right2
        (fun b u out -> mk_forall u (fst b) out)
        binders
        (universe_of_binders binders)
        body
    in
    quant

(* End SMT Lemma utilities *)


(* Effect utilities *)

(*
 * Mainly reading the combinators out of the eff_decl record
 *
 * For combinators that are present only in either wp or layered effects,
 *   their getters return option<tscheme>
 * Leaving it to the callers to deal with it
 *)

let eff_decl_of_new_effect (se:sigelt) :eff_decl =
  match se.sigel with
  | Sig_new_effect ne -> ne
  | _ -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"

let is_layered (ed:eff_decl) : bool =
  match ed.combinators with
  | Layered_eff _ -> true
  | _ -> false

let is_dm4f (ed:eff_decl) : bool =
  match ed.combinators with
  | DM4F_eff _ -> true
  | _ -> false

let apply_wp_eff_combinators (f:tscheme -> tscheme) (combs:wp_eff_combinators)
: wp_eff_combinators
= { ret_wp = f combs.ret_wp;
    bind_wp = f combs.bind_wp;
    stronger = f combs.stronger;
    if_then_else = f combs.if_then_else;
    ite_wp = f combs.ite_wp;
    close_wp = f combs.close_wp;
    trivial = f combs.trivial;
    
    repr = map_option f combs.repr;
    return_repr = map_option f combs.return_repr;
    bind_repr = map_option f combs.bind_repr }

let apply_layered_eff_combinators (f:tscheme -> tscheme) (combs:layered_eff_combinators)
: layered_eff_combinators
= let map_tuple (ts1, ts2) = (f ts1, f ts2) in
  { l_repr = map_tuple combs.l_repr;
    l_return = map_tuple combs.l_return;
    l_bind = map_tuple combs.l_bind;
    l_subcomp = map_tuple combs.l_subcomp;
    l_if_then_else = map_tuple combs.l_if_then_else }

let apply_eff_combinators (f:tscheme -> tscheme) (combs:eff_combinators) : eff_combinators =
  match combs with
  | Primitive_eff combs -> Primitive_eff (apply_wp_eff_combinators f combs)
  | DM4F_eff combs -> DM4F_eff (apply_wp_eff_combinators f combs)
  | Layered_eff combs -> Layered_eff (apply_layered_eff_combinators f combs)

let get_wp_close_combinator (ed:eff_decl) : option<tscheme> =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> Some combs.close_wp
  | _ -> None

let get_eff_repr (ed:eff_decl) : option<tscheme> =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> combs.repr
  | Layered_eff combs -> combs.l_repr |> fst |> Some
  
let get_bind_vc_combinator (ed:eff_decl) : tscheme =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> combs.bind_wp
  | Layered_eff combs -> combs.l_bind |> snd

let get_return_vc_combinator (ed:eff_decl) : tscheme =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> combs.ret_wp
  | Layered_eff combs -> combs.l_return |> snd
  
let get_bind_repr (ed:eff_decl) : option<tscheme> =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> combs.bind_repr
  | Layered_eff combs -> combs.l_bind |> fst |> Some

let get_return_repr (ed:eff_decl) : option<tscheme> =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> combs.return_repr  
  | Layered_eff combs -> combs.l_return |> fst |> Some

let get_wp_trivial_combinator (ed:eff_decl) : option<tscheme> =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> combs.trivial |> Some
  | _ -> None

let get_layered_if_then_else_combinator (ed:eff_decl) : option<tscheme> =
  match ed.combinators with
  | Layered_eff combs -> combs.l_if_then_else |> fst |> Some
  | _ -> None

let get_wp_if_then_else_combinator (ed:eff_decl) : option<tscheme> =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> combs.if_then_else |> Some
  | _ -> None

let get_wp_ite_combinator (ed:eff_decl) : option<tscheme> =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> combs.ite_wp |> Some
  | _ -> None

let get_stronger_vc_combinator (ed:eff_decl) : tscheme =
  match ed.combinators with
  | Primitive_eff combs
  | DM4F_eff combs -> combs.stronger
  | Layered_eff combs -> combs.l_subcomp |> snd

let get_stronger_repr (ed:eff_decl) : option<tscheme> =
  match ed.combinators with
  | Primitive_eff _
  | DM4F_eff _ -> None
  | Layered_eff combs -> combs.l_subcomp |> fst |> Some

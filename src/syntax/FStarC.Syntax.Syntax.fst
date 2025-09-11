(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or impliedmk_
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Syntax.Syntax
open FStarC.Effect
open FStarC.List
(* Type definitions for the core AST *)

open FStarC
open FStarC.Range
open FStarC.Ident
open FStarC.Const
open FStarC.Dyn
open FStarC.VConfig

open FStarC.Class.Ord
open FStarC.Class.HasRange
open FStarC.Class.Setlike
open FStarC.Order

module PC   = FStarC.Parser.Const
module GS   = FStarC.GenSym

let pragma_to_string (p:pragma) : string =
  match p with
  | ShowOptions           -> "#show-options"
  | ResetOptions None     -> "#reset-options"
  | ResetOptions (Some s) -> Format.fmt1 "#reset-options \"%s\"" s
  | SetOptions s          -> Format.fmt1 "#set-options \"%s\"" s
  | PushOptions None      -> "#push-options"
  | PushOptions (Some s)  -> Format.fmt1 "#push-options \"%s\"" s
  | RestartSolver         -> "#restart-solver"
  | PrintEffectsGraph     -> "#print-effects-graph"
  | PopOptions            -> "#pop-options"
  | Check t               -> "check _" // can't print a term here... move this to Syntax.Print?

instance showable_pragma = {
  show = pragma_to_string;
}

let rec emb_typ_to_string = function
    | ET_abstract -> "abstract"
    | ET_app (h, []) -> h
    | ET_app(h, args) -> "(" ^h^ " " ^ (List.map emb_typ_to_string args |> String.concat " ")  ^")"
    | ET_fun(a, b) -> "(" ^ emb_typ_to_string a ^ ") -> " ^ emb_typ_to_string b

instance showable_emb_typ = {
  show = emb_typ_to_string;
}


let rec delta_depth_to_string = function
    | Delta_constant_at_level i   -> "Delta_constant_at_level " ^ show i
    | Delta_equational_at_level i -> "Delta_equational_at_level " ^ show i
    | Delta_abstract d -> "Delta_abstract (" ^ delta_depth_to_string d ^ ")"

instance showable_delta_depth = {
  show = delta_depth_to_string;
}

instance showable_should_check_uvar = {
  show = (function
          | Allow_unresolved s -> "Allow_unresolved " ^ s
          | Allow_untyped s -> "Allow_untyped " ^ s
          | Allow_ghost s -> "Allow_ghost " ^ s
          | Strict -> "Strict"
          | Already_checked -> "Already_checked");
}

// This is set in FStarC.Main.main, where all modules are in-scope.
let lazy_chooser : ref (option (lazy_kind -> lazyinfo -> term)) = mk_ref None

let cmp_qualifier (q1 q2 : qualifier) : FStarC.Order.order =
  match q1, q2 with
  | Assumption, Assumption -> Eq
  | New, New -> Eq
  | Private, Private -> Eq
  | Unfold_for_unification_and_vcgen, Unfold_for_unification_and_vcgen -> Eq
  | Irreducible, Irreducible -> Eq
  | Inline_for_extraction, Inline_for_extraction -> Eq
  | NoExtract, NoExtract -> Eq
  | Noeq, Noeq -> Eq
  | Unopteq, Unopteq -> Eq
  | TotalEffect, TotalEffect -> Eq
  | Logic, Logic -> Eq
  | Reifiable, Reifiable -> Eq
  | Reflectable l1, Reflectable l2 -> cmp l1 l2
  | Visible_default, Visible_default -> Eq
  | Discriminator l1, Discriminator l2 -> cmp l1 l2
  | Projector (l1, i1), Projector (l2, i2) -> cmp (l1, i1) (l2, i2)
  | RecordType (l1, i1), RecordType (l2, i2) -> cmp (l1, i1) (l2, i2)
  | RecordConstructor (l1, i1), RecordConstructor (l2, i2) -> cmp (l1, i1) (l2, i2)
  | Action l1, Action l2 -> cmp l1 l2
  | ExceptionConstructor, ExceptionConstructor -> Eq
  | HasMaskedEffect, HasMaskedEffect -> Eq
  | Effect, Effect -> Eq
  | OnlyName, OnlyName -> Eq
  | InternalAssumption, InternalAssumption -> Eq

  | Assumption, _ -> Lt          | _, Assumption -> Gt
  | New, _ -> Lt                 | _, New -> Gt
  | Private, _ -> Lt             | _, Private -> Gt
  | Unfold_for_unification_and_vcgen, _ -> Lt | _, Unfold_for_unification_and_vcgen -> Gt
  | Irreducible, _ -> Lt         | _, Irreducible -> Gt
  | Inline_for_extraction, _ -> Lt | _, Inline_for_extraction -> Gt
  | NoExtract, _ -> Lt          | _, NoExtract -> Gt
  | Noeq, _ -> Lt               | _, Noeq -> Gt
  | Unopteq, _ -> Lt            | _, Unopteq -> Gt
  | TotalEffect, _ -> Lt        | _, TotalEffect -> Gt
  | Logic, _ -> Lt              | _, Logic -> Gt
  | Reifiable, _ -> Lt          | _, Reifiable -> Gt
  | Reflectable _, _ -> Lt      | _, Reflectable _ -> Gt
  | Visible_default, _ -> Lt    | _, Visible_default -> Gt
  | Discriminator _, _ -> Lt    | _, Discriminator _ -> Gt
  | Projector _, _ -> Lt        | _, Projector _ -> Gt
  | RecordType _, _ -> Lt       | _, RecordType _ -> Gt
  | RecordConstructor _, _ -> Lt | _, RecordConstructor _ -> Gt
  | Action _, _ -> Lt           | _, Action _ -> Gt
  | ExceptionConstructor, _ -> Lt | _, ExceptionConstructor -> Gt
  | HasMaskedEffect, _ -> Lt    | _, HasMaskedEffect -> Gt
  | Effect, _ -> Lt             | _, Effect -> Gt
  | OnlyName, _ -> Lt           | _, OnlyName -> Gt
  | InternalAssumption, _ -> Lt | _, InternalAssumption -> Gt

instance deq_qualifier : deq qualifier = {
  (=?) = (fun q1 q2 -> cmp_qualifier q1 q2 = Eq);
}

instance ord_qualifier : ord qualifier = {
  super = deq_qualifier;
  cmp = cmp_qualifier;
}

let is_internal_qualifier (q:qualifier) : bool =
  match q with
  | Visible_default
  | Discriminator _
  | Projector _
  | RecordType _
  | RecordConstructor _
  | Action _
  | ExceptionConstructor
  | HasMaskedEffect
  | Effect
  | OnlyName
  | InternalAssumption ->
      true
  | _ ->
      false

instance showable_indexed_effect_binder_kind : showable indexed_effect_binder_kind = {
  show = (function
          | Type_binder -> "Type_binder"
          | Substitutive_binder -> "Substitutive_binder"
          | BindCont_no_abstraction_binder -> "BindCont_no_abstraction_binder"
          | Range_binder -> "Range_binder"
          | Repr_binder -> "Repr_binder"
          | Ad_hoc_binder -> "Ad_hoc_binder"
  );
}

instance tagged_indexed_effect_binder_kind : tagged indexed_effect_binder_kind = {
  tag_of = (function
            | Type_binder -> "Type_binder"
            | Substitutive_binder -> "Substitutive_binder"
            | BindCont_no_abstraction_binder -> "BindCont_no_abstraction_binder"
            | Range_binder -> "Range_binder"
            | Repr_binder -> "Repr_binder"
            | Ad_hoc_binder -> "Ad_hoc_binder"
  );
}

instance showable_indexed_effect_combinator_kind : showable indexed_effect_combinator_kind = {
  show = (function
          | Substitutive_combinator ks -> "Substitutive_combinator " ^ show ks
          | Substitutive_invariant_combinator -> "Substitutive_invariant_combinator"
          | Ad_hoc_combinator -> "Ad_hoc_combinator"
  );
}

instance tagged_indexed_effect_combinator_kind : tagged indexed_effect_combinator_kind = {
  tag_of = (function
            | Substitutive_combinator _ -> "Substitutive_combinator"
            | Substitutive_invariant_combinator -> "Substitutive_invariant_combinator"
            | Ad_hoc_combinator -> "Ad_hoc_combinator"
  );
}

instance showable_eff_extraction_mode : showable eff_extraction_mode = {
  show = (function
          | Extract_none s -> "Extract_none " ^ s
          | Extract_reify -> "Extract_reify"	
          | Extract_primitive -> "Extract_primitive"
  );
}

instance tagged_eff_extraction_mode : tagged eff_extraction_mode = {
  tag_of = (function
            | Extract_none _ -> "Extract_none"
            | Extract_reify -> "Extract_reify"
            | Extract_primitive -> "Extract_primitive"
  );
}

let mod_name (m: modul) = m.name

(*********************************************************************************)
(* Identifiers to/from strings *)
(*********************************************************************************)
let withinfo v r = {v=v; p=r}

let order_bv (x y : bv) : int  = x.index - y.index
let bv_eq    (x y : bv) : bool = order_bv x y = 0

let order_ident x y = String.compare (string_of_id x) (string_of_id y)
let order_fv x y = String.compare (string_of_lid x) (string_of_lid y)

let range_of_lbname (l:lbname) = match l with
    | Inl x -> range_of_id x.ppname
    | Inr fv -> range_of_lid fv.fv_name
let range_of_bv x = range_of_id x.ppname

let set_range_of_bv x r = {x with ppname = set_id_range r x.ppname }


(* Helpers *)
let on_antiquoted (f : (term -> term)) (qi : quoteinfo) : quoteinfo =
  let (s, aqs) = qi.antiquotations in
  let aqs' = List.map f aqs in
  { qi with antiquotations = (s, aqs') }

(* Requires that bv.index is in scope. *)
let lookup_aq (bv : bv) (aq : antiquotations) : term =
    try List.nth (snd aq) (List.length (snd aq) - 1 - bv.index + fst aq) // subtract shift
    with
    | _ ->
      failwith "antiquotation out of bounds"

(*********************************************************************************)
(* Syntax builders *)
(*********************************************************************************)

// Cleanup this mess please
let deq_instance_from_cmp f = {
  (=?) = (fun x y -> Order.eq (f x y));
}
let ord_instance_from_cmp f = {
  super = deq_instance_from_cmp f;
  cmp = f;
}
let order_univ_name x y = String.compare (Ident.string_of_id x) (Ident.string_of_id y)

instance deq_bv : deq bv =
  deq_instance_from_cmp (fun x y -> Order.order_from_int (order_bv x y))
instance deq_ident : deq ident =
  deq_instance_from_cmp (fun x y -> Order.order_from_int (order_ident x y))
instance deq_fv : deq lident =
  deq_instance_from_cmp (fun x y -> Order.order_from_int (order_fv x y))
instance deq_univ_name : deq univ_name =
  deq_instance_from_cmp (fun x y -> Order.order_from_int (order_univ_name x y))
instance deq_delta_depth : deq delta_depth = {
  (=?) = (fun x y -> x = y);
}

instance ord_bv : ord bv =
  ord_instance_from_cmp (fun x y -> Order.order_from_int (order_bv x y))
instance ord_ident : ord ident =
  ord_instance_from_cmp (fun x y -> Order.order_from_int (order_ident x y))
instance ord_fv : ord lident =
  ord_instance_from_cmp (fun x y -> Order.order_from_int (order_fv x y))

(* Constructors for each term form; NO HASH CONSING; just makes all the auxiliary data at each node *)
let mk (t:'a) r = {
    n=t;
    pos=r;
    vars=mk_ref None;
    hash_code=mk_ref None;
}

let bv_to_tm   bv :term = mk (Tm_bvar bv) (range_of_bv bv)
let bv_to_name bv :term = mk (Tm_name bv) (range_of_bv bv)
let binders_to_names (bs:binders) : list term = bs |> List.map (fun b -> bv_to_name b.binder_bv)
let mk_Tm_app (t1:typ) (args:list arg) p =
    match args with
    | [] -> t1
    | _ -> mk (Tm_app {hd=t1; args}) p
let mk_Tm_uinst (t:term) (us:universes) =
  match t.n with
  | Tm_fvar _ ->
    begin match us with
    | [] -> t
    | us -> mk (Tm_uinst(t, us)) t.pos
    end
  | _ -> failwith "Unexpected universe instantiation"

let extend_app_n t args' r = match t.n with
    | Tm_app {hd; args} -> mk_Tm_app hd (args@args') r
    | _ -> mk_Tm_app t args' r
let extend_app t arg r = extend_app_n t [arg] r
let mk_Tm_delayed lr pos : term = mk (Tm_delayed {tm=fst lr; substs=snd lr}) pos
let mk_Total t = mk (Total t) t.pos
let mk_GTotal t : comp = mk (GTotal t) t.pos
let mk_Comp (ct:comp_typ) : comp  = mk (Comp ct) ct.result_typ.pos
let mk_lb (x, univs, eff, t, e, attrs, pos) = {
    lbname=x;
    lbunivs=univs;
    lbtyp=t;
    lbeff=eff;
    lbdef=e;
    lbattrs=attrs;
    lbpos=pos;
  }

let mk_Tac t =
    mk_Comp ({ comp_univs = [U_zero];
               effect_name = PC.effect_Tac_lid;
               result_typ = t;
               effect_args = [];
               flags = [SOMETRIVIAL; TRIVIAL_POSTCONDITION];
            })

let default_sigmeta = {
    sigmeta_active=true;
    sigmeta_fact_db_ids=[];
    sigmeta_spliced=false;
    sigmeta_admit=false;
    sigmeta_already_checked=false;
    sigmeta_extension_data=[]
}
let mk_sigelt (e: sigelt') = { 
    sigel = e;
    sigrng = Range.dummyRange;
    sigquals=[];
    sigmeta=default_sigmeta;
    sigattrs = [] ;
    sigopts = None;
    sigopens_and_abbrevs = [] }
let mk_subst (s:subst_t)   = s
let extend_subst x s : subst_t = x::s
let argpos (x:arg) = (fst x).pos

let tun : term = mk (Tm_unknown) dummyRange
let teff : term = mk (Tm_constant Const_effect) dummyRange

(* no compress call? *)
let is_teff (t:term) = match t.n with
    | Tm_constant Const_effect -> true
    | _ -> false
(* no compress call? *)
let is_type (t:term) = match t.n with
    | Tm_type _ -> true
    | _ -> false

(* Gen sym *)
let null_id  = mk_ident("_", dummyRange)
let null_bv k = {ppname=null_id; index=GS.next_id(); sort=k}

let is_null_bv (b:bv) = string_of_id b.ppname = string_of_id null_id
let is_null_binder (b:binder) = is_null_bv b.binder_bv
let range_of_ropt = function
    | None -> dummyRange
    | Some r -> r

let gen_bv' (id : ident) (r : option Range.t) (t : typ) : bv =
  {ppname=id; index=GS.next_id(); sort=t}

let gen_bv (s : string) (r : option Range.t) (t : typ) : bv =
  let id = mk_ident(s, range_of_ropt r) in
  gen_bv' id r t

let new_bv ropt t = gen_bv Ident.reserved_prefix ropt t
let freshen_bv bv =
    if is_null_bv bv
    then new_bv (Some (range_of_bv bv)) bv.sort
    else {bv with index=GS.next_id()}
let mk_binder_with_attrs bv aqual pqual attrs = {
  binder_bv = bv;
  binder_qual = aqual;
  binder_positivity = pqual;
  binder_attrs = attrs
}
let mk_binder a = mk_binder_with_attrs a None None []
let null_binder t : binder = mk_binder (null_bv t)
let imp_tag = Implicit false
let iarg t : arg = t, Some ({ aqual_implicit = true; aqual_attributes = [] })
let as_arg t : arg = t, None


let is_top_level = function
    | {lbname=Inr _}::_ -> true
    | _ -> false

let freenames_of_binders (bs:binders) : freenames =
    List.fold_right (fun b out -> add b.binder_bv out) bs (empty ())

let binders_of_list fvs : binders = (fvs |> List.map (fun t -> mk_binder t))
let binders_of_freenames (fvs:freenames) = elems fvs |> binders_of_list
let is_bqual_implicit = function Some (Implicit _) -> true | _ -> false
let is_aqual_implicit = function Some { aqual_implicit = b } -> b | _ -> false
let is_bqual_implicit_or_meta = function Some (Implicit _) | Some (Meta _) -> true | _ -> false
let as_bqual_implicit = function true -> Some imp_tag | _ -> None
let as_aqual_implicit = function true -> Some ({aqual_implicit=true; aqual_attributes=[]}) | _ -> None
let pat_bvs (p:pat) : list bv =
    let rec aux b p = match p.v with
        | Pat_dot_term _
        | Pat_constant _ -> b
        | Pat_var x -> x::b
        | Pat_cons(_, _, pats) -> List.fold_left (fun b (p, _) -> aux b p) b pats
    in
  List.rev <| aux [] p


let freshen_binder (b:binder) = { b with binder_bv = freshen_bv b.binder_bv }

let new_univ_name ropt =
    let id = GS.next_id() in
    mk_ident (Ident.reserved_prefix ^ show id, range_of_ropt ropt)
let lbname_eq l1 l2 = match l1, l2 with
  | Inl x, Inl y -> bv_eq x y
  | Inr l, Inr m -> lid_equals l m
  | _ -> false
let fv_eq fv1 fv2 = lid_equals fv1.fv_name fv2.fv_name
let fv_eq_lid fv lid = lid_equals fv.fv_name lid

let set_bv_range bv r = {bv with ppname = set_id_range r bv.ppname}

let lid_and_dd_as_fv l dq : fv = {
    fv_name = l;
    fv_qual = dq;
}
let lid_as_fv l dq : fv = {
    fv_name = l;
    fv_qual = dq;
}
let fv_to_tm (fv:fv) : term = mk (Tm_fvar fv) (range_of_lid fv.fv_name)
let fvar_with_dd l dq =  fv_to_tm (lid_and_dd_as_fv l dq)
let fvar l dq = fv_to_tm (lid_as_fv l dq)
let lid_of_fv (fv:fv) = fv.fv_name
let range_of_fv (fv:fv) = range_of_lid (lid_of_fv fv)
let set_range_of_fv (fv:fv) (r:Range.t) =
    {fv with fv_name = Ident.set_lid_range fv.fv_name r}
let has_simple_attribute (l: list term) s =
  List.existsb (function
    | { n = Tm_constant (Const_string (data, _)) } when data = s ->
        true
    | _ ->
        false
  ) l

// Compares the SHAPE of the patterns, *ignoring bound variables and universes*
let rec eq_pat (p1 : pat) (p2 : pat) : bool =
    match p1.v, p2.v with
    | Pat_constant c1, Pat_constant c2 -> eq_const c1 c2
    | Pat_cons (fv1, us1, as1), Pat_cons (fv2, us2, as2) ->
        if fv_eq fv1 fv2
        && List.length as1 = List.length as2
        then List.forall2 (fun (p1, b1) (p2, b2) -> b1 = b2 && eq_pat p1 p2) as1 as2
          && (match us1, us2 with
              | None, None -> true
              | Some us1, Some us2 -> 
                List.length us1 = List.length us2
              | _ -> false)
        else false
    | Pat_var _, Pat_var _ -> true
    | Pat_dot_term _, Pat_dot_term _ -> true
    | _, _ -> false

///////////////////////////////////////////////////////////////////////
//Some common constants
///////////////////////////////////////////////////////////////////////
let delta_constant = Delta_constant_at_level 0
let delta_equational = Delta_equational_at_level 0
let fvconst l = lid_and_dd_as_fv l None
let tconst l = mk (Tm_fvar (fvconst l)) Range.dummyRange
let tabbrev l = mk (Tm_fvar(lid_and_dd_as_fv l None)) Range.dummyRange
let tdataconstr l = fv_to_tm (lid_and_dd_as_fv l (Some Data_ctor))
let t_unit      = tconst PC.unit_lid
let t_bool      = tconst PC.bool_lid
let t_int       = tconst PC.int_lid
let t_string    = tconst PC.string_lid
let t_exn       = tconst PC.exn_lid
let t_real      = tconst PC.real_lid
let t_float     = tconst PC.float_lid
let t_char      = tabbrev PC.char_lid
let t_range     = tconst PC.range_lid
let t___range   = tconst PC.__range_lid
let t_vconfig   = tconst PC.vconfig_lid
let t_term      = tconst PC.term_lid
let t_term_view = tabbrev PC.term_view_lid
let t_order     = tconst PC.order_lid
let t_decls     = tabbrev PC.decls_lid
let t_binder    = tconst PC.binder_lid
let t_binders   = tconst PC.binders_lid
let t_bv        = tconst PC.bv_lid
let t_fv        = tconst PC.fv_lid
let t_norm_step = tconst PC.norm_step_lid
let t_tac_of a b =
    mk_Tm_app (mk_Tm_uinst (tabbrev PC.tac_lid) [U_zero; U_zero])
              [as_arg a; as_arg b] Range.dummyRange
let t_tactic_of t =
    mk_Tm_app (mk_Tm_uinst (tabbrev PC.tactic_lid) [U_zero])
              [as_arg t] Range.dummyRange

let t_tactic_unit = t_tactic_of t_unit

(*
 * AR: what's up with all the U_zero below?
 *)
let t_list_of t = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.list_lid) [U_zero])
  [as_arg t]
  Range.dummyRange
let t_option_of t = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.option_lid) [U_zero])
  [as_arg t]
  Range.dummyRange
let t_tuple2_of t1 t2 = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.lid_tuple2) [U_zero;U_zero])
  [as_arg t1; as_arg t2]
  Range.dummyRange
let t_tuple3_of t1 t2 t3 = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.lid_tuple3) [U_zero;U_zero;U_zero])
  [as_arg t1; as_arg t2; as_arg t3]
  Range.dummyRange
let t_tuple4_of t1 t2 t3 t4 = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.lid_tuple4) [U_zero;U_zero;U_zero;U_zero])
  [as_arg t1; as_arg t2; as_arg t3; as_arg t4]
  Range.dummyRange
let t_tuple5_of t1 t2 t3 t4 t5 = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.lid_tuple5) [U_zero;U_zero;U_zero;U_zero;U_zero])
  [as_arg t1; as_arg t2; as_arg t3; as_arg t4; as_arg t5]
  Range.dummyRange
let t_either_of t1 t2 = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.either_lid) [U_zero;U_zero])
  [as_arg t1; as_arg t2]
  Range.dummyRange
let t_sealed_of t = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.sealed_lid) [U_zero])
  [as_arg t]
  Range.dummyRange
let t_erased_of t = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.erased_lid) [U_zero])
  [as_arg t]
  Range.dummyRange

let unit_const_with_range r = mk (Tm_constant FStarC.Const.Const_unit) r
let unit_const = unit_const_with_range Range.dummyRange

instance show_restriction: showable restriction = {
   show = (function
          | Unrestricted -> "Unrestricted"
          | AllowList allow_list -> "(AllowList " ^ show allow_list ^ ")")
}

let is_ident_allowed_by_restriction' id
  = function | Unrestricted         -> Some id
             | AllowList allow_list ->
               Option.map fst (find FStarC.Class.Deq.(fun (dest_id, renamed_id) ->
                       Option.dflt dest_id renamed_id =? id
               ) allow_list)

let is_ident_allowed_by_restriction
  = let debug = FStarC.Debug.get_toggle "open_include_restrictions" in
    fun id restriction ->
    let result = is_ident_allowed_by_restriction' id restriction in
    if !debug then Format.print_string ( "is_ident_allowed_by_restriction(" ^ show id ^ ", "
                                                                      ^ show restriction ^ ") = "
                                                                      ^ show result ^ "\n" );
    result

instance has_range_syntax #a (_:unit) : Tot (hasRange (syntax a)) = {
  pos = (fun (t:syntax a) -> t.pos);
  setPos = (fun r t -> { t with pos = r });
}

instance has_range_withinfo #a (_:unit) : Tot (hasRange (withinfo_t a)) = {
  pos = (fun t -> t.p);
  setPos = (fun r t -> { t with p = r });
}

instance has_range_sigelt : hasRange sigelt = {
  pos = (fun t -> t.sigrng);
  setPos = (fun r t -> { t with sigrng = r });
}

instance hasRange_fv : hasRange fv = {
  pos = range_of_fv;
  setPos = (fun r f -> set_range_of_fv f r);
}

instance hasRange_bv : hasRange bv = {
  pos = range_of_bv;
  setPos = (fun r f -> set_range_of_bv f r);
}

instance hasRange_binder : hasRange binder = {
  pos = (fun b -> pos b.binder_bv);
  setPos = (fun r b -> { b with binder_bv = setPos r b.binder_bv });
}

instance hasRange_ctx_uvar : hasRange ctx_uvar = {
  pos = (fun u -> u.ctx_uvar_range);
  setPos = (fun r u -> { u with ctx_uvar_range = r });
}

let sli (l:lident) : string =
    if Options.print_real_names()
    then string_of_lid l
    else string_of_id (ident_of_lid l)

instance showable_fv : showable fv = {
  show = (fun fv -> sli fv.fv_name);
}

instance showable_lazy_kind = {
  show = (function
          | BadLazy -> "BadLazy"
          | Lazy_bv -> "Lazy_bv"
          | Lazy_namedv -> "Lazy_namedv"
          | Lazy_binder -> "Lazy_binder"
          | Lazy_optionstate -> "Lazy_optionstate"
          | Lazy_fvar -> "Lazy_fvar"
          | Lazy_comp -> "Lazy_comp"
          | Lazy_env -> "Lazy_env"
          | Lazy_proofstate -> "Lazy_proofstate"
          | Lazy_ref_proofstate -> "Lazy_ref_proofstate"
          | Lazy_goal -> "Lazy_goal"
          | Lazy_sigelt -> "Lazy_sigelt"
          | Lazy_letbinding -> "Lazy_letbinding"
          | Lazy_uvar -> "Lazy_uvar"
          | Lazy_universe -> "Lazy_universe"
          | Lazy_universe_uvar -> "Lazy_universe_uvar"
          | Lazy_issue -> "Lazy_issue"
          | Lazy_doc -> "Lazy_doc"
          | Lazy_ident -> "Lazy_ident"
          | Lazy_tref -> "Lazy_tref"
          | Lazy_embedding _ -> "Lazy_embedding _"
          | Lazy_extension s -> "Lazy_extension " ^ s
          | _ -> failwith "FIXME! lazy_kind_to_string must be complete"
  );
}

instance showable_restriction: showable restriction = {
  show = (function | Unrestricted -> "Unrestricted"
                   | AllowList l  -> "AllowList " ^ show l);
}

instance showable_unresolved_constructor : showable unresolved_constructor = {
  show = (fun uc ->
           "{ uc_base_term = " ^ show uc.uc_base_term ^
           "; uc_typename = " ^ show uc.uc_typename ^
           "; uc_fields = " ^ show uc.uc_fields ^ " }"
  );
}

instance showable_fv_qual : showable fv_qual = {
  show = (function
          | Data_ctor -> "Data_ctor"
          | Record_projector p -> "Record_projector (" ^ show p ^ ")"
          | Record_ctor      p -> "Record_ctor (" ^ show p ^ ")"
          | Unresolved_projector p -> "Unresolved_projector (" ^ show p^ ")"
          | Unresolved_constructor p -> "Unresolved_constructor (" ^ show p ^ ")"
  );
}

instance deq_lazy_kind : deq lazy_kind = {
  (=?) = (fun k k' ->
(* NOTE: Lazy_embedding compares false to itself, by design. *)
          match k, k' with
          | BadLazy, BadLazy
          | Lazy_bv, Lazy_bv
          | Lazy_namedv, Lazy_namedv
          | Lazy_binder, Lazy_binder
          | Lazy_optionstate, Lazy_optionstate
          | Lazy_fvar, Lazy_fvar
          | Lazy_comp, Lazy_comp
          | Lazy_env, Lazy_env
          | Lazy_proofstate, Lazy_proofstate
          | Lazy_ref_proofstate, Lazy_ref_proofstate
          | Lazy_goal, Lazy_goal
          | Lazy_sigelt, Lazy_sigelt
          | Lazy_letbinding, Lazy_letbinding
          | Lazy_uvar, Lazy_uvar
          | Lazy_universe, Lazy_universe
          | Lazy_universe_uvar, Lazy_universe_uvar
          | Lazy_issue, Lazy_issue
          | Lazy_ident, Lazy_ident
          | Lazy_doc, Lazy_doc
          | Lazy_tref, Lazy_tref
            -> true
          | Lazy_extension s, Lazy_extension t ->
            s = t
          | Lazy_embedding _, _
          | _, Lazy_embedding _ -> false
          | _ -> false);
}

instance tagged_term : tagged term = {
  tag_of = (fun t -> match t.n with
  | Tm_bvar {} -> "Tm_bvar" 
  | Tm_name {} -> "Tm_name"
  | Tm_fvar {} -> "Tm_fvar"
  | Tm_uinst {} -> "Tm_uinst"
  | Tm_constant _ -> "Tm_constant"
  | Tm_type _ -> "Tm_type"
  | Tm_quoted (_, {qkind=Quote_static}) -> "Tm_quoted(static)"
  | Tm_quoted (_, {qkind=Quote_dynamic}) -> "Tm_quoted(dynamic)"
  | Tm_abs {} -> "Tm_abs"
  | Tm_arrow {} -> "Tm_arrow"
  | Tm_refine {} -> "Tm_refine"
  | Tm_app {} -> "Tm_app"
  | Tm_match {} -> "Tm_match"
  | Tm_ascribed {} -> "Tm_ascribed"
  | Tm_let {} -> "Tm_let"
  | Tm_uvar {} -> "Tm_uvar"
  | Tm_delayed {} -> "Tm_delayed"
  | Tm_meta {} -> "Tm_meta"
  | Tm_unknown -> "Tm_unknown"
  | Tm_lazy {} -> "Tm_lazy"
  );
}

instance tagged_sigelt : tagged sigelt = {
  tag_of = (fun se -> match se.sigel with
  | Sig_inductive_typ {} -> "Sig_inductive_typ"
  | Sig_bundle {} -> "Sig_bundle"
  | Sig_datacon {} -> "Sig_datacon"
  | Sig_declare_typ {} -> "Sig_declare_typ"
  | Sig_let {} -> "Sig_let"
  | Sig_assume {} -> "Sig_assume"
  | Sig_new_effect {} -> "Sig_new_effect"
  | Sig_sub_effect {} -> "Sig_sub_effect"
  | Sig_effect_abbrev {} -> "Sig_effect_abbrev"
  | Sig_pragma _ -> "Sig_pragma"
  | Sig_splice {} -> "Sig_splice"
  | Sig_polymonadic_bind {} -> "Sig_polymonadic_bind"
  | Sig_polymonadic_subcomp {} -> "Sig_polymonadic_subcomp"
  | Sig_fail {} -> "Sig_fail"
  );
}

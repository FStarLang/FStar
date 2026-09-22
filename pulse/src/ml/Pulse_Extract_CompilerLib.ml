(* NOTE: the effect names used below must be the *root* effects (the ones Prims
   actually declares), not their abbreviations: this file builds syntax by hand,
   so it bypasses the desugarer, which is what resolves an abbreviation such as
   [DIV] or [PURE] to its root ([Div], [Tot]).  Naming an abbreviation here
   leaves a comp/meta node the typechecker and the extractor cannot look up. *)
module U = FStarC_Syntax_Util
module C = FStarC_Parser_Const
module S = FStarC_Syntax_Syntax

type term = S.term
type binder = S.binder
let unit_tm = S.unit_const
let unit_ty = S.t_unit
let mk_return (t:term) : term =
  S.mk
    (S.Tm_meta {tm2=t; meta=S.Meta_monadic_lift (C.primitive_pure_lid, C.primitive_div_lid, S.tun)})
    FStarC_Range.dummyRange
let mk_meta_monadic (t: term): term =
  S.mk (S.Tm_meta {tm2=t; meta=S.Meta_monadic (C.primitive_div_lid, S.tun)})
    FStarC_Range.dummyRange

(* Pulse's ANF hoisting (Pulse.Checker.Base.bind_st_term) tags the binders it
   generates with a synthetic attribute `Pulse.Lib.Core.__anf<n>_binder__`,
   whose fvar does not resolve to any actual definition. Keep those out of the
   let bindings we generate, so that only user-written attributes (e.g.
   FStar.Attributes.rename_let) reach F*'s extraction. *)
let is_anf_binder_attr (t:term) : bool =
  match (FStarC_Syntax_Subst.compress t).n with
  | S.Tm_fvar fv ->
    let s = FStarC_Ident.string_of_lid (S.lid_of_fv fv) in
    FStarC_Util.starts_with s "Pulse.Lib.Core.__anf" && FStarC_Util.ends_with s "_binder__"
  | _ -> false

let lbattrs_of_binder (b:binder) : term list =
  FStarC_List.filter (fun a -> not (is_anf_binder_attr a)) b.binder_attrs

let mk_pure_let (b:binder) (head:term) (body:term) : term =
  let lb = U.mk_letbinding
    (Inl b.binder_bv) [] b.binder_bv.sort C.primitive_pure_lid head (lbattrs_of_binder b) FStarC_Range.dummyRange in
  S.mk (S.Tm_let {lbs=(false, [lb]); body1=body}) FStarC_Range.dummyRange
let mk_let (b:binder) (head:term) (body:term) : term =
  let lb = U.mk_letbinding
    (Inl b.binder_bv) [] b.binder_bv.sort C.primitive_div_lid head (lbattrs_of_binder b) FStarC_Range.dummyRange in
  let tm_let =
    S.mk (S.Tm_let {lbs=(false, [lb]); body1=body}) FStarC_Range.dummyRange in
  S.mk (S.Tm_meta {tm2=tm_let; meta=S.Meta_monadic (C.primitive_div_lid, S.tun)}) FStarC_Range.dummyRange
let mk_if (b:term) (then_:term) (else_:term) : term =
  U.if_then_else b then_ else_

let mk_extracted_as_attr (impl: term) : term =
  S.mk_Tm_app (S.tconst FStarC_Parser_Const_ExtractAs.extract_as_lid)
    [S.mk (S.Tm_quoted (impl, {qkind=S.Quote_static; antiquotations=(Prims.int_zero,[])})) FStarC_Range.dummyRange, None]
    FStarC_Range.dummyRange

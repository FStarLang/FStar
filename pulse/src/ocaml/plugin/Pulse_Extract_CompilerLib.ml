module U = FStar_Syntax_Util
module C = FStar_Parser_Const
module S = FStar_Syntax_Syntax

type const = S.sconst
type fv = S.fv
type term = S.term
type binder = S.binder
let unit_tm = S.unit_const
let unit_ty = S.t_unit
type binder_qualifier = S.binder_qualifier
let implicit_qual = S.Implicit false
let mk_binder (sort:term) (ppname:string) (q:binder_qualifier option) (attrs:term list) : S.binder =
  S.mk_binder_with_attrs (S.gen_bv ppname None sort) q None attrs
let mk_abs (b:binder) (body:term) : term =
  S.mk (S.Tm_abs {bs=[b];body=body;rc_opt=None}) FStar_Compiler_Range.dummyRange
let mk_return (t:term) : term =
  S.mk
    (S.Tm_meta {tm2=t; meta=S.Meta_monadic_lift (C.effect_PURE_lid, C.effect_DIV_lid, S.tun)})
    FStar_Compiler_Range.dummyRange
let mk_meta_monadic (t: term): term =
  S.mk (S.Tm_meta {tm2=t; meta=S.Meta_monadic (C.effect_DIV_lid, S.tun)})
    FStar_Compiler_Range.dummyRange
let mk_let (b:binder) (head:term) (body:term) : term =
  let lb = U.mk_letbinding
    (Inl b.binder_bv) [] b.binder_bv.sort C.effect_DIV_lid head [] FStar_Compiler_Range.dummyRange in
  let tm_let =
    S.mk (S.Tm_let {lbs=(false, [lb]); body1=body}) FStar_Compiler_Range.dummyRange in
  S.mk (S.Tm_meta {tm2=tm_let; meta=S.Meta_monadic (C.effect_DIV_lid, S.tun)}) FStar_Compiler_Range.dummyRange
let mk_if (b:term) (then_:term) (else_:term) : term =
  U.if_then_else b then_ else_
let mk_const (c:FStar_Reflection_V2_Data.vconst) : const =
  FStar_Reflection_V2_Builtins.pack_const c

let mk_extracted_as_attr (impl: term) : term =
  S.mk_Tm_app (S.tconst FStar_Parser_Const.extract_as_lid)
    [S.mk (S.Tm_quoted (impl, {qkind=S.Quote_static; antiquotations=(Prims.int_zero,[])})) FStar_Compiler_Range.dummyRange, None]
    FStar_Compiler_Range.dummyRange

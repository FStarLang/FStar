module U = FStarC_Syntax_Util
module C = FStarC_Parser_Const
module S = FStarC_Syntax_Syntax

type term = S.term
type binder = S.binder
let unit_tm = S.unit_const
let unit_ty = S.t_unit
let mk_return (t:term) : term =
  S.mk
    (S.Tm_meta {tm2=t; meta=S.Meta_monadic_lift (C.effect_PURE_lid, C.effect_DIV_lid, S.tun)})
    FStarC_Compiler_Range.dummyRange
let mk_meta_monadic (t: term): term =
  S.mk (S.Tm_meta {tm2=t; meta=S.Meta_monadic (C.effect_DIV_lid, S.tun)})
    FStarC_Compiler_Range.dummyRange
let mk_let (b:binder) (head:term) (body:term) : term =
  let lb = U.mk_letbinding
    (Inl b.binder_bv) [] b.binder_bv.sort C.effect_DIV_lid head [] FStarC_Compiler_Range.dummyRange in
  let tm_let =
    S.mk (S.Tm_let {lbs=(false, [lb]); body1=body}) FStarC_Compiler_Range.dummyRange in
  S.mk (S.Tm_meta {tm2=tm_let; meta=S.Meta_monadic (C.effect_DIV_lid, S.tun)}) FStarC_Compiler_Range.dummyRange
let mk_if (b:term) (then_:term) (else_:term) : term =
  U.if_then_else b then_ else_

let mk_extracted_as_attr (impl: term) : term =
  S.mk_Tm_app (S.tconst FStarC_Parser_Const.extract_as_lid)
    [S.mk (S.Tm_quoted (impl, {qkind=S.Quote_static; antiquotations=(Prims.int_zero,[])})) FStarC_Compiler_Range.dummyRange, None]
    FStarC_Compiler_Range.dummyRange

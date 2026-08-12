(* The Custard flavour of ../Pulse_Extract_CompilerLib.ml.

   A realization is a contract with a *particular* extractor (custard.md
   section 8.2), and this file is the one place in Pulse where the two
   extractors' contracts differ.  Both differences are about the record a
   constructor's payload becomes:

   - ML extraction disambiguates field names across the whole module, so
     FStarC.Syntax.Syntax's several `tm' and `body' fields become `tm2' and
     `body1'.  Custard gives each payload its own type, so each keeps the
     name the source gave it.
   - `Tm_let' stores a `letbindings', which is a pair.  Custard inlines a
     tuple field into the record that holds it (section 5.7), so one `lbs'
     field of pair type becomes `lbs' and `lbs1'.

   Custard's names are the better ones, and there is no way to write one file
   that satisfies both, so the Custard build overlays this directory on top of
   ../ after copying it.  Nothing else in src/ml needs a copy. *)

module U = FStarC_Syntax_Util
module C = FStarC_Parser_Const
module S = FStarC_Syntax_Syntax

type term = S.term
type binder = S.binder
let unit_tm = S.unit_const
let unit_ty = S.t_unit
let mk_return (t:term) : term =
  S.mk
    (S.Tm_meta {tm=t; meta=S.Meta_monadic_lift (C.effect_PURE_lid, C.effect_DIV_lid, S.tun)})
    FStarC_Range.dummyRange
let mk_meta_monadic (t: term): term =
  S.mk (S.Tm_meta {tm=t; meta=S.Meta_monadic (C.effect_DIV_lid, S.tun)})
    FStarC_Range.dummyRange
let mk_pure_let (b:binder) (head:term) (body:term) : term =
  let lb = U.mk_letbinding
    (Inl b.binder_bv) [] b.binder_bv.sort C.effect_PURE_lid head [] FStarC_Range.dummyRange in
  S.mk (S.Tm_let {lbs=false; lbs1=[lb]; body=body}) FStarC_Range.dummyRange
let mk_let (b:binder) (head:term) (body:term) : term =
  let lb = U.mk_letbinding
    (Inl b.binder_bv) [] b.binder_bv.sort C.effect_DIV_lid head [] FStarC_Range.dummyRange in
  let tm_let =
    S.mk (S.Tm_let {lbs=false; lbs1=[lb]; body=body}) FStarC_Range.dummyRange in
  S.mk (S.Tm_meta {tm=tm_let; meta=S.Meta_monadic (C.effect_DIV_lid, S.tun)}) FStarC_Range.dummyRange
let mk_if (b:term) (then_:term) (else_:term) : term =
  U.if_then_else b then_ else_

let mk_extracted_as_attr (impl: term) : term =
  S.mk_Tm_app (S.tconst FStarC_Parser_Const_ExtractAs.extract_as_lid)
    [S.mk (S.Tm_quoted (impl, {qkind=S.Quote_static; antiquotations=Prims.int_zero; antiquotations1=[]})) FStarC_Range.dummyRange, None]
    FStarC_Range.dummyRange

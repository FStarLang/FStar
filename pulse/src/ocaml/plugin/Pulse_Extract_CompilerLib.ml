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
type pattern = S.pat
let mk_fv (s:string list) =
  S.fvconst (FStar_Ident.lid_of_ids ((List.map FStar_Ident.id_of_text s)))
let mk_fv_tm (fv:fv) : term = S.fv_to_tm fv 
let mk_pat_cons (fv:fv) (pats:pattern list) : pattern =
  S.withinfo
    (S.Pat_cons (fv, None, (List.map (fun p -> (p, false)) pats)))
    FStar_Compiler_Range.dummyRange
let mk_pat_constant (c:const) : pattern =
  S.withinfo (S.Pat_constant c) FStar_Compiler_Range.dummyRange
let mk_pat_var (ppname:string) (sort:term) : pattern =
  S.withinfo (S.Pat_var (S.gen_bv ppname None sort)) FStar_Compiler_Range.dummyRange
let mk_dot_pat (t:term option) : pattern =
  S.withinfo (S.Pat_dot_term t) FStar_Compiler_Range.dummyRange
let mk_const (c:FStar_Reflection_V2_Data.vconst) : const =
  FStar_Reflection_V2_Builtins.pack_const c
type branch = S.branch
let mk_branch (p:pattern) (body:term) : branch =
  (p, None, body)
let mk_match (scrutinee:term) (brs:branch list) : term =
  S.mk
    (S.Tm_match { scrutinee; ret_opt=None; brs; rc_opt1=None })
    FStar_Compiler_Range.dummyRange

let mk_extracted_as_attr (impl: term) : term =
  S.mk_Tm_app (S.tconst FStar_Parser_Const.extract_as_lid)
    [S.mk (S.Tm_quoted (impl, {qkind=S.Quote_static; antiquotations=(Prims.int_zero,[])})) FStar_Compiler_Range.dummyRange, None]
    FStar_Compiler_Range.dummyRange

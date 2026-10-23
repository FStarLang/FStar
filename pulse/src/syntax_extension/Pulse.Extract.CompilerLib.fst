(*
   Copyright 2023 Microsoft Research

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

module Pulse.Extract.CompilerLib

(* Builds compiler syntax for Pulse's extraction.  As in Pulse.RuntimeUtils,
   the interface's reflection types are the compiler's at runtime.

   NOTE: the effect names used below must be the *root* effects (the ones
   Prims actually declares), not their abbreviations: this module builds
   syntax by hand, so it bypasses the desugarer, which is what resolves an
   abbreviation such as [DIV] or [PURE] to its root ([Div], [Tot]).  Naming an
   abbreviation here leaves a comp/meta node the typechecker and the extractor
   cannot look up. *)

open FStarC
open FStarC.Effect
module R = FStar.Reflection.V2
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module C = FStarC.Parser.Const

let co (#a #b : Type) (x:a) : b = FStar.Pervasives.coerce_eq (admit ()) x
let ml_dv (#a:Type) (f:unit -> ML a) : Dv a = (co f <: unit -> Dv a) ()

let r_ = FStarC.Range.dummyRange

let unit_tm : R.term = co S.unit_const
let unit_ty : R.term = co S.t_unit

let mk_return (t:R.term) : Dv R.term =
  ml_dv (fun () ->
    co (S.mk (S.Tm_meta { tm = co t;
                          meta = S.Meta_monadic_lift (C.primitive_pure_lid, C.primitive_div_lid, S.tun) })
             r_))

let mk_meta_monadic (t:R.term) : Dv R.term =
  ml_dv (fun () ->
    co (S.mk (S.Tm_meta { tm = co t; meta = S.Meta_monadic (C.primitive_div_lid, S.tun) }) r_))

(* Pulse's ANF hoisting (Pulse.Checker.Base.bind_st_term) tags the binders it
   generates with a synthetic attribute `Pulse.Lib.Core.__anf<n>_binder__`,
   whose fvar does not resolve to any actual definition. Keep those out of the
   let bindings we generate, so that only user-written attributes (e.g.
   FStar.Attributes.rename_let) reach F*'s extraction. *)
let is_anf_binder_attr (t:S.term) : ML bool =
  match (FStarC.Syntax.Subst.compress t).n with
  | S.Tm_fvar fv ->
    let s = Ident.string_of_lid (S.lid_of_fv fv) in
    Util.starts_with s "Pulse.Lib.Core.__anf" && Util.ends_with s "_binder__"
  | _ -> false

let mk_let_eff (eff:Ident.lident) (b:R.binder) (head body:R.term) : ML S.term =
  let b : S.binder = co b in
  let lb =
    U.mk_letbinding (Inl b.binder_bv) [] b.binder_bv.sort eff (co head)
      (List.filter (fun a -> not (is_anf_binder_attr a)) b.binder_attrs) r_
  in
  S.mk (S.Tm_let { lbs = (false, [lb]); body = co body }) r_

let mk_pure_let (b:R.binder) (head body:R.term) : Dv R.term =
  ml_dv (fun () -> co (mk_let_eff C.primitive_pure_lid b head body))

let mk_let (b:R.binder) (head body:R.term) : Dv R.term =
  ml_dv (fun () ->
    let tm_let = mk_let_eff C.primitive_div_lid b head body in
    co (S.mk (S.Tm_meta { tm = tm_let; meta = S.Meta_monadic (C.primitive_div_lid, S.tun) }) r_))

let mk_if (b then_ else_:R.term) : Dv R.term =
  ml_dv (fun () -> co (U.if_then_else (co b) (co then_) (co else_)))

let mk_extracted_as_attr (impl:R.term) : Dv R.term =
  ml_dv (fun () ->
    let q = S.mk (S.Tm_quoted (co impl, { S.qkind = S.Quote_static; S.antiquotations = (0, []) })) r_ in
    co (S.mk_Tm_app (S.tconst FStarC.Parser.Const.ExtractAs.extract_as_lid) [q, None] r_))

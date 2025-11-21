module ExtractPulseOCaml

(* This module implements a simple extraction to ocaml, without
relying on fstar.lib. Integer types (both bounded and unbounded) become
OCaml's `int`. So, this is not sound wrt overflow, but it allows us to
extract Quicksort.Task simply, without needing to build fstar.lib in
OCaml 5. (We could.. but the compiled fstar.lib that F* comes with
is in OCaml 4.X, so we'd need more build logic.) *)

open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Util
open FStarC.Extraction
open FStarC.Extraction.ML
open FStarC.Extraction.ML.Syntax
open FStarC.Const
open FStarC.BaseTypes

module BU = FStarC.Util

open FStarC.Class.Show

open FStarC.Syntax.Syntax
open FStarC.Extraction.ML.UEnv
open FStarC.Extraction.ML.Term

module SS = FStarC.Syntax.Subst
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module Ident = FStarC.Ident

let dbg = Debug.get_toggle "extraction"

let hua (t:term) : option (S.fv & list S.universe & S.args) =
  let t = U.unmeta t in
  let hd, args = U.head_and_args_full t in
  let hd = U.unmeta hd in
  match (SS.compress hd).n with
  | Tm_fvar fv -> Some (fv, [], args)
  | Tm_uinst ({ n = Tm_fvar fv }, us) -> Some (fv, us, args)
  | _ -> None

let tr_typ (g:uenv) (t:term) : mlty =
  (* Only enabled with an extension flag *)
  if Options.Ext.get "pulse:extract_ocaml_bare" = "" then
    raise NotSupportedByExtension;
  let cb = FStarC.Extraction.ML.Term.term_as_mlty in
  let hua = hua t in
  if None? hua then
    raise NotSupportedByExtension;
  let Some (fv, us, args) = hua in
  // if !dbg then Format.print1 "GGG checking typ %s\n" (show hua);
  match fv, us, args with
  | _, _, [(t, _)] when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Array.Core.array") ->
    MLTY_Named ([cb g t], ([], "array"))

  | _, _, [(t, _)] when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Reference.ref") ->
    MLTY_Named ([cb g t], ([], "ref"))
  | _, _, [(t, _)] when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Box.box") ->
    MLTY_Named ([cb g t], ([], "ref"))

  | _, _, [] when S.fv_eq_lid fv (Ident.lid_of_str "FStar.SizeT.t") -> MLTY_Named ([], ([], "int"))
  | _, _, [] when S.fv_eq_lid fv (Ident.lid_of_str "Prims.nat") -> MLTY_Named ([], ([], "int"))
  | _, _, [] when S.fv_eq_lid fv (Ident.lid_of_str "Prims.int") -> MLTY_Named ([], ([], "int"))
  | _, _, [(t, _)] when S.fv_eq_lid fv (Ident.lid_of_str "Prims.list") ->
    MLTY_Named ([cb g t], ([], "list"))
  | _, _, [(t, _)] when S.fv_eq_lid fv (Ident.lid_of_str "FStar.Pervasives.Native.option") ->
    MLTY_Named ([cb g t], ([], "option"))

  | _, _, [] when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.SpinLock.lock") ->
    MLTY_Named ([], ([], "Mutex.t"))

  | _ -> 
    raise NotSupportedByExtension

let tr_expr (g:uenv) (t:term) : mlexpr & e_tag & mlty =
  (* Only enabled with an extension flag *)
  if Options.Ext.get "pulse:extract_ocaml_bare" = "" then
    raise NotSupportedByExtension;
  let cb = FStarC.Extraction.ML.Term.term_as_mlexpr in
  let hua = hua t in
  if None? hua then
    raise NotSupportedByExtension;
  let Some (fv, us, args) = hua in
  // if !dbg then Format.print1 "GGG checking expr %s\n" (show hua);
  match fv, us, args with
  | _, _, [(x, _)]
      when S.fv_eq_lid fv (Ident.lid_of_str "FStar.SizeT.uint_to_t") ->
    cb g x

  | _, _, [(t, _)]
      when S.fv_eq_lid fv (Ident.lid_of_str "FStar.Pervasives.Native.None") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "None" in
    (* let e = with_ty mlty <| MLE_App (bang, [(cb g v0)._1]) in *)
    bang, E_PURE, mlty

  | _, _, [(t, _); (v, _)]
      when S.fv_eq_lid fv (Ident.lid_of_str "FStar.Pervasives.Native.Some") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "Some" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g v)._1]) in
    e, E_PURE, mlty

  | _, _, [_a; _pre; _post; (f, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Core.hide_div") ->
    let f = U.mk_app f [S.as_arg S.t_unit] in
    cb g f

  (* Pulse.Lib.Reference *)
  | _, _, [(t, _); (v0, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Box.alloc") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "ref" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g v0)._1]) in
    e, E_PURE, mlty

  | _, _, [(t, _); _; (v0, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Reference.alloc") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "ref" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g v0)._1]) in
    e, E_PURE, mlty

  | _, _, [(t, _); (v0, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Reference.free")
        || S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Box.free") ->
    (* We translate 'free' as no-ops in OCaml. *)
    ml_unit, E_PURE, ml_unit_ty

  | _, _, [(t, _); (r, None); _n; _p]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Reference.read")
        || S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Box.op_Bang") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "!" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g r)._1]) in
    e, E_PURE, mlty

  | _, _, [(t, _); (r, None); (x, None); _n]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Reference.write")
        || S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Box.op_Colon_Equals") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "(:=)" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g r)._1; (cb g x)._1]) in
    e, E_PURE, mlty

  | _, _, [(t, _); _; (x, None); (sz, None); _; _]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Array.Core.mask_alloc_with_vis") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "Array.make" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g sz)._1; (cb g x)._1]) in
    e, E_PURE, mlty

  | _, _, [(t, _); (a, None); (i, None); _p; _s; _m]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Array.Core.mask_read") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "Array.get" in
    let a = (cb g a)._1 in
    // let i = U.mk_app (S.fvar (Ident.lid_of_str "FStar.SizeT.v") None) [S.as_arg i] in
    let i = (cb g i)._1 in
    // let i = with_ty ml_unit_ty <| MLE_App ((with_ty ml_unit_ty <| MLE_Var "Z.to_int"), [i]) in
    let e = with_ty mlty <| MLE_App (bang, [a; i]) in
    e, E_PURE, mlty

  | _, _, [(t, _); (a, None); (i, None); (v, None); _s; _m]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.Array.Core.mask_write") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "Array.set" in
    let a = (cb g a)._1 in
    // let i = U.mk_app (S.fvar (Ident.lid_of_str "FStar.SizeT.v") None) [S.as_arg i] in
    let i = (cb g i)._1 in
    // let i = with_ty ml_unit_ty <| MLE_App ((with_ty ml_unit_ty <| MLE_Var "Z.to_int"), [i]) in
    let v = (cb g v)._1 in
    let e = with_ty mlty <| MLE_App (bang, [a; i; v]) in
    e, E_PURE, mlty

  | _, _, [p]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.SpinLock.new_lock") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "Mutex.create" in
    let e = with_ty mlty <| MLE_App (bang, [ml_unit]) in
    e, E_PURE, mlty

  | _, _, [_v; _p; (m, _)]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.SpinLock.acquire") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "Mutex.lock" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g m)._1]) in
    e, E_PURE, mlty

  | _, _, [_v; _p; (m, _)]
      when S.fv_eq_lid fv (Ident.lid_of_str "Pulse.Lib.SpinLock.release") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "Mutex.unlock" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g m)._1]) in
    e, E_PURE, mlty

  | _, _, [(b, _)]
      when S.fv_eq_lid fv (Ident.lid_of_str "Prims.op_Negation") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "not" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g b)._1]) in
    e, E_PURE, mlty

  | _ -> 
    raise NotSupportedByExtension

let _ = register_pre_translate_typ tr_typ
let _ = register_pre_translate tr_expr

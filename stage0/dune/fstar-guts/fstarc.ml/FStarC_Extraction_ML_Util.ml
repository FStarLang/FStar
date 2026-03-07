open Prims
let codegen_fsharp (uu___ : unit) : Prims.bool=
  let c = FStarC_Options.codegen () in
  c = (FStar_Pervasives_Native.Some FStarC_Options.FSharp)
let pruneNones (l : 'a FStar_Pervasives_Native.option Prims.list) :
  'a Prims.list=
  FStarC_List.fold_right
    (fun x ll ->
       match x with
       | FStar_Pervasives_Native.Some xs -> xs :: ll
       | FStar_Pervasives_Native.None -> ll) l []
let mk_range_mle : FStarC_Extraction_ML_Syntax.mlexpr=
  FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.MLTY_Top
    (FStarC_Extraction_ML_Syntax.MLE_Name (["FStar"; "Range"], "mk_range"))
let dummy_range_mle : FStarC_Extraction_ML_Syntax.mlexpr=
  FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.MLTY_Top
    (FStarC_Extraction_ML_Syntax.MLE_Name (["FStar"; "Range"], "dummyRange"))
let mlconst_of_const' (sctt : FStarC_Const.sconst) :
  FStarC_Extraction_ML_Syntax.mlconstant=
  match sctt with
  | FStarC_Const.Const_effect ->
      FStarC_Effect.failwith "Unsupported constant"
  | FStarC_Const.Const_range uu___ -> FStarC_Extraction_ML_Syntax.MLC_Unit
  | FStarC_Const.Const_unit -> FStarC_Extraction_ML_Syntax.MLC_Unit
  | FStarC_Const.Const_char c -> FStarC_Extraction_ML_Syntax.MLC_Char c
  | FStarC_Const.Const_int (s, i) ->
      FStarC_Extraction_ML_Syntax.MLC_Int (s, i)
  | FStarC_Const.Const_bool b -> FStarC_Extraction_ML_Syntax.MLC_Bool b
  | FStarC_Const.Const_string (s, uu___) ->
      FStarC_Extraction_ML_Syntax.MLC_String s
  | FStarC_Const.Const_range_of ->
      FStarC_Effect.failwith "Unhandled constant: range_of/set_range_of"
  | FStarC_Const.Const_set_range_of ->
      FStarC_Effect.failwith "Unhandled constant: range_of/set_range_of"
  | FStarC_Const.Const_real uu___ ->
      FStarC_Effect.failwith "Unhandled constant: real/reify/reflect"
  | FStarC_Const.Const_reify uu___ ->
      FStarC_Effect.failwith "Unhandled constant: real/reify/reflect"
  | FStarC_Const.Const_reflect uu___ ->
      FStarC_Effect.failwith "Unhandled constant: real/reify/reflect"
let mlconst_of_const (p : FStarC_Range_Type.t) (c : FStarC_Const.sconst) :
  FStarC_Extraction_ML_Syntax.mlconstant=
  try (fun uu___ -> match () with | () -> mlconst_of_const' c) ()
  with
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Range_Ops.string_of_range p in
        let uu___3 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_const c in
        FStarC_Format.fmt2 "(%s) Failed to translate constant %s " uu___2
          uu___3 in
      FStarC_Effect.failwith uu___1
let mlexpr_of_range (r : FStarC_Range_Type.t) :
  FStarC_Extraction_ML_Syntax.mlexpr'=
  let cint i =
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
          (uu___3, FStar_Pervasives_Native.None) in
        FStarC_Extraction_ML_Syntax.MLC_Int uu___2 in
      FStarC_Extraction_ML_Syntax.MLE_Const uu___1 in
    FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.ml_int_ty
      uu___ in
  let cstr s =
    FStarC_Extraction_ML_Syntax.with_ty
      FStarC_Extraction_ML_Syntax.ml_string_ty
      (FStarC_Extraction_ML_Syntax.MLE_Const
         (FStarC_Extraction_ML_Syntax.MLC_String s)) in
  let drop_path = FStarC_Filepath.basename in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          cint
            (FStarC_Range_Ops.line_of_pos (FStarC_Range_Ops.start_of_range r)) in
        let uu___4 =
          let uu___5 =
            cint
              (FStarC_Range_Ops.col_of_pos
                 (FStarC_Range_Ops.start_of_range r)) in
          let uu___6 =
            let uu___7 =
              cint
                (FStarC_Range_Ops.line_of_pos
                   (FStarC_Range_Ops.end_of_range r)) in
            let uu___8 =
              let uu___9 =
                cint
                  (FStarC_Range_Ops.col_of_pos
                     (FStarC_Range_Ops.end_of_range r)) in
              [uu___9] in
            uu___7 :: uu___8 in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      (cstr (drop_path (FStarC_Range_Ops.file_of_range r))) :: uu___2 in
    (mk_range_mle, uu___1) in
  FStarC_Extraction_ML_Syntax.MLE_App uu___
let mlexpr_of_const (p : FStarC_Range_Type.t) (c : FStarC_Const.sconst) :
  FStarC_Extraction_ML_Syntax.mlexpr'=
  match c with
  | FStarC_Const.Const_range r -> mlexpr_of_range r
  | uu___ ->
      let uu___1 = mlconst_of_const p c in
      FStarC_Extraction_ML_Syntax.MLE_Const uu___1
let rec subst_aux
  (subst :
    (FStarC_Extraction_ML_Syntax.mlident * FStarC_Extraction_ML_Syntax.mlty)
      Prims.list)
  (t : FStarC_Extraction_ML_Syntax.mlty) : FStarC_Extraction_ML_Syntax.mlty=
  match t with
  | FStarC_Extraction_ML_Syntax.MLTY_Var x ->
      let uu___ =
        FStarC_Option.find
          (fun uu___1 -> match uu___1 with | (y, uu___2) -> y = x) subst in
      (match uu___ with
       | FStar_Pervasives_Native.Some ts -> FStar_Pervasives_Native.snd ts
       | FStar_Pervasives_Native.None -> t)
  | FStarC_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
      let uu___ =
        let uu___1 = subst_aux subst t1 in
        let uu___2 = subst_aux subst t2 in (uu___1, f, uu___2) in
      FStarC_Extraction_ML_Syntax.MLTY_Fun uu___
  | FStarC_Extraction_ML_Syntax.MLTY_Named (args, path) ->
      let uu___ =
        let uu___1 = FStarC_List.map (subst_aux subst) args in (uu___1, path) in
      FStarC_Extraction_ML_Syntax.MLTY_Named uu___
  | FStarC_Extraction_ML_Syntax.MLTY_Tuple ts ->
      let uu___ = FStarC_List.map (subst_aux subst) ts in
      FStarC_Extraction_ML_Syntax.MLTY_Tuple uu___
  | FStarC_Extraction_ML_Syntax.MLTY_Top -> t
  | FStarC_Extraction_ML_Syntax.MLTY_Erased -> t
let try_subst (ts : FStarC_Extraction_ML_Syntax.mltyscheme)
  (args : FStarC_Extraction_ML_Syntax.mlty Prims.list) :
  FStarC_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option=
  let uu___ = ts in
  match uu___ with
  | (formals, t) ->
      if (FStarC_List.length formals) <> (FStarC_List.length args)
      then FStar_Pervasives_Native.None
      else
        (let uu___2 =
           let uu___3 =
             let uu___4 = FStarC_Extraction_ML_Syntax.ty_param_names formals in
             FStarC_List.zip uu___4 args in
           subst_aux uu___3 t in
         FStar_Pervasives_Native.Some uu___2)
let subst
  (ts :
    (FStarC_Extraction_ML_Syntax.ty_param Prims.list *
      FStarC_Extraction_ML_Syntax.mlty))
  (args : FStarC_Extraction_ML_Syntax.mlty Prims.list) :
  FStarC_Extraction_ML_Syntax.mlty=
  let uu___ = try_subst ts args in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      FStarC_Effect.failwith
        "Substitution must be fully applied (see GitHub issue #490)"
  | FStar_Pervasives_Native.Some t -> t
let udelta_unfold (g : FStarC_Extraction_ML_UEnv.uenv)
  (t : FStarC_Extraction_ML_Syntax.mlty) :
  FStarC_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option=
  match t with
  | FStarC_Extraction_ML_Syntax.MLTY_Named (args, n) ->
      let uu___ = FStarC_Extraction_ML_UEnv.lookup_tydef g n in
      (match uu___ with
       | FStar_Pervasives_Native.Some ts ->
           let uu___1 = try_subst ts args in
           (match uu___1 with
            | FStar_Pervasives_Native.None ->
                let uu___2 =
                  let uu___3 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                      (FStarC_List.length args) in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                      (FStarC_List.length (FStar_Pervasives_Native.fst ts)) in
                  FStarC_Format.fmt3
                    "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                    (FStarC_Extraction_ML_Syntax.string_of_mlpath n) uu___3
                    uu___4 in
                FStarC_Effect.failwith uu___2
            | FStar_Pervasives_Native.Some r ->
                FStar_Pervasives_Native.Some r)
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let eff_leq (f : FStarC_Extraction_ML_Syntax.e_tag)
  (f' : FStarC_Extraction_ML_Syntax.e_tag) : Prims.bool=
  match (f, f') with
  | (FStarC_Extraction_ML_Syntax.E_PURE, uu___) -> true
  | (FStarC_Extraction_ML_Syntax.E_ERASABLE,
     FStarC_Extraction_ML_Syntax.E_ERASABLE) -> true
  | (FStarC_Extraction_ML_Syntax.E_IMPURE,
     FStarC_Extraction_ML_Syntax.E_IMPURE) -> true
  | uu___ -> false
let eff_to_string (uu___ : FStarC_Extraction_ML_Syntax.e_tag) : Prims.string=
  match uu___ with
  | FStarC_Extraction_ML_Syntax.E_PURE -> "Pure"
  | FStarC_Extraction_ML_Syntax.E_ERASABLE -> "Erasable"
  | FStarC_Extraction_ML_Syntax.E_IMPURE -> "Impure"
let join (r : FStarC_Range_Type.t) (f : FStarC_Extraction_ML_Syntax.e_tag)
  (f' : FStarC_Extraction_ML_Syntax.e_tag) :
  FStarC_Extraction_ML_Syntax.e_tag=
  match (f, f') with
  | (FStarC_Extraction_ML_Syntax.E_IMPURE,
     FStarC_Extraction_ML_Syntax.E_PURE) ->
      FStarC_Extraction_ML_Syntax.E_IMPURE
  | (FStarC_Extraction_ML_Syntax.E_PURE,
     FStarC_Extraction_ML_Syntax.E_IMPURE) ->
      FStarC_Extraction_ML_Syntax.E_IMPURE
  | (FStarC_Extraction_ML_Syntax.E_IMPURE,
     FStarC_Extraction_ML_Syntax.E_IMPURE) ->
      FStarC_Extraction_ML_Syntax.E_IMPURE
  | (FStarC_Extraction_ML_Syntax.E_ERASABLE,
     FStarC_Extraction_ML_Syntax.E_ERASABLE) ->
      FStarC_Extraction_ML_Syntax.E_ERASABLE
  | (FStarC_Extraction_ML_Syntax.E_PURE,
     FStarC_Extraction_ML_Syntax.E_ERASABLE) ->
      FStarC_Extraction_ML_Syntax.E_ERASABLE
  | (FStarC_Extraction_ML_Syntax.E_ERASABLE,
     FStarC_Extraction_ML_Syntax.E_PURE) ->
      FStarC_Extraction_ML_Syntax.E_ERASABLE
  | (FStarC_Extraction_ML_Syntax.E_PURE, FStarC_Extraction_ML_Syntax.E_PURE)
      -> FStarC_Extraction_ML_Syntax.E_PURE
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Range_Ops.string_of_range r in
        FStarC_Format.fmt3 "Impossible (%s): Inconsistent effects %s and %s"
          uu___2 (eff_to_string f) (eff_to_string f') in
      FStarC_Effect.failwith uu___1
let join_l (r : FStarC_Range_Type.t)
  (fs : FStarC_Extraction_ML_Syntax.e_tag Prims.list) :
  FStarC_Extraction_ML_Syntax.e_tag=
  FStarC_List.fold_left (join r) FStarC_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun (bs : FStarC_Extraction_ML_Syntax.mlbinder Prims.list)
  (t : FStarC_Extraction_ML_Syntax.mlty) : FStarC_Extraction_ML_Syntax.mlty=
  FStarC_List.fold_right
    (fun uu___ t1 ->
       match uu___ with
       | { FStarC_Extraction_ML_Syntax.mlbinder_name = uu___1;
           FStarC_Extraction_ML_Syntax.mlbinder_ty = mlbinder_ty;
           FStarC_Extraction_ML_Syntax.mlbinder_attrs = uu___2;_} ->
           FStarC_Extraction_ML_Syntax.MLTY_Fun
             (mlbinder_ty, FStarC_Extraction_ML_Syntax.E_PURE, t1)) bs t
type unfold_t =
  FStarC_Extraction_ML_Syntax.mlty ->
    FStarC_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
let rec type_leq_c (unfold_ty : unfold_t)
  (e : FStarC_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option)
  (t : FStarC_Extraction_ML_Syntax.mlty)
  (t' : FStarC_Extraction_ML_Syntax.mlty) :
  (Prims.bool * FStarC_Extraction_ML_Syntax.mlexpr
    FStar_Pervasives_Native.option)=
  match (t, t') with
  | (FStarC_Extraction_ML_Syntax.MLTY_Var x,
     FStarC_Extraction_ML_Syntax.MLTY_Var y) ->
      if x = y then (true, e) else (false, FStar_Pervasives_Native.None)
  | (FStarC_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2),
     FStarC_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) ->
      let mk_fun xs body =
        match xs with
        | [] -> body
        | uu___ ->
            let e1 =
              match body.FStarC_Extraction_ML_Syntax.expr with
              | FStarC_Extraction_ML_Syntax.MLE_Fun (ys, body1) ->
                  FStarC_Extraction_ML_Syntax.MLE_Fun
                    ((FStarC_List.op_At xs ys), body1)
              | uu___1 -> FStarC_Extraction_ML_Syntax.MLE_Fun (xs, body) in
            let uu___1 = mk_ty_fun xs body.FStarC_Extraction_ML_Syntax.mlty in
            FStarC_Extraction_ML_Syntax.with_ty uu___1 e1 in
      (match e with
       | FStar_Pervasives_Native.Some
           {
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Fun (x::xs, body);
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_}
           ->
           let tl1 = type_leq unfold_ty t1' t1 in
           if (if tl1 then eff_leq f f' else false)
           then
             (if
                (if f = FStarC_Extraction_ML_Syntax.E_PURE
                 then f' = FStarC_Extraction_ML_Syntax.E_ERASABLE
                 else false)
              then
                let tl2 = type_leq unfold_ty t2 t2' in
                (if tl2
                 then
                   let tl3 =
                     type_leq unfold_ty t2
                       FStarC_Extraction_ML_Syntax.ml_unit_ty in
                   let body1 =
                     if tl3
                     then FStarC_Extraction_ML_Syntax.ml_unit
                     else
                       FStarC_Extraction_ML_Syntax.with_ty t2'
                         (FStarC_Extraction_ML_Syntax.MLE_Coerce
                            (FStarC_Extraction_ML_Syntax.ml_unit,
                              FStarC_Extraction_ML_Syntax.ml_unit_ty, t2')) in
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         mk_ty_fun [x] body1.FStarC_Extraction_ML_Syntax.mlty in
                       FStarC_Extraction_ML_Syntax.with_ty uu___4
                         (FStarC_Extraction_ML_Syntax.MLE_Fun ([x], body1)) in
                     FStar_Pervasives_Native.Some uu___3 in
                   (true, uu___2)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu___3 =
                   let uu___4 =
                     let uu___5 = mk_fun xs body in
                     FStar_Pervasives_Native.Some uu___5 in
                   type_leq_c unfold_ty uu___4 t2 t2' in
                 match uu___3 with
                 | (ok, body1) ->
                     let res =
                       match body1 with
                       | FStar_Pervasives_Native.Some body2 ->
                           let uu___4 = mk_fun [x] body2 in
                           FStar_Pervasives_Native.Some uu___4
                       | uu___4 -> FStar_Pervasives_Native.None in
                     (ok, res)))
           else (false, FStar_Pervasives_Native.None)
       | uu___ ->
           let tl1 = type_leq unfold_ty t1' t1 in
           let tl2 = type_leq unfold_ty t2 t2' in
           if (if (if tl1 then eff_leq f f' else false) then tl2 else false)
           then (true, e)
           else (false, FStar_Pervasives_Native.None))
  | (FStarC_Extraction_ML_Syntax.MLTY_Named (args, path),
     FStarC_Extraction_ML_Syntax.MLTY_Named (args', path')) ->
      if path = path'
      then
        let uu___ = FStarC_List.forall2 (type_leq unfold_ty) args args' in
        (if uu___ then (true, e) else (false, FStar_Pervasives_Native.None))
      else
        (let uu___1 = unfold_ty t in
         match uu___1 with
         | FStar_Pervasives_Native.Some t1 -> type_leq_c unfold_ty e t1 t'
         | FStar_Pervasives_Native.None ->
             let uu___2 = unfold_ty t' in
             (match uu___2 with
              | FStar_Pervasives_Native.None ->
                  (false, FStar_Pervasives_Native.None)
              | FStar_Pervasives_Native.Some t'1 ->
                  type_leq_c unfold_ty e t t'1))
  | (FStarC_Extraction_ML_Syntax.MLTY_Tuple ts,
     FStarC_Extraction_ML_Syntax.MLTY_Tuple ts') ->
      let uu___ = FStarC_List.forall2 (type_leq unfold_ty) ts ts' in
      if uu___ then (true, e) else (false, FStar_Pervasives_Native.None)
  | (FStarC_Extraction_ML_Syntax.MLTY_Top,
     FStarC_Extraction_ML_Syntax.MLTY_Top) -> (true, e)
  | (FStarC_Extraction_ML_Syntax.MLTY_Named uu___, uu___1) ->
      let uu___2 = unfold_ty t in
      (match uu___2 with
       | FStar_Pervasives_Native.Some t1 -> type_leq_c unfold_ty e t1 t'
       | uu___3 -> (false, FStar_Pervasives_Native.None))
  | (uu___, FStarC_Extraction_ML_Syntax.MLTY_Named uu___1) ->
      let uu___2 = unfold_ty t' in
      (match uu___2 with
       | FStar_Pervasives_Native.Some t'1 -> type_leq_c unfold_ty e t t'1
       | uu___3 -> (false, FStar_Pervasives_Native.None))
  | (FStarC_Extraction_ML_Syntax.MLTY_Erased,
     FStarC_Extraction_ML_Syntax.MLTY_Erased) -> (true, e)
  | uu___ -> (false, FStar_Pervasives_Native.None)
and type_leq (g : unfold_t) (t1 : FStarC_Extraction_ML_Syntax.mlty)
  (t2 : FStarC_Extraction_ML_Syntax.mlty) : Prims.bool=
  let r = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
  FStar_Pervasives_Native.fst r
let rec erase_effect_annotations (t : FStarC_Extraction_ML_Syntax.mlty) :
  FStarC_Extraction_ML_Syntax.mlty=
  match t with
  | FStarC_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
      FStarC_Extraction_ML_Syntax.MLTY_Fun
        ((erase_effect_annotations t1), FStarC_Extraction_ML_Syntax.E_PURE,
          (erase_effect_annotations t2))
  | uu___ -> t
let is_type_abstraction
  (uu___ : (('a, 'b) FStar_Pervasives.either * 'c) Prims.list) : Prims.bool=
  match uu___ with
  | (FStar_Pervasives.Inl uu___1, uu___2)::uu___3 -> true
  | uu___1 -> false
let is_xtuple (uu___ : (Prims.string Prims.list * Prims.string)) :
  Prims.int FStar_Pervasives_Native.option=
  match uu___ with
  | (ns, n) ->
      FStarC_Parser_Const_Tuples.get_tuple_datacon_arity
        (FStarC_Util.concat_l "." (FStarC_List.op_At ns [n]))
let is_xtuple_ty (uu___ : (Prims.string Prims.list * Prims.string)) :
  Prims.int FStar_Pervasives_Native.option=
  match uu___ with
  | (ns, n) ->
      FStarC_Parser_Const_Tuples.get_tuple_tycon_arity
        (FStarC_Util.concat_l "." (FStarC_List.op_At ns [n]))
let resugar_exp (e : FStarC_Extraction_ML_Syntax.mlexpr) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  match e.FStarC_Extraction_ML_Syntax.expr with
  | FStarC_Extraction_ML_Syntax.MLE_CTor (mlp, args) ->
      (match is_xtuple mlp with
       | FStar_Pervasives_Native.Some n ->
           FStarC_Extraction_ML_Syntax.with_ty
             e.FStarC_Extraction_ML_Syntax.mlty
             (FStarC_Extraction_ML_Syntax.MLE_Tuple args)
       | uu___ -> e)
  | uu___ -> e
let record_field_path (fs : FStarC_Ident.lident Prims.list) :
  Prims.string Prims.list=
  match fs with
  | f::uu___ ->
      let uu___1 = FStarC_Util.prefix (FStarC_Ident.ns_of_lid f) in
      (match uu___1 with
       | (ns, uu___2) ->
           FStarC_List.map (fun id -> FStarC_Ident.string_of_id id) ns)
  | uu___ -> FStarC_Effect.failwith "impos"
let record_fields (fs : FStarC_Ident.lident Prims.list) (vs : 'a Prims.list)
  : (Prims.string * 'a) Prims.list=
  FStarC_List.map2
    (fun f e ->
       ((FStarC_Ident.string_of_id (FStarC_Ident.ident_of_lid f)), e)) fs vs
let resugar_mlty (t : FStarC_Extraction_ML_Syntax.mlty) :
  FStarC_Extraction_ML_Syntax.mlty=
  match t with
  | FStarC_Extraction_ML_Syntax.MLTY_Named (args, mlp) ->
      (match is_xtuple_ty mlp with
       | FStar_Pervasives_Native.Some n ->
           FStarC_Extraction_ML_Syntax.MLTY_Tuple args
       | uu___ -> t)
  | uu___ -> t
let flatten_ns (ns : Prims.string Prims.list) : Prims.string=
  FStarC_String.concat "_" ns
let flatten_mlpath (uu___ : (Prims.string Prims.list * Prims.string)) :
  Prims.string=
  match uu___ with
  | (ns, n) -> FStarC_String.concat "_" (FStarC_List.op_At ns [n])
let ml_module_name_of_lid (l : FStarC_Ident.lident) : Prims.string=
  let ns_strs =
    FStarC_List.map FStarC_Ident.string_of_id (FStarC_Ident.ns_of_lid l) in
  let mlp =
    (ns_strs, (FStarC_Ident.string_of_id (FStarC_Ident.ident_of_lid l))) in
  flatten_mlpath mlp
let rec erasableType (unfold_ty : unfold_t)
  (t : FStarC_Extraction_ML_Syntax.mlty) : Prims.bool=
  let erasableTypeNoDelta t1 =
    if t1 = FStarC_Extraction_ML_Syntax.ml_unit_ty
    then true
    else
      (match t1 with
       | FStarC_Extraction_ML_Syntax.MLTY_Named
           (uu___1, ("FStar"::"Ghost"::[], "erased")) -> true
       | FStarC_Extraction_ML_Syntax.MLTY_Named
           (uu___1, ("FStar"::"Tactics"::"Effect"::[], "tactic")) ->
           let c = FStarC_Options.codegen () in
           c <> (FStar_Pervasives_Native.Some FStarC_Options.Plugin)
       | uu___1 -> false) in
  let uu___ = erasableTypeNoDelta t in
  if uu___
  then true
  else
    (let uu___2 = unfold_ty t in
     match uu___2 with
     | FStar_Pervasives_Native.Some t1 -> erasableType unfold_ty t1
     | FStar_Pervasives_Native.None -> false)
let rec eraseTypeDeep (unfold_ty : unfold_t)
  (t : FStarC_Extraction_ML_Syntax.mlty) : FStarC_Extraction_ML_Syntax.mlty=
  match t with
  | FStarC_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) ->
      if etag = FStarC_Extraction_ML_Syntax.E_PURE
      then
        let uu___ =
          let uu___1 = eraseTypeDeep unfold_ty tyd in
          let uu___2 = eraseTypeDeep unfold_ty tycd in (uu___1, etag, uu___2) in
        FStarC_Extraction_ML_Syntax.MLTY_Fun uu___
      else t
  | FStarC_Extraction_ML_Syntax.MLTY_Named (lty, mlp) ->
      let uu___ = erasableType unfold_ty t in
      if uu___
      then FStarC_Extraction_ML_Syntax.MLTY_Erased
      else
        (let uu___2 =
           let uu___3 = FStarC_List.map (eraseTypeDeep unfold_ty) lty in
           (uu___3, mlp) in
         FStarC_Extraction_ML_Syntax.MLTY_Named uu___2)
  | FStarC_Extraction_ML_Syntax.MLTY_Tuple lty ->
      let uu___ = FStarC_List.map (eraseTypeDeep unfold_ty) lty in
      FStarC_Extraction_ML_Syntax.MLTY_Tuple uu___
  | uu___ -> t
let prims_op_equality : FStarC_Extraction_ML_Syntax.mlexpr=
  FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.MLTY_Top
    (FStarC_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp : FStarC_Extraction_ML_Syntax.mlexpr=
  let uu___ =
    mk_ty_fun
      [{
         FStarC_Extraction_ML_Syntax.mlbinder_name = "x";
         FStarC_Extraction_ML_Syntax.mlbinder_ty =
           FStarC_Extraction_ML_Syntax.ml_bool_ty;
         FStarC_Extraction_ML_Syntax.mlbinder_attrs = []
       };
      {
        FStarC_Extraction_ML_Syntax.mlbinder_name = "y";
        FStarC_Extraction_ML_Syntax.mlbinder_ty =
          FStarC_Extraction_ML_Syntax.ml_bool_ty;
        FStarC_Extraction_ML_Syntax.mlbinder_attrs = []
      }] FStarC_Extraction_ML_Syntax.ml_bool_ty in
  FStarC_Extraction_ML_Syntax.with_ty uu___
    (FStarC_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_AmpAmp"))
let conjoin (e1 : FStarC_Extraction_ML_Syntax.mlexpr)
  (e2 : FStarC_Extraction_ML_Syntax.mlexpr) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.ml_bool_ty
    (FStarC_Extraction_ML_Syntax.MLE_App (prims_op_amp_amp, [e1; e2]))
let conjoin_opt
  (e1 : FStarC_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option)
  (e2 : FStarC_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) :
  FStarC_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option=
  match (e1, e2) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      FStar_Pervasives_Native.None
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.None) ->
      FStar_Pervasives_Native.Some x
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some x) ->
      FStar_Pervasives_Native.Some x
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
      FStar_Pervasives_Native.Some (conjoin x y)
let mlloc_of_range (r : FStarC_Range_Type.t) : (Prims.int * Prims.string)=
  let pos = FStarC_Range_Ops.start_of_range r in
  let line = FStarC_Range_Ops.line_of_pos pos in
  (line, (FStarC_Range_Ops.file_of_range r))
let rec doms_and_cod (t : FStarC_Extraction_ML_Syntax.mlty) :
  (FStarC_Extraction_ML_Syntax.mlty Prims.list *
    FStarC_Extraction_ML_Syntax.mlty)=
  match t with
  | FStarC_Extraction_ML_Syntax.MLTY_Fun (a, uu___, b) ->
      let uu___1 = doms_and_cod b in
      (match uu___1 with | (ds, c) -> ((a :: ds), c))
  | uu___ -> ([], t)
let argTypes (t : FStarC_Extraction_ML_Syntax.mlty) :
  FStarC_Extraction_ML_Syntax.mlty Prims.list=
  FStar_Pervasives_Native.fst (doms_and_cod t)
let rec uncurry_mlty_fun (t : FStarC_Extraction_ML_Syntax.mlty) :
  (FStarC_Extraction_ML_Syntax.mlty Prims.list *
    FStarC_Extraction_ML_Syntax.mlty)=
  match t with
  | FStarC_Extraction_ML_Syntax.MLTY_Fun (a, uu___, b) ->
      let uu___1 = uncurry_mlty_fun b in
      (match uu___1 with | (args, res) -> ((a :: args), res))
  | uu___ -> ([], t)
let list_elements (e : FStarC_Extraction_ML_Syntax.mlexpr) :
  FStarC_Extraction_ML_Syntax.mlexpr Prims.list
    FStar_Pervasives_Native.option=
  let rec list_elements1 acc e1 =
    match e1.FStarC_Extraction_ML_Syntax.expr with
    | FStarC_Extraction_ML_Syntax.MLE_CTor
        (("Fstarcompiler.Prims"::[], "Cons"), hd::tl::[]) ->
        list_elements1 (hd :: acc) tl
    | FStarC_Extraction_ML_Syntax.MLE_CTor
        (("Fstarcompiler.Prims"::[], "Nil"), []) ->
        FStar_Pervasives_Native.Some (FStarC_List.rev acc)
    | FStarC_Extraction_ML_Syntax.MLE_CTor
        (("Prims"::[], "Cons"), hd::tl::[]) -> list_elements1 (hd :: acc) tl
    | FStarC_Extraction_ML_Syntax.MLE_CTor (("Prims"::[], "Nil"), []) ->
        FStar_Pervasives_Native.Some (FStarC_List.rev acc)
    | uu___ -> FStar_Pervasives_Native.None in
  list_elements1 [] e

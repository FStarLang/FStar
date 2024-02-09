open Prims
type var = Prims.string
type binding = (var * Pulse2Rust_Rust_Syntax.typ * Prims.bool)
type reachable_defs = Prims.string FStar_Compiler_Set.set
let (reachable_defs_to_string : reachable_defs -> Prims.string) =
  fun d ->
    let uu___ =
      let uu___1 = FStar_Compiler_Set.elems FStar_Class_Ord.ord_string d in
      FStar_Compiler_String.concat ";" uu___1 in
    FStar_Compiler_Util.format1 "[%s]" uu___
type env =
  {
  fns: (Prims.string * Pulse2Rust_Rust_Syntax.fn_signature) Prims.list ;
  statics: (Prims.string * Pulse2Rust_Rust_Syntax.typ) Prims.list ;
  gamma: binding Prims.list ;
  record_field_names: Prims.string Prims.list FStar_Compiler_Util.psmap ;
  reachable_defs: reachable_defs }
let (__proj__Mkenv__item__fns :
  env -> (Prims.string * Pulse2Rust_Rust_Syntax.fn_signature) Prims.list) =
  fun projectee ->
    match projectee with
    | { fns; statics; gamma; record_field_names;
        reachable_defs = reachable_defs1;_} -> fns
let (__proj__Mkenv__item__statics :
  env -> (Prims.string * Pulse2Rust_Rust_Syntax.typ) Prims.list) =
  fun projectee ->
    match projectee with
    | { fns; statics; gamma; record_field_names;
        reachable_defs = reachable_defs1;_} -> statics
let (__proj__Mkenv__item__gamma : env -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { fns; statics; gamma; record_field_names;
        reachable_defs = reachable_defs1;_} -> gamma
let (__proj__Mkenv__item__record_field_names :
  env -> Prims.string Prims.list FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with
    | { fns; statics; gamma; record_field_names;
        reachable_defs = reachable_defs1;_} -> record_field_names
let (__proj__Mkenv__item__reachable_defs : env -> reachable_defs) =
  fun projectee ->
    match projectee with
    | { fns; statics; gamma; record_field_names;
        reachable_defs = reachable_defs1;_} -> reachable_defs1
let (tyvar_of : Prims.string -> Prims.string) =
  fun s ->
    let uu___ =
      FStar_Compiler_String.substring s Prims.int_one
        ((FStar_Compiler_String.length s) - Prims.int_one) in
    FStar_Compiler_String.uppercase uu___
let (varname : Prims.string -> Prims.string) =
  fun s -> FStar_Compiler_Util.replace_char s 39 95
let (enum_or_struct_name : Prims.string -> Prims.string) = fun s -> s
let (is_internal_name : Prims.string -> Prims.bool) =
  fun s ->
    (((((FStar_Compiler_Util.starts_with s "uu___") || (s = "_fret")) ||
         (s = "_bind_c"))
        || (s = "_while_c"))
       || (s = "_while_b"))
      || (s = "_if_br")
let fail : 'uuuuu . Prims.string -> 'uuuuu =
  fun s ->
    let uu___ =
      FStar_Compiler_Util.format1 "Pulse to Rust extraction failed: %s" s in
    FStar_Compiler_Effect.failwith uu___
let fail_nyi : 'uuuuu . Prims.string -> 'uuuuu =
  fun s ->
    let uu___ =
      FStar_Compiler_Util.format1
        "Pulse to Rust extraction failed: no support yet for %s" s in
    FStar_Compiler_Effect.failwith uu___
let (empty_env : reachable_defs -> env) =
  fun reachable_defs1 ->
    let uu___ = FStar_Compiler_Util.psmap_empty () in
    {
      fns = [];
      statics = [];
      gamma = [];
      record_field_names = uu___;
      reachable_defs = reachable_defs1
    }
let (lookup_global_fn :
  env ->
    Prims.string ->
      Pulse2Rust_Rust_Syntax.fn_signature FStar_Pervasives_Native.option)
  =
  fun g ->
    fun s ->
      let uu___ =
        FStar_Compiler_List.tryFind
          (fun uu___1 -> match uu___1 with | (f, uu___2) -> f = s) g.fns in
      FStar_Compiler_Util.map_option
        (fun uu___1 -> match uu___1 with | (uu___2, t) -> t) uu___
let (lookup_local :
  env ->
    Prims.string ->
      (Pulse2Rust_Rust_Syntax.typ * Prims.bool)
        FStar_Pervasives_Native.option)
  =
  fun g ->
    fun s ->
      let uu___ =
        FStar_Compiler_List.tryFind
          (fun uu___1 -> match uu___1 with | (x, uu___2, uu___3) -> x = s)
          g.gamma in
      FStar_Compiler_Util.map_option
        (fun uu___1 -> match uu___1 with | (uu___2, t, b) -> (t, b)) uu___
let (push_fn :
  env -> Prims.string -> Pulse2Rust_Rust_Syntax.fn_signature -> env) =
  fun g ->
    fun s ->
      fun t ->
        {
          fns = ((s, t) :: (g.fns));
          statics = (g.statics);
          gamma = (g.gamma);
          record_field_names = (g.record_field_names);
          reachable_defs = (g.reachable_defs)
        }
let (push_static : env -> Prims.string -> Pulse2Rust_Rust_Syntax.typ -> env)
  =
  fun g ->
    fun s ->
      fun t ->
        {
          fns = (g.fns);
          statics = ((s, t) :: (g.statics));
          gamma = (g.gamma);
          record_field_names = (g.record_field_names);
          reachable_defs = (g.reachable_defs)
        }
let (push_local :
  env -> Prims.string -> Pulse2Rust_Rust_Syntax.typ -> Prims.bool -> env) =
  fun g ->
    fun s ->
      fun t ->
        fun is_mut ->
          {
            fns = (g.fns);
            statics = (g.statics);
            gamma = ((s, t, is_mut) :: (g.gamma));
            record_field_names = (g.record_field_names);
            reachable_defs = (g.reachable_defs)
          }
let (type_of : env -> Pulse2Rust_Rust_Syntax.expr -> Prims.bool) =
  fun g ->
    fun e ->
      match e with
      | Pulse2Rust_Rust_Syntax.Expr_path (s::[]) ->
          let uu___ = lookup_local g s in
          (match uu___ with
           | FStar_Pervasives_Native.Some (_t, b) -> b
           | FStar_Pervasives_Native.None ->
               let uu___1 =
                 FStar_Compiler_Util.format1 "lookup in env for %s" s in
               fail uu___1)
      | uu___ -> false
let rec (uncurry_arrow :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu___, t2) ->
        let uu___1 = uncurry_arrow t2 in
        (match uu___1 with | (arg_ts, ret_t) -> ((t1 :: arg_ts), ret_t))
    | uu___ -> ([], t)
let (arg_ts_and_ret_t :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty
      Prims.list * FStar_Extraction_ML_Syntax.mlty))
  =
  fun t ->
    let uu___ = t in
    match uu___ with
    | (tvars, t1) ->
        (match t1 with
         | FStar_Extraction_ML_Syntax.MLTY_Fun
             (uu___1, FStar_Extraction_ML_Syntax.E_PURE, uu___2) ->
             let uu___3 = uncurry_arrow t1 in
             (match uu___3 with | (arg_ts, ret_t) -> (tvars, arg_ts, ret_t))
         | FStar_Extraction_ML_Syntax.MLTY_Fun
             (uu___1, FStar_Extraction_ML_Syntax.E_IMPURE, uu___2) ->
             let uu___3 = uncurry_arrow t1 in
             (match uu___3 with | (arg_ts, ret_t) -> (tvars, arg_ts, ret_t))
         | uu___1 ->
             let uu___2 =
               let uu___3 = FStar_Extraction_ML_Syntax.mlty_to_string t1 in
               FStar_Compiler_Util.format1 "top level arg_ts and ret_t %s"
                 uu___3 in
             fail_nyi uu___2)
let rec (extract_mlty :
  env -> FStar_Extraction_ML_Syntax.mlty -> Pulse2Rust_Rust_Syntax.typ) =
  fun g ->
    fun t ->
      let mk_slice is_mut t1 =
        let uu___ =
          let uu___1 = extract_mlty g t1 in
          Pulse2Rust_Rust_Syntax.mk_slice_typ uu___1 in
        Pulse2Rust_Rust_Syntax.mk_ref_typ is_mut uu___ in
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var s ->
          let uu___ = tyvar_of s in
          Pulse2Rust_Rust_Syntax.mk_scalar_typ uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.UInt8.t" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "u8"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.UInt32.t" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "u32"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.Int32.t" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "i32"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.UInt64.t" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "u64"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Prims.string" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "String"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          ((let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___ = "FStar.Int64.t") ||
             (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___ = "Prims.int"))
            ||
            (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___ = "Prims.nat")
          -> Pulse2Rust_Rust_Syntax.mk_scalar_typ "i64"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.SizeT.t" ->
          Pulse2Rust_Rust_Syntax.mk_scalar_typ "usize"
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Prims.bool" -> Pulse2Rust_Rust_Syntax.mk_scalar_typ "bool"
      | FStar_Extraction_ML_Syntax.MLTY_Named (l, p) when
          (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___ = "FStar.Pervasives.Native.tuple2") ||
            (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___ = "FStar.Pervasives.Native.tuple3")
          ->
          let uu___ = FStar_Compiler_List.map (extract_mlty g) l in
          Pulse2Rust_Rust_Syntax.mk_tuple_typ uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.Reference.ref" ->
          let is_mut = true in
          let uu___ = extract_mlty g arg in
          Pulse2Rust_Rust_Syntax.mk_ref_typ is_mut uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.Box.box" ->
          let uu___ = extract_mlty g arg in
          Pulse2Rust_Rust_Syntax.mk_box_typ uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.Array.Core.array" ->
          let is_mut = true in mk_slice is_mut arg
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu___::[], p) when
          let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___1 = "Pulse.Lib.Array.Core.larray" ->
          let is_mut = true in mk_slice is_mut arg
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.Vec.vec" ->
          let uu___ = extract_mlty g arg in
          Pulse2Rust_Rust_Syntax.mk_vec_typ uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu___, p) when
          let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___1 = "Pulse.Lib.Mutex.mutex" ->
          let uu___1 = extract_mlty g arg in
          Pulse2Rust_Rust_Syntax.mk_mutex_typ uu___1
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.Pervasives.Native.option" ->
          let uu___ = extract_mlty g arg in
          Pulse2Rust_Rust_Syntax.mk_option_typ uu___
      | FStar_Extraction_ML_Syntax.MLTY_Erased ->
          Pulse2Rust_Rust_Syntax.Typ_unit
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, p) ->
          let uu___ = FStar_Compiler_List.map (extract_mlty g) args in
          Pulse2Rust_Rust_Syntax.mk_named_typ (FStar_Pervasives_Native.snd p)
            uu___
      | FStar_Extraction_ML_Syntax.MLTY_Fun uu___ ->
          let uu___1 = arg_ts_and_ret_t ([], t) in
          (match uu___1 with
           | (uu___2, arg_ts, ret_t) ->
               let uu___3 = FStar_Compiler_List.map (extract_mlty g) arg_ts in
               let uu___4 = extract_mlty g ret_t in
               Pulse2Rust_Rust_Syntax.mk_fn_typ uu___3 uu___4)
      | FStar_Extraction_ML_Syntax.MLTY_Top ->
          Pulse2Rust_Rust_Syntax.Typ_infer
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_Syntax.mlty_to_string t in
            FStar_Compiler_Util.format1 "mlty %s" uu___2 in
          fail_nyi uu___1
let (extract_mltyopt :
  env ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
      Pulse2Rust_Rust_Syntax.typ)
  =
  fun g ->
    fun t ->
      match t with
      | FStar_Pervasives_Native.None -> Pulse2Rust_Rust_Syntax.Typ_infer
      | FStar_Pervasives_Native.Some t1 -> extract_mlty g t1
let (arg_has_mut_attribute :
  FStar_Extraction_ML_Syntax.mlexpr Prims.list -> Prims.bool) =
  fun attrs ->
    FStar_Compiler_List.existsb
      (fun attr ->
         match attr.FStar_Extraction_ML_Syntax.expr with
         | FStar_Extraction_ML_Syntax.MLE_CTor (p, uu___) when
             let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___1 = "Pulse.Lib.Pervasives.Rust_mut_binder" -> true
         | uu___ -> false) attrs
let (extract_top_level_fn_arg :
  env ->
    Prims.string ->
      FStar_Extraction_ML_Syntax.mlexpr Prims.list ->
        FStar_Extraction_ML_Syntax.mlty -> Pulse2Rust_Rust_Syntax.fn_arg)
  =
  fun g ->
    fun arg_name ->
      fun arg_attrs ->
        fun t ->
          let uu___ = arg_has_mut_attribute arg_attrs in
          let uu___1 = extract_mlty g t in
          Pulse2Rust_Rust_Syntax.mk_scalar_fn_arg arg_name uu___ uu___1
let (push_fn_arg :
  env -> Prims.string -> Pulse2Rust_Rust_Syntax.fn_arg -> env) =
  fun g ->
    fun arg_name ->
      fun arg ->
        match arg with
        | Pulse2Rust_Rust_Syntax.Fn_arg_pat
            { Pulse2Rust_Rust_Syntax.pat_typ_pat = uu___;
              Pulse2Rust_Rust_Syntax.pat_typ_typ = pat_typ_typ;_}
            -> let is_mut = false in push_local g arg_name pat_typ_typ false
let (extract_top_level_sig :
  env ->
    Prims.bool ->
      Prims.string ->
        Pulse2Rust_Rust_Syntax.generic_type_param Prims.list ->
          Prims.string Prims.list ->
            FStar_Extraction_ML_Syntax.mlexpr Prims.list Prims.list ->
              FStar_Extraction_ML_Syntax.mlty Prims.list ->
                FStar_Extraction_ML_Syntax.mlty
                  FStar_Pervasives_Native.option ->
                  (Pulse2Rust_Rust_Syntax.fn_signature * env))
  =
  fun g ->
    fun fn_const ->
      fun fn_name ->
        fun generic_type_params ->
          fun arg_names ->
            fun arg_attrs ->
              fun arg_ts ->
                fun ret_t ->
                  let fn_args =
                    let uu___ = FStar_Compiler_List.map varname arg_names in
                    FStar_Compiler_List.map3 (extract_top_level_fn_arg g)
                      uu___ arg_attrs arg_ts in
                  let fn_ret_t = extract_mltyopt g ret_t in
                  let uu___ =
                    Pulse2Rust_Rust_Syntax.mk_fn_signature fn_const fn_name
                      generic_type_params fn_args fn_ret_t in
                  let uu___1 =
                    let uu___2 = FStar_Compiler_List.zip arg_names fn_args in
                    FStar_Compiler_List.fold_left
                      (fun g1 ->
                         fun uu___3 ->
                           match uu___3 with
                           | (arg_name, arg) -> push_fn_arg g1 arg_name arg)
                      g uu___2 in
                  (uu___, uu___1)
let (is_binop :
  Prims.string -> Pulse2Rust_Rust_Syntax.binop FStar_Pervasives_Native.option)
  =
  fun s ->
    if
      ((s = "Prims.op_Addition") || (s = "FStar.UInt32.add")) ||
        (s = "FStar.SizeT.add")
    then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Add
    else
      if
        ((s = "Prims.op_Subtraction") || (s = "FStar.SizeT.sub")) ||
          (s = "FStar.UInt32.sub")
      then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Sub
      else
        if
          (((((s = "Prims.op_Multiply") || (s = "FStar.Mul.op_Star")) ||
               (s = "FStar.UInt32.mul"))
              || (s = "FStar.UInt32.op_Star_Hat"))
             || (s = "FStar.SizeT.mul"))
            || (s = "FStar.SizeT.op_Star_Hat")
        then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Mul
        else
          if s = "Prims.op_disEquality"
          then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Ne
          else
            if
              ((s = "Prims.op_LessThanOrEqual") || (s = "FStar.UInt32.lte"))
                || (s = "FStar.SizeT.lte")
            then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Le
            else
              if
                ((s = "Prims.op_LessThan") || (s = "FStar.UInt32.lt")) ||
                  (s = "FStar.SizeT.lt")
              then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Lt
              else
                if
                  ((s = "Prims.op_GreaterThanOrEqual") ||
                     (s = "FStar.UInt32.gte"))
                    || (s = "FStar.SizeT.gte")
                then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Ge
                else
                  if
                    ((s = "Prims.op_GreaterThan") || (s = "FStar.UInt32.gt"))
                      || (s = "FStar.SizeT.gt")
                  then FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Gt
                  else
                    if s = "Prims.op_Equality"
                    then
                      FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.Eq
                    else
                      if
                        ((s = "Prims.rem") || (s = "FStar.UInt32.rem")) ||
                          (s = "FStar.SizeT.rem")
                      then
                        FStar_Pervasives_Native.Some
                          Pulse2Rust_Rust_Syntax.Rem
                      else
                        if s = "Prims.op_AmpAmp"
                        then
                          FStar_Pervasives_Native.Some
                            Pulse2Rust_Rust_Syntax.And
                        else
                          if s = "Prims.op_BarBar"
                          then
                            FStar_Pervasives_Native.Some
                              Pulse2Rust_Rust_Syntax.Or
                          else FStar_Pervasives_Native.None
let (extract_mlconstant_to_lit :
  FStar_Extraction_ML_Syntax.mlconstant -> Pulse2Rust_Rust_Syntax.lit) =
  fun c ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Int (lit_int_val, swopt) ->
        let lit_int_signed =
          match swopt with
          | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, uu___) ->
              FStar_Pervasives_Native.Some false
          | FStar_Pervasives_Native.Some (FStar_Const.Signed, uu___) ->
              FStar_Pervasives_Native.Some true
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
        let lit_int_width =
          match swopt with
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Int8) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I8
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Int16) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I16
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Int32) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I32
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Int64) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I64
          | FStar_Pervasives_Native.Some (uu___, FStar_Const.Sizet) ->
              FStar_Pervasives_Native.Some Pulse2Rust_Rust_Syntax.I64
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
        Pulse2Rust_Rust_Syntax.Lit_int
          {
            Pulse2Rust_Rust_Syntax.lit_int_val = lit_int_val;
            Pulse2Rust_Rust_Syntax.lit_int_signed = lit_int_signed;
            Pulse2Rust_Rust_Syntax.lit_int_width = lit_int_width
          }
    | FStar_Extraction_ML_Syntax.MLC_Bool b ->
        Pulse2Rust_Rust_Syntax.Lit_bool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        Pulse2Rust_Rust_Syntax.Lit_string s
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Extraction_ML_Syntax.mlconstant_to_string c in
          FStar_Compiler_Util.format1 "mlconstant_to_lit %s" uu___2 in
        fail_nyi uu___1
let rec (extract_mlpattern_to_pat :
  env ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      (env * Pulse2Rust_Rust_Syntax.pat))
  =
  fun g ->
    fun p ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Wild ->
          (g, Pulse2Rust_Rust_Syntax.Pat_wild)
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu___ =
            let uu___1 = extract_mlconstant_to_lit c in
            Pulse2Rust_Rust_Syntax.Pat_lit uu___1 in
          (g, uu___)
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          let uu___ = push_local g x Pulse2Rust_Rust_Syntax.Typ_infer false in
          let uu___1 =
            let uu___2 = is_internal_name x in
            if uu___2
            then Pulse2Rust_Rust_Syntax.Pat_wild
            else
              (let uu___4 = varname x in
               Pulse2Rust_Rust_Syntax.mk_pat_ident uu___4) in
          (uu___, uu___1)
      | FStar_Extraction_ML_Syntax.MLP_CTor (p1, ps) when
          ((FStar_Pervasives_Native.snd p1) = "Mktuple2") ||
            ((FStar_Pervasives_Native.snd p1) = "Mktuple3")
          ->
          let uu___ =
            FStar_Compiler_List.fold_left_map extract_mlpattern_to_pat g ps in
          (match uu___ with
           | (g1, ps1) ->
               let uu___1 = Pulse2Rust_Rust_Syntax.mk_pat_tuple ps1 in
               (g1, uu___1))
      | FStar_Extraction_ML_Syntax.MLP_CTor (p1, ps) ->
          let uu___ =
            FStar_Compiler_List.fold_left_map extract_mlpattern_to_pat g ps in
          (match uu___ with
           | (g1, ps1) ->
               let uu___1 =
                 Pulse2Rust_Rust_Syntax.mk_pat_ts
                   (FStar_Pervasives_Native.snd p1) ps1 in
               (g1, uu___1))
      | FStar_Extraction_ML_Syntax.MLP_Record (p1, fs) ->
          let uu___ =
            let uu___1 =
              FStar_Compiler_List.map FStar_Pervasives_Native.snd fs in
            FStar_Compiler_List.fold_left_map extract_mlpattern_to_pat g
              uu___1 in
          (match uu___ with
           | (g1, ps) ->
               let uu___1 =
                 let uu___2 = FStar_Compiler_List.last p1 in
                 let uu___3 =
                   let uu___4 =
                     FStar_Compiler_List.map FStar_Pervasives_Native.fst fs in
                   FStar_Compiler_List.zip uu___4 ps in
                 Pulse2Rust_Rust_Syntax.mk_pat_struct uu___2 uu___3 in
               (g1, uu___1))
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_Syntax.mlpattern_to_string p in
            FStar_Compiler_Util.format1 "mlpattern_to_pat %s" uu___2 in
          fail_nyi uu___1
let rec (lb_init_and_def :
  env ->
    FStar_Extraction_ML_Syntax.mllb ->
      (Prims.bool * Pulse2Rust_Rust_Syntax.typ * Pulse2Rust_Rust_Syntax.expr))
  =
  fun g ->
    fun lb ->
      let is_mut =
        FStar_Compiler_List.contains FStar_Extraction_ML_Syntax.Mutable
          lb.FStar_Extraction_ML_Syntax.mllb_meta in
      if is_mut
      then
        match (((lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr),
                (lb.FStar_Extraction_ML_Syntax.mllb_tysc))
        with
        | (FStar_Extraction_ML_Syntax.MLE_App
           ({
              FStar_Extraction_ML_Syntax.expr =
                FStar_Extraction_ML_Syntax.MLE_Name pe;
              FStar_Extraction_ML_Syntax.mlty = uu___;
              FStar_Extraction_ML_Syntax.loc = uu___1;_},
            init::[]),
           FStar_Pervasives_Native.Some
           ([], FStar_Extraction_ML_Syntax.MLTY_Named (ty::[], pt))) when
            (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath pe in
             uu___2 = "Pulse.Lib.Reference.alloc") &&
              (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath pt in
               uu___2 = "Pulse.Lib.Reference.ref")
            ->
            let uu___2 = extract_mlty g ty in
            let uu___3 = extract_mlexpr g init in (is_mut, uu___2, uu___3)
        | (FStar_Extraction_ML_Syntax.MLE_App
           ({
              FStar_Extraction_ML_Syntax.expr =
                FStar_Extraction_ML_Syntax.MLE_Name pe;
              FStar_Extraction_ML_Syntax.mlty = uu___;
              FStar_Extraction_ML_Syntax.loc = uu___1;_},
            init::len::[]),
           FStar_Pervasives_Native.Some
           ([], FStar_Extraction_ML_Syntax.MLTY_Named (ty::[], pt))) when
            (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath pe in
             uu___2 = "Pulse.Lib.Array.Core.alloc") &&
              (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath pt in
               uu___2 = "Pulse.Lib.Array.Core.array")
            ->
            let init1 = extract_mlexpr g init in
            let len1 = extract_mlexpr g len in
            let is_mut1 = false in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Compiler_Util.must
                    lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                FStar_Pervasives_Native.snd uu___4 in
              extract_mlty g uu___3 in
            let uu___3 =
              let uu___4 = Pulse2Rust_Rust_Syntax.mk_repeat init1 len1 in
              Pulse2Rust_Rust_Syntax.mk_reference_expr true uu___4 in
            (is_mut1, uu___2, uu___3)
        | uu___ ->
            let uu___1 =
              let uu___2 =
                FStar_Extraction_ML_Syntax.mlexpr_to_string
                  lb.FStar_Extraction_ML_Syntax.mllb_def in
              FStar_Compiler_Util.format1
                "unexpected initializer for mutable local: %s" uu___2 in
            fail uu___1
      else
        (let is_mut1 =
           match (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
           with
           | FStar_Extraction_ML_Syntax.MLE_App
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Name p;
                       FStar_Extraction_ML_Syntax.mlty = uu___1;
                       FStar_Extraction_ML_Syntax.loc = uu___2;_},
                     uu___3::[]);
                  FStar_Extraction_ML_Syntax.mlty = uu___4;
                  FStar_Extraction_ML_Syntax.loc = uu___5;_},
                uu___6)
               ->
               (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu___7 = "Pulse.Lib.Vec.alloc") ||
                 (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___7 = "Pulse.Lib.Box.alloc")
           | uu___1 -> false in
         let uu___1 =
           let uu___2 =
             let uu___3 =
               FStar_Compiler_Util.must
                 lb.FStar_Extraction_ML_Syntax.mllb_tysc in
             FStar_Pervasives_Native.snd uu___3 in
           extract_mlty g uu___2 in
         let uu___2 = extract_mlexpr g lb.FStar_Extraction_ML_Syntax.mllb_def in
         (is_mut1, uu___1, uu___2))
and (extract_mlexpr :
  env -> FStar_Extraction_ML_Syntax.mlexpr -> Pulse2Rust_Rust_Syntax.expr) =
  fun g ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit) ->
          Pulse2Rust_Rust_Syntax.Expr_lit Pulse2Rust_Rust_Syntax.Lit_unit
      | FStar_Extraction_ML_Syntax.MLE_Const c ->
          let lit = extract_mlconstant_to_lit c in
          Pulse2Rust_Rust_Syntax.Expr_lit lit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           e1::[])
          when
          let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "FStar.SizeT.uint_to_t" -> extract_mlexpr g e1
      | FStar_Extraction_ML_Syntax.MLE_Var x ->
          let uu___ = varname x in
          Pulse2Rust_Rust_Syntax.mk_expr_path_singl uu___
      | FStar_Extraction_ML_Syntax.MLE_Name p ->
          Pulse2Rust_Rust_Syntax.mk_expr_path_singl
            (FStar_Pervasives_Native.snd p)
      | FStar_Extraction_ML_Syntax.MLE_Let uu___ ->
          let uu___1 = extract_mlexpr_to_stmts g e in
          Pulse2Rust_Rust_Syntax.mk_block_expr uu___1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "Pulse.Lib.Pervasives.tfst") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.Pervasives.Native.fst")
          ->
          let e2 = extract_mlexpr g e1 in
          Pulse2Rust_Rust_Syntax.mk_expr_field_unnamed e2 Prims.int_zero
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "Pulse.Lib.Pervasives.tsnd") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.Pervasives.Native.snd")
          ->
          let e2 = extract_mlexpr g e1 in
          Pulse2Rust_Rust_Syntax.mk_expr_field_unnamed e2 Prims.int_one
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Pervasives.tthd" ->
          let e2 = extract_mlexpr g e1 in
          Pulse2Rust_Rust_Syntax.mk_expr_field_unnamed e2 (Prims.of_int (2))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5::e1::[])
          when
          FStar_Compiler_Util.starts_with (FStar_Pervasives_Native.snd p)
            "explode_ref_"
          ->
          let n = FStar_Compiler_String.length "explode_ref_" in
          let rname =
            FStar_Compiler_String.substring (FStar_Pervasives_Native.snd p) n
              ((FStar_Compiler_String.length (FStar_Pervasives_Native.snd p))
                 - n) in
          let flds =
            FStar_Compiler_Util.psmap_try_find g.record_field_names rname in
          let flds1 = FStar_Compiler_Util.must flds in
          let e2 = extract_mlexpr g e1 in
          let es =
            FStar_Compiler_List.map
              (fun f ->
                 let uu___6 = Pulse2Rust_Rust_Syntax.mk_expr_field e2 f in
                 Pulse2Rust_Rust_Syntax.mk_reference_expr true uu___6) flds1 in
          Pulse2Rust_Rust_Syntax.mk_expr_tuple es
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::uu___5::[])
          when
          (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Reference.op_Colon_Equals") ||
            (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "Pulse.Lib.Box.op_Colon_Equals")
          ->
          let e11 = extract_mlexpr g e1 in
          let e21 = extract_mlexpr g e2 in
          let b = type_of g e11 in
          if b
          then Pulse2Rust_Rust_Syntax.mk_assign e11 e21
          else Pulse2Rust_Rust_Syntax.mk_ref_assign e11 e21
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::uu___5::uu___6::[])
          when
          (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___7 = "Pulse.Lib.Reference.op_Bang") ||
            (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___7 = "Pulse.Lib.Box.op_Bang")
          ->
          let e2 = extract_mlexpr g e1 in
          let b = type_of g e2 in
          if b then e2 else Pulse2Rust_Rust_Syntax.mk_ref_read e2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::uu___5::[])
          when
          let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "Pulse.Lib.Pervasives.ref_apply" ->
          let uu___6 = extract_mlexpr g e1 in
          let uu___7 = let uu___8 = extract_mlexpr g e2 in [uu___8] in
          Pulse2Rust_Rust_Syntax.mk_call uu___6 uu___7
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Box.box_to_ref" ->
          let e2 = extract_mlexpr g e1 in
          let is_mut = true in
          Pulse2Rust_Rust_Syntax.mk_reference_expr is_mut e2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Box.alloc" ->
          let e2 = extract_mlexpr g e1 in
          let uu___5 =
            Pulse2Rust_Rust_Syntax.mk_expr_path
              ["std"; "boxed"; "Box"; "new"] in
          Pulse2Rust_Rust_Syntax.mk_call uu___5 [e2]
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::i::uu___5::uu___6::[])
          when
          ((let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___7 = "Pulse.Lib.Array.Core.op_Array_Access") ||
             (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___7 = "Pulse.Lib.Vec.op_Array_Access"))
            ||
            (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___7 = "Pulse.Lib.Vec.read_ref")
          ->
          let uu___7 = extract_mlexpr g e1 in
          let uu___8 = extract_mlexpr g i in
          Pulse2Rust_Rust_Syntax.mk_expr_index uu___7 uu___8
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::e3::uu___5)
          when
          ((let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___6 = "Pulse.Lib.Array.Core.op_Array_Assignment") ||
             (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___6 = "Pulse.Lib.Vec.op_Array_Assignment"))
            ||
            (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "Pulse.Lib.Vec.write_ref")
          ->
          let e11 = extract_mlexpr g e1 in
          let e21 = extract_mlexpr g e2 in
          let e31 = extract_mlexpr g e3 in
          let uu___6 = Pulse2Rust_Rust_Syntax.mk_expr_index e11 e21 in
          Pulse2Rust_Rust_Syntax.mk_assign uu___6 e31
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e_v::e_i::e_x::uu___5)
          when
          (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Vec.replace_i") ||
            (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "Pulse.Lib.Vec.replace_i_ref")
          ->
          let e_v1 = extract_mlexpr g e_v in
          let e_i1 = extract_mlexpr g e_i in
          let e_x1 = extract_mlexpr g e_x in
          let is_mut = true in
          let uu___6 =
            let uu___7 = Pulse2Rust_Rust_Syntax.mk_expr_index e_v1 e_i1 in
            Pulse2Rust_Rust_Syntax.mk_reference_expr is_mut uu___7 in
          Pulse2Rust_Rust_Syntax.mk_mem_replace uu___6 e_x1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e_r::e_x::uu___5)
          when
          let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "Pulse.Lib.Reference.replace" ->
          let uu___6 = extract_mlexpr g e_r in
          let uu___7 = extract_mlexpr g e_x in
          Pulse2Rust_Rust_Syntax.mk_mem_replace uu___6 uu___7
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Vec.vec_to_array" ->
          let e2 = extract_mlexpr g e1 in
          let is_mut = true in
          Pulse2Rust_Rust_Syntax.mk_reference_expr is_mut e2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Vec.alloc" ->
          let e11 = extract_mlexpr g e1 in
          let e21 = extract_mlexpr g e2 in
          let uu___5 =
            Pulse2Rust_Rust_Syntax.mk_expr_path_singl
              Pulse2Rust_Rust_Syntax.vec_new_fn in
          Pulse2Rust_Rust_Syntax.mk_call uu___5 [e11; e21]
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Array.Core.alloc" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
            FStar_Compiler_Util.format1 "mlexpr %s" uu___6 in
          fail_nyi uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::uu___5::[])
          when
          (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Vec.free") ||
            (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "Pulse.Lib.Box.free")
          ->
          let e2 = extract_mlexpr g e1 in
          let uu___6 = Pulse2Rust_Rust_Syntax.mk_expr_path_singl "drop" in
          Pulse2Rust_Rust_Syntax.mk_call uu___6 [e2]
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5::e1::uu___6)
          when
          let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___7 = "Pulse.Lib.Mutex.new_mutex" ->
          let e2 = extract_mlexpr g e1 in
          Pulse2Rust_Rust_Syntax.mk_new_mutex e2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5::e1::uu___6)
          when
          let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___7 = "Pulse.Lib.Mutex.lock" ->
          let e2 = extract_mlexpr g e1 in
          Pulse2Rust_Rust_Syntax.mk_lock_mutex e2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Array.Core.free" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
            FStar_Compiler_Util.format1 "mlexpr %s" uu___6 in
          fail_nyi uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Fun (uu___2, cond);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_}::{
                                                           FStar_Extraction_ML_Syntax.expr
                                                             =
                                                             FStar_Extraction_ML_Syntax.MLE_Fun
                                                             (uu___5, body);
                                                           FStar_Extraction_ML_Syntax.mlty
                                                             = uu___6;
                                                           FStar_Extraction_ML_Syntax.loc
                                                             = uu___7;_}::[])
          when
          let uu___8 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___8 = "Pulse.Lib.Core.while_" ->
          let expr_while_cond = extract_mlexpr g cond in
          let expr_while_body = extract_mlexpr_to_stmts g body in
          Pulse2Rust_Rust_Syntax.Expr_while
            {
              Pulse2Rust_Rust_Syntax.expr_while_cond = expr_while_cond;
              Pulse2Rust_Rust_Syntax.expr_while_body = expr_while_body
            }
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5::e1::uu___6)
          when
          let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___7 = "DPE.run_stt" -> extract_mlexpr g e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5)
          when
          (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "failwith") ||
            (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "Pulse.Lib.Core.unreachable")
          ->
          let uu___6 =
            Pulse2Rust_Rust_Syntax.mk_expr_path_singl
              Pulse2Rust_Rust_Syntax.panic_fn in
          Pulse2Rust_Rust_Syntax.mk_call uu___6 []
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           uu___2)
          when
          (let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___3 = "failwith") ||
            (let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___3 = "Pulse.Lib.Core.unreachable")
          ->
          let uu___3 =
            Pulse2Rust_Rust_Syntax.mk_expr_path_singl
              Pulse2Rust_Rust_Syntax.panic_fn in
          Pulse2Rust_Rust_Syntax.mk_call uu___3 []
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           e1::e2::[])
          when
          let uu___2 =
            let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            is_binop uu___3 in
          FStar_Pervasives_Native.uu___is_Some uu___2 ->
          let e11 = extract_mlexpr g e1 in
          let op =
            let uu___2 =
              let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              is_binop uu___3 in
            FStar_Compiler_Util.must uu___2 in
          let e21 = extract_mlexpr g e2 in
          Pulse2Rust_Rust_Syntax.mk_binop e11 op e21
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 =
            let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            is_binop uu___6 in
          FStar_Pervasives_Native.uu___is_Some uu___5 ->
          let e11 = extract_mlexpr g e1 in
          let op =
            let uu___5 =
              let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              is_binop uu___6 in
            FStar_Compiler_Util.must uu___5 in
          let e21 = extract_mlexpr g e2 in
          Pulse2Rust_Rust_Syntax.mk_binop e11 op e21
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           e1::e2::[])
          when
          let uu___2 =
            let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            is_binop uu___3 in
          FStar_Pervasives_Native.uu___is_Some uu___2 ->
          let e11 = extract_mlexpr g e1 in
          let op =
            let uu___2 =
              let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              is_binop uu___3 in
            FStar_Compiler_Util.must uu___2 in
          let e21 = extract_mlexpr g e2 in
          Pulse2Rust_Rust_Syntax.mk_binop e11 op e21
      | FStar_Extraction_ML_Syntax.MLE_App (head, args) ->
          let head1 = extract_mlexpr g head in
          let args1 = FStar_Compiler_List.map (extract_mlexpr g) args in
          Pulse2Rust_Rust_Syntax.mk_call head1 args1
      | FStar_Extraction_ML_Syntax.MLE_CTor (p, args) ->
          let is_native =
            ((FStar_Extraction_ML_Syntax.mlpath_to_string p) =
               "FStar.Pervasives.Native.Some")
              ||
              ((FStar_Extraction_ML_Syntax.mlpath_to_string p) =
                 "FStar.Pervasives.Native.None") in
          let ty_name =
            match e.FStar_Extraction_ML_Syntax.mlty with
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu___, p1) ->
                enum_or_struct_name (FStar_Pervasives_Native.snd p1)
            | uu___ ->
                FStar_Compiler_Effect.failwith "S.MLE_CTor: unexpected type" in
          let dexpr =
            if is_native
            then
              Pulse2Rust_Rust_Syntax.mk_expr_path_singl
                (FStar_Pervasives_Native.snd p)
            else
              Pulse2Rust_Rust_Syntax.mk_expr_path
                [ty_name; FStar_Pervasives_Native.snd p] in
          if (FStar_Compiler_List.length args) = Prims.int_zero
          then dexpr
          else
            (let uu___1 = FStar_Compiler_List.map (extract_mlexpr g) args in
             Pulse2Rust_Rust_Syntax.mk_call dexpr uu___1)
      | FStar_Extraction_ML_Syntax.MLE_TApp (head, uu___) ->
          extract_mlexpr g head
      | FStar_Extraction_ML_Syntax.MLE_If (cond, if_then, if_else_opt) ->
          let cond1 = extract_mlexpr g cond in
          let then_ = extract_mlexpr_to_stmts g if_then in
          let else_ =
            FStar_Compiler_Util.map_option (extract_mlexpr g) if_else_opt in
          let else_1 =
            match else_ with
            | FStar_Pervasives_Native.None -> else_
            | FStar_Pervasives_Native.Some (Pulse2Rust_Rust_Syntax.Expr_if
                uu___) -> else_
            | FStar_Pervasives_Native.Some (Pulse2Rust_Rust_Syntax.Expr_block
                uu___) -> else_
            | FStar_Pervasives_Native.Some else_2 ->
                let uu___ =
                  Pulse2Rust_Rust_Syntax.mk_block_expr
                    [Pulse2Rust_Rust_Syntax.Stmt_expr else_2] in
                FStar_Pervasives_Native.Some uu___ in
          Pulse2Rust_Rust_Syntax.mk_if cond1 then_ else_1
      | FStar_Extraction_ML_Syntax.MLE_Match (e1, branches) ->
          let e2 = extract_mlexpr g e1 in
          let uu___ =
            FStar_Compiler_List.map (extract_mlbranch_to_arm g) branches in
          Pulse2Rust_Rust_Syntax.mk_match e2 uu___
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, uu___, uu___1) ->
          extract_mlexpr g e1
      | FStar_Extraction_ML_Syntax.MLE_Record (uu___, nm, fields) ->
          let uu___1 =
            FStar_Compiler_List.map
              (fun uu___2 ->
                 match uu___2 with
                 | (f, e1) -> let uu___3 = extract_mlexpr g e1 in (f, uu___3))
              fields in
          Pulse2Rust_Rust_Syntax.mk_expr_struct [nm] uu___1
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, p) ->
          let uu___ = extract_mlexpr g e1 in
          Pulse2Rust_Rust_Syntax.mk_expr_field uu___
            (FStar_Pervasives_Native.snd p)
      | FStar_Extraction_ML_Syntax.MLE_Tuple l ->
          let uu___ = FStar_Compiler_List.map (extract_mlexpr g) l in
          Pulse2Rust_Rust_Syntax.mk_expr_tuple uu___
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
            FStar_Compiler_Util.format1 "mlexpr %s" uu___2 in
          fail_nyi uu___1
and (extract_mlexpr_to_stmts :
  env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      Pulse2Rust_Rust_Syntax.stmt Prims.list)
  =
  fun g ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit) -> []
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((uu___,
            { FStar_Extraction_ML_Syntax.mllb_name = uu___1;
              FStar_Extraction_ML_Syntax.mllb_tysc = uu___2;
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu___3;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Const
                    (FStar_Extraction_ML_Syntax.MLC_Unit);
                  FStar_Extraction_ML_Syntax.mlty = uu___4;
                  FStar_Extraction_ML_Syntax.loc = uu___5;_};
              FStar_Extraction_ML_Syntax.mllb_attrs = uu___6;
              FStar_Extraction_ML_Syntax.mllb_meta = uu___7;
              FStar_Extraction_ML_Syntax.print_typ = uu___8;_}::[]),
           e1)
          -> extract_mlexpr_to_stmts g e1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((FStar_Extraction_ML_Syntax.NonRec, lb::[]), e1) ->
          (match (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
           with
           | FStar_Extraction_ML_Syntax.MLE_App
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_TApp
                    ({
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Name p;
                       FStar_Extraction_ML_Syntax.mlty = uu___;
                       FStar_Extraction_ML_Syntax.loc = uu___1;_},
                     uu___2);
                  FStar_Extraction_ML_Syntax.mlty = uu___3;
                  FStar_Extraction_ML_Syntax.loc = uu___4;_},
                uu___5)
               when
               (FStar_Compiler_Util.starts_with
                  (FStar_Pervasives_Native.snd p) "unexplode_ref")
                 ||
                 ((FStar_Extraction_ML_Syntax.mlpath_to_string p) =
                    "Pulse.Lib.Mutex.unlock")
               -> extract_mlexpr_to_stmts g e1
           | uu___ ->
               let uu___1 = lb_init_and_def g lb in
               (match uu___1 with
                | (is_mut, ty, init) ->
                    let topt =
                      match (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                      with
                      | FStar_Extraction_ML_Syntax.MLE_App
                          ({
                             FStar_Extraction_ML_Syntax.expr =
                               FStar_Extraction_ML_Syntax.MLE_TApp
                               ({
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Name p;
                                  FStar_Extraction_ML_Syntax.mlty = uu___2;
                                  FStar_Extraction_ML_Syntax.loc = uu___3;_},
                                uu___4::[]);
                             FStar_Extraction_ML_Syntax.mlty = uu___5;
                             FStar_Extraction_ML_Syntax.loc = uu___6;_},
                           uu___7::e2::uu___8)
                          when
                          let uu___9 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath p in
                          uu___9 = "Pulse.Lib.Mutex.lock" ->
                          FStar_Pervasives_Native.Some ty
                      | uu___2 -> FStar_Pervasives_Native.None in
                    let s =
                      let uu___2 =
                        match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
                        | FStar_Pervasives_Native.Some
                            (uu___3, FStar_Extraction_ML_Syntax.MLTY_Erased)
                            -> FStar_Pervasives_Native.None
                        | uu___3 ->
                            let uu___4 =
                              varname lb.FStar_Extraction_ML_Syntax.mllb_name in
                            FStar_Pervasives_Native.Some uu___4 in
                      Pulse2Rust_Rust_Syntax.mk_local_stmt uu___2 topt is_mut
                        init in
                    let uu___2 =
                      let uu___3 =
                        push_local g lb.FStar_Extraction_ML_Syntax.mllb_name
                          ty is_mut in
                      extract_mlexpr_to_stmts uu___3 e1 in
                    s :: uu___2))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5)
          when
          let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "failwith" ->
          let uu___6 =
            let uu___7 =
              let uu___8 =
                Pulse2Rust_Rust_Syntax.mk_expr_path_singl
                  Pulse2Rust_Rust_Syntax.panic_fn in
              Pulse2Rust_Rust_Syntax.mk_call uu___8 [] in
            Pulse2Rust_Rust_Syntax.Stmt_expr uu___7 in
          [uu___6]
      | uu___ ->
          let uu___1 =
            let uu___2 = extract_mlexpr g e in
            Pulse2Rust_Rust_Syntax.Stmt_expr uu___2 in
          [uu___1]
and (extract_mlbranch_to_arm :
  env -> FStar_Extraction_ML_Syntax.mlbranch -> Pulse2Rust_Rust_Syntax.arm) =
  fun g ->
    fun uu___ ->
      match uu___ with
      | (pat, pat_guard, body) ->
          (match pat_guard with
           | FStar_Pervasives_Native.Some e ->
               let uu___1 =
                 let uu___2 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
                 FStar_Compiler_Util.format1
                   "mlbranch_to_arm with pat guard %s" uu___2 in
               fail_nyi uu___1
           | FStar_Pervasives_Native.None ->
               let uu___1 = extract_mlpattern_to_pat g pat in
               (match uu___1 with
                | (g1, pat1) ->
                    let arm_body = extract_mlexpr g1 body in
                    Pulse2Rust_Rust_Syntax.mk_arm pat1 arm_body))
let (has_rust_const_fn_attribute :
  FStar_Extraction_ML_Syntax.mllb -> Prims.bool) =
  fun lb ->
    FStar_Compiler_List.existsb
      (fun attr ->
         match attr.FStar_Extraction_ML_Syntax.expr with
         | FStar_Extraction_ML_Syntax.MLE_CTor (p, uu___) when
             let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___1 = "Pulse.Lib.Pervasives.Rust_const_fn" -> true
         | uu___ -> false) lb.FStar_Extraction_ML_Syntax.mllb_attrs
let (extract_generic_type_param_trait_bounds_aux :
  FStar_Extraction_ML_Syntax.mlexpr Prims.list ->
    Prims.string Prims.list Prims.list Prims.list)
  =
  fun attrs ->
    let uu___ =
      let uu___1 =
        FStar_Compiler_List.tryFind
          (fun attr ->
             match attr.FStar_Extraction_ML_Syntax.expr with
             | FStar_Extraction_ML_Syntax.MLE_CTor (p, uu___2) when
                 let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___3 = "Pulse.Lib.Pervasives.Rust_generics_bounds" -> true
             | uu___2 -> false) attrs in
      FStar_Compiler_Util.map_option
        (fun attr ->
           let uu___2 = attr.FStar_Extraction_ML_Syntax.expr in
           match uu___2 with
           | FStar_Extraction_ML_Syntax.MLE_CTor (p, args) ->
               let uu___3 =
                 let uu___4 = FStar_Compiler_List.hd args in
                 FStar_Extraction_ML_Util.list_elements uu___4 in
               (match uu___3 with
                | FStar_Pervasives_Native.Some l ->
                    FStar_Compiler_List.map
                      (fun tyvar_bounds ->
                         let uu___4 =
                           FStar_Extraction_ML_Util.list_elements
                             tyvar_bounds in
                         match uu___4 with
                         | FStar_Pervasives_Native.Some l1 ->
                             let uu___5 =
                               FStar_Compiler_List.map
                                 (fun e ->
                                    match e.FStar_Extraction_ML_Syntax.expr
                                    with
                                    | FStar_Extraction_ML_Syntax.MLE_Const
                                        (FStar_Extraction_ML_Syntax.MLC_String
                                        s) -> s
                                    | uu___6 ->
                                        FStar_Compiler_Effect.failwith
                                          "unexpected generic type param bounds")
                                 l1 in
                             FStar_Compiler_List.map
                               (fun bound ->
                                  FStar_Compiler_Util.split bound "::")
                               uu___5) l)) uu___1 in
    FStar_Compiler_Util.dflt [] uu___
let expand_list_with : 'a . 'a Prims.list -> Prims.nat -> 'a -> 'a Prims.list
  =
  fun l ->
    fun n ->
      fun x ->
        let rec nlist n1 x1 =
          if n1 = Prims.int_zero
          then []
          else (let uu___1 = nlist (n1 - Prims.int_one) x1 in x1 :: uu___1) in
        if n <= (FStar_Compiler_List.length l)
        then l
        else
          (let uu___1 = nlist (n - (FStar_Compiler_List.length l)) x in
           FStar_Compiler_List.op_At l uu___1)
let (extract_generic_type_param_trait_bounds :
  Prims.nat ->
    FStar_Extraction_ML_Syntax.mlattribute Prims.list ->
      Prims.string Prims.list Prims.list Prims.list)
  =
  fun n ->
    fun attrs ->
      let l = extract_generic_type_param_trait_bounds_aux attrs in
      expand_list_with l n []
let (extract_generic_type_params :
  FStar_Extraction_ML_Syntax.mlident Prims.list ->
    FStar_Extraction_ML_Syntax.mlattribute Prims.list ->
      Pulse2Rust_Rust_Syntax.generic_type_param Prims.list)
  =
  fun tyvars ->
    fun attrs ->
      let uu___ =
        extract_generic_type_param_trait_bounds
          (FStar_Compiler_List.length tyvars) attrs in
      FStar_Compiler_List.map2
        (fun tvar ->
           fun bounds ->
             let uu___1 = tyvar_of tvar in
             Pulse2Rust_Rust_Syntax.mk_generic_type_param uu___1 bounds)
        tyvars uu___
let (extract_top_level_lb :
  env ->
    FStar_Extraction_ML_Syntax.mlletbinding ->
      (Pulse2Rust_Rust_Syntax.item * env))
  =
  fun g ->
    fun lbs ->
      let uu___ = lbs in
      match uu___ with
      | (is_rec, lbs1) ->
          if is_rec = FStar_Extraction_ML_Syntax.Rec
          then fail_nyi "recursive let bindings"
          else
            (let uu___2 = lbs1 in
             match uu___2 with
             | lb::[] ->
                 (match (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                  with
                  | FStar_Extraction_ML_Syntax.MLE_Fun (bs, body) ->
                      let arg_names =
                        FStar_Compiler_List.map
                          (fun b ->
                             b.FStar_Extraction_ML_Syntax.mlbinder_name) bs in
                      let arg_attrs =
                        FStar_Compiler_List.map
                          (fun b ->
                             b.FStar_Extraction_ML_Syntax.mlbinder_attrs) bs in
                      let uu___3 =
                        match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
                        | FStar_Pervasives_Native.Some tsc ->
                            let uu___4 = arg_ts_and_ret_t tsc in
                            (match uu___4 with
                             | (tvars, arg_ts, ret_t) ->
                                 (tvars, arg_ts,
                                   (FStar_Pervasives_Native.Some ret_t)))
                        | FStar_Pervasives_Native.None ->
                            let uu___4 =
                              FStar_Compiler_List.map
                                (fun b ->
                                   b.FStar_Extraction_ML_Syntax.mlbinder_ty)
                                bs in
                            ([], uu___4, FStar_Pervasives_Native.None) in
                      (match uu___3 with
                       | (tvars, arg_ts, ret_t) ->
                           let fn_const = has_rust_const_fn_attribute lb in
                           let uu___4 =
                             let uu___5 =
                               extract_generic_type_params tvars
                                 lb.FStar_Extraction_ML_Syntax.mllb_attrs in
                             extract_top_level_sig g fn_const
                               lb.FStar_Extraction_ML_Syntax.mllb_name uu___5
                               arg_names arg_attrs arg_ts ret_t in
                           (match uu___4 with
                            | (fn_sig, g_body) ->
                                let fn_body =
                                  extract_mlexpr_to_stmts g_body body in
                                let uu___5 =
                                  let uu___6 =
                                    Pulse2Rust_Rust_Syntax.mk_fn fn_sig
                                      fn_body in
                                  Pulse2Rust_Rust_Syntax.Item_fn uu___6 in
                                let uu___6 =
                                  push_fn g
                                    lb.FStar_Extraction_ML_Syntax.mllb_name
                                    fn_sig in
                                (uu___5, uu___6)))
                  | uu___3 ->
                      (match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
                       | FStar_Pervasives_Native.Some ([], ty) ->
                           let name = lb.FStar_Extraction_ML_Syntax.mllb_name in
                           let ty1 = extract_mlty g ty in
                           let uu___4 =
                             let uu___5 =
                               extract_mlexpr g
                                 lb.FStar_Extraction_ML_Syntax.mllb_def in
                             Pulse2Rust_Rust_Syntax.mk_item_static name ty1
                               uu___5 in
                           let uu___5 = push_static g name ty1 in
                           (uu___4, uu___5)
                       | uu___4 ->
                           let uu___5 =
                             let uu___6 =
                               FStar_Extraction_ML_Syntax.mlexpr_to_string
                                 lb.FStar_Extraction_ML_Syntax.mllb_def in
                             FStar_Compiler_Util.format1
                               "top level lb def with either no tysc or generics %s"
                               uu___6 in
                           fail_nyi uu___5)))
let (has_rust_derive_attr :
  FStar_Extraction_ML_Syntax.mlattribute Prims.list ->
    Pulse2Rust_Rust_Syntax.attribute FStar_Pervasives_Native.option)
  =
  fun attrs ->
    let uu___ =
      FStar_Compiler_List.tryFind
        (fun attr ->
           match attr.FStar_Extraction_ML_Syntax.expr with
           | FStar_Extraction_ML_Syntax.MLE_CTor (p, uu___1) when
               let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___2 = "Pulse.Lib.Pervasives.Rust_derive" -> true
           | uu___1 -> false) attrs in
    FStar_Compiler_Util.map_option
      (fun attr ->
         let uu___1 = attr.FStar_Extraction_ML_Syntax.expr in
         match uu___1 with
         | FStar_Extraction_ML_Syntax.MLE_CTor (p, arg::uu___2) ->
             let uu___3 = arg.FStar_Extraction_ML_Syntax.expr in
             (match uu___3 with
              | FStar_Extraction_ML_Syntax.MLE_Const
                  (FStar_Extraction_ML_Syntax.MLC_String s) ->
                  Pulse2Rust_Rust_Syntax.mk_derive_attr s)) uu___
let (extract_struct_defn :
  env ->
    FStar_Extraction_ML_Syntax.mlattribute Prims.list ->
      FStar_Extraction_ML_Syntax.one_mltydecl ->
        (Pulse2Rust_Rust_Syntax.item * env))
  =
  fun g ->
    fun attrs ->
      fun d ->
        let uu___ = d.FStar_Extraction_ML_Syntax.tydecl_defn in
        match uu___ with
        | FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fts) ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = has_rust_derive_attr attrs in
                  FStar_Compiler_Util.map_option (fun a -> [a]) uu___4 in
                FStar_Compiler_Util.dflt [] uu___3 in
              let uu___3 =
                enum_or_struct_name d.FStar_Extraction_ML_Syntax.tydecl_name in
              let uu___4 =
                extract_generic_type_params
                  d.FStar_Extraction_ML_Syntax.tydecl_parameters attrs in
              let uu___5 =
                FStar_Compiler_List.map
                  (fun uu___6 ->
                     match uu___6 with
                     | (f, t) -> let uu___7 = extract_mlty g t in (f, uu___7))
                  fts in
              Pulse2Rust_Rust_Syntax.mk_item_struct uu___2 uu___3 uu___4
                uu___5 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Compiler_List.map FStar_Pervasives_Native.fst fts in
                FStar_Compiler_Util.psmap_add g.record_field_names
                  d.FStar_Extraction_ML_Syntax.tydecl_name uu___4 in
              {
                fns = (g.fns);
                statics = (g.statics);
                gamma = (g.gamma);
                record_field_names = uu___3;
                reachable_defs = (g.reachable_defs)
              } in
            (uu___1, uu___2)
let (extract_type_abbrev :
  env ->
    FStar_Extraction_ML_Syntax.mlattribute Prims.list ->
      FStar_Extraction_ML_Syntax.one_mltydecl ->
        (Pulse2Rust_Rust_Syntax.item * env))
  =
  fun g ->
    fun attrs ->
      fun d ->
        let uu___ = d.FStar_Extraction_ML_Syntax.tydecl_defn in
        match uu___ with
        | FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
            let uu___1 =
              let uu___2 =
                extract_generic_type_params
                  d.FStar_Extraction_ML_Syntax.tydecl_parameters attrs in
              let uu___3 = extract_mlty g t in
              Pulse2Rust_Rust_Syntax.mk_item_type
                d.FStar_Extraction_ML_Syntax.tydecl_name uu___2 uu___3 in
            (uu___1, g)
let (extract_enum :
  env ->
    FStar_Extraction_ML_Syntax.mlattribute Prims.list ->
      FStar_Extraction_ML_Syntax.one_mltydecl ->
        (Pulse2Rust_Rust_Syntax.item * env))
  =
  fun g ->
    fun attrs ->
      fun d ->
        let uu___ = d.FStar_Extraction_ML_Syntax.tydecl_defn in
        match uu___ with
        | FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType
            cts) ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = has_rust_derive_attr attrs in
                  FStar_Compiler_Util.map_option (fun a -> [a]) uu___4 in
                FStar_Compiler_Util.dflt [] uu___3 in
              let uu___3 =
                enum_or_struct_name d.FStar_Extraction_ML_Syntax.tydecl_name in
              let uu___4 =
                extract_generic_type_params
                  d.FStar_Extraction_ML_Syntax.tydecl_parameters attrs in
              let uu___5 =
                FStar_Compiler_List.map
                  (fun uu___6 ->
                     match uu___6 with
                     | (cname, dts) ->
                         let uu___7 =
                           FStar_Compiler_List.map
                             (fun uu___8 ->
                                match uu___8 with
                                | (uu___9, t) -> extract_mlty g t) dts in
                         (cname, uu___7)) cts in
              Pulse2Rust_Rust_Syntax.mk_item_enum uu___2 uu___3 uu___4 uu___5 in
            (uu___1, g)
let (extract_mltydecl :
  env ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.list ->
      FStar_Extraction_ML_Syntax.mltydecl ->
        (Pulse2Rust_Rust_Syntax.item Prims.list * env))
  =
  fun g ->
    fun mlattrs ->
      fun d ->
        FStar_Compiler_List.fold_left
          (fun uu___ ->
             fun d1 ->
               match uu___ with
               | (items, g1) ->
                   let f =
                     match d1.FStar_Extraction_ML_Syntax.tydecl_defn with
                     | FStar_Pervasives_Native.Some
                         (FStar_Extraction_ML_Syntax.MLTD_Abbrev uu___1) ->
                         extract_type_abbrev
                     | FStar_Pervasives_Native.Some
                         (FStar_Extraction_ML_Syntax.MLTD_Record uu___1) ->
                         extract_struct_defn
                     | FStar_Pervasives_Native.Some
                         (FStar_Extraction_ML_Syntax.MLTD_DType uu___1) ->
                         extract_enum
                     | uu___1 ->
                         let uu___2 =
                           let uu___3 =
                             FStar_Extraction_ML_Syntax.one_mltydecl_to_string
                               d1 in
                           FStar_Compiler_Util.format1 "mltydecl %s" uu___3 in
                         fail_nyi uu___2 in
                   let uu___1 = f g1 mlattrs d1 in
                   (match uu___1 with
                    | (item, g2) ->
                        ((FStar_Compiler_List.op_At items [item]), g2)))
          ([], g) d
let (empty_defs : reachable_defs) =
  FStar_Compiler_Set.empty FStar_Class_Ord.ord_string ()
let (singleton : FStar_Extraction_ML_Syntax.mlpath -> reachable_defs) =
  fun p ->
    let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
    FStar_Compiler_Set.singleton FStar_Class_Ord.ord_string uu___
let reachable_defs_list :
  'a . ('a -> reachable_defs) -> 'a Prims.list -> reachable_defs =
  fun f ->
    fun l ->
      let uu___ = FStar_Compiler_Set.empty FStar_Class_Ord.ord_string () in
      FStar_Compiler_List.fold_left
        (fun defs ->
           fun x ->
             let uu___1 = f x in
             FStar_Compiler_Set.union FStar_Class_Ord.ord_string defs uu___1)
        uu___ l
let reachable_defs_option :
  'a .
    ('a -> reachable_defs) ->
      'a FStar_Pervasives_Native.option -> reachable_defs
  =
  fun f ->
    fun o ->
      match o with
      | FStar_Pervasives_Native.None -> empty_defs
      | FStar_Pervasives_Native.Some x -> f x
let rec (reachable_defs_mlty :
  FStar_Extraction_ML_Syntax.mlty -> reachable_defs) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu___, t2) ->
        let uu___1 = reachable_defs_mlty t1 in
        let uu___2 = reachable_defs_mlty t2 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___1 uu___2
    | FStar_Extraction_ML_Syntax.MLTY_Named (tps, p) ->
        let uu___ = reachable_defs_list reachable_defs_mlty tps in
        let uu___1 = singleton p in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
        reachable_defs_list reachable_defs_mlty ts
    | FStar_Extraction_ML_Syntax.MLTY_Top -> empty_defs
    | FStar_Extraction_ML_Syntax.MLTY_Erased -> empty_defs
let (reachable_defs_mltyscheme :
  FStar_Extraction_ML_Syntax.mltyscheme -> reachable_defs) =
  fun uu___ -> match uu___ with | (uu___1, t) -> reachable_defs_mlty t
let rec (reachable_defs_mlpattern :
  FStar_Extraction_ML_Syntax.mlpattern -> reachable_defs) =
  fun p ->
    match p with
    | FStar_Extraction_ML_Syntax.MLP_Wild -> empty_defs
    | FStar_Extraction_ML_Syntax.MLP_Const uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLP_Var uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLP_CTor (c, ps) ->
        let uu___ = singleton c in
        let uu___1 = reachable_defs_list reachable_defs_mlpattern ps in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
        reachable_defs_list reachable_defs_mlpattern ps
    | FStar_Extraction_ML_Syntax.MLP_Record (syms, fs) ->
        let uu___ =
          FStar_Compiler_Set.singleton FStar_Class_Ord.ord_string
            (FStar_Compiler_String.concat "." syms) in
        let uu___1 =
          reachable_defs_list
            (fun uu___2 ->
               match uu___2 with
               | (uu___3, p1) -> reachable_defs_mlpattern p1) fs in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
        reachable_defs_list reachable_defs_mlpattern ps
let rec (reachable_defs_expr' :
  FStar_Extraction_ML_Syntax.mlexpr' -> reachable_defs) =
  fun e ->
    match e with
    | FStar_Extraction_ML_Syntax.MLE_Const uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLE_Var uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLE_Name p -> singleton p
    | FStar_Extraction_ML_Syntax.MLE_Let (lb, e1) ->
        let uu___ = reachable_defs_mlletbinding lb in
        let uu___1 = reachable_defs_expr e1 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_App (e1, es) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 = reachable_defs_list reachable_defs_expr es in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_TApp (e1, ts) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 = reachable_defs_list reachable_defs_mlty ts in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Fun (args, e1) ->
        let uu___ =
          reachable_defs_list
            (fun b ->
               reachable_defs_mlty b.FStar_Extraction_ML_Syntax.mlbinder_ty)
            args in
        let uu___1 = reachable_defs_expr e1 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Match (e1, bs) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 = reachable_defs_list reachable_defs_mlbranch bs in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t1, t2) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 =
          let uu___2 = reachable_defs_mlty t1 in
          let uu___3 = reachable_defs_mlty t2 in
          FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___2 uu___3 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_CTor (p, es) ->
        let uu___ = singleton p in
        let uu___1 = reachable_defs_list reachable_defs_expr es in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Seq es ->
        reachable_defs_list reachable_defs_expr es
    | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
        reachable_defs_list reachable_defs_expr es
    | FStar_Extraction_ML_Syntax.MLE_Record (p, n, fs) ->
        let uu___ =
          FStar_Compiler_Set.singleton FStar_Class_Ord.ord_string
            (FStar_Compiler_String.concat "."
               (FStar_Compiler_List.op_At p [n])) in
        let uu___1 =
          reachable_defs_list
            (fun uu___2 ->
               match uu___2 with | (uu___3, e1) -> reachable_defs_expr e1) fs in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Proj (e1, uu___) ->
        reachable_defs_expr e1
    | FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3_opt) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 =
          let uu___2 = reachable_defs_expr e2 in
          let uu___3 = reachable_defs_option reachable_defs_expr e3_opt in
          FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___2 uu___3 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Raise (p, es) ->
        let uu___ = singleton p in
        let uu___1 = reachable_defs_list reachable_defs_expr es in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Try (e1, bs) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 = reachable_defs_list reachable_defs_mlbranch bs in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
and (reachable_defs_expr :
  FStar_Extraction_ML_Syntax.mlexpr -> reachable_defs) =
  fun e ->
    let uu___ = reachable_defs_expr' e.FStar_Extraction_ML_Syntax.expr in
    let uu___1 = reachable_defs_mlty e.FStar_Extraction_ML_Syntax.mlty in
    FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
and (reachable_defs_mlbranch :
  FStar_Extraction_ML_Syntax.mlbranch -> reachable_defs) =
  fun uu___ ->
    match uu___ with
    | (p, wopt, e) ->
        let uu___1 = reachable_defs_mlpattern p in
        let uu___2 =
          let uu___3 = reachable_defs_option reachable_defs_expr wopt in
          let uu___4 = reachable_defs_expr e in
          FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___3 uu___4 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___1 uu___2
and (reachable_defs_mllb : FStar_Extraction_ML_Syntax.mllb -> reachable_defs)
  =
  fun lb ->
    let uu___ =
      reachable_defs_option reachable_defs_mltyscheme
        lb.FStar_Extraction_ML_Syntax.mllb_tysc in
    let uu___1 = reachable_defs_expr lb.FStar_Extraction_ML_Syntax.mllb_def in
    FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
and (reachable_defs_mlletbinding :
  FStar_Extraction_ML_Syntax.mlletbinding ->
    Prims.string FStar_Compiler_Set.set)
  =
  fun uu___ ->
    match uu___ with
    | (uu___1, lbs) -> reachable_defs_list reachable_defs_mllb lbs
let (reachable_defs_mltybody :
  FStar_Extraction_ML_Syntax.mltybody -> reachable_defs) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTD_Abbrev t1 -> reachable_defs_mlty t1
    | FStar_Extraction_ML_Syntax.MLTD_Record fs ->
        reachable_defs_list
          (fun uu___ ->
             match uu___ with | (uu___1, t1) -> reachable_defs_mlty t1) fs
    | FStar_Extraction_ML_Syntax.MLTD_DType cts ->
        reachable_defs_list
          (fun uu___ ->
             match uu___ with
             | (uu___1, dts) ->
                 reachable_defs_list
                   (fun uu___2 ->
                      match uu___2 with
                      | (uu___3, t1) -> reachable_defs_mlty t1) dts) cts
let (reachable_defs_one_mltydecl :
  FStar_Extraction_ML_Syntax.one_mltydecl -> reachable_defs) =
  fun t ->
    reachable_defs_option reachable_defs_mltybody
      t.FStar_Extraction_ML_Syntax.tydecl_defn
let (reachable_defs_mltydecl :
  FStar_Extraction_ML_Syntax.mltydecl -> reachable_defs) =
  fun t -> reachable_defs_list reachable_defs_one_mltydecl t
let (mlmodule1_name :
  FStar_Extraction_ML_Syntax.mlmodule1 ->
    FStar_Extraction_ML_Syntax.mlsymbol Prims.list)
  =
  fun m ->
    match m.FStar_Extraction_ML_Syntax.mlmodule1_m with
    | FStar_Extraction_ML_Syntax.MLM_Ty l ->
        FStar_Compiler_List.map
          (fun t -> t.FStar_Extraction_ML_Syntax.tydecl_name) l
    | FStar_Extraction_ML_Syntax.MLM_Let (uu___, lbs) ->
        FStar_Compiler_List.map
          (fun lb -> lb.FStar_Extraction_ML_Syntax.mllb_name) lbs
    | FStar_Extraction_ML_Syntax.MLM_Exn (s, uu___) -> [s]
    | FStar_Extraction_ML_Syntax.MLM_Top uu___ -> []
    | FStar_Extraction_ML_Syntax.MLM_Loc uu___ -> []
let (reachable_defs_mlmodule1 :
  FStar_Extraction_ML_Syntax.mlmodule1 -> reachable_defs) =
  fun m ->
    let defs =
      match m.FStar_Extraction_ML_Syntax.mlmodule1_m with
      | FStar_Extraction_ML_Syntax.MLM_Ty t -> reachable_defs_mltydecl t
      | FStar_Extraction_ML_Syntax.MLM_Let lb ->
          reachable_defs_mlletbinding lb
      | FStar_Extraction_ML_Syntax.MLM_Exn (uu___, args) ->
          reachable_defs_list
            (fun uu___1 ->
               match uu___1 with | (uu___2, t) -> reachable_defs_mlty t) args
      | FStar_Extraction_ML_Syntax.MLM_Top e -> reachable_defs_expr e
      | FStar_Extraction_ML_Syntax.MLM_Loc uu___ -> empty_defs in
    defs
let (reachable_defs_decls :
  FStar_Extraction_ML_Syntax.mlmodule -> reachable_defs) =
  fun decls -> reachable_defs_list reachable_defs_mlmodule1 decls
let (decl_reachable :
  reachable_defs ->
    Prims.string -> FStar_Extraction_ML_Syntax.mlmodule1 -> Prims.bool)
  =
  fun reachable_defs1 ->
    fun mname ->
      fun d ->
        match d.FStar_Extraction_ML_Syntax.mlmodule1_m with
        | FStar_Extraction_ML_Syntax.MLM_Ty t ->
            FStar_Compiler_List.existsb
              (fun ty_decl ->
                 FStar_Compiler_Set.mem FStar_Class_Ord.ord_string
                   (Prims.strcat mname
                      (Prims.strcat "."
                         ty_decl.FStar_Extraction_ML_Syntax.tydecl_name))
                   reachable_defs1) t
        | FStar_Extraction_ML_Syntax.MLM_Let (uu___, lbs) ->
            FStar_Compiler_List.existsb
              (fun lb ->
                 FStar_Compiler_Set.mem FStar_Class_Ord.ord_string
                   (Prims.strcat mname
                      (Prims.strcat "."
                         lb.FStar_Extraction_ML_Syntax.mllb_name))
                   reachable_defs1) lbs
        | FStar_Extraction_ML_Syntax.MLM_Exn (p, uu___) -> false
        | FStar_Extraction_ML_Syntax.MLM_Top uu___ -> false
        | FStar_Extraction_ML_Syntax.MLM_Loc uu___ -> false
let (extract_one :
  env ->
    Prims.string ->
      FStar_Extraction_ML_UEnv.binding Prims.list ->
        FStar_Extraction_ML_Syntax.mlmodule -> (Prims.string * env))
  =
  fun g ->
    fun mname ->
      fun gamma ->
        fun decls ->
          let uu___ =
            FStar_Compiler_List.fold_left
              (fun uu___1 ->
                 fun d ->
                   match uu___1 with
                   | (items, g1) ->
                       let uu___2 =
                         let uu___3 =
                           decl_reachable g1.reachable_defs mname d in
                         Prims.op_Negation uu___3 in
                       if uu___2
                       then (items, g1)
                       else
                         (match d.FStar_Extraction_ML_Syntax.mlmodule1_m with
                          | FStar_Extraction_ML_Syntax.MLM_Let
                              (FStar_Extraction_ML_Syntax.NonRec,
                               {
                                 FStar_Extraction_ML_Syntax.mllb_name =
                                   mllb_name;
                                 FStar_Extraction_ML_Syntax.mllb_tysc =
                                   uu___4;
                                 FStar_Extraction_ML_Syntax.mllb_add_unit =
                                   uu___5;
                                 FStar_Extraction_ML_Syntax.mllb_def = uu___6;
                                 FStar_Extraction_ML_Syntax.mllb_attrs =
                                   uu___7;
                                 FStar_Extraction_ML_Syntax.mllb_meta =
                                   uu___8;
                                 FStar_Extraction_ML_Syntax.print_typ =
                                   uu___9;_}::[])
                              when
                              (((FStar_Compiler_Util.starts_with mllb_name
                                   "explode_ref")
                                  ||
                                  (FStar_Compiler_Util.starts_with mllb_name
                                     "unexplode_ref"))
                                 ||
                                 (FStar_Compiler_Util.starts_with mllb_name
                                    "uu___is_"))
                                ||
                                (FStar_Compiler_Util.starts_with mllb_name
                                   "__proj__")
                              -> (items, g1)
                          | FStar_Extraction_ML_Syntax.MLM_Let lb ->
                              let uu___4 = extract_top_level_lb g1 lb in
                              (match uu___4 with
                               | (f, g2) ->
                                   ((FStar_Compiler_List.op_At items [f]),
                                     g2))
                          | FStar_Extraction_ML_Syntax.MLM_Loc uu___4 ->
                              (items, g1)
                          | FStar_Extraction_ML_Syntax.MLM_Ty td ->
                              let uu___4 =
                                extract_mltydecl g1
                                  d.FStar_Extraction_ML_Syntax.mlmodule1_attrs
                                  td in
                              (match uu___4 with
                               | (d_items, g2) ->
                                   ((FStar_Compiler_List.op_At items d_items),
                                     g2))
                          | uu___4 ->
                              let uu___5 =
                                let uu___6 =
                                  FStar_Extraction_ML_Syntax.mlmodule1_to_string
                                    d in
                                FStar_Compiler_Util.format1
                                  "top level decl %s" uu___6 in
                              fail_nyi uu___5)) ([], g) decls in
          match uu___ with
          | (items, env1) ->
              let f = Pulse2Rust_Rust_Syntax.mk_file "a.rs" items in
              let s = RustBindings.file_to_rust f in (s, env1)
let (file_to_module_name : Prims.string -> Prims.string) =
  fun f ->
    let suffix = ".ast" in
    let s = FStar_Compiler_Util.basename f in
    let s1 =
      FStar_Compiler_String.substring s Prims.int_zero
        ((FStar_Compiler_String.length s) -
           (FStar_Compiler_String.length suffix)) in
    FStar_Compiler_Util.replace_chars s1 95 "."
type dict =
  (Prims.string Prims.list * FStar_Extraction_ML_UEnv.binding Prims.list *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Compiler_Util.smap
let rec (topsort :
  dict ->
    Prims.string Prims.list ->
      Prims.string Prims.list ->
        Prims.string -> (Prims.string Prims.list * Prims.string Prims.list))
  =
  fun d ->
    fun grey ->
      fun black ->
        fun root ->
          let grey1 = root :: grey in
          let deps =
            let uu___ =
              let uu___1 = FStar_Compiler_Util.smap_try_find d root in
              FStar_Compiler_Util.must uu___1 in
            match uu___ with | (deps1, uu___1, uu___2) -> deps1 in
          let deps1 =
            FStar_Compiler_List.filter
              (fun f ->
                 (let uu___ = FStar_Compiler_Util.smap_keys d in
                  FStar_Compiler_List.mem f uu___) &&
                   (Prims.op_Negation (f = root))) deps in
          (let uu___1 =
             FStar_Compiler_List.existsb
               (fun d1 -> FStar_Compiler_List.mem d1 grey1) deps1 in
           if uu___1
           then
             let uu___2 =
               FStar_Compiler_Util.format1 "cyclic dependency: %s" root in
             FStar_Compiler_Effect.failwith uu___2
           else ());
          (let deps2 =
             FStar_Compiler_List.filter
               (fun f -> Prims.op_Negation (FStar_Compiler_List.mem f black))
               deps1 in
           let uu___1 =
             FStar_Compiler_List.fold_left
               (fun uu___2 ->
                  fun dep ->
                    match uu___2 with
                    | (grey2, black1) -> topsort d grey2 black1 dep)
               (grey1, black) deps2 in
           match uu___1 with
           | (grey2, black1) ->
               let uu___2 =
                 FStar_Compiler_List.filter
                   (fun g -> Prims.op_Negation (g = root)) grey2 in
               (uu___2,
                 (if FStar_Compiler_List.mem root black1
                  then black1
                  else root :: black1)))
let rec (topsort_all :
  dict -> Prims.string Prims.list -> Prims.string Prims.list) =
  fun d ->
    fun black ->
      let uu___ =
        let uu___1 = FStar_Compiler_Util.smap_keys d in
        FStar_Compiler_List.for_all
          (fun f -> FStar_Compiler_List.contains f black) uu___1 in
      if uu___
      then black
      else
        (let rem =
           let uu___2 = FStar_Compiler_Util.smap_keys d in
           FStar_Compiler_List.filter
             (fun f ->
                Prims.op_Negation (FStar_Compiler_List.contains f black))
             uu___2 in
         let root =
           FStar_Compiler_List.nth rem
             ((FStar_Compiler_List.length rem) - Prims.int_one) in
         let uu___2 = topsort d [] black root in
         match uu___2 with
         | (grey, black1) ->
             (if (FStar_Compiler_List.length grey) <> Prims.int_zero
              then
                FStar_Compiler_Effect.failwith
                  "topsort_all: not all files are reachable"
              else ();
              topsort_all d black1))
let (read_all_ast_files : Prims.string Prims.list -> dict) =
  fun files ->
    let d = FStar_Compiler_Util.smap_create (Prims.of_int (100)) in
    FStar_Compiler_List.iter
      (fun f ->
         let contents =
           let uu___1 = FStar_Compiler_Util.load_value_from_file f in
           match uu___1 with
           | FStar_Pervasives_Native.Some r -> r
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 FStar_Compiler_Util.format1 "Could not load file %s" f in
               FStar_Compiler_Effect.failwith uu___2 in
         let uu___1 = file_to_module_name f in
         FStar_Compiler_Util.smap_add d uu___1 contents) files;
    d
let (build_decls_dict :
  dict -> FStar_Extraction_ML_Syntax.mlmodule1 FStar_Compiler_Util.smap) =
  fun d ->
    let dd = FStar_Compiler_Util.smap_create (Prims.of_int (100)) in
    FStar_Compiler_Util.smap_iter d
      (fun module_nm ->
         fun uu___1 ->
           match uu___1 with
           | (uu___2, uu___3, decls) ->
               FStar_Compiler_List.iter
                 (fun decl ->
                    let uu___4 = mlmodule1_name decl in
                    FStar_Compiler_List.iter
                      (fun decl_nm ->
                         FStar_Compiler_Util.smap_add dd
                           (Prims.strcat module_nm (Prims.strcat "." decl_nm))
                           decl) uu___4) decls);
    dd
let rec (collect_reachable_defs_aux :
  FStar_Extraction_ML_Syntax.mlmodule1 FStar_Compiler_Util.smap ->
    reachable_defs -> reachable_defs -> reachable_defs)
  =
  fun dd ->
    fun worklist ->
      fun reachable_defs1 ->
        let uu___ =
          FStar_Compiler_Set.is_empty FStar_Class_Ord.ord_string worklist in
        if uu___
        then reachable_defs1
        else
          (let uu___2 =
             FStar_Compiler_Set.elems FStar_Class_Ord.ord_string worklist in
           match uu___2 with
           | hd::uu___3 ->
               let worklist1 =
                 FStar_Compiler_Set.remove FStar_Class_Ord.ord_string hd
                   worklist in
               let reachable_defs2 =
                 FStar_Compiler_Set.add FStar_Class_Ord.ord_string hd
                   reachable_defs1 in
               let worklist2 =
                 let hd_decl = FStar_Compiler_Util.smap_try_find dd hd in
                 match hd_decl with
                 | FStar_Pervasives_Native.None -> worklist1
                 | FStar_Pervasives_Native.Some hd_decl1 ->
                     let hd_reachable_defs =
                       reachable_defs_mlmodule1 hd_decl1 in
                     let uu___4 =
                       FStar_Compiler_Set.elems FStar_Class_Ord.ord_string
                         hd_reachable_defs in
                     FStar_Compiler_List.fold_left
                       (fun worklist3 ->
                          fun def ->
                            let uu___5 =
                              (FStar_Compiler_Set.mem
                                 FStar_Class_Ord.ord_string def
                                 reachable_defs2)
                                ||
                                (FStar_Compiler_Set.mem
                                   FStar_Class_Ord.ord_string def worklist3) in
                            if uu___5
                            then worklist3
                            else
                              FStar_Compiler_Set.add
                                FStar_Class_Ord.ord_string def worklist3)
                       worklist1 uu___4 in
               collect_reachable_defs_aux dd worklist2 reachable_defs2)
let (collect_reachable_defs : dict -> Prims.string -> reachable_defs) =
  fun d ->
    fun root_module ->
      let dd = build_decls_dict d in
      let root_decls =
        let uu___ =
          let uu___1 = FStar_Compiler_Util.smap_try_find d root_module in
          FStar_Compiler_Util.must uu___1 in
        match uu___ with | (uu___1, uu___2, decls) -> decls in
      let worklist =
        FStar_Compiler_List.fold_left
          (fun worklist1 ->
             fun decl ->
               let uu___ =
                 let uu___1 = mlmodule1_name decl in
                 FStar_Compiler_List.map
                   (fun s -> Prims.strcat root_module (Prims.strcat "." s))
                   uu___1 in
               FStar_Compiler_Set.addn FStar_Class_Ord.ord_string uu___
                 worklist1) empty_defs root_decls in
      collect_reachable_defs_aux dd worklist empty_defs
let (extract : Prims.string Prims.list -> Prims.string) =
  fun files ->
    let d = read_all_ast_files files in
    let all_modules = topsort_all d [] in
    FStar_Compiler_Util.print1 "order: %s\n"
      (FStar_Compiler_String.concat "; " all_modules);
    (let uu___1 = all_modules in
     match uu___1 with
     | root_module::uu___2 ->
         let reachable_defs1 = collect_reachable_defs d root_module in
         let g = empty_env reachable_defs1 in
         let s =
           let uu___3 =
             let uu___4 =
               FStar_Compiler_List.fold_left_map
                 (fun g1 ->
                    fun f ->
                      let uu___5 =
                        let uu___6 = FStar_Compiler_Util.smap_try_find d f in
                        FStar_Compiler_Util.must uu___6 in
                      match uu___5 with
                      | (uu___6, bs, ds) ->
                          let uu___7 = extract_one g1 f bs ds in
                          (match uu___7 with | (s1, g2) -> (g2, s1))) g
                 (FStar_Compiler_List.rev all_modules) in
             FStar_Pervasives_Native.snd uu___4 in
           FStar_Compiler_String.concat " " uu___3 in
         s)
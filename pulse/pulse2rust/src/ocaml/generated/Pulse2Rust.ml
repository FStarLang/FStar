open Prims
let (tyvar_of : Prims.string -> Prims.string) =
  fun s ->
    let uu___ =
      FStar_String.substring s Prims.int_one
        ((FStar_String.length s) - Prims.int_one) in
    FStar_String.uppercase uu___
let (varname : Prims.string -> Prims.string) =
  fun s -> FStar_Compiler_Util.replace_char s 39 95
let fail : 'uuuuu . Prims.string -> 'uuuuu =
  fun s ->
    let uu___ =
      FStar_Compiler_Util.format1 "Pulse to Rust extraction failed: %s" s in
    failwith uu___
let fail_nyi : 'uuuuu . Prims.string -> 'uuuuu =
  fun s ->
    let uu___ =
      FStar_Compiler_Util.format1
        "Pulse to Rust extraction failed: no support yet for %s" s in
    failwith uu___
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
let (extract_mlty :
  FStar_Extraction_ML_Syntax.mlty -> Pulse2Rust_Rust_Syntax.typ) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var s ->
        let uu___ = tyvar_of s in Pulse2Rust_Rust_Syntax.Typ_name uu___
    | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
        let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
        uu___ = "FStar.UInt32.t" -> Pulse2Rust_Rust_Syntax.Typ_name "u32"
    | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
        let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
        uu___ = "FStar.Int32.t" -> Pulse2Rust_Rust_Syntax.Typ_name "i32"
    | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
        let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
        uu___ = "FStar.UInt64.t" -> Pulse2Rust_Rust_Syntax.Typ_name "u64"
    | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
        let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
        uu___ = "FStar.Int64.t" -> Pulse2Rust_Rust_Syntax.Typ_name "i64"
    | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
        let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
        uu___ = "Prims.bool" -> Pulse2Rust_Rust_Syntax.Typ_name "bool"
    | FStar_Extraction_ML_Syntax.MLTY_Erased ->
        Pulse2Rust_Rust_Syntax.Typ_name "unit"
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Extraction_ML_Syntax.mlty_to_string t in
          FStar_Compiler_Util.format1 "mlty %s" uu___2 in
        fail_nyi uu___1
let (extract_top_level_fn_arg :
  Prims.string ->
    FStar_Extraction_ML_Syntax.mlty -> Pulse2Rust_Rust_Syntax.fn_arg)
  =
  fun arg_name ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var s ->
          let uu___ =
            let uu___1 = tyvar_of s in Pulse2Rust_Rust_Syntax.Typ_name uu___1 in
          Pulse2Rust_Rust_Syntax.mk_scalar_fn_arg arg_name uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          ((((let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___ = "FStar.UInt32.t") ||
               (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu___ = "FStar.Int32.t"))
              ||
              (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___ = "FStar.UInt64.t"))
             ||
             (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___ = "FStar.Int64.t"))
            ||
            (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___ = "Prims.bool")
          ->
          let uu___ = extract_mlty t in
          Pulse2Rust_Rust_Syntax.mk_scalar_fn_arg arg_name uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Pulse.Lib.Reference.ref" ->
          let is_mut = true in
          let uu___ = extract_mlty arg in
          Pulse2Rust_Rust_Syntax.mk_ref_fn_arg arg_name is_mut uu___
      | FStar_Extraction_ML_Syntax.MLTY_Erased ->
          Pulse2Rust_Rust_Syntax.mk_scalar_fn_arg arg_name
            (Pulse2Rust_Rust_Syntax.Typ_name "unit")
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_Syntax.mlty_to_string t in
            FStar_Compiler_Util.format1 "top level fn arg %s" uu___2 in
          fail_nyi uu___1
let (extract_top_level_sig :
  Prims.string ->
    FStar_Extraction_ML_Syntax.mlidents ->
      Prims.string Prims.list ->
        FStar_Extraction_ML_Syntax.mlty Prims.list ->
          FStar_Extraction_ML_Syntax.mlty ->
            Pulse2Rust_Rust_Syntax.fn_signature)
  =
  fun fn_name ->
    fun tvars ->
      fun arg_names ->
        fun arg_ts ->
          fun ret_t ->
            let fn_args =
              let uu___ = FStar_Compiler_List.map varname arg_names in
              FStar_Compiler_List.map2 extract_top_level_fn_arg uu___ arg_ts in
            let fn_ret_t = extract_mlty ret_t in
            Pulse2Rust_Rust_Syntax.mk_fn_signature fn_name tvars fn_args
              fn_ret_t
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
let rec (extract_mlexpr :
  FStar_Extraction_ML_Syntax.mlexpr -> Pulse2Rust_Rust_Syntax.expr) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const
        (FStar_Extraction_ML_Syntax.MLC_Unit) ->
        Pulse2Rust_Rust_Syntax.Expr_path "unitv"
    | FStar_Extraction_ML_Syntax.MLE_Const
        (FStar_Extraction_ML_Syntax.MLC_Int (lit_int_val, swopt)) ->
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
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
        Pulse2Rust_Rust_Syntax.Expr_lit
          (Pulse2Rust_Rust_Syntax.Lit_int
             {
               Pulse2Rust_Rust_Syntax.lit_int_val = lit_int_val;
               Pulse2Rust_Rust_Syntax.lit_int_signed = lit_int_signed;
               Pulse2Rust_Rust_Syntax.lit_int_width = lit_int_width
             })
    | FStar_Extraction_ML_Syntax.MLE_Var x ->
        let uu___ = varname x in Pulse2Rust_Rust_Syntax.Expr_path uu___
    | FStar_Extraction_ML_Syntax.MLE_Name p ->
        Pulse2Rust_Rust_Syntax.Expr_path (FStar_Pervasives_Native.snd p)
    | FStar_Extraction_ML_Syntax.MLE_Let uu___ ->
        let uu___1 =
          FStar_Compiler_Effect.op_Bar_Greater e extract_mlexpr_to_stmts in
        FStar_Compiler_Effect.op_Bar_Greater uu___1
          Pulse2Rust_Rust_Syntax.mk_block_expr
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
        let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
        uu___6 = "Pulse.Lib.Reference.op_Colon_Equals" ->
        let e11 = extract_mlexpr e1 in
        let e21 = extract_mlexpr e2 in
        Pulse2Rust_Rust_Syntax.mk_ref_assign e11 e21
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
        let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
        uu___7 = "Pulse.Lib.Reference.op_Bang" ->
        let e2 = extract_mlexpr e1 in Pulse2Rust_Rust_Syntax.mk_ref_read e2
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
        let expr_while_cond = extract_mlexpr cond in
        let expr_while_body = extract_mlexpr_to_stmts body in
        Pulse2Rust_Rust_Syntax.Expr_while
          {
            Pulse2Rust_Rust_Syntax.expr_while_cond = expr_while_cond;
            Pulse2Rust_Rust_Syntax.expr_while_body = expr_while_body
          }
    | FStar_Extraction_ML_Syntax.MLE_App (head, args) ->
        let head1 = extract_mlexpr head in
        let args1 = FStar_Compiler_List.map extract_mlexpr args in
        Pulse2Rust_Rust_Syntax.mk_call head1 args1
    | FStar_Extraction_ML_Syntax.MLE_TApp (head, uu___) ->
        extract_mlexpr head
    | FStar_Extraction_ML_Syntax.MLE_If (cond, if_then, if_else_opt) ->
        let cond1 = extract_mlexpr cond in
        let then_ = extract_mlexpr_to_stmts if_then in
        let else_ = FStar_Compiler_Util.map_option extract_mlexpr if_else_opt in
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
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
          FStar_Compiler_Util.format1 "mlexpr %s" uu___2 in
        fail_nyi uu___1
and (extract_mlexpr_to_stmts :
  FStar_Extraction_ML_Syntax.mlexpr -> Pulse2Rust_Rust_Syntax.stmt Prims.list)
  =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const
        (FStar_Extraction_ML_Syntax.MLC_Unit) -> []
    | FStar_Extraction_ML_Syntax.MLE_Var x ->
        let uu___ =
          let uu___1 =
            let uu___2 = varname x in Pulse2Rust_Rust_Syntax.Expr_path uu___2 in
          Pulse2Rust_Rust_Syntax.Stmt_expr uu___1 in
        [uu___]
    | FStar_Extraction_ML_Syntax.MLE_Name p ->
        [Pulse2Rust_Rust_Syntax.Stmt_expr
           (Pulse2Rust_Rust_Syntax.Expr_path
              (FStar_Extraction_ML_Syntax.mlpath_to_string p))]
    | FStar_Extraction_ML_Syntax.MLE_Let
        ((FStar_Extraction_ML_Syntax.NonRec, lb::[]), e1) ->
        let is_mut = false in
        let s =
          let uu___ = extract_mlexpr lb.FStar_Extraction_ML_Syntax.mllb_def in
          Pulse2Rust_Rust_Syntax.mk_local_stmt
            lb.FStar_Extraction_ML_Syntax.mllb_name is_mut uu___ in
        let uu___ = extract_mlexpr_to_stmts e1 in s :: uu___
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Extraction_ML_Syntax.mlexpr_to_string e in
          FStar_Compiler_Util.format1 "mlexpr_to_stmt  %s" uu___2 in
        fail_nyi uu___1
let (extract_top_level_lb :
  FStar_Extraction_ML_Syntax.mlletbinding -> Pulse2Rust_Rust_Syntax.fn) =
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
               (if
                  FStar_Pervasives_Native.uu___is_None
                    lb.FStar_Extraction_ML_Syntax.mllb_tysc
                then
                  (let uu___4 =
                     FStar_Compiler_Util.format1
                       "unexpected: mllb_tsc is None for %s"
                       lb.FStar_Extraction_ML_Syntax.mllb_name in
                   fail uu___4)
                else ();
                (let uu___4 = lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                 match uu___4 with
                 | FStar_Pervasives_Native.Some tsc ->
                     let uu___5 =
                       match (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                       with
                       | FStar_Extraction_ML_Syntax.MLE_Fun (bs, body) ->
                           let uu___6 =
                             FStar_Compiler_List.map
                               FStar_Pervasives_Native.fst bs in
                           (uu___6, body)
                       | uu___6 ->
                           let uu___7 =
                             let uu___8 =
                               FStar_Extraction_ML_Syntax.mlexpr_to_string
                                 lb.FStar_Extraction_ML_Syntax.mllb_def in
                             FStar_Compiler_Util.format1
                               "top level lb def %s" uu___8 in
                           fail_nyi uu___7 in
                     (match uu___5 with
                      | (arg_names, body) ->
                          let uu___6 = arg_ts_and_ret_t tsc in
                          (match uu___6 with
                           | (tvars, arg_ts, ret_t) ->
                               let fn_sig =
                                 let uu___7 =
                                   FStar_Compiler_List.map tyvar_of tvars in
                                 extract_top_level_sig
                                   lb.FStar_Extraction_ML_Syntax.mllb_name
                                   uu___7 arg_names arg_ts ret_t in
                               let fn_body = extract_mlexpr_to_stmts body in
                               Pulse2Rust_Rust_Syntax.mk_fn fn_sig fn_body)))))
let (extract_one : Prims.string -> unit) =
  fun file ->
    let uu___ =
      let uu___1 = FStar_Compiler_Util.load_value_from_file file in
      match uu___1 with
      | FStar_Pervasives_Native.Some r -> r
      | FStar_Pervasives_Native.None -> failwith "Could not load file" in
    match uu___ with
    | (gamma, decls) ->
        let uu___1 = uu___ in
        FStar_Compiler_List.iter
          (fun d ->
             match d with
             | FStar_Extraction_ML_Syntax.MLM_Let lb ->
                 let f = extract_top_level_lb lb in
                 (FStar_Compiler_Util.print_string "Extracted to:\n";
                  (let uu___3 =
                     let uu___4 = RustBindings.fn_to_string f in
                     Prims.op_Hat uu___4 "\n" in
                   FStar_Compiler_Util.print_string uu___3))
             | uu___2 ->
                 let uu___3 =
                   let uu___4 =
                     FStar_Extraction_ML_Syntax.mlmodule1_to_string d in
                   FStar_Compiler_Util.format1 "top level decl %s" uu___4 in
                 fail_nyi uu___3) decls
let (extract : Prims.string Prims.list -> unit) =
  fun files -> FStar_Compiler_List.iter extract_one files
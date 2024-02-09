open Prims
let (pulse_translate_type_without_decay :
  FStar_Extraction_Krml.translate_type_without_decay_t) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let p1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          (p1 = "Pulse.Lib.Reference.ref") ||
            (p1 = "Pulse.Lib.Array.Core.array")
          ->
          let uu___ =
            FStar_Extraction_Krml.translate_type_without_decay env arg in
          FStar_Extraction_Krml.TBuf uu___
      | uu___ ->
          FStar_Compiler_Effect.raise
            FStar_Extraction_Krml.NotSupportedByKrmlExtension
let (flatten_app :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e ->
    let rec aux args e1 =
      match e1.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_App (head, args0) ->
          aux (FStar_Compiler_List.op_At args0 args) head
      | uu___ ->
          (match args with
           | [] -> e1
           | uu___1 ->
               {
                 FStar_Extraction_ML_Syntax.expr =
                   (FStar_Extraction_ML_Syntax.MLE_App (e1, args));
                 FStar_Extraction_ML_Syntax.mlty =
                   (e1.FStar_Extraction_ML_Syntax.mlty);
                 FStar_Extraction_ML_Syntax.loc =
                   (e1.FStar_Extraction_ML_Syntax.loc)
               }) in
    aux [] e
let (pulse_translate_expr : FStar_Extraction_Krml.translate_expr_t) =
  fun env ->
    fun e ->
      let e1 = flatten_app e in
      match e1.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           init::[])
          when
          let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "Pulse.Lib.Reference.alloc" ->
          let uu___2 =
            let uu___3 = FStar_Extraction_Krml.translate_expr env init in
            (FStar_Extraction_Krml.Stack, uu___3,
              (FStar_Extraction_Krml.EConstant
                 (FStar_Extraction_Krml.UInt32, "1"))) in
          FStar_Extraction_Krml.EBufCreate uu___2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_App
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_App
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
                     e2::[]);
                  FStar_Extraction_ML_Syntax.mlty = uu___5;
                  FStar_Extraction_ML_Syntax.loc = uu___6;_},
                _v::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___7;
             FStar_Extraction_ML_Syntax.loc = uu___8;_},
           _perm::[])
          when
          let uu___9 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___9 = "Pulse.Lib.Reference.op_Bang" ->
          let uu___9 =
            let uu___10 = FStar_Extraction_Krml.translate_expr env e2 in
            (uu___10,
              (FStar_Extraction_Krml.EQualified (["C"], "_zero_for_deref"))) in
          FStar_Extraction_Krml.EBufRead uu___9
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
           e2::_v::_perm::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Reference.op_Bang" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e2 in
            (uu___6,
              (FStar_Extraction_Krml.EQualified (["C"], "_zero_for_deref"))) in
          FStar_Extraction_Krml.EBufRead uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_App
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_App
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
                     e11::[]);
                  FStar_Extraction_ML_Syntax.mlty = uu___5;
                  FStar_Extraction_ML_Syntax.loc = uu___6;_},
                e2::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___7;
             FStar_Extraction_ML_Syntax.loc = uu___8;_},
           _e3::[])
          when
          let uu___9 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___9 = "Pulse.Lib.Reference.op_Colon_Equals" ->
          let uu___9 =
            let uu___10 = FStar_Extraction_Krml.translate_expr env e11 in
            let uu___11 = FStar_Extraction_Krml.translate_expr env e2 in
            (uu___10,
              (FStar_Extraction_Krml.EQualified (["C"], "_zero_for_deref")),
              uu___11) in
          FStar_Extraction_Krml.EBufWrite uu___9
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
           e11::e2::_e3::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Reference.op_Colon_Equals" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env e2 in
            (uu___6,
              (FStar_Extraction_Krml.EQualified (["C"], "_zero_for_deref")),
              uu___7) in
          FStar_Extraction_Krml.EBufWrite uu___5
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
           x::n::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Array.Core.alloc" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env x in
            let uu___7 = FStar_Extraction_Krml.translate_expr env n in
            (FStar_Extraction_Krml.ManuallyManaged, uu___6, uu___7) in
          FStar_Extraction_Krml.EBufCreate uu___5
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
           e2::i::_p::_w::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Array.Core.op_Array_Access" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e2 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env i in
            (uu___6, uu___7) in
          FStar_Extraction_Krml.EBufRead uu___5
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
           e2::i::v::_w::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Array.Core.op_Array_Assignment" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e2 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env i in
            let uu___8 = FStar_Extraction_Krml.translate_expr env v in
            (uu___6, uu___7, uu___8) in
          FStar_Extraction_Krml.EBufWrite uu___5
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
           e2::i::uu___5)
          when
          let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "Pulse.Lib.Array.Core.pts_to_range_index" ->
          let uu___6 =
            let uu___7 = FStar_Extraction_Krml.translate_expr env e2 in
            let uu___8 = FStar_Extraction_Krml.translate_expr env i in
            (uu___7, uu___8) in
          FStar_Extraction_Krml.EBufRead uu___6
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
           e2::i::v::uu___5)
          when
          let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "Pulse.Lib.Array.Core.pts_to_range_upd" ->
          let uu___6 =
            let uu___7 = FStar_Extraction_Krml.translate_expr env e2 in
            let uu___8 = FStar_Extraction_Krml.translate_expr env i in
            let uu___9 = FStar_Extraction_Krml.translate_expr env v in
            (uu___7, uu___8, uu___9) in
          FStar_Extraction_Krml.EBufWrite uu___6
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
           x::_w::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Pulse.Lib.Array.Core.free" ->
          let uu___5 = FStar_Extraction_Krml.translate_expr env x in
          FStar_Extraction_Krml.EBufFree uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Fun (uu___2, test);
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
          let uu___8 =
            let uu___9 = FStar_Extraction_Krml.translate_expr env test in
            let uu___10 = FStar_Extraction_Krml.translate_expr env body in
            (uu___9, uu___10) in
          FStar_Extraction_Krml.EWhile uu___8
      | uu___ ->
          FStar_Compiler_Effect.raise
            FStar_Extraction_Krml.NotSupportedByKrmlExtension
let (uu___189 : unit) =
  FStar_Extraction_Krml.register_pre_translate_type_without_decay
    pulse_translate_type_without_decay;
  FStar_Extraction_Krml.register_pre_translate_expr pulse_translate_expr
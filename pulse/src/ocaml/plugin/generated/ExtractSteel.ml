open Prims
let (steel_translate_type_without_decay :
  FStar_Extraction_Krml.translate_type_without_decay_t) =
  fun env ->
    fun t ->
      (let uu___1 = FStar_Extraction_ML_Syntax.mlty_to_string t in
       FStar_Compiler_Util.print1
         "Got control in steel_translate_type for (%s)!\n" uu___1);
      (match t with
       | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
           let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___1 = "Steel.TLArray.t" ->
           let uu___1 =
             FStar_Extraction_Krml.translate_type_without_decay env arg in
           FStar_Extraction_Krml.TConstBuf uu___1
       | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
           let p1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           (((p1 = "Steel.Reference.ref") || (p1 = "Steel.ST.Reference.ref"))
              || (p1 = "Steel.ST.HigherArray.ptr"))
             || (p1 = "Pulse.Lib.Reference.ref")
           ->
           let uu___1 =
             FStar_Extraction_Krml.translate_type_without_decay env arg in
           FStar_Extraction_Krml.TBuf uu___1
       | uu___1 ->
           FStar_Compiler_Effect.raise
             FStar_Extraction_Krml.NotSupportedByKrmlExtension)
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
let (steel_translate_expr : FStar_Extraction_Krml.translate_expr_t) =
  fun env ->
    fun e ->
      let e1 = flatten_app e in
      match e1.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_},
           uu___4)
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.null_ptr" ->
          let uu___5 = FStar_Extraction_Krml.translate_type env t in
          FStar_Extraction_Krml.EBufNull uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_},
           arg::[])
          when
          let uu___4 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___4 = "Steel.ST.HigherArray.is_null_ptr" ->
          let uu___4 = FStar_Extraction_Krml.translate_type env t in
          let uu___5 = FStar_Extraction_Krml.translate_expr env arg in
          FStar_Extraction_Krml.generate_is_null uu___4 uu___5
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
           _perm0::_perm1::_seq0::_seq1::e0::_len0::e11::_len1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.ptrdiff_ptr" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e0 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env e11 in
            (uu___6, uu___7) in
          FStar_Extraction_Krml.EBufDiff uu___5
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
           e11::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.TLArray.get" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env e2 in
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
           _perm::e11::_len::_seq::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.index_ptr" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env e2 in
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
           e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.Reference.read" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e2 in
            (uu___6,
              (FStar_Extraction_Krml.EQualified (["C"], "_zero_for_deref"))) in
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
           _perm::_v::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.Reference.read" ->
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
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           init::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.Reference._alloca" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env init in
            (FStar_Extraction_Krml.Stack, uu___6,
              (FStar_Extraction_Krml.EConstant
                 (FStar_Extraction_Krml.UInt32, "1"))) in
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
           init::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "Steel.Reference.malloc") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.ST.Reference.alloc")
          ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env init in
            (FStar_Extraction_Krml.ManuallyManaged, uu___6,
              (FStar_Extraction_Krml.EConstant
                 (FStar_Extraction_Krml.UInt32, "1"))) in
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
           e0::e11::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.malloc_ptr" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e0 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env e11 in
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
           e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.Reference.free" ->
          let uu___5 = FStar_Extraction_Krml.translate_expr env e2 in
          FStar_Extraction_Krml.EBufFree uu___5
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
           _v::e2::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "Steel.ST.HigherArray.free_ptr") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.ST.Reference.free")
          ->
          let uu___5 = FStar_Extraction_Krml.translate_expr env e2 in
          FStar_Extraction_Krml.EBufFree uu___5
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
           e11::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.ptr_shift" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env e2 in
            (uu___6, uu___7) in
          FStar_Extraction_Krml.EBufSub uu___5
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
           e11::_len::_s::e2::e3::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.upd_ptr" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env e2 in
            let uu___8 = FStar_Extraction_Krml.translate_expr env e3 in
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
           e11::_len::_s::e2::e3::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.HigherArray.upd_ptr" ->
          let uu___5 =
            let uu___6 = FStar_Extraction_Krml.translate_expr env e11 in
            let uu___7 = FStar_Extraction_Krml.translate_expr env e2 in
            let uu___8 = FStar_Extraction_Krml.translate_expr env e3 in
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
           e11::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.Reference.write" ->
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
           _v::e11::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.ST.Reference.write" ->
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
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           uu___2::[])
          when
          let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___3 = "Steel.ST.Reference._push_frame" ->
          FStar_Extraction_Krml.EPushFrame
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
           uu___5::uu___6::[])
          when
          let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___7 = "Steel.ST.Reference._free_and_pop_frame" ->
          FStar_Extraction_Krml.EPopFrame
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
           uu___5::uu___6::uu___7::e11::uu___8::e2::e3::uu___9::e4::e5::[])
          when
          let uu___10 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___10 = "Steel.ST.HigherArray.blit_ptr" ->
          let uu___10 =
            let uu___11 = FStar_Extraction_Krml.translate_expr env e11 in
            let uu___12 = FStar_Extraction_Krml.translate_expr env e2 in
            let uu___13 = FStar_Extraction_Krml.translate_expr env e3 in
            let uu___14 = FStar_Extraction_Krml.translate_expr env e4 in
            let uu___15 = FStar_Extraction_Krml.translate_expr env e5 in
            (uu___11, uu___12, uu___13, uu___14, uu___15) in
          FStar_Extraction_Krml.EBufBlit uu___10
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
           uu___5::uu___6::e2::[])
          when
          let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___7 = "Steel.Effect.Atomic.return" ->
          FStar_Extraction_Krml.translate_expr env e2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           _inv::test::body::[])
          when
          let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "Steel.ST.Loops.while_loop" ->
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Extraction_Krml.translate_expr env test in
                let uu___6 =
                  let uu___7 = FStar_Extraction_Krml.translate_expr env body in
                  [uu___7] in
                uu___5 :: uu___6 in
              FStar_Extraction_Krml.EUnit :: uu___4 in
            ((FStar_Extraction_Krml.EQualified
                (["Steel"; "Loops"], "while_loop")), uu___3) in
          FStar_Extraction_Krml.EApp uu___2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("Steel"::"ST"::"Printf"::[], fn);
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           args)
          ->
          let uu___2 =
            let uu___3 =
              FStar_Compiler_List.map
                (FStar_Extraction_Krml.translate_expr env) args in
            ((FStar_Extraction_Krml.EQualified (["LowStar"; "Printf"], fn)),
              uu___3) in
          FStar_Extraction_Krml.EApp uu___2
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
           uu___5::uu___6::e2::[])
          when
          (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___7 = "Steel.Effect.Atomic.return") ||
            (let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___7 = "Steel.ST.Util.return")
          -> FStar_Extraction_Krml.translate_expr env e2
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
           _fp::_fp'::_opened::_p::_i::{
                                         FStar_Extraction_ML_Syntax.expr =
                                           FStar_Extraction_ML_Syntax.MLE_Fun
                                           (uu___5, body);
                                         FStar_Extraction_ML_Syntax.mlty =
                                           uu___6;
                                         FStar_Extraction_ML_Syntax.loc =
                                           uu___7;_}::[])
          when
          (let uu___8 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___8 = "Steel.ST.Util.with_invariant") ||
            (let uu___8 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___8 = "Steel.Effect.Atomic.with_invariant")
          -> FStar_Extraction_Krml.translate_expr env body
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
           _fp::_fp'::_opened::_p::_i::e2::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "Steel.ST.Util.with_invariant") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.Effect.Atomic.with_invariant")
          ->
          let uu___5 =
            let uu___6 =
              let uu___7 =
                FStar_Compiler_Util.string_of_int
                  (FStar_Pervasives_Native.fst
                     e2.FStar_Extraction_ML_Syntax.loc) in
              FStar_Compiler_Util.format2
                "Extraction of with_invariant requires its argument to be a function literal at extraction time, try marking its argument inline_for_extraction (%s, %s)"
                uu___7
                (FStar_Pervasives_Native.snd
                   e2.FStar_Extraction_ML_Syntax.loc) in
            (FStar_Errors_Codes.Fatal_ExtractionUnsupported, uu___6) in
          FStar_Errors.raise_error uu___5
            FStar_Compiler_Range_Type.dummyRange
      | uu___ ->
          FStar_Compiler_Effect.raise
            FStar_Extraction_Krml.NotSupportedByKrmlExtension
let (steel_translate_let : FStar_Extraction_Krml.translate_let_t) =
  fun env ->
    fun flavor ->
      fun lb ->
        match lb with
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_App
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_TApp
                       ({
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name p;
                          FStar_Extraction_ML_Syntax.mlty = uu___1;
                          FStar_Extraction_ML_Syntax.loc = uu___2;_},
                        uu___3);
                     FStar_Extraction_ML_Syntax.mlty = uu___4;
                     FStar_Extraction_ML_Syntax.loc = uu___5;_},
                   l::[]);
                FStar_Extraction_ML_Syntax.mlty = uu___6;
                FStar_Extraction_ML_Syntax.loc = uu___7;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu___8;_} when
            let uu___9 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___9 = "Steel.TLArray.create" ->
            if
              FStar_Compiler_List.mem FStar_Extraction_ML_Syntax.NoExtract
                meta
            then FStar_Pervasives_Native.None
            else
              (let meta1 = FStar_Extraction_Krml.translate_flags meta in
               let env1 =
                 FStar_Compiler_List.fold_left
                   (fun env2 ->
                      fun name1 -> FStar_Extraction_Krml.extend_t env2 name1)
                   env tvars in
               let t1 = FStar_Extraction_Krml.translate_type env1 t in
               let name1 = ((env1.FStar_Extraction_Krml.module_name), name) in
               try
                 (fun uu___10 ->
                    match () with
                    | () ->
                        let expr =
                          let uu___11 = FStar_Extraction_Krml.list_elements l in
                          FStar_Compiler_List.map
                            (FStar_Extraction_Krml.translate_expr env1)
                            uu___11 in
                        FStar_Pervasives_Native.Some
                          (FStar_Extraction_Krml.DGlobal
                             (meta1, name1,
                               (FStar_Compiler_List.length tvars), t1,
                               (FStar_Extraction_Krml.EBufCreateL
                                  (FStar_Extraction_Krml.Eternal, expr)))))
                   ()
               with
               | uu___10 ->
                   ((let uu___12 =
                       let uu___13 =
                         let uu___14 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                         let uu___15 = FStar_Compiler_Util.print_exn uu___10 in
                         FStar_Compiler_Util.format2
                           "Error extracting %s to KaRaMeL (%s)\n" uu___14
                           uu___15 in
                       (FStar_Errors_Codes.Warning_DefinitionNotTranslated,
                         uu___13) in
                     FStar_Errors.log_issue
                       FStar_Compiler_Range_Type.dummyRange uu___12);
                    FStar_Pervasives_Native.Some
                      (FStar_Extraction_Krml.DGlobal
                         (meta1, name1, (FStar_Compiler_List.length tvars),
                           t1, FStar_Extraction_Krml.EAny))))
        | uu___ ->
            FStar_Compiler_Effect.raise
              FStar_Extraction_Krml.NotSupportedByKrmlExtension
let (uu___465 : unit) =
  FStar_Extraction_Krml.register_pre_translate_type_without_decay
    steel_translate_type_without_decay;
  FStar_Extraction_Krml.register_pre_translate_expr steel_translate_expr;
  FStar_Extraction_Krml.register_pre_translate_let steel_translate_let
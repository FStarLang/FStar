open Prims
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
let (dbg : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "extraction"
let (pulse_translate_type_without_decay :
  FStar_Extraction_Krml.translate_type_without_decay_t) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let p1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          (((p1 = "Pulse.Lib.Reference.ref") ||
              (p1 = "Pulse.Lib.Array.Core.array"))
             || (p1 = "Pulse.Lib.Vec.vec"))
            || (p1 = "Pulse.Lib.Box.box")
          ->
          let uu___ =
            FStar_Extraction_Krml.translate_type_without_decay env arg in
          FStar_Extraction_Krml.TBuf uu___
      | uu___ ->
          FStar_Compiler_Effect.raise
            FStar_Extraction_Krml.NotSupportedByKrmlExtension
let (head_and_args :
  FStar_Extraction_ML_Syntax.mlexpr ->
    (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlexpr
      Prims.list))
  =
  fun e ->
    let rec aux acc e1 =
      match e1.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_App (head, args) ->
          aux (FStar_Compiler_List.op_At args acc) head
      | uu___ -> (e1, acc) in
    aux [] e
let (zero_for_deref : FStar_Extraction_Krml.expr) =
  FStar_Extraction_Krml.EQualified (["C"], "_zero_for_deref")
let (pulse_translate_expr : FStar_Extraction_Krml.translate_expr_t) =
  fun env ->
    fun e ->
      let e1 = flatten_app e in
      (let uu___1 = FStar_Compiler_Effect.op_Bang dbg in
       if uu___1
       then
         let uu___2 = FStar_Extraction_ML_Syntax.mlexpr_to_string e1 in
         FStar_Compiler_Util.print1_warning
           "ExtractPulse.pulse_translate_expr %s\n" uu___2
       else ());
      (let cb = FStar_Extraction_Krml.translate_expr env in
       match e1.FStar_Extraction_ML_Syntax.expr with
       | FStar_Extraction_ML_Syntax.MLE_App
           ({
              FStar_Extraction_ML_Syntax.expr =
                FStar_Extraction_ML_Syntax.MLE_Name p;
              FStar_Extraction_ML_Syntax.mlty = uu___1;
              FStar_Extraction_ML_Syntax.loc = uu___2;_},
            init::[])
           when
           let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___3 = "Pulse.Lib.Reference.alloc" ->
           let uu___3 =
             let uu___4 = cb init in
             (FStar_Extraction_Krml.Stack, uu___4,
               (FStar_Extraction_Krml.EConstant
                  (FStar_Extraction_Krml.UInt32, "1"))) in
           FStar_Extraction_Krml.EBufCreate uu___3
       | FStar_Extraction_ML_Syntax.MLE_App
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
            init::[])
           when
           let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Reference.alloc" ->
           let uu___6 =
             let uu___7 = cb init in
             (FStar_Extraction_Krml.Stack, uu___7,
               (FStar_Extraction_Krml.EConstant
                  (FStar_Extraction_Krml.UInt32, "1"))) in
           FStar_Extraction_Krml.EBufCreate uu___6
       | FStar_Extraction_ML_Syntax.MLE_App
           ({
              FStar_Extraction_ML_Syntax.expr =
                FStar_Extraction_ML_Syntax.MLE_Name p;
              FStar_Extraction_ML_Syntax.mlty = uu___1;
              FStar_Extraction_ML_Syntax.loc = uu___2;_},
            init::[])
           when
           let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___3 = "Pulse.Lib.Box.alloc" ->
           let uu___3 =
             let uu___4 = cb init in
             (FStar_Extraction_Krml.ManuallyManaged, uu___4,
               (FStar_Extraction_Krml.EConstant
                  (FStar_Extraction_Krml.UInt32, "1"))) in
           FStar_Extraction_Krml.EBufCreate uu___3
       | FStar_Extraction_ML_Syntax.MLE_App
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
            init::[])
           when
           let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Box.alloc" ->
           let uu___6 =
             let uu___7 = cb init in
             (FStar_Extraction_Krml.ManuallyManaged, uu___7,
               (FStar_Extraction_Krml.EConstant
                  (FStar_Extraction_Krml.UInt32, "1"))) in
           FStar_Extraction_Krml.EBufCreate uu___6
       | FStar_Extraction_ML_Syntax.MLE_App
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
            x::_w::[])
           when
           let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Box.free" ->
           let uu___6 = cb x in FStar_Extraction_Krml.EBufFree uu___6
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
                             FStar_Extraction_ML_Syntax.mlty = uu___1;
                             FStar_Extraction_ML_Syntax.loc = uu___2;_},
                           uu___3);
                        FStar_Extraction_ML_Syntax.mlty = uu___4;
                        FStar_Extraction_ML_Syntax.loc = uu___5;_},
                      e2::[]);
                   FStar_Extraction_ML_Syntax.mlty = uu___6;
                   FStar_Extraction_ML_Syntax.loc = uu___7;_},
                 _v::[]);
              FStar_Extraction_ML_Syntax.mlty = uu___8;
              FStar_Extraction_ML_Syntax.loc = uu___9;_},
            _perm::[])
           when
           (let uu___10 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___10 = "Pulse.Lib.Reference.op_Bang") ||
             (let uu___10 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___10 = "Pulse.Lib.Box.op_Bang")
           ->
           let uu___10 = let uu___11 = cb e2 in (uu___11, zero_for_deref) in
           FStar_Extraction_Krml.EBufRead uu___10
       | FStar_Extraction_ML_Syntax.MLE_App
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
            e2::_v::_perm::[])
           when
           (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___6 = "Pulse.Lib.Reference.op_Bang") ||
             (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___6 = "Pulse.Lib.Box.op_Bang")
           ->
           let uu___6 = let uu___7 = cb e2 in (uu___7, zero_for_deref) in
           FStar_Extraction_Krml.EBufRead uu___6
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
                             FStar_Extraction_ML_Syntax.mlty = uu___1;
                             FStar_Extraction_ML_Syntax.loc = uu___2;_},
                           uu___3);
                        FStar_Extraction_ML_Syntax.mlty = uu___4;
                        FStar_Extraction_ML_Syntax.loc = uu___5;_},
                      e11::[]);
                   FStar_Extraction_ML_Syntax.mlty = uu___6;
                   FStar_Extraction_ML_Syntax.loc = uu___7;_},
                 e2::[]);
              FStar_Extraction_ML_Syntax.mlty = uu___8;
              FStar_Extraction_ML_Syntax.loc = uu___9;_},
            _e3::[])
           when
           (let uu___10 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___10 = "Pulse.Lib.Reference.op_Colon_Equals") ||
             (let uu___10 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___10 = "Pulse.Lib.Box.op_Colon_Equals")
           ->
           let uu___10 =
             let uu___11 = cb e11 in
             let uu___12 = cb e2 in (uu___11, zero_for_deref, uu___12) in
           FStar_Extraction_Krml.EBufWrite uu___10
       | FStar_Extraction_ML_Syntax.MLE_App
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
            e11::e2::_e3::[])
           when
           (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___6 = "Pulse.Lib.Reference.op_Colon_Equals") ||
             (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___6 = "Pulse.Lib.Box.op_Colon_Equals")
           ->
           let uu___6 =
             let uu___7 = cb e11 in
             let uu___8 = cb e2 in (uu___7, zero_for_deref, uu___8) in
           FStar_Extraction_Krml.EBufWrite uu___6
       | FStar_Extraction_ML_Syntax.MLE_App
           ({
              FStar_Extraction_ML_Syntax.expr =
                FStar_Extraction_ML_Syntax.MLE_Name p;
              FStar_Extraction_ML_Syntax.mlty = uu___1;
              FStar_Extraction_ML_Syntax.loc = uu___2;_},
            x::n::[])
           when
           let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___3 = "Pulse.Lib.Array.Core.alloc" ->
           let uu___3 =
             let uu___4 = cb x in
             let uu___5 = cb n in
             (FStar_Extraction_Krml.ManuallyManaged, uu___4, uu___5) in
           FStar_Extraction_Krml.EBufCreate uu___3
       | FStar_Extraction_ML_Syntax.MLE_App
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
            x::n::[])
           when
           let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Array.Core.alloc" ->
           let uu___6 =
             let uu___7 = cb x in
             let uu___8 = cb n in
             (FStar_Extraction_Krml.ManuallyManaged, uu___7, uu___8) in
           FStar_Extraction_Krml.EBufCreate uu___6
       | FStar_Extraction_ML_Syntax.MLE_App
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
            e2::i::_p::_w::[])
           when
           let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Array.Core.op_Array_Access" ->
           let uu___6 =
             let uu___7 = cb e2 in let uu___8 = cb i in (uu___7, uu___8) in
           FStar_Extraction_Krml.EBufRead uu___6
       | FStar_Extraction_ML_Syntax.MLE_App
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
            e2::i::v::_w::[])
           when
           let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Array.Core.op_Array_Assignment" ->
           let uu___6 =
             let uu___7 = cb e2 in
             let uu___8 = cb i in
             let uu___9 = cb v in (uu___7, uu___8, uu___9) in
           FStar_Extraction_Krml.EBufWrite uu___6
       | FStar_Extraction_ML_Syntax.MLE_App
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
            e2::i::uu___6)
           when
           let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___7 = "Pulse.Lib.Array.Core.pts_to_range_index" ->
           let uu___7 =
             let uu___8 = cb e2 in let uu___9 = cb i in (uu___8, uu___9) in
           FStar_Extraction_Krml.EBufRead uu___7
       | FStar_Extraction_ML_Syntax.MLE_App
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
            e2::i::v::uu___6)
           when
           let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___7 = "Pulse.Lib.Array.Core.pts_to_range_upd" ->
           let uu___7 =
             let uu___8 = cb e2 in
             let uu___9 = cb i in
             let uu___10 = cb v in (uu___8, uu___9, uu___10) in
           FStar_Extraction_Krml.EBufWrite uu___7
       | FStar_Extraction_ML_Syntax.MLE_App
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
            x::_w::[])
           when
           let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Array.Core.free" ->
           let uu___6 = cb x in FStar_Extraction_Krml.EBufFree uu___6
       | FStar_Extraction_ML_Syntax.MLE_App
           ({
              FStar_Extraction_ML_Syntax.expr =
                FStar_Extraction_ML_Syntax.MLE_Name p;
              FStar_Extraction_ML_Syntax.mlty = uu___1;
              FStar_Extraction_ML_Syntax.loc = uu___2;_},
            {
              FStar_Extraction_ML_Syntax.expr =
                FStar_Extraction_ML_Syntax.MLE_Fun (uu___3, test);
              FStar_Extraction_ML_Syntax.mlty = uu___4;
              FStar_Extraction_ML_Syntax.loc = uu___5;_}::{
                                                            FStar_Extraction_ML_Syntax.expr
                                                              =
                                                              FStar_Extraction_ML_Syntax.MLE_Fun
                                                              (uu___6, body);
                                                            FStar_Extraction_ML_Syntax.mlty
                                                              = uu___7;
                                                            FStar_Extraction_ML_Syntax.loc
                                                              = uu___8;_}::[])
           when
           let uu___9 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___9 = "Pulse.Lib.Dv.while_" ->
           let uu___9 =
             let uu___10 = cb test in
             let uu___11 = cb body in (uu___10, uu___11) in
           FStar_Extraction_Krml.EWhile uu___9
       | FStar_Extraction_ML_Syntax.MLE_App
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
            uu___6::[])
           when
           let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___7 = "Pulse.Lib.Dv.unreachable" ->
           let uu___7 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           FStar_Extraction_Krml.EAbortS uu___7
       | FStar_Extraction_ML_Syntax.MLE_App
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
            b::[])
           when
           let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "Pulse.Lib.Box.box_to_ref" -> cb b
       | FStar_Extraction_ML_Syntax.MLE_App
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
            _post::body::[])
           when
           let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___6 = "DPE.run_stt" -> cb body
       | uu___1 ->
           FStar_Compiler_Effect.raise
             FStar_Extraction_Krml.NotSupportedByKrmlExtension)
let (uu___0 : unit) =
  FStar_Extraction_Krml.register_pre_translate_type_without_decay
    pulse_translate_type_without_decay;
  FStar_Extraction_Krml.register_pre_translate_expr pulse_translate_expr
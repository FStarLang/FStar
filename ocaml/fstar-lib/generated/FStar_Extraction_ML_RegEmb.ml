open Prims
exception NoEmbedding of Prims.string 
let (uu___is_NoEmbedding : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NoEmbedding uu___ -> true | uu___ -> false
let (__proj__NoEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | NoEmbedding uu___ -> uu___
exception Unsupported of Prims.string 
let (uu___is_Unsupported : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Unsupported uu___ -> true | uu___ -> false
let (__proj__Unsupported__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Unsupported uu___ -> uu___
let splitlast : 'uuuuu . 'uuuuu Prims.list -> ('uuuuu Prims.list * 'uuuuu) =
  fun s ->
    let uu___ = FStar_Compiler_List.rev s in
    match uu___ with | x::xs -> ((FStar_Compiler_List.rev xs), x)
let (mk :
  FStar_Extraction_ML_Syntax.mlexpr' -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e ->
    FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top e
let (ml_name : FStar_Ident.lid -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun l ->
    let s = FStar_Ident.path_of_lid l in
    let uu___ = splitlast s in
    match uu___ with
    | (ns, id) -> mk (FStar_Extraction_ML_Syntax.MLE_Name (ns, id))
let (ml_name' : Prims.string -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun s -> let uu___ = FStar_Ident.lid_of_str s in ml_name uu___
let (ml_ctor :
  FStar_Ident.lid ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.list ->
      FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun l ->
    fun args ->
      let s = FStar_Ident.path_of_lid l in
      let uu___ = splitlast s in
      match uu___ with
      | (ns, id) -> mk (FStar_Extraction_ML_Syntax.MLE_CTor ((ns, id), args))
let (ml_record :
  FStar_Ident.lid ->
    (Prims.string * FStar_Extraction_ML_Syntax.mlexpr) Prims.list ->
      FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun l ->
    fun args ->
      let s = FStar_Ident.path_of_lid l in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Ident.ident_of_lid l in
            FStar_Ident.string_of_id uu___3 in
          ([], uu___2, args) in
        FStar_Extraction_ML_Syntax.MLE_Record uu___1 in
      mk uu___
let (mk_binder :
  FStar_Extraction_ML_Syntax.mlident ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlbinder)
  =
  fun x ->
    fun t ->
      {
        FStar_Extraction_ML_Syntax.mlbinder_name = x;
        FStar_Extraction_ML_Syntax.mlbinder_ty = t;
        FStar_Extraction_ML_Syntax.mlbinder_attrs = []
      }
let (ml_lam :
  FStar_Extraction_ML_Syntax.mlident ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun nm ->
    fun e ->
      mk
        (FStar_Extraction_ML_Syntax.MLE_Fun
           ([mk_binder nm FStar_Extraction_ML_Syntax.MLTY_Top], e))
let (ml_none : FStar_Extraction_ML_Syntax.mlexpr) =
  mk
    (FStar_Extraction_ML_Syntax.MLE_Name
       (["FStar"; "Pervasives"; "Native"], "None"))
let (ml_some : FStar_Extraction_ML_Syntax.mlexpr) =
  mk
    (FStar_Extraction_ML_Syntax.MLE_Name
       (["FStar"; "Pervasives"; "Native"], "Some"))
let (tm_fvar_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Syntax.Syntax.Tm_fvar"
let (fv_eq_lid_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Syntax.Syntax.fv_eq_lid"
let (s_tdataconstr_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Syntax.Syntax.tdataconstr"
let (lid_of_str_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Ident.lid_of_str"
let (mk_app_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Syntax.Util.mk_app"
let (nil_lid : FStar_Ident.lident) = FStar_Ident.lid_of_str "Prims.Nil"
let (cons_lid : FStar_Ident.lident) = FStar_Ident.lid_of_str "Prims.Cons"
let (embed_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.Base.extracted_embed"
let (unembed_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.Base.extracted_unembed"
let (bind_opt_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Compiler.Util.bind_opt"
let (ml_nbe_unsupported : FStar_Extraction_ML_Syntax.mlexpr) =
  let hd =
    mk
      (FStar_Extraction_ML_Syntax.MLE_Name
         (["FStar"; "TypeChecker"; "NBETerm"], "e_unsupported")) in
  mk
    (FStar_Extraction_ML_Syntax.MLE_App
       (hd, [FStar_Extraction_ML_Syntax.ml_unit]))
let (ml_magic : FStar_Extraction_ML_Syntax.mlexpr) =
  mk
    (FStar_Extraction_ML_Syntax.MLE_Coerce
       (FStar_Extraction_ML_Syntax.ml_unit,
         FStar_Extraction_ML_Syntax.MLTY_Top,
         FStar_Extraction_ML_Syntax.MLTY_Top))
let (as_name :
  FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun mlp ->
    FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top
      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
let (ml_failwith : Prims.string -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun s ->
    let uu___ =
      let uu___1 =
        let uu___2 = as_name ([], "failwith") in
        let uu___3 =
          let uu___4 =
            mk
              (FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String s)) in
          [uu___4] in
        (uu___2, uu___3) in
      FStar_Extraction_ML_Syntax.MLE_App uu___1 in
    mk uu___
let rec (as_ml_list :
  FStar_Extraction_ML_Syntax.mlexpr Prims.list ->
    FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun ts ->
    match ts with
    | [] -> ml_ctor nil_lid []
    | t::ts1 ->
        let uu___ =
          let uu___1 = let uu___2 = as_ml_list ts1 in [uu___2] in t :: uu___1 in
        ml_ctor cons_lid uu___
let rec (pats_to_list_pat :
  FStar_Extraction_ML_Syntax.mlpattern Prims.list ->
    FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun vs ->
    match vs with
    | [] -> FStar_Extraction_ML_Syntax.MLP_CTor ((["Prims"], "Nil"), [])
    | p::ps ->
        let uu___ =
          let uu___1 =
            let uu___2 = let uu___3 = pats_to_list_pat ps in [uu___3] in p ::
              uu___2 in
          ((["Prims"], "Cons"), uu___1) in
        FStar_Extraction_ML_Syntax.MLP_CTor uu___
let (fresh : Prims.string -> Prims.string) =
  let r = FStar_Compiler_Util.mk_ref Prims.int_zero in
  fun s ->
    let v = FStar_Compiler_Effect.op_Bang r in
    FStar_Compiler_Effect.op_Colon_Equals r (v + Prims.int_one);
    Prims.strcat s (Prims.strcat "_" (Prims.string_of_int v))
let (not_implemented_warning :
  FStar_Compiler_Range_Type.range -> Prims.string -> Prims.string -> unit) =
  fun r ->
    fun t ->
      fun msg ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Compiler_Util.format1
                  "Plugin `%s' can not run natively because:" t in
              FStar_Errors_Msg.text uu___3 in
            let uu___3 = FStar_Errors_Msg.text msg in
            FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one uu___2
              uu___3 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Errors_Msg.text "Use --warn_error -" in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStar_Errors.lookup
                        FStar_Errors_Codes.Warning_PluginNotImplemented in
                    FStar_Errors.error_number uu___8 in
                  FStar_Class_PP.pp FStar_Class_PP.pp_int uu___7 in
                let uu___7 = FStar_Errors_Msg.text "to carry on." in
                FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
              FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStar_Errors.log_issue FStar_Class_HasRange.hasRange_range r
          FStar_Errors_Codes.Warning_PluginNotImplemented ()
          (Obj.magic FStar_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___)
type embedding_data =
  {
  arity: Prims.int ;
  syn_emb: FStar_Ident.lid ;
  nbe_emb: FStar_Ident.lid FStar_Pervasives_Native.option }
let (__proj__Mkembedding_data__item__arity : embedding_data -> Prims.int) =
  fun projectee ->
    match projectee with | { arity; syn_emb; nbe_emb;_} -> arity
let (__proj__Mkembedding_data__item__syn_emb :
  embedding_data -> FStar_Ident.lid) =
  fun projectee ->
    match projectee with | { arity; syn_emb; nbe_emb;_} -> syn_emb
let (__proj__Mkembedding_data__item__nbe_emb :
  embedding_data -> FStar_Ident.lid FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { arity; syn_emb; nbe_emb;_} -> nbe_emb
let (builtin_embeddings : (FStar_Ident.lident * embedding_data) Prims.list) =
  let syn_emb_lid s =
    FStar_Ident.lid_of_path ["FStar"; "Syntax"; "Embeddings"; s]
      FStar_Compiler_Range_Type.dummyRange in
  let nbe_emb_lid s =
    FStar_Ident.lid_of_path ["FStar"; "TypeChecker"; "NBETerm"; s]
      FStar_Compiler_Range_Type.dummyRange in
  let refl_emb_lid s =
    FStar_Ident.lid_of_path ["FStar"; "Reflection"; "V2"; "Embeddings"; s]
      FStar_Compiler_Range_Type.dummyRange in
  let nbe_refl_emb_lid s =
    FStar_Ident.lid_of_path ["FStar"; "Reflection"; "V2"; "NBEEmbeddings"; s]
      FStar_Compiler_Range_Type.dummyRange in
  let uu___ =
    let uu___1 =
      let uu___2 = syn_emb_lid "e_int" in
      let uu___3 =
        let uu___4 = nbe_emb_lid "e_int" in
        FStar_Pervasives_Native.Some uu___4 in
      { arity = Prims.int_zero; syn_emb = uu___2; nbe_emb = uu___3 } in
    (FStar_Parser_Const.int_lid, uu___1) in
  let uu___1 =
    let uu___2 =
      let uu___3 =
        let uu___4 = syn_emb_lid "e_bool" in
        let uu___5 =
          let uu___6 = nbe_emb_lid "e_bool" in
          FStar_Pervasives_Native.Some uu___6 in
        { arity = Prims.int_zero; syn_emb = uu___4; nbe_emb = uu___5 } in
      (FStar_Parser_Const.bool_lid, uu___3) in
    let uu___3 =
      let uu___4 =
        let uu___5 =
          let uu___6 = syn_emb_lid "e_unit" in
          let uu___7 =
            let uu___8 = nbe_emb_lid "e_unit" in
            FStar_Pervasives_Native.Some uu___8 in
          { arity = Prims.int_zero; syn_emb = uu___6; nbe_emb = uu___7 } in
        (FStar_Parser_Const.unit_lid, uu___5) in
      let uu___5 =
        let uu___6 =
          let uu___7 =
            let uu___8 = syn_emb_lid "e_string" in
            let uu___9 =
              let uu___10 = nbe_emb_lid "e_string" in
              FStar_Pervasives_Native.Some uu___10 in
            { arity = Prims.int_zero; syn_emb = uu___8; nbe_emb = uu___9 } in
          (FStar_Parser_Const.string_lid, uu___7) in
        let uu___7 =
          let uu___8 =
            let uu___9 =
              let uu___10 = syn_emb_lid "e_norm_step" in
              let uu___11 =
                let uu___12 = nbe_emb_lid "e_norm_step" in
                FStar_Pervasives_Native.Some uu___12 in
              { arity = Prims.int_zero; syn_emb = uu___10; nbe_emb = uu___11
              } in
            (FStar_Parser_Const.norm_step_lid, uu___9) in
          let uu___9 =
            let uu___10 =
              let uu___11 =
                let uu___12 = syn_emb_lid "e___range" in
                let uu___13 =
                  let uu___14 = nbe_emb_lid "e___range" in
                  FStar_Pervasives_Native.Some uu___14 in
                {
                  arity = Prims.int_zero;
                  syn_emb = uu___12;
                  nbe_emb = uu___13
                } in
              (FStar_Parser_Const.__range_lid, uu___11) in
            let uu___11 =
              let uu___12 =
                let uu___13 =
                  let uu___14 = syn_emb_lid "e_vconfig" in
                  let uu___15 =
                    let uu___16 = nbe_emb_lid "e_vconfig" in
                    FStar_Pervasives_Native.Some uu___16 in
                  {
                    arity = Prims.int_zero;
                    syn_emb = uu___14;
                    nbe_emb = uu___15
                  } in
                (FStar_Parser_Const.vconfig_lid, uu___13) in
              let uu___13 =
                let uu___14 =
                  let uu___15 =
                    let uu___16 = syn_emb_lid "e_list" in
                    let uu___17 =
                      let uu___18 = nbe_emb_lid "e_list" in
                      FStar_Pervasives_Native.Some uu___18 in
                    {
                      arity = Prims.int_one;
                      syn_emb = uu___16;
                      nbe_emb = uu___17
                    } in
                  (FStar_Parser_Const.list_lid, uu___15) in
                let uu___15 =
                  let uu___16 =
                    let uu___17 =
                      let uu___18 = syn_emb_lid "e_option" in
                      let uu___19 =
                        let uu___20 = nbe_emb_lid "e_option" in
                        FStar_Pervasives_Native.Some uu___20 in
                      {
                        arity = Prims.int_one;
                        syn_emb = uu___18;
                        nbe_emb = uu___19
                      } in
                    (FStar_Parser_Const.option_lid, uu___17) in
                  let uu___17 =
                    let uu___18 =
                      let uu___19 =
                        let uu___20 = syn_emb_lid "e_sealed" in
                        let uu___21 =
                          let uu___22 = nbe_emb_lid "e_sealed" in
                          FStar_Pervasives_Native.Some uu___22 in
                        {
                          arity = Prims.int_one;
                          syn_emb = uu___20;
                          nbe_emb = uu___21
                        } in
                      (FStar_Parser_Const.sealed_lid, uu___19) in
                    let uu___19 =
                      let uu___20 =
                        let uu___21 =
                          FStar_Parser_Const.mk_tuple_lid (Prims.of_int (2))
                            FStar_Compiler_Range_Type.dummyRange in
                        let uu___22 =
                          let uu___23 = syn_emb_lid "e_tuple2" in
                          let uu___24 =
                            let uu___25 = nbe_emb_lid "e_tuple2" in
                            FStar_Pervasives_Native.Some uu___25 in
                          {
                            arity = (Prims.of_int (2));
                            syn_emb = uu___23;
                            nbe_emb = uu___24
                          } in
                        (uu___21, uu___22) in
                      let uu___21 =
                        let uu___22 =
                          let uu___23 =
                            FStar_Parser_Const.mk_tuple_lid
                              (Prims.of_int (3))
                              FStar_Compiler_Range_Type.dummyRange in
                          let uu___24 =
                            let uu___25 = syn_emb_lid "e_tuple3" in
                            let uu___26 =
                              let uu___27 = nbe_emb_lid "e_tuple3" in
                              FStar_Pervasives_Native.Some uu___27 in
                            {
                              arity = (Prims.of_int (3));
                              syn_emb = uu___25;
                              nbe_emb = uu___26
                            } in
                          (uu___23, uu___24) in
                        let uu___23 =
                          let uu___24 =
                            let uu___25 =
                              let uu___26 = syn_emb_lid "e_either" in
                              let uu___27 =
                                let uu___28 = nbe_emb_lid "e_either" in
                                FStar_Pervasives_Native.Some uu___28 in
                              {
                                arity = (Prims.of_int (2));
                                syn_emb = uu___26;
                                nbe_emb = uu___27
                              } in
                            (FStar_Parser_Const.either_lid, uu___25) in
                          let uu___25 =
                            let uu___26 =
                              let uu___27 =
                                FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                  "namedv" in
                              let uu___28 =
                                let uu___29 = refl_emb_lid "e_namedv" in
                                let uu___30 =
                                  let uu___31 = nbe_refl_emb_lid "e_namedv" in
                                  FStar_Pervasives_Native.Some uu___31 in
                                {
                                  arity = Prims.int_zero;
                                  syn_emb = uu___29;
                                  nbe_emb = uu___30
                                } in
                              (uu___27, uu___28) in
                            let uu___27 =
                              let uu___28 =
                                let uu___29 =
                                  FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                    "bv" in
                                let uu___30 =
                                  let uu___31 = refl_emb_lid "e_bv" in
                                  let uu___32 =
                                    let uu___33 = nbe_refl_emb_lid "e_bv" in
                                    FStar_Pervasives_Native.Some uu___33 in
                                  {
                                    arity = Prims.int_zero;
                                    syn_emb = uu___31;
                                    nbe_emb = uu___32
                                  } in
                                (uu___29, uu___30) in
                              let uu___29 =
                                let uu___30 =
                                  let uu___31 =
                                    FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                      "binder" in
                                  let uu___32 =
                                    let uu___33 = refl_emb_lid "e_binder" in
                                    let uu___34 =
                                      let uu___35 =
                                        nbe_refl_emb_lid "e_binder" in
                                      FStar_Pervasives_Native.Some uu___35 in
                                    {
                                      arity = Prims.int_zero;
                                      syn_emb = uu___33;
                                      nbe_emb = uu___34
                                    } in
                                  (uu___31, uu___32) in
                                let uu___31 =
                                  let uu___32 =
                                    let uu___33 =
                                      FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                        "term" in
                                    let uu___34 =
                                      let uu___35 = refl_emb_lid "e_term" in
                                      let uu___36 =
                                        let uu___37 =
                                          nbe_refl_emb_lid "e_term" in
                                        FStar_Pervasives_Native.Some uu___37 in
                                      {
                                        arity = Prims.int_zero;
                                        syn_emb = uu___35;
                                        nbe_emb = uu___36
                                      } in
                                    (uu___33, uu___34) in
                                  let uu___33 =
                                    let uu___34 =
                                      let uu___35 =
                                        FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                          "env" in
                                      let uu___36 =
                                        let uu___37 = refl_emb_lid "e_env" in
                                        let uu___38 =
                                          let uu___39 =
                                            nbe_refl_emb_lid "e_env" in
                                          FStar_Pervasives_Native.Some
                                            uu___39 in
                                        {
                                          arity = Prims.int_zero;
                                          syn_emb = uu___37;
                                          nbe_emb = uu___38
                                        } in
                                      (uu___35, uu___36) in
                                    let uu___35 =
                                      let uu___36 =
                                        let uu___37 =
                                          FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                            "fv" in
                                        let uu___38 =
                                          let uu___39 = refl_emb_lid "e_fv" in
                                          let uu___40 =
                                            let uu___41 =
                                              nbe_refl_emb_lid "e_fv" in
                                            FStar_Pervasives_Native.Some
                                              uu___41 in
                                          {
                                            arity = Prims.int_zero;
                                            syn_emb = uu___39;
                                            nbe_emb = uu___40
                                          } in
                                        (uu___37, uu___38) in
                                      let uu___37 =
                                        let uu___38 =
                                          let uu___39 =
                                            FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                              "comp" in
                                          let uu___40 =
                                            let uu___41 =
                                              refl_emb_lid "e_comp" in
                                            let uu___42 =
                                              let uu___43 =
                                                nbe_refl_emb_lid "e_comp" in
                                              FStar_Pervasives_Native.Some
                                                uu___43 in
                                            {
                                              arity = Prims.int_zero;
                                              syn_emb = uu___41;
                                              nbe_emb = uu___42
                                            } in
                                          (uu___39, uu___40) in
                                        let uu___39 =
                                          let uu___40 =
                                            let uu___41 =
                                              FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                                "sigelt" in
                                            let uu___42 =
                                              let uu___43 =
                                                refl_emb_lid "e_sigelt" in
                                              let uu___44 =
                                                let uu___45 =
                                                  nbe_refl_emb_lid "e_sigelt" in
                                                FStar_Pervasives_Native.Some
                                                  uu___45 in
                                              {
                                                arity = Prims.int_zero;
                                                syn_emb = uu___43;
                                                nbe_emb = uu___44
                                              } in
                                            (uu___41, uu___42) in
                                          let uu___41 =
                                            let uu___42 =
                                              let uu___43 =
                                                FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                                  "ctx_uvar_and_subst" in
                                              let uu___44 =
                                                let uu___45 =
                                                  refl_emb_lid
                                                    "e_ctx_uvar_and_subst" in
                                                let uu___46 =
                                                  let uu___47 =
                                                    nbe_refl_emb_lid
                                                      "e_ctx_uvar_and_subst" in
                                                  FStar_Pervasives_Native.Some
                                                    uu___47 in
                                                {
                                                  arity = Prims.int_zero;
                                                  syn_emb = uu___45;
                                                  nbe_emb = uu___46
                                                } in
                                              (uu___43, uu___44) in
                                            let uu___43 =
                                              let uu___44 =
                                                let uu___45 =
                                                  FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                                    "letbinding" in
                                                let uu___46 =
                                                  let uu___47 =
                                                    refl_emb_lid
                                                      "e_letbinding" in
                                                  let uu___48 =
                                                    let uu___49 =
                                                      nbe_refl_emb_lid
                                                        "e_letbinding" in
                                                    FStar_Pervasives_Native.Some
                                                      uu___49 in
                                                  {
                                                    arity = Prims.int_zero;
                                                    syn_emb = uu___47;
                                                    nbe_emb = uu___48
                                                  } in
                                                (uu___45, uu___46) in
                                              let uu___45 =
                                                let uu___46 =
                                                  let uu___47 =
                                                    FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                                      "ident" in
                                                  let uu___48 =
                                                    let uu___49 =
                                                      refl_emb_lid "e_ident" in
                                                    let uu___50 =
                                                      let uu___51 =
                                                        nbe_refl_emb_lid
                                                          "e_ident" in
                                                      FStar_Pervasives_Native.Some
                                                        uu___51 in
                                                    {
                                                      arity = Prims.int_zero;
                                                      syn_emb = uu___49;
                                                      nbe_emb = uu___50
                                                    } in
                                                  (uu___47, uu___48) in
                                                let uu___47 =
                                                  let uu___48 =
                                                    let uu___49 =
                                                      FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                                        "universe_uvar" in
                                                    let uu___50 =
                                                      let uu___51 =
                                                        refl_emb_lid
                                                          "e_universe_uvar" in
                                                      let uu___52 =
                                                        let uu___53 =
                                                          nbe_refl_emb_lid
                                                            "e_universe_uvar" in
                                                        FStar_Pervasives_Native.Some
                                                          uu___53 in
                                                      {
                                                        arity =
                                                          Prims.int_zero;
                                                        syn_emb = uu___51;
                                                        nbe_emb = uu___52
                                                      } in
                                                    (uu___49, uu___50) in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      let uu___51 =
                                                        FStar_Reflection_V2_Constants.fstar_refl_types_lid
                                                          "universe" in
                                                      let uu___52 =
                                                        let uu___53 =
                                                          refl_emb_lid
                                                            "e_universe" in
                                                        let uu___54 =
                                                          let uu___55 =
                                                            nbe_refl_emb_lid
                                                              "e_universe" in
                                                          FStar_Pervasives_Native.Some
                                                            uu___55 in
                                                        {
                                                          arity =
                                                            Prims.int_zero;
                                                          syn_emb = uu___53;
                                                          nbe_emb = uu___54
                                                        } in
                                                      (uu___51, uu___52) in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        let uu___53 =
                                                          FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                            "vconst" in
                                                        let uu___54 =
                                                          let uu___55 =
                                                            refl_emb_lid
                                                              "e_vconst" in
                                                          let uu___56 =
                                                            let uu___57 =
                                                              nbe_refl_emb_lid
                                                                "e_vconst" in
                                                            FStar_Pervasives_Native.Some
                                                              uu___57 in
                                                          {
                                                            arity =
                                                              Prims.int_zero;
                                                            syn_emb = uu___55;
                                                            nbe_emb = uu___56
                                                          } in
                                                        (uu___53, uu___54) in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          let uu___55 =
                                                            FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                              "aqualv" in
                                                          let uu___56 =
                                                            let uu___57 =
                                                              refl_emb_lid
                                                                "e_aqualv" in
                                                            let uu___58 =
                                                              let uu___59 =
                                                                nbe_refl_emb_lid
                                                                  "e_aqualv" in
                                                              FStar_Pervasives_Native.Some
                                                                uu___59 in
                                                            {
                                                              arity =
                                                                Prims.int_zero;
                                                              syn_emb =
                                                                uu___57;
                                                              nbe_emb =
                                                                uu___58
                                                            } in
                                                          (uu___55, uu___56) in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            let uu___57 =
                                                              FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                "pattern" in
                                                            let uu___58 =
                                                              let uu___59 =
                                                                refl_emb_lid
                                                                  "e_pattern" in
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  nbe_refl_emb_lid
                                                                    "e_pattern" in
                                                                FStar_Pervasives_Native.Some
                                                                  uu___61 in
                                                              {
                                                                arity =
                                                                  Prims.int_zero;
                                                                syn_emb =
                                                                  uu___59;
                                                                nbe_emb =
                                                                  uu___60
                                                              } in
                                                            (uu___57,
                                                              uu___58) in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              let uu___59 =
                                                                FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                  "namedv_view" in
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  refl_emb_lid
                                                                    "e_namedv_view" in
                                                                let uu___62 =
                                                                  let uu___63
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_namedv_view" in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu___63 in
                                                                {
                                                                  arity =
                                                                    Prims.int_zero;
                                                                  syn_emb =
                                                                    uu___61;
                                                                  nbe_emb =
                                                                    uu___62
                                                                } in
                                                              (uu___59,
                                                                uu___60) in
                                                            let uu___59 =
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "bv_view" in
                                                                let uu___62 =
                                                                  let uu___63
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_bv_view" in
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_bv_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___65 in
                                                                  {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___63;
                                                                    nbe_emb =
                                                                    uu___64
                                                                  } in
                                                                (uu___61,
                                                                  uu___62) in
                                                              let uu___61 =
                                                                let uu___62 =
                                                                  let uu___63
                                                                    =
                                                                    FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "binder_view" in
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_binder_view" in
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_binder_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___67 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___65;
                                                                    nbe_emb =
                                                                    uu___66
                                                                    } in
                                                                  (uu___63,
                                                                    uu___64) in
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "binding" in
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_binding" in
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_binding" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___69 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___67;
                                                                    nbe_emb =
                                                                    uu___68
                                                                    } in
                                                                    (uu___65,
                                                                    uu___66) in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
                                                                    =
                                                                    FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "universe_view" in
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_universe_view" in
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_universe_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___71 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___69;
                                                                    nbe_emb =
                                                                    uu___70
                                                                    } in
                                                                    (uu___67,
                                                                    uu___68) in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "term_view" in
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_term_view" in
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_term_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___73 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___71;
                                                                    nbe_emb =
                                                                    uu___72
                                                                    } in
                                                                    (uu___69,
                                                                    uu___70) in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "comp_view" in
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_comp_view" in
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_comp_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___75 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___73;
                                                                    nbe_emb =
                                                                    uu___74
                                                                    } in
                                                                    (uu___71,
                                                                    uu___72) in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
                                                                    =
                                                                    FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "lb_view" in
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_lb_view" in
                                                                    let uu___76
                                                                    =
                                                                    let uu___77
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_lb_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___77 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___75;
                                                                    nbe_emb =
                                                                    uu___76
                                                                    } in
                                                                    (uu___73,
                                                                    uu___74) in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
                                                                    =
                                                                    FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "sigelt_view" in
                                                                    let uu___76
                                                                    =
                                                                    let uu___77
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_sigelt_view" in
                                                                    let uu___78
                                                                    =
                                                                    let uu___79
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_sigelt_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___79 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___77;
                                                                    nbe_emb =
                                                                    uu___78
                                                                    } in
                                                                    (uu___75,
                                                                    uu___76) in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    let uu___77
                                                                    =
                                                                    FStar_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "qualifier" in
                                                                    let uu___78
                                                                    =
                                                                    let uu___79
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_qualifier" in
                                                                    let uu___80
                                                                    =
                                                                    let uu___81
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_qualifier" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___81 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___79;
                                                                    nbe_emb =
                                                                    uu___80
                                                                    } in
                                                                    (uu___77,
                                                                    uu___78) in
                                                                    [uu___76] in
                                                                    uu___74
                                                                    ::
                                                                    uu___75 in
                                                                    uu___72
                                                                    ::
                                                                    uu___73 in
                                                                    uu___70
                                                                    ::
                                                                    uu___71 in
                                                                    uu___68
                                                                    ::
                                                                    uu___69 in
                                                                    uu___66
                                                                    ::
                                                                    uu___67 in
                                                                  uu___64 ::
                                                                    uu___65 in
                                                                uu___62 ::
                                                                  uu___63 in
                                                              uu___60 ::
                                                                uu___61 in
                                                            uu___58 ::
                                                              uu___59 in
                                                          uu___56 :: uu___57 in
                                                        uu___54 :: uu___55 in
                                                      uu___52 :: uu___53 in
                                                    uu___50 :: uu___51 in
                                                  uu___48 :: uu___49 in
                                                uu___46 :: uu___47 in
                                              uu___44 :: uu___45 in
                                            uu___42 :: uu___43 in
                                          uu___40 :: uu___41 in
                                        uu___38 :: uu___39 in
                                      uu___36 :: uu___37 in
                                    uu___34 :: uu___35 in
                                  uu___32 :: uu___33 in
                                uu___30 :: uu___31 in
                              uu___28 :: uu___29 in
                            uu___26 :: uu___27 in
                          uu___24 :: uu___25 in
                        uu___22 :: uu___23 in
                      uu___20 :: uu___21 in
                    uu___18 :: uu___19 in
                  uu___16 :: uu___17 in
                uu___14 :: uu___15 in
              uu___12 :: uu___13 in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1
let (dbg_plugin : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "Plugins"
let (local_fv_embeddings :
  (FStar_Ident.lident * embedding_data) Prims.list FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref []
let (register_embedding : FStar_Ident.lident -> embedding_data -> unit) =
  fun l ->
    fun d ->
      (let uu___1 = FStar_Compiler_Effect.op_Bang dbg_plugin in
       if uu___1
       then
         let uu___2 = FStar_Ident.string_of_lid l in
         FStar_Compiler_Util.print1 "Registering local embedding for %s\n"
           uu___2
       else ());
      (let uu___1 =
         let uu___2 = FStar_Compiler_Effect.op_Bang local_fv_embeddings in
         (l, d) :: uu___2 in
       FStar_Compiler_Effect.op_Colon_Equals local_fv_embeddings uu___1)
let (list_local : unit -> (FStar_Ident.lident * embedding_data) Prims.list) =
  fun uu___ -> FStar_Compiler_Effect.op_Bang local_fv_embeddings
let (find_fv_embedding' :
  FStar_Ident.lident -> embedding_data FStar_Pervasives_Native.option) =
  fun l ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Compiler_Effect.op_Bang local_fv_embeddings in
        FStar_Compiler_List.op_At uu___2 builtin_embeddings in
      FStar_Compiler_List.find
        (fun uu___2 ->
           match uu___2 with | (l', uu___3) -> FStar_Ident.lid_equals l l')
        uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some (uu___1, data) ->
        FStar_Pervasives_Native.Some data
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (find_fv_embedding : FStar_Ident.lident -> embedding_data) =
  fun l ->
    let uu___ = find_fv_embedding' l in
    match uu___ with
    | FStar_Pervasives_Native.Some data -> data
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Ident.string_of_lid l in
            Prims.strcat "Embedding not defined for type " uu___3 in
          NoEmbedding uu___2 in
        FStar_Compiler_Effect.raise uu___1
type embedding_kind =
  | SyntaxTerm 
  | NBETerm 
let (uu___is_SyntaxTerm : embedding_kind -> Prims.bool) =
  fun projectee -> match projectee with | SyntaxTerm -> true | uu___ -> false
let (uu___is_NBETerm : embedding_kind -> Prims.bool) =
  fun projectee -> match projectee with | NBETerm -> true | uu___ -> false
let rec (embedding_for :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lid Prims.list ->
      embedding_kind ->
        (FStar_Syntax_Syntax.bv * Prims.string) Prims.list ->
          FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun tcenv ->
    fun mutuals ->
      fun k ->
        fun env ->
          fun t ->
            let str_to_name s = as_name ([], s) in
            let emb_arrow e1 e2 =
              let comb =
                match k with
                | SyntaxTerm -> ml_name' "FStar.Syntax.Embeddings.e_arrow"
                | NBETerm -> ml_name' "FStar.TypeChecker.NBETerm.e_arrow" in
              mk (FStar_Extraction_ML_Syntax.MLE_App (comb, [e1; e2])) in
            let find_env_entry bv uu___ =
              match uu___ with
              | (bv', uu___1) -> FStar_Syntax_Syntax.bv_eq bv bv' in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t in
            let t2 = FStar_Syntax_Util.un_uinst t1 in
            let t3 = FStar_Syntax_Subst.compress t2 in
            match t3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name bv when
                FStar_Compiler_Util.for_some (find_env_entry bv) env ->
                let comb =
                  match k with
                  | SyntaxTerm ->
                      ml_name' "FStar.Syntax.Embeddings.mk_any_emb"
                  | NBETerm ->
                      ml_name' "FStar.TypeChecker.NBETerm.mk_any_emb" in
                let s =
                  let uu___ =
                    let uu___1 =
                      FStar_Compiler_Util.find_opt (find_env_entry bv) env in
                    FStar_Compiler_Util.must uu___1 in
                  FStar_Pervasives_Native.snd uu___ in
                let uu___ =
                  let uu___1 =
                    let uu___2 = let uu___3 = str_to_name s in [uu___3] in
                    (comb, uu___2) in
                  FStar_Extraction_ML_Syntax.MLE_App uu___1 in
                mk uu___
            | FStar_Syntax_Syntax.Tm_refine
                { FStar_Syntax_Syntax.b = x;
                  FStar_Syntax_Syntax.phi = uu___;_}
                ->
                embedding_for tcenv mutuals k env x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed
                { FStar_Syntax_Syntax.tm = t4;
                  FStar_Syntax_Syntax.asc = uu___;
                  FStar_Syntax_Syntax.eff_opt = uu___1;_}
                -> embedding_for tcenv mutuals k env t4
            | FStar_Syntax_Syntax.Tm_arrow
                { FStar_Syntax_Syntax.bs1 = b::[];
                  FStar_Syntax_Syntax.comp = c;_}
                when FStar_Syntax_Util.is_pure_comp c ->
                let uu___ = FStar_Syntax_Subst.open_comp [b] c in
                (match uu___ with
                 | (b1::[], c1) ->
                     let t0 =
                       (b1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                     let t11 = FStar_Syntax_Util.comp_result c1 in
                     let uu___1 = embedding_for tcenv mutuals k env t0 in
                     let uu___2 = embedding_for tcenv mutuals k env t11 in
                     emb_arrow uu___1 uu___2)
            | FStar_Syntax_Syntax.Tm_arrow
                { FStar_Syntax_Syntax.bs1 = b::more::bs;
                  FStar_Syntax_Syntax.comp = c;_}
                ->
                let tail =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow
                       {
                         FStar_Syntax_Syntax.bs1 = (more :: bs);
                         FStar_Syntax_Syntax.comp = c
                       }) t3.FStar_Syntax_Syntax.pos in
                let t4 =
                  let uu___ =
                    let uu___1 =
                      let uu___2 = FStar_Syntax_Syntax.mk_Total tail in
                      {
                        FStar_Syntax_Syntax.bs1 = [b];
                        FStar_Syntax_Syntax.comp = uu___2
                      } in
                    FStar_Syntax_Syntax.Tm_arrow uu___1 in
                  FStar_Syntax_Syntax.mk uu___ t3.FStar_Syntax_Syntax.pos in
                embedding_for tcenv mutuals k env t4
            | FStar_Syntax_Syntax.Tm_app uu___ ->
                let uu___1 = FStar_Syntax_Util.head_and_args t3 in
                (match uu___1 with
                 | (head, args) ->
                     let e_head = embedding_for tcenv mutuals k env head in
                     let e_args =
                       FStar_Compiler_List.map
                         (fun uu___2 ->
                            match uu___2 with
                            | (t4, uu___3) ->
                                embedding_for tcenv mutuals k env t4) args in
                     mk (FStar_Extraction_ML_Syntax.MLE_App (e_head, e_args)))
            | FStar_Syntax_Syntax.Tm_fvar fv when
                FStar_Compiler_List.existsb
                  (FStar_Ident.lid_equals
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                  mutuals
                ->
                let head =
                  let uu___ =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          FStar_Ident.ident_of_lid
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        FStar_Ident.string_of_id uu___3 in
                      Prims.strcat "__knot_e_" uu___2 in
                    FStar_Extraction_ML_Syntax.MLE_Var uu___1 in
                  mk uu___ in
                mk
                  (FStar_Extraction_ML_Syntax.MLE_App
                     (head, [FStar_Extraction_ML_Syntax.ml_unit]))
            | FStar_Syntax_Syntax.Tm_fvar fv when
                let uu___ =
                  find_fv_embedding'
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                FStar_Pervasives_Native.uu___is_Some uu___ ->
                let emb_data =
                  find_fv_embedding
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match k with
                 | SyntaxTerm -> ml_name emb_data.syn_emb
                 | NBETerm ->
                     (match emb_data.nbe_emb with
                      | FStar_Pervasives_Native.Some lid -> ml_name lid
                      | FStar_Pervasives_Native.None -> ml_nbe_unsupported))
            | FStar_Syntax_Syntax.Tm_fvar fv when
                FStar_TypeChecker_Env.fv_has_attr tcenv fv
                  FStar_Parser_Const.plugin_attr
                ->
                (match k with
                 | SyntaxTerm ->
                     let lid =
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                     let uu___ =
                       let uu___1 =
                         let uu___2 = FStar_Ident.ns_of_lid lid in
                         FStar_Compiler_List.map FStar_Ident.string_of_id
                           uu___2 in
                       let uu___2 =
                         let uu___3 =
                           let uu___4 = FStar_Ident.ident_of_lid lid in
                           FStar_Ident.string_of_id uu___4 in
                         Prims.strcat "e_" uu___3 in
                       (uu___1, uu___2) in
                     as_name uu___
                 | NBETerm -> ml_nbe_unsupported)
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      FStar_Class_Show.show FStar_Syntax_Print.showable_term
                        t3 in
                    FStar_Compiler_Util.format1
                      "Embedding not defined for name `%s'" uu___2 in
                  NoEmbedding uu___1 in
                FStar_Compiler_Effect.raise uu___
            | uu___ ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      FStar_Class_Show.show FStar_Syntax_Print.showable_term
                        t3 in
                    let uu___4 =
                      FStar_Class_Tagged.tag_of
                        FStar_Syntax_Syntax.tagged_term t3 in
                    FStar_Compiler_Util.format2 "Cannot embed type `%s' (%s)"
                      uu___3 uu___4 in
                  NoEmbedding uu___2 in
                FStar_Compiler_Effect.raise uu___1
type wrapped_term =
  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlexpr *
    Prims.int * Prims.bool)
let (interpret_plugin_as_term_fun :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ ->
        Prims.int FStar_Pervasives_Native.option ->
          FStar_Extraction_ML_Syntax.mlexpr' ->
            (FStar_Extraction_ML_Syntax.mlexpr *
              FStar_Extraction_ML_Syntax.mlexpr * Prims.int * Prims.bool)
              FStar_Pervasives_Native.option)
  =
  fun env ->
    fun fv ->
      fun t ->
        fun arity_opt ->
          fun ml_fv ->
            let fv_lid =
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let tcenv = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            let t1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.EraseUniverses;
                FStar_TypeChecker_Env.AllowUnboundUniverses;
                FStar_TypeChecker_Env.UnfoldUntil
                  FStar_Syntax_Syntax.delta_constant;
                FStar_TypeChecker_Env.ForExtraction] tcenv t in
            let as_name1 mlp =
              FStar_Extraction_ML_Syntax.with_ty
                FStar_Extraction_ML_Syntax.MLTY_Top
                (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
            let lid_to_name l =
              let uu___ =
                let uu___1 = FStar_Extraction_ML_UEnv.mlpath_of_lident env l in
                FStar_Extraction_ML_Syntax.MLE_Name uu___1 in
              FStar_Extraction_ML_Syntax.with_ty
                FStar_Extraction_ML_Syntax.MLTY_Top uu___ in
            let str_to_name s = as_name1 ([], s) in
            let fv_lid_embedded =
              let uu___ =
                let uu___1 =
                  let uu___2 = as_name1 (["FStar_Ident"], "lid_of_str") in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = FStar_Ident.string_of_lid fv_lid in
                          FStar_Extraction_ML_Syntax.MLC_String uu___7 in
                        FStar_Extraction_ML_Syntax.MLE_Const uu___6 in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu___5 in
                    [uu___4] in
                  (uu___2, uu___3) in
                FStar_Extraction_ML_Syntax.MLE_App uu___1 in
              FStar_Extraction_ML_Syntax.with_ty
                FStar_Extraction_ML_Syntax.MLTY_Top uu___ in
            let mk_tactic_interpretation l arity =
              if arity > FStar_Tactics_InterpFuns.max_tac_arity
              then
                FStar_Compiler_Effect.raise
                  (NoEmbedding
                     "tactic plugins can only take up to 20 arguments")
              else
                (let idroot =
                   match l with
                   | SyntaxTerm -> "mk_tactic_interpretation_"
                   | NBETerm -> "mk_nbe_tactic_interpretation_" in
                 as_name1
                   (["FStar_Tactics_InterpFuns"],
                     (Prims.strcat idroot (Prims.string_of_int arity)))) in
            let mk_from_tactic l arity =
              let idroot =
                match l with
                | SyntaxTerm -> "from_tactic_"
                | NBETerm -> "from_nbe_tactic_" in
              as_name1
                (["FStar_Tactics_Native"],
                  (Prims.strcat idroot (Prims.string_of_int arity))) in
            let mk_arrow_as_prim_step k arity =
              let modul =
                match k with
                | SyntaxTerm -> ["FStar"; "Syntax"; "Embeddings"]
                | NBETerm -> ["FStar"; "TypeChecker"; "NBETerm"] in
              as_name1
                (modul,
                  (Prims.strcat "arrow_as_prim_step_"
                     (Prims.string_of_int arity))) in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          as_name1
                            (["FStar_Syntax_Embeddings"], "debug_wrap") in
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 = FStar_Ident.string_of_lid fv_lid in
                                FStar_Extraction_ML_Syntax.MLC_String uu___7 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu___6 in
                            FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top uu___5 in
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 = str_to_name "args" in
                                      [uu___11] in
                                    (body, uu___10) in
                                  FStar_Extraction_ML_Syntax.MLE_App uu___9 in
                                mk uu___8 in
                              ml_lam "_" uu___7 in
                            [uu___6] in
                          uu___4 :: uu___5 in
                        (uu___2, uu___3) in
                      FStar_Extraction_ML_Syntax.MLE_App uu___1 in
                    mk uu___ in
                  ml_lam "args" body1
              | uu___ ->
                  let args_tail =
                    FStar_Extraction_ML_Syntax.MLP_Var "args_tail" in
                  let mk_cons hd_pat tail_pat =
                    FStar_Extraction_ML_Syntax.MLP_CTor
                      ((["Prims"], "Cons"), [hd_pat; tail_pat]) in
                  let fst_pat v =
                    FStar_Extraction_ML_Syntax.MLP_Tuple
                      [FStar_Extraction_ML_Syntax.MLP_Var v;
                      FStar_Extraction_ML_Syntax.MLP_Wild] in
                  let pattern =
                    FStar_Compiler_List.fold_right
                      (fun hd_var -> mk_cons (fst_pat hd_var)) tvar_names
                      args_tail in
                  let branch =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 = as_name1 ([], "args_tail") in
                            [uu___5] in
                          (body, uu___4) in
                        FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                      mk uu___2 in
                    (pattern, FStar_Pervasives_Native.None, uu___1) in
                  let default_branch =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = str_to_name "failwith" in
                          let uu___5 =
                            let uu___6 =
                              mk
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_String
                                      "arity mismatch")) in
                            [uu___6] in
                          (uu___4, uu___5) in
                        FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                      mk uu___2 in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu___1) in
                  let body1 =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = as_name1 ([], "args") in
                        (uu___3, [branch; default_branch]) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu___2 in
                    mk uu___1 in
                  let body2 =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          as_name1
                            (["FStar_Syntax_Embeddings"], "debug_wrap") in
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = FStar_Ident.string_of_lid fv_lid in
                                FStar_Extraction_ML_Syntax.MLC_String uu___8 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu___7 in
                            FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top uu___6 in
                          let uu___6 =
                            let uu___7 = ml_lam "_" body1 in [uu___7] in
                          uu___5 :: uu___6 in
                        (uu___3, uu___4) in
                      FStar_Extraction_ML_Syntax.MLE_App uu___2 in
                    mk uu___1 in
                  ml_lam "args" body2 in
            let uu___ = FStar_Syntax_Util.arrow_formals_comp t1 in
            match uu___ with
            | (bs, c) ->
                let uu___1 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None -> (bs, c)
                  | FStar_Pervasives_Native.Some n ->
                      let n_bs = FStar_Compiler_List.length bs in
                      if n = n_bs
                      then (bs, c)
                      else
                        if n < n_bs
                        then
                          (let uu___3 = FStar_Compiler_Util.first_N n bs in
                           match uu___3 with
                           | (bs1, rest) ->
                               let c1 =
                                 let uu___4 = FStar_Syntax_Util.arrow rest c in
                                 FStar_Syntax_Syntax.mk_Total uu___4 in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu___4 = FStar_Ident.string_of_lid fv_lid in
                             let uu___5 = FStar_Compiler_Util.string_of_int n in
                             let uu___6 =
                               FStar_Compiler_Util.string_of_int n_bs in
                             FStar_Compiler_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu___4 uu___5 uu___6 in
                           FStar_Compiler_Effect.raise (NoEmbedding msg)) in
                (match uu___1 with
                 | (bs1, c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1 in
                     let arity = FStar_Compiler_List.length bs1 in
                     let uu___2 =
                       let uu___3 =
                         FStar_Compiler_Util.prefix_until
                           (fun uu___4 ->
                              match uu___4 with
                              | { FStar_Syntax_Syntax.binder_bv = b;
                                  FStar_Syntax_Syntax.binder_qual = uu___5;
                                  FStar_Syntax_Syntax.binder_positivity =
                                    uu___6;
                                  FStar_Syntax_Syntax.binder_attrs = uu___7;_}
                                  ->
                                  let uu___8 =
                                    let uu___9 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort in
                                    uu___9.FStar_Syntax_Syntax.n in
                                  (match uu___8 with
                                   | FStar_Syntax_Syntax.Tm_type uu___9 ->
                                       false
                                   | uu___9 -> true)) bs1 in
                       match uu___3 with
                       | FStar_Pervasives_Native.None -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars, x, rest) ->
                           (tvars, (x :: rest)) in
                     (match uu___2 with
                      | (type_vars, bs2) ->
                          let tvar_arity =
                            FStar_Compiler_List.length type_vars in
                          let non_tvar_arity = FStar_Compiler_List.length bs2 in
                          let tvar_names =
                            FStar_Compiler_List.mapi
                              (fun i ->
                                 fun tv ->
                                   Prims.strcat "tv_" (Prims.string_of_int i))
                              type_vars in
                          let tvar_context =
                            FStar_Compiler_List.map2
                              (fun b ->
                                 fun nm ->
                                   ((b.FStar_Syntax_Syntax.binder_bv), nm))
                              type_vars tvar_names in
                          let rec aux loc accum_embeddings bs3 =
                            match bs3 with
                            | [] ->
                                let arg_unembeddings =
                                  FStar_Compiler_List.rev accum_embeddings in
                                let res_embedding =
                                  embedding_for tcenv [] loc tvar_context
                                    result_typ in
                                let fv_lid1 =
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                let uu___3 =
                                  FStar_Syntax_Util.is_pure_comp c1 in
                                if uu___3
                                then
                                  let cb = str_to_name "cb" in
                                  let us = str_to_name "us" in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity in
                                  let args =
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 = lid_to_name fv_lid1 in
                                        [uu___6; fv_lid_embedded; cb; us] in
                                      res_embedding :: uu___5 in
                                    FStar_Compiler_List.op_At
                                      arg_unembeddings uu___4 in
                                  let fun_embedding =
                                    mk
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (embed_fun_N, args)) in
                                  let tabs =
                                    abstract_tvars tvar_names fun_embedding in
                                  let cb_tabs =
                                    let uu___4 = ml_lam "us" tabs in
                                    ml_lam "cb" uu___4 in
                                  let uu___4 =
                                    if loc = NBETerm
                                    then cb_tabs
                                    else ml_lam "_psc" cb_tabs in
                                  (uu___4, arity, true)
                                else
                                  (let uu___5 =
                                     let uu___6 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1) in
                                     FStar_Ident.lid_equals uu___6
                                       FStar_Parser_Const.effect_TAC_lid in
                                   if uu___5
                                   then
                                     let h =
                                       mk_tactic_interpretation loc
                                         non_tvar_arity in
                                     let tac_fun =
                                       let uu___6 =
                                         let uu___7 =
                                           let uu___8 =
                                             mk_from_tactic loc
                                               non_tvar_arity in
                                           let uu___9 =
                                             let uu___10 =
                                               lid_to_name fv_lid1 in
                                             [uu___10] in
                                           (uu___8, uu___9) in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu___7 in
                                       mk uu___6 in
                                     let psc = str_to_name "psc" in
                                     let ncb = str_to_name "ncb" in
                                     let us = str_to_name "us" in
                                     let all_args = str_to_name "args" in
                                     let args =
                                       let uu___6 =
                                         let uu___7 =
                                           let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   FStar_Ident.string_of_lid
                                                     fv_lid1 in
                                                 Prims.strcat uu___11
                                                   " (plugin)" in
                                               FStar_Extraction_ML_Syntax.MLC_String
                                                 uu___10 in
                                             FStar_Extraction_ML_Syntax.MLE_Const
                                               uu___9 in
                                           mk uu___8 in
                                         [uu___7] in
                                       FStar_Compiler_List.op_At uu___6
                                         (FStar_Compiler_List.op_At [tac_fun]
                                            (FStar_Compiler_List.op_At
                                               arg_unembeddings
                                               [res_embedding; psc; ncb; us])) in
                                     let tabs =
                                       match tvar_names with
                                       | [] ->
                                           let uu___6 =
                                             mk
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_Compiler_List.op_At
                                                       args [all_args]))) in
                                           ml_lam "args" uu___6
                                       | uu___6 ->
                                           let uu___7 =
                                             mk
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args)) in
                                           abstract_tvars tvar_names uu___7 in
                                     let uu___6 =
                                       let uu___7 =
                                         let uu___8 = ml_lam "us" tabs in
                                         ml_lam "ncb" uu___8 in
                                       ml_lam "psc" uu___7 in
                                     (uu___6, (arity + Prims.int_one), false)
                                   else
                                     (let uu___7 =
                                        let uu___8 =
                                          let uu___9 =
                                            FStar_Class_Show.show
                                              FStar_Syntax_Print.showable_term
                                              t1 in
                                          Prims.strcat
                                            "Plugins not defined for type "
                                            uu___9 in
                                        NoEmbedding uu___8 in
                                      FStar_Compiler_Effect.raise uu___7))
                            | { FStar_Syntax_Syntax.binder_bv = b;
                                FStar_Syntax_Syntax.binder_qual = uu___3;
                                FStar_Syntax_Syntax.binder_positivity =
                                  uu___4;
                                FStar_Syntax_Syntax.binder_attrs = uu___5;_}::bs4
                                ->
                                let uu___6 =
                                  let uu___7 =
                                    embedding_for tcenv [] loc tvar_context
                                      b.FStar_Syntax_Syntax.sort in
                                  uu___7 :: accum_embeddings in
                                aux loc uu___6 bs4 in
                          (try
                             (fun uu___3 ->
                                match () with
                                | () ->
                                    let uu___4 = aux SyntaxTerm [] bs2 in
                                    (match uu___4 with
                                     | (w, a, b) ->
                                         let uu___5 = aux NBETerm [] bs2 in
                                         (match uu___5 with
                                          | (w', uu___6, uu___7) ->
                                              FStar_Pervasives_Native.Some
                                                (w, w', a, b)))) ()
                           with
                           | NoEmbedding msg ->
                               ((let uu___5 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 let uu___6 =
                                   FStar_Class_Show.show
                                     FStar_Syntax_Print.showable_fv fv in
                                 not_implemented_warning uu___5 uu___6 msg);
                                FStar_Pervasives_Native.None))))
let (mk_unembed :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lid Prims.list ->
      FStar_Extraction_ML_Syntax.mlpath Prims.list
        FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun tcenv ->
    fun mutuals ->
      fun record_fields ->
        fun ctors ->
          let e_branches = FStar_Compiler_Util.mk_ref [] in
          let arg_v = fresh "tm" in
          FStar_Compiler_List.iter
            (fun ctor ->
               match ctor.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_datacon
                   { FStar_Syntax_Syntax.lid1 = lid;
                     FStar_Syntax_Syntax.us1 = us;
                     FStar_Syntax_Syntax.t1 = t;
                     FStar_Syntax_Syntax.ty_lid = ty_lid;
                     FStar_Syntax_Syntax.num_ty_params = num_ty_params;
                     FStar_Syntax_Syntax.mutuals1 = uu___1;
                     FStar_Syntax_Syntax.injective_type_params1 = uu___2;_}
                   ->
                   let fv = fresh "fv" in
                   let uu___3 = FStar_Syntax_Util.arrow_formals t in
                   (match uu___3 with
                    | (bs, c) ->
                        let vs =
                          FStar_Compiler_List.map
                            (fun b ->
                               let uu___4 =
                                 let uu___5 =
                                   FStar_Ident.string_of_id
                                     (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname in
                                 fresh uu___5 in
                               (uu___4,
                                 ((b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort)))
                            bs in
                        let pat_s =
                          let uu___4 =
                            let uu___5 = FStar_Ident.string_of_lid lid in
                            FStar_Extraction_ML_Syntax.MLC_String uu___5 in
                          FStar_Extraction_ML_Syntax.MLP_Const uu___4 in
                        let pat_args =
                          let uu___4 =
                            FStar_Compiler_List.map
                              (fun uu___5 ->
                                 match uu___5 with
                                 | (v, uu___6) ->
                                     FStar_Extraction_ML_Syntax.MLP_Var v) vs in
                          pats_to_list_pat uu___4 in
                        let pat_both =
                          FStar_Extraction_ML_Syntax.MLP_Tuple
                            [pat_s; pat_args] in
                        let ret =
                          match record_fields with
                          | FStar_Pervasives_Native.Some fields ->
                              let uu___4 =
                                FStar_Compiler_List.map2
                                  (fun uu___5 ->
                                     fun fld ->
                                       match uu___5 with
                                       | (v, uu___6) ->
                                           let uu___7 =
                                             mk
                                               (FStar_Extraction_ML_Syntax.MLE_Var
                                                  v) in
                                           ((FStar_Pervasives_Native.snd fld),
                                             uu___7)) vs fields in
                              ml_record lid uu___4
                          | FStar_Pervasives_Native.None ->
                              let uu___4 =
                                FStar_Compiler_List.map
                                  (fun uu___5 ->
                                     match uu___5 with
                                     | (v, uu___6) ->
                                         mk
                                           (FStar_Extraction_ML_Syntax.MLE_Var
                                              v)) vs in
                              ml_ctor lid uu___4 in
                        let ret1 =
                          mk
                            (FStar_Extraction_ML_Syntax.MLE_App
                               (ml_some, [ret])) in
                        let body =
                          FStar_Compiler_List.fold_right
                            (fun uu___4 ->
                               fun body1 ->
                                 match uu___4 with
                                 | (v, ty) ->
                                     let body2 =
                                       mk
                                         (FStar_Extraction_ML_Syntax.MLE_Fun
                                            ([mk_binder v
                                                FStar_Extraction_ML_Syntax.MLTY_Top],
                                              body1)) in
                                     let uu___5 =
                                       let uu___6 =
                                         let uu___7 = ml_name bind_opt_lid in
                                         let uu___8 =
                                           let uu___9 =
                                             let uu___10 =
                                               let uu___11 =
                                                 let uu___12 =
                                                   ml_name unembed_lid in
                                                 let uu___13 =
                                                   let uu___14 =
                                                     embedding_for tcenv
                                                       mutuals SyntaxTerm []
                                                       ty in
                                                   let uu___15 =
                                                     let uu___16 =
                                                       mk
                                                         (FStar_Extraction_ML_Syntax.MLE_Var
                                                            v) in
                                                     [uu___16] in
                                                   uu___14 :: uu___15 in
                                                 (uu___12, uu___13) in
                                               FStar_Extraction_ML_Syntax.MLE_App
                                                 uu___11 in
                                             mk uu___10 in
                                           [uu___9; body2] in
                                         (uu___7, uu___8) in
                                       FStar_Extraction_ML_Syntax.MLE_App
                                         uu___6 in
                                     mk uu___5) vs ret1 in
                        let br =
                          (pat_both, FStar_Pervasives_Native.None, body) in
                        let uu___4 =
                          let uu___5 =
                            FStar_Compiler_Effect.op_Bang e_branches in
                          br :: uu___5 in
                        FStar_Compiler_Effect.op_Colon_Equals e_branches
                          uu___4)
               | uu___1 -> failwith "impossible, filter above") ctors;
          (let nomatch =
             (FStar_Extraction_ML_Syntax.MLP_Wild,
               FStar_Pervasives_Native.None, ml_none) in
           let branches =
             let uu___1 =
               let uu___2 = FStar_Compiler_Effect.op_Bang e_branches in
               nomatch :: uu___2 in
             FStar_Compiler_List.rev uu___1 in
           let sc = mk (FStar_Extraction_ML_Syntax.MLE_Var arg_v) in
           let def = mk (FStar_Extraction_ML_Syntax.MLE_Match (sc, branches)) in
           let lam =
             mk
               (FStar_Extraction_ML_Syntax.MLE_Fun
                  ([mk_binder arg_v FStar_Extraction_ML_Syntax.MLTY_Top],
                    def)) in
           lam)
let (mk_embed :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lid Prims.list ->
      FStar_Extraction_ML_Syntax.mlpath Prims.list
        FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun tcenv ->
    fun mutuals ->
      fun record_fields ->
        fun ctors ->
          let e_branches = FStar_Compiler_Util.mk_ref [] in
          let arg_v = fresh "tm" in
          FStar_Compiler_List.iter
            (fun ctor ->
               match ctor.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_datacon
                   { FStar_Syntax_Syntax.lid1 = lid;
                     FStar_Syntax_Syntax.us1 = us;
                     FStar_Syntax_Syntax.t1 = t;
                     FStar_Syntax_Syntax.ty_lid = ty_lid;
                     FStar_Syntax_Syntax.num_ty_params = num_ty_params;
                     FStar_Syntax_Syntax.mutuals1 = uu___1;
                     FStar_Syntax_Syntax.injective_type_params1 = uu___2;_}
                   ->
                   let fv = fresh "fv" in
                   let uu___3 = FStar_Syntax_Util.arrow_formals t in
                   (match uu___3 with
                    | (bs, c) ->
                        let vs =
                          FStar_Compiler_List.map
                            (fun b ->
                               let uu___4 =
                                 let uu___5 =
                                   FStar_Ident.string_of_id
                                     (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname in
                                 fresh uu___5 in
                               (uu___4,
                                 ((b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort)))
                            bs in
                        let pat =
                          match record_fields with
                          | FStar_Pervasives_Native.Some fields ->
                              let uu___4 =
                                let uu___5 =
                                  FStar_Compiler_List.map2
                                    (fun v ->
                                       fun fld ->
                                         ((FStar_Pervasives_Native.snd fld),
                                           (FStar_Extraction_ML_Syntax.MLP_Var
                                              (FStar_Pervasives_Native.fst v))))
                                    vs fields in
                                ([], uu___5) in
                              FStar_Extraction_ML_Syntax.MLP_Record uu___4
                          | FStar_Pervasives_Native.None ->
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 = FStar_Ident.path_of_lid lid in
                                  splitlast uu___6 in
                                let uu___6 =
                                  FStar_Compiler_List.map
                                    (fun v ->
                                       FStar_Extraction_ML_Syntax.MLP_Var
                                         (FStar_Pervasives_Native.fst v)) vs in
                                (uu___5, uu___6) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu___4 in
                        let fvar = ml_name s_tdataconstr_lid in
                        let lid_of_str = ml_name lid_of_str_lid in
                        let head =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        let uu___11 =
                                          let uu___12 =
                                            let uu___13 =
                                              let uu___14 =
                                                FStar_Ident.string_of_lid lid in
                                              FStar_Extraction_ML_Syntax.MLC_String
                                                uu___14 in
                                            FStar_Extraction_ML_Syntax.MLE_Const
                                              uu___13 in
                                          mk uu___12 in
                                        [uu___11] in
                                      (lid_of_str, uu___10) in
                                    FStar_Extraction_ML_Syntax.MLE_App uu___9 in
                                  mk uu___8 in
                                [uu___7] in
                              (fvar, uu___6) in
                            FStar_Extraction_ML_Syntax.MLE_App uu___5 in
                          mk uu___4 in
                        let mk_mk_app t1 ts =
                          let ts1 =
                            FStar_Compiler_List.map
                              (fun t2 ->
                                 mk
                                   (FStar_Extraction_ML_Syntax.MLE_Tuple
                                      [t2; ml_none])) ts in
                          let uu___4 =
                            let uu___5 =
                              let uu___6 = ml_name mk_app_lid in
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 = as_ml_list ts1 in [uu___9] in
                                t1 :: uu___8 in
                              (uu___6, uu___7) in
                            FStar_Extraction_ML_Syntax.MLE_App uu___5 in
                          mk uu___4 in
                        let args =
                          FStar_Compiler_List.map
                            (fun uu___4 ->
                               match uu___4 with
                               | (v, ty) ->
                                   let vt =
                                     mk
                                       (FStar_Extraction_ML_Syntax.MLE_Var v) in
                                   let uu___5 =
                                     let uu___6 =
                                       let uu___7 = ml_name embed_lid in
                                       let uu___8 =
                                         let uu___9 =
                                           embedding_for tcenv mutuals
                                             SyntaxTerm [] ty in
                                         [uu___9; vt] in
                                       (uu___7, uu___8) in
                                     FStar_Extraction_ML_Syntax.MLE_App
                                       uu___6 in
                                   mk uu___5) vs in
                        let ret = mk_mk_app head args in
                        let br = (pat, FStar_Pervasives_Native.None, ret) in
                        let uu___4 =
                          let uu___5 =
                            FStar_Compiler_Effect.op_Bang e_branches in
                          br :: uu___5 in
                        FStar_Compiler_Effect.op_Colon_Equals e_branches
                          uu___4)
               | uu___1 -> failwith "impossible, filter above") ctors;
          (let branches =
             let uu___1 = FStar_Compiler_Effect.op_Bang e_branches in
             FStar_Compiler_List.rev uu___1 in
           let sc = mk (FStar_Extraction_ML_Syntax.MLE_Var arg_v) in
           let def = mk (FStar_Extraction_ML_Syntax.MLE_Match (sc, branches)) in
           let lam =
             mk
               (FStar_Extraction_ML_Syntax.MLE_Fun
                  ([mk_binder arg_v FStar_Extraction_ML_Syntax.MLTY_Top],
                    def)) in
           lam)
let (__do_handle_plugin :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.int FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.sigelt ->
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g ->
    fun arity_opt ->
      fun se ->
        let r = se.FStar_Syntax_Syntax.sigrng in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let
            { FStar_Syntax_Syntax.lbs1 = lbs;
              FStar_Syntax_Syntax.lids1 = uu___;_}
            ->
            let mk_registration lb =
              let fv =
                FStar_Compiler_Util.right lb.FStar_Syntax_Syntax.lbname in
              let fv_lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let fv_t = lb.FStar_Syntax_Syntax.lbtyp in
              let ml_name_str =
                let uu___1 =
                  let uu___2 = FStar_Ident.string_of_lid fv_lid in
                  FStar_Extraction_ML_Syntax.MLC_String uu___2 in
                FStar_Extraction_ML_Syntax.MLE_Const uu___1 in
              let uu___1 =
                interpret_plugin_as_term_fun g fv fv_t arity_opt ml_name_str in
              match uu___1 with
              | FStar_Pervasives_Native.Some
                  (interp, nbe_interp, arity, plugin) ->
                  let uu___2 =
                    if plugin
                    then
                      ((["FStar_Tactics_Native"], "register_plugin"),
                        [interp; nbe_interp])
                    else
                      ((["FStar_Tactics_Native"], "register_tactic"),
                        [interp]) in
                  (match uu___2 with
                   | (register, args) ->
                       let h =
                         FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top
                           (FStar_Extraction_ML_Syntax.MLE_Name register) in
                       let arity1 =
                         FStar_Extraction_ML_Syntax.MLE_Const
                           (FStar_Extraction_ML_Syntax.MLC_Int
                              ((Prims.string_of_int arity),
                                FStar_Pervasives_Native.None)) in
                       let app =
                         let uu___3 =
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 = mk ml_name_str in
                                 let uu___8 =
                                   let uu___9 = mk arity1 in [uu___9] in
                                 uu___7 :: uu___8 in
                               FStar_Compiler_List.op_At uu___6 args in
                             (h, uu___5) in
                           FStar_Extraction_ML_Syntax.MLE_App uu___4 in
                         FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top uu___3 in
                       let uu___3 =
                         FStar_Extraction_ML_Syntax.mk_mlmodule1
                           (FStar_Extraction_ML_Syntax.MLM_Top app) in
                       [uu___3])
              | FStar_Pervasives_Native.None -> [] in
            FStar_Compiler_List.collect mk_registration
              (FStar_Pervasives_Native.snd lbs)
        | FStar_Syntax_Syntax.Sig_bundle
            { FStar_Syntax_Syntax.ses = ses;
              FStar_Syntax_Syntax.lids = uu___;_}
            ->
            let mutual_sigelts =
              FStar_Compiler_List.filter
                (fun se1 ->
                   match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ uu___1 -> true
                   | uu___1 -> false) ses in
            let mutual_lids =
              FStar_Compiler_List.map
                (fun se1 ->
                   match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       { FStar_Syntax_Syntax.lid = lid;
                         FStar_Syntax_Syntax.us = uu___1;
                         FStar_Syntax_Syntax.params = uu___2;
                         FStar_Syntax_Syntax.num_uniform_params = uu___3;
                         FStar_Syntax_Syntax.t = uu___4;
                         FStar_Syntax_Syntax.mutuals = uu___5;
                         FStar_Syntax_Syntax.ds = uu___6;
                         FStar_Syntax_Syntax.injective_type_params = uu___7;_}
                       -> lid) mutual_sigelts in
            let proc_one typ_sigelt =
              let uu___1 = typ_sigelt.FStar_Syntax_Syntax.sigel in
              match uu___1 with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  { FStar_Syntax_Syntax.lid = tlid;
                    FStar_Syntax_Syntax.us = uu___2;
                    FStar_Syntax_Syntax.params = ps;
                    FStar_Syntax_Syntax.num_uniform_params = uu___3;
                    FStar_Syntax_Syntax.t = uu___4;
                    FStar_Syntax_Syntax.mutuals = uu___5;
                    FStar_Syntax_Syntax.ds = uu___6;
                    FStar_Syntax_Syntax.injective_type_params = uu___7;_}
                  ->
                  (if (FStar_Compiler_List.length ps) > Prims.int_zero
                   then
                     FStar_Compiler_Effect.raise
                       (Unsupported "parameters on inductive")
                   else ();
                   (let ns = FStar_Ident.ns_of_lid tlid in
                    let name =
                      let uu___9 =
                        let uu___10 = FStar_Ident.ids_of_lid tlid in
                        FStar_Compiler_List.last uu___10 in
                      FStar_Ident.string_of_id uu___9 in
                    let ctors =
                      FStar_Compiler_List.filter
                        (fun se1 ->
                           match se1.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               { FStar_Syntax_Syntax.lid1 = uu___9;
                                 FStar_Syntax_Syntax.us1 = uu___10;
                                 FStar_Syntax_Syntax.t1 = uu___11;
                                 FStar_Syntax_Syntax.ty_lid = ty_lid;
                                 FStar_Syntax_Syntax.num_ty_params = uu___12;
                                 FStar_Syntax_Syntax.mutuals1 = uu___13;
                                 FStar_Syntax_Syntax.injective_type_params1 =
                                   uu___14;_}
                               -> FStar_Ident.lid_equals ty_lid tlid
                           | uu___9 -> false) ses in
                    let ml_name1 =
                      let uu___9 =
                        let uu___10 =
                          let uu___11 = FStar_Ident.string_of_lid tlid in
                          FStar_Extraction_ML_Syntax.MLC_String uu___11 in
                        FStar_Extraction_ML_Syntax.MLE_Const uu___10 in
                      mk uu___9 in
                    let record_fields =
                      let uu___9 =
                        FStar_Compiler_List.find
                          (fun uu___10 ->
                             match uu___10 with
                             | FStar_Syntax_Syntax.RecordType uu___11 -> true
                             | uu___11 -> false)
                          typ_sigelt.FStar_Syntax_Syntax.sigquals in
                      match uu___9 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.RecordType (uu___10, b)) ->
                          let uu___11 =
                            FStar_Compiler_List.map
                              (fun f ->
                                 FStar_Extraction_ML_UEnv.lookup_record_field_name
                                   g (tlid, f)) b in
                          FStar_Pervasives_Native.Some uu___11
                      | uu___10 -> FStar_Pervasives_Native.None in
                    let tcenv = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    let ml_unembed =
                      mk_unembed tcenv mutual_lids record_fields ctors in
                    let ml_embed =
                      mk_embed tcenv mutual_lids record_fields ctors in
                    let def =
                      let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            mk
                              (FStar_Extraction_ML_Syntax.MLE_Name
                                 (["FStar"; "Syntax"; "Embeddings"; "Base"],
                                   "mk_extracted_embedding")) in
                          (uu___11, [ml_name1; ml_unembed; ml_embed]) in
                        FStar_Extraction_ML_Syntax.MLE_App uu___10 in
                      mk uu___9 in
                    let def1 =
                      mk
                        (FStar_Extraction_ML_Syntax.MLE_Fun
                           ([mk_binder "_"
                               FStar_Extraction_ML_Syntax.MLTY_Erased], def)) in
                    let lb =
                      {
                        FStar_Extraction_ML_Syntax.mllb_name =
                          (Prims.strcat "__knot_e_" name);
                        FStar_Extraction_ML_Syntax.mllb_tysc =
                          FStar_Pervasives_Native.None;
                        FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                        FStar_Extraction_ML_Syntax.mllb_def = def1;
                        FStar_Extraction_ML_Syntax.mllb_attrs = [];
                        FStar_Extraction_ML_Syntax.mllb_meta = [];
                        FStar_Extraction_ML_Syntax.print_typ = false
                      } in
                    (let uu___10 =
                       let uu___11 =
                         let uu___12 =
                           FStar_Ident.mk_ident
                             ((Prims.strcat "e_" name),
                               FStar_Compiler_Range_Type.dummyRange) in
                         FStar_Ident.lid_of_ns_and_id ns uu___12 in
                       {
                         arity = Prims.int_zero;
                         syn_emb = uu___11;
                         nbe_emb = FStar_Pervasives_Native.None
                       } in
                     register_embedding tlid uu___10);
                    [lb])) in
            let lbs = FStar_Compiler_List.concatMap proc_one mutual_sigelts in
            let unthunking =
              FStar_Compiler_List.concatMap
                (fun se1 ->
                   let tlid =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         { FStar_Syntax_Syntax.lid = tlid1;
                           FStar_Syntax_Syntax.us = uu___1;
                           FStar_Syntax_Syntax.params = uu___2;
                           FStar_Syntax_Syntax.num_uniform_params = uu___3;
                           FStar_Syntax_Syntax.t = uu___4;
                           FStar_Syntax_Syntax.mutuals = uu___5;
                           FStar_Syntax_Syntax.ds = uu___6;
                           FStar_Syntax_Syntax.injective_type_params = uu___7;_}
                         -> tlid1 in
                   let name =
                     let uu___1 =
                       let uu___2 = FStar_Ident.ids_of_lid tlid in
                       FStar_Compiler_List.last uu___2 in
                     FStar_Ident.string_of_id uu___1 in
                   let app =
                     let head =
                       mk
                         (FStar_Extraction_ML_Syntax.MLE_Var
                            (Prims.strcat "__knot_e_" name)) in
                     mk
                       (FStar_Extraction_ML_Syntax.MLE_App
                          (head, [FStar_Extraction_ML_Syntax.ml_unit])) in
                   let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (Prims.strcat "e_" name);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = app;
                       FStar_Extraction_ML_Syntax.mllb_attrs = [];
                       FStar_Extraction_ML_Syntax.mllb_meta = [];
                       FStar_Extraction_ML_Syntax.print_typ = false
                     } in
                   let uu___1 =
                     FStar_Extraction_ML_Syntax.mk_mlmodule1
                       (FStar_Extraction_ML_Syntax.MLM_Let
                          (FStar_Extraction_ML_Syntax.NonRec, [lb])) in
                   [uu___1]) mutual_sigelts in
            let uu___1 =
              let uu___2 =
                FStar_Extraction_ML_Syntax.mk_mlmodule1
                  (FStar_Extraction_ML_Syntax.MLM_Let
                     (FStar_Extraction_ML_Syntax.Rec, lbs)) in
              [uu___2] in
            FStar_Compiler_List.op_At uu___1 unthunking
        | uu___ -> []
let (do_handle_plugin :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.int FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.sigelt ->
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g ->
    fun arity_opt ->
      fun se ->
        try
          (fun uu___ ->
             match () with | () -> __do_handle_plugin g arity_opt se) ()
        with
        | Unsupported msg ->
            ((let uu___2 =
                let uu___3 = FStar_Syntax_Print.sigelt_to_string_short se in
                FStar_Compiler_Util.format2
                  "Could not generate a plugin for %s, reason = %s" uu___3
                  msg in
              FStar_Errors.log_issue FStar_Syntax_Syntax.has_range_sigelt se
                FStar_Errors_Codes.Warning_PluginNotImplemented ()
                (Obj.magic FStar_Errors_Msg.is_error_message_string)
                (Obj.magic uu___2));
             [])
        | NoEmbedding msg ->
            ((let uu___2 = FStar_Syntax_Print.sigelt_to_string_short se in
              not_implemented_warning se.FStar_Syntax_Syntax.sigrng uu___2
                msg);
             [])
let (maybe_register_plugin :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g ->
    fun se ->
      let plugin_with_arity attrs =
        FStar_Compiler_Util.find_map attrs
          (fun t ->
             let uu___ = FStar_Syntax_Util.head_and_args t in
             match uu___ with
             | (head, args) ->
                 let uu___1 =
                   let uu___2 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head in
                   Prims.op_Negation uu___2 in
                 if uu___1
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | (a, uu___3)::[] ->
                        let nopt =
                          FStar_Syntax_Embeddings_Base.unembed
                            FStar_Syntax_Embeddings.e_fsint a
                            FStar_Syntax_Embeddings_Base.id_norm_cb in
                        FStar_Pervasives_Native.Some nopt
                    | uu___3 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None)) in
      let uu___ =
        let uu___1 = FStar_Options.codegen () in
        uu___1 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin) in
      if uu___
      then []
      else
        (let uu___2 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs in
         match uu___2 with
         | FStar_Pervasives_Native.None -> []
         | FStar_Pervasives_Native.Some uu___3 when
             FStar_Compiler_List.existsb
               (fun uu___4 ->
                  match uu___4 with
                  | FStar_Syntax_Syntax.Projector uu___5 -> true
                  | FStar_Syntax_Syntax.Discriminator uu___5 -> true
                  | uu___5 -> false) se.FStar_Syntax_Syntax.sigquals
             -> []
         | FStar_Pervasives_Native.Some arity_opt ->
             do_handle_plugin g arity_opt se)
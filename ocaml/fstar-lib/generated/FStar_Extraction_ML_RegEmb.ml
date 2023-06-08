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
      mk (FStar_Extraction_ML_Syntax.MLE_Record ([], args))
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
let (s_fvar_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Syntax.Syntax.fvar"
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
let (ml_magic : FStar_Extraction_ML_Syntax.mlexpr) =
  mk
    (FStar_Extraction_ML_Syntax.MLE_Coerce
       (FStar_Extraction_ML_Syntax.ml_unit,
         FStar_Extraction_ML_Syntax.MLTY_Top,
         FStar_Extraction_ML_Syntax.MLTY_Top))
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
    Prims.op_Hat s (Prims.op_Hat "_" (Prims.string_of_int v))
let (not_implemented_warning :
  FStar_Compiler_Range_Type.range -> Prims.string -> Prims.string -> unit) =
  fun r ->
    fun t ->
      fun msg ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Errors.lookup
                    FStar_Errors_Codes.Warning_PluginNotImplemented in
                FStar_Errors.error_number uu___4 in
              FStar_Compiler_Effect.op_Less_Bar Prims.string_of_int uu___3 in
            FStar_Compiler_Util.format3
              "Plugin `%s' can not run natively because %s (use --warn_error -%s to carry on)."
              t msg uu___2 in
          (FStar_Errors_Codes.Warning_PluginNotImplemented, uu___1) in
        FStar_Errors.log_issue r uu___
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
let (known_fv_embeddings :
  (FStar_Ident.lident * embedding_data) Prims.list FStar_Compiler_Effect.ref)
  =
  let syn_emb_lid s =
    FStar_Ident.lid_of_path ["FStar"; "Syntax"; "Embeddings"; s]
      FStar_Compiler_Range_Type.dummyRange in
  let nbe_emb_lid s =
    FStar_Ident.lid_of_path ["FStar"; "TypeChecker"; "NBETerm"; s]
      FStar_Compiler_Range_Type.dummyRange in
  let refl_emb_lid s =
    FStar_Ident.lid_of_path ["FStar"; "Reflection"; "Embeddings"; s]
      FStar_Compiler_Range_Type.dummyRange in
  let nbe_refl_emb_lid s =
    FStar_Ident.lid_of_path ["FStar"; "Reflection"; "NBEEmbeddings"; s]
      FStar_Compiler_Range_Type.dummyRange in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = syn_emb_lid "e_int" in
        let uu___4 =
          let uu___5 = nbe_emb_lid "e_int" in
          FStar_Pervasives_Native.Some uu___5 in
        { arity = Prims.int_zero; syn_emb = uu___3; nbe_emb = uu___4 } in
      (FStar_Parser_Const.int_lid, uu___2) in
    let uu___2 =
      let uu___3 =
        let uu___4 =
          let uu___5 = syn_emb_lid "e_bool" in
          let uu___6 =
            let uu___7 = nbe_emb_lid "e_bool" in
            FStar_Pervasives_Native.Some uu___7 in
          { arity = Prims.int_zero; syn_emb = uu___5; nbe_emb = uu___6 } in
        (FStar_Parser_Const.bool_lid, uu___4) in
      let uu___4 =
        let uu___5 =
          let uu___6 =
            let uu___7 = syn_emb_lid "e_unit" in
            let uu___8 =
              let uu___9 = nbe_emb_lid "e_unit" in
              FStar_Pervasives_Native.Some uu___9 in
            { arity = Prims.int_zero; syn_emb = uu___7; nbe_emb = uu___8 } in
          (FStar_Parser_Const.unit_lid, uu___6) in
        let uu___6 =
          let uu___7 =
            let uu___8 =
              let uu___9 = syn_emb_lid "e_string" in
              let uu___10 =
                let uu___11 = nbe_emb_lid "e_string" in
                FStar_Pervasives_Native.Some uu___11 in
              { arity = Prims.int_zero; syn_emb = uu___9; nbe_emb = uu___10 } in
            (FStar_Parser_Const.string_lid, uu___8) in
          let uu___8 =
            let uu___9 =
              let uu___10 =
                let uu___11 = syn_emb_lid "e_norm_step" in
                let uu___12 =
                  let uu___13 = nbe_emb_lid "e_norm_step" in
                  FStar_Pervasives_Native.Some uu___13 in
                {
                  arity = Prims.int_zero;
                  syn_emb = uu___11;
                  nbe_emb = uu___12
                } in
              (FStar_Parser_Const.norm_step_lid, uu___10) in
            let uu___10 =
              let uu___11 =
                let uu___12 =
                  let uu___13 = syn_emb_lid "e_range" in
                  let uu___14 =
                    let uu___15 = nbe_emb_lid "e_range" in
                    FStar_Pervasives_Native.Some uu___15 in
                  {
                    arity = Prims.int_zero;
                    syn_emb = uu___13;
                    nbe_emb = uu___14
                  } in
                (FStar_Parser_Const.__range_lid, uu___12) in
              let uu___12 =
                let uu___13 =
                  let uu___14 =
                    let uu___15 = syn_emb_lid "e_vconfig" in
                    let uu___16 =
                      let uu___17 = nbe_emb_lid "e_vconfig" in
                      FStar_Pervasives_Native.Some uu___17 in
                    {
                      arity = Prims.int_zero;
                      syn_emb = uu___15;
                      nbe_emb = uu___16
                    } in
                  (FStar_Parser_Const.vconfig_lid, uu___14) in
                let uu___14 =
                  let uu___15 =
                    let uu___16 =
                      let uu___17 = syn_emb_lid "e_list" in
                      let uu___18 =
                        let uu___19 = nbe_emb_lid "e_list" in
                        FStar_Pervasives_Native.Some uu___19 in
                      {
                        arity = Prims.int_one;
                        syn_emb = uu___17;
                        nbe_emb = uu___18
                      } in
                    (FStar_Parser_Const.list_lid, uu___16) in
                  let uu___16 =
                    let uu___17 =
                      let uu___18 =
                        let uu___19 = syn_emb_lid "e_option" in
                        let uu___20 =
                          let uu___21 = nbe_emb_lid "e_option" in
                          FStar_Pervasives_Native.Some uu___21 in
                        {
                          arity = Prims.int_one;
                          syn_emb = uu___19;
                          nbe_emb = uu___20
                        } in
                      (FStar_Parser_Const.option_lid, uu___18) in
                    let uu___18 =
                      let uu___19 =
                        let uu___20 =
                          let uu___21 = syn_emb_lid "e_sealed" in
                          let uu___22 =
                            let uu___23 = nbe_emb_lid "e_sealed" in
                            FStar_Pervasives_Native.Some uu___23 in
                          {
                            arity = Prims.int_one;
                            syn_emb = uu___21;
                            nbe_emb = uu___22
                          } in
                        (FStar_Parser_Const.sealed_lid, uu___20) in
                      let uu___20 =
                        let uu___21 =
                          let uu___22 =
                            FStar_Parser_Const.mk_tuple_lid
                              (Prims.of_int (2))
                              FStar_Compiler_Range_Type.dummyRange in
                          let uu___23 =
                            let uu___24 = syn_emb_lid "e_tuple2" in
                            let uu___25 =
                              let uu___26 = nbe_emb_lid "e_tuple2" in
                              FStar_Pervasives_Native.Some uu___26 in
                            {
                              arity = (Prims.of_int (2));
                              syn_emb = uu___24;
                              nbe_emb = uu___25
                            } in
                          (uu___22, uu___23) in
                        let uu___22 =
                          let uu___23 =
                            let uu___24 =
                              let uu___25 = syn_emb_lid "e_either" in
                              let uu___26 =
                                let uu___27 = nbe_emb_lid "e_either" in
                                FStar_Pervasives_Native.Some uu___27 in
                              {
                                arity = (Prims.of_int (2));
                                syn_emb = uu___25;
                                nbe_emb = uu___26
                              } in
                            (FStar_Parser_Const.either_lid, uu___24) in
                          let uu___24 =
                            let uu___25 =
                              let uu___26 =
                                FStar_Reflection_Constants.fstar_refl_types_lid
                                  "namedv" in
                              let uu___27 =
                                let uu___28 = refl_emb_lid "e_namedv" in
                                let uu___29 =
                                  let uu___30 = nbe_refl_emb_lid "e_namedv" in
                                  FStar_Pervasives_Native.Some uu___30 in
                                {
                                  arity = Prims.int_zero;
                                  syn_emb = uu___28;
                                  nbe_emb = uu___29
                                } in
                              (uu___26, uu___27) in
                            let uu___26 =
                              let uu___27 =
                                let uu___28 =
                                  FStar_Reflection_Constants.fstar_refl_types_lid
                                    "bv" in
                                let uu___29 =
                                  let uu___30 = refl_emb_lid "e_bv" in
                                  let uu___31 =
                                    let uu___32 = nbe_refl_emb_lid "e_bv" in
                                    FStar_Pervasives_Native.Some uu___32 in
                                  {
                                    arity = Prims.int_zero;
                                    syn_emb = uu___30;
                                    nbe_emb = uu___31
                                  } in
                                (uu___28, uu___29) in
                              let uu___28 =
                                let uu___29 =
                                  let uu___30 =
                                    FStar_Reflection_Constants.fstar_refl_types_lid
                                      "binder" in
                                  let uu___31 =
                                    let uu___32 = refl_emb_lid "e_binder" in
                                    let uu___33 =
                                      let uu___34 =
                                        nbe_refl_emb_lid "e_binder" in
                                      FStar_Pervasives_Native.Some uu___34 in
                                    {
                                      arity = Prims.int_zero;
                                      syn_emb = uu___32;
                                      nbe_emb = uu___33
                                    } in
                                  (uu___30, uu___31) in
                                let uu___30 =
                                  let uu___31 =
                                    let uu___32 =
                                      FStar_Reflection_Constants.fstar_refl_types_lid
                                        "term" in
                                    let uu___33 =
                                      let uu___34 = refl_emb_lid "e_term" in
                                      let uu___35 =
                                        let uu___36 =
                                          nbe_refl_emb_lid "e_term" in
                                        FStar_Pervasives_Native.Some uu___36 in
                                      {
                                        arity = Prims.int_zero;
                                        syn_emb = uu___34;
                                        nbe_emb = uu___35
                                      } in
                                    (uu___32, uu___33) in
                                  let uu___32 =
                                    let uu___33 =
                                      let uu___34 =
                                        FStar_Reflection_Constants.fstar_refl_types_lid
                                          "env" in
                                      let uu___35 =
                                        let uu___36 = refl_emb_lid "e_env" in
                                        let uu___37 =
                                          let uu___38 =
                                            nbe_refl_emb_lid "e_env" in
                                          FStar_Pervasives_Native.Some
                                            uu___38 in
                                        {
                                          arity = Prims.int_zero;
                                          syn_emb = uu___36;
                                          nbe_emb = uu___37
                                        } in
                                      (uu___34, uu___35) in
                                    let uu___34 =
                                      let uu___35 =
                                        let uu___36 =
                                          FStar_Reflection_Constants.fstar_refl_types_lid
                                            "fv" in
                                        let uu___37 =
                                          let uu___38 = refl_emb_lid "e_fv" in
                                          let uu___39 =
                                            let uu___40 =
                                              nbe_refl_emb_lid "e_fv" in
                                            FStar_Pervasives_Native.Some
                                              uu___40 in
                                          {
                                            arity = Prims.int_zero;
                                            syn_emb = uu___38;
                                            nbe_emb = uu___39
                                          } in
                                        (uu___36, uu___37) in
                                      let uu___36 =
                                        let uu___37 =
                                          let uu___38 =
                                            FStar_Reflection_Constants.fstar_refl_types_lid
                                              "comp" in
                                          let uu___39 =
                                            let uu___40 =
                                              refl_emb_lid "e_comp" in
                                            let uu___41 =
                                              let uu___42 =
                                                nbe_refl_emb_lid "e_comp" in
                                              FStar_Pervasives_Native.Some
                                                uu___42 in
                                            {
                                              arity = Prims.int_zero;
                                              syn_emb = uu___40;
                                              nbe_emb = uu___41
                                            } in
                                          (uu___38, uu___39) in
                                        let uu___38 =
                                          let uu___39 =
                                            let uu___40 =
                                              FStar_Reflection_Constants.fstar_refl_types_lid
                                                "sigelt" in
                                            let uu___41 =
                                              let uu___42 =
                                                refl_emb_lid "e_sigelt" in
                                              let uu___43 =
                                                let uu___44 =
                                                  nbe_refl_emb_lid "e_sigelt" in
                                                FStar_Pervasives_Native.Some
                                                  uu___44 in
                                              {
                                                arity = Prims.int_zero;
                                                syn_emb = uu___42;
                                                nbe_emb = uu___43
                                              } in
                                            (uu___40, uu___41) in
                                          let uu___40 =
                                            let uu___41 =
                                              let uu___42 =
                                                FStar_Reflection_Constants.fstar_refl_types_lid
                                                  "ctx_uvar_and_subst" in
                                              let uu___43 =
                                                let uu___44 =
                                                  refl_emb_lid
                                                    "e_ctx_uvar_and_subst" in
                                                let uu___45 =
                                                  let uu___46 =
                                                    nbe_refl_emb_lid
                                                      "e_ctx_uvar_and_subst" in
                                                  FStar_Pervasives_Native.Some
                                                    uu___46 in
                                                {
                                                  arity = Prims.int_zero;
                                                  syn_emb = uu___44;
                                                  nbe_emb = uu___45
                                                } in
                                              (uu___42, uu___43) in
                                            let uu___42 =
                                              let uu___43 =
                                                let uu___44 =
                                                  FStar_Reflection_Constants.fstar_refl_types_lid
                                                    "letbinding" in
                                                let uu___45 =
                                                  let uu___46 =
                                                    refl_emb_lid
                                                      "e_letbinding" in
                                                  let uu___47 =
                                                    let uu___48 =
                                                      nbe_refl_emb_lid
                                                        "e_letbinding" in
                                                    FStar_Pervasives_Native.Some
                                                      uu___48 in
                                                  {
                                                    arity = Prims.int_zero;
                                                    syn_emb = uu___46;
                                                    nbe_emb = uu___47
                                                  } in
                                                (uu___44, uu___45) in
                                              let uu___44 =
                                                let uu___45 =
                                                  let uu___46 =
                                                    FStar_Reflection_Constants.fstar_refl_types_lid
                                                      "__ident" in
                                                  let uu___47 =
                                                    let uu___48 =
                                                      refl_emb_lid
                                                        "e___ident" in
                                                    let uu___49 =
                                                      let uu___50 =
                                                        nbe_refl_emb_lid
                                                          "e___ident" in
                                                      FStar_Pervasives_Native.Some
                                                        uu___50 in
                                                    {
                                                      arity = Prims.int_zero;
                                                      syn_emb = uu___48;
                                                      nbe_emb = uu___49
                                                    } in
                                                  (uu___46, uu___47) in
                                                let uu___46 =
                                                  let uu___47 =
                                                    let uu___48 =
                                                      FStar_Reflection_Constants.fstar_refl_types_lid
                                                        "universe_uvar" in
                                                    let uu___49 =
                                                      let uu___50 =
                                                        refl_emb_lid
                                                          "e_universe_uvar" in
                                                      let uu___51 =
                                                        let uu___52 =
                                                          nbe_refl_emb_lid
                                                            "e_universe_uvar" in
                                                        FStar_Pervasives_Native.Some
                                                          uu___52 in
                                                      {
                                                        arity =
                                                          Prims.int_zero;
                                                        syn_emb = uu___50;
                                                        nbe_emb = uu___51
                                                      } in
                                                    (uu___48, uu___49) in
                                                  let uu___48 =
                                                    let uu___49 =
                                                      let uu___50 =
                                                        FStar_Reflection_Constants.fstar_refl_types_lid
                                                          "universe" in
                                                      let uu___51 =
                                                        let uu___52 =
                                                          refl_emb_lid
                                                            "e_universe" in
                                                        let uu___53 =
                                                          let uu___54 =
                                                            nbe_refl_emb_lid
                                                              "e_universe" in
                                                          FStar_Pervasives_Native.Some
                                                            uu___54 in
                                                        {
                                                          arity =
                                                            Prims.int_zero;
                                                          syn_emb = uu___52;
                                                          nbe_emb = uu___53
                                                        } in
                                                      (uu___50, uu___51) in
                                                    let uu___50 =
                                                      let uu___51 =
                                                        let uu___52 =
                                                          FStar_Reflection_Constants.fstar_refl_data_lid
                                                            "vconst" in
                                                        let uu___53 =
                                                          let uu___54 =
                                                            refl_emb_lid
                                                              "e_vconst" in
                                                          let uu___55 =
                                                            let uu___56 =
                                                              nbe_refl_emb_lid
                                                                "e_vconst" in
                                                            FStar_Pervasives_Native.Some
                                                              uu___56 in
                                                          {
                                                            arity =
                                                              Prims.int_zero;
                                                            syn_emb = uu___54;
                                                            nbe_emb = uu___55
                                                          } in
                                                        (uu___52, uu___53) in
                                                      let uu___52 =
                                                        let uu___53 =
                                                          let uu___54 =
                                                            FStar_Reflection_Constants.fstar_refl_data_lid
                                                              "aqualv" in
                                                          let uu___55 =
                                                            let uu___56 =
                                                              refl_emb_lid
                                                                "e_aqualv" in
                                                            let uu___57 =
                                                              let uu___58 =
                                                                nbe_refl_emb_lid
                                                                  "e_aqualv" in
                                                              FStar_Pervasives_Native.Some
                                                                uu___58 in
                                                            {
                                                              arity =
                                                                Prims.int_zero;
                                                              syn_emb =
                                                                uu___56;
                                                              nbe_emb =
                                                                uu___57
                                                            } in
                                                          (uu___54, uu___55) in
                                                        let uu___54 =
                                                          let uu___55 =
                                                            let uu___56 =
                                                              FStar_Reflection_Constants.fstar_refl_data_lid
                                                                "pattern" in
                                                            let uu___57 =
                                                              let uu___58 =
                                                                refl_emb_lid
                                                                  "e_pattern" in
                                                              let uu___59 =
                                                                let uu___60 =
                                                                  nbe_refl_emb_lid
                                                                    "e_pattern" in
                                                                FStar_Pervasives_Native.Some
                                                                  uu___60 in
                                                              {
                                                                arity =
                                                                  Prims.int_zero;
                                                                syn_emb =
                                                                  uu___58;
                                                                nbe_emb =
                                                                  uu___59
                                                              } in
                                                            (uu___56,
                                                              uu___57) in
                                                          let uu___56 =
                                                            let uu___57 =
                                                              let uu___58 =
                                                                FStar_Reflection_Constants.fstar_refl_data_lid
                                                                  "namedv_view" in
                                                              let uu___59 =
                                                                let uu___60 =
                                                                  refl_emb_lid
                                                                    "e_namedv_view" in
                                                                let uu___61 =
                                                                  let uu___62
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_namedv_view" in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu___62 in
                                                                {
                                                                  arity =
                                                                    Prims.int_zero;
                                                                  syn_emb =
                                                                    uu___60;
                                                                  nbe_emb =
                                                                    uu___61
                                                                } in
                                                              (uu___58,
                                                                uu___59) in
                                                            let uu___58 =
                                                              let uu___59 =
                                                                let uu___60 =
                                                                  FStar_Reflection_Constants.fstar_refl_data_lid
                                                                    "bv_view" in
                                                                let uu___61 =
                                                                  let uu___62
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_bv_view" in
                                                                  let uu___63
                                                                    =
                                                                    let uu___64
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_bv_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___64 in
                                                                  {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___62;
                                                                    nbe_emb =
                                                                    uu___63
                                                                  } in
                                                                (uu___60,
                                                                  uu___61) in
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  let uu___62
                                                                    =
                                                                    FStar_Reflection_Constants.fstar_refl_data_lid
                                                                    "binder_view" in
                                                                  let uu___63
                                                                    =
                                                                    let uu___64
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_binder_view" in
                                                                    let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_binder_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___66 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___64;
                                                                    nbe_emb =
                                                                    uu___65
                                                                    } in
                                                                  (uu___62,
                                                                    uu___63) in
                                                                let uu___62 =
                                                                  let uu___63
                                                                    =
                                                                    let uu___64
                                                                    =
                                                                    FStar_Reflection_Constants.fstar_refl_data_lid
                                                                    "binding" in
                                                                    let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_binding" in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_binding" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___68 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___66;
                                                                    nbe_emb =
                                                                    uu___67
                                                                    } in
                                                                    (uu___64,
                                                                    uu___65) in
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    FStar_Reflection_Constants.fstar_refl_data_lid
                                                                    "universe_view" in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_universe_view" in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_universe_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___70 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___68;
                                                                    nbe_emb =
                                                                    uu___69
                                                                    } in
                                                                    (uu___66,
                                                                    uu___67) in
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    FStar_Reflection_Constants.fstar_refl_data_lid
                                                                    "term_view" in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_term_view" in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_term_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___72 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___70;
                                                                    nbe_emb =
                                                                    uu___71
                                                                    } in
                                                                    (uu___68,
                                                                    uu___69) in
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    FStar_Reflection_Constants.fstar_refl_data_lid
                                                                    "comp_view" in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_comp_view" in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_comp_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___74 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___72;
                                                                    nbe_emb =
                                                                    uu___73
                                                                    } in
                                                                    (uu___70,
                                                                    uu___71) in
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    FStar_Reflection_Constants.fstar_refl_data_lid
                                                                    "lb_view" in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_lb_view" in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_lb_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___76 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___74;
                                                                    nbe_emb =
                                                                    uu___75
                                                                    } in
                                                                    (uu___72,
                                                                    uu___73) in
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    FStar_Reflection_Constants.fstar_refl_data_lid
                                                                    "sigelt_view" in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_sigelt_view" in
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_sigelt_view" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___78 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___76;
                                                                    nbe_emb =
                                                                    uu___77
                                                                    } in
                                                                    (uu___74,
                                                                    uu___75) in
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    FStar_Reflection_Constants.fstar_refl_data_lid
                                                                    "qualifier" in
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    refl_emb_lid
                                                                    "e_qualifier" in
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
                                                                    =
                                                                    nbe_refl_emb_lid
                                                                    "e_qualifier" in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___80 in
                                                                    {
                                                                    arity =
                                                                    Prims.int_zero;
                                                                    syn_emb =
                                                                    uu___78;
                                                                    nbe_emb =
                                                                    uu___79
                                                                    } in
                                                                    (uu___76,
                                                                    uu___77) in
                                                                    [uu___75] in
                                                                    uu___73
                                                                    ::
                                                                    uu___74 in
                                                                    uu___71
                                                                    ::
                                                                    uu___72 in
                                                                    uu___69
                                                                    ::
                                                                    uu___70 in
                                                                    uu___67
                                                                    ::
                                                                    uu___68 in
                                                                    uu___65
                                                                    ::
                                                                    uu___66 in
                                                                  uu___63 ::
                                                                    uu___64 in
                                                                uu___61 ::
                                                                  uu___62 in
                                                              uu___59 ::
                                                                uu___60 in
                                                            uu___57 ::
                                                              uu___58 in
                                                          uu___55 :: uu___56 in
                                                        uu___53 :: uu___54 in
                                                      uu___51 :: uu___52 in
                                                    uu___49 :: uu___50 in
                                                  uu___47 :: uu___48 in
                                                uu___45 :: uu___46 in
                                              uu___43 :: uu___44 in
                                            uu___41 :: uu___42 in
                                          uu___39 :: uu___40 in
                                        uu___37 :: uu___38 in
                                      uu___35 :: uu___36 in
                                    uu___33 :: uu___34 in
                                  uu___31 :: uu___32 in
                                uu___29 :: uu___30 in
                              uu___27 :: uu___28 in
                            uu___25 :: uu___26 in
                          uu___23 :: uu___24 in
                        uu___21 :: uu___22 in
                      uu___19 :: uu___20 in
                    uu___17 :: uu___18 in
                  uu___15 :: uu___16 in
                uu___13 :: uu___14 in
              uu___11 :: uu___12 in
            uu___9 :: uu___10 in
          uu___7 :: uu___8 in
        uu___5 :: uu___6 in
      uu___3 :: uu___4 in
    uu___1 :: uu___2 in
  FStar_Compiler_Util.mk_ref uu___
let (register_embedding : FStar_Ident.lident -> embedding_data -> unit) =
  fun l ->
    fun d ->
      let uu___ =
        let uu___1 = FStar_Compiler_Effect.op_Bang known_fv_embeddings in
        (l, d) :: uu___1 in
      FStar_Compiler_Effect.op_Colon_Equals known_fv_embeddings uu___
let (find_fv_embedding' :
  FStar_Ident.lident -> embedding_data FStar_Pervasives_Native.option) =
  fun l ->
    let uu___ =
      let uu___1 = FStar_Compiler_Effect.op_Bang known_fv_embeddings in
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
            Prims.op_Hat "Embedding not defined for type " uu___3 in
          NoEmbedding uu___2 in
        FStar_Compiler_Effect.raise uu___1
let (as_name :
  FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun mlp ->
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
type embedding_kind =
  | SyntaxTerm 
  | NBETerm 
let (uu___is_SyntaxTerm : embedding_kind -> Prims.bool) =
  fun projectee -> match projectee with | SyntaxTerm -> true | uu___ -> false
let (uu___is_NBETerm : embedding_kind -> Prims.bool) =
  fun projectee -> match projectee with | NBETerm -> true | uu___ -> false
let rec (embedding_for :
  FStar_TypeChecker_Env.env ->
    embedding_kind ->
      (FStar_Syntax_Syntax.bv * Prims.string) Prims.list ->
        FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun tcenv ->
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
                | SyntaxTerm -> ml_name' "FStar.Syntax.Embeddings.mk_any_emb"
                | NBETerm -> ml_name' "FStar.TypeChecker.NBETerm.mk_any_emb" in
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
              FStar_Compiler_Effect.op_Less_Bar mk uu___
          | FStar_Syntax_Syntax.Tm_refine
              { FStar_Syntax_Syntax.b = x; FStar_Syntax_Syntax.phi = uu___;_}
              -> embedding_for tcenv k env x.FStar_Syntax_Syntax.sort
          | FStar_Syntax_Syntax.Tm_ascribed
              { FStar_Syntax_Syntax.tm = t4; FStar_Syntax_Syntax.asc = uu___;
                FStar_Syntax_Syntax.eff_opt = uu___1;_}
              -> embedding_for tcenv k env t4
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
                   let uu___1 = embedding_for tcenv k env t0 in
                   let uu___2 = embedding_for tcenv k env t11 in
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
              embedding_for tcenv k env t4
          | FStar_Syntax_Syntax.Tm_app uu___ ->
              let uu___1 = FStar_Syntax_Util.head_and_args t3 in
              (match uu___1 with
               | (head, args) ->
                   let e_head = embedding_for tcenv k env head in
                   let e_args =
                     FStar_Compiler_List.map
                       (fun uu___2 ->
                          match uu___2 with
                          | (t4, uu___3) -> embedding_for tcenv k env t4)
                       args in
                   FStar_Compiler_Effect.op_Less_Bar mk
                     (FStar_Extraction_ML_Syntax.MLE_App (e_head, e_args)))
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
                    | FStar_Pervasives_Native.None -> ml_magic))
          | FStar_Syntax_Syntax.Tm_fvar fv ->
              let uu___ =
                let uu___1 =
                  let uu___2 = FStar_Syntax_Print.term_to_string t3 in
                  FStar_Compiler_Util.format1
                    "Embedding not defined for name `%s'" uu___2 in
                NoEmbedding uu___1 in
              FStar_Compiler_Effect.raise uu___
          | uu___ ->
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStar_Syntax_Print.term_to_string t3 in
                  let uu___4 = FStar_Syntax_Print.tag_of_term t3 in
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
              FStar_Compiler_Effect.op_Less_Bar
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top)
                (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
            let lid_to_name l =
              let uu___ =
                let uu___1 = FStar_Extraction_ML_UEnv.mlpath_of_lident env l in
                FStar_Extraction_ML_Syntax.MLE_Name uu___1 in
              FStar_Compiler_Effect.op_Less_Bar
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu___ in
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
                      FStar_Compiler_Effect.op_Less_Bar
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu___5 in
                    [uu___4] in
                  (uu___2, uu___3) in
                FStar_Extraction_ML_Syntax.MLE_App uu___1 in
              FStar_Compiler_Effect.op_Less_Bar
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu___ in
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
                     (Prims.op_Hat idroot (Prims.string_of_int arity)))) in
            let mk_from_tactic l arity =
              let idroot =
                match l with
                | SyntaxTerm -> "from_tactic_"
                | NBETerm -> "from_nbe_tactic_" in
              as_name1
                (["FStar_Tactics_Native"],
                  (Prims.op_Hat idroot (Prims.string_of_int arity))) in
            let mk_arrow_as_prim_step k arity =
              let modul =
                match k with
                | SyntaxTerm -> ["FStar"; "Syntax"; "Embeddings"]
                | NBETerm -> ["FStar"; "TypeChecker"; "NBETerm"] in
              as_name1
                (modul,
                  (Prims.op_Hat "arrow_as_prim_step_"
                     (Prims.string_of_int arity))) in
            let mk_lam nm e =
              FStar_Compiler_Effect.op_Less_Bar mk
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e)) in
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
                            FStar_Compiler_Effect.op_Less_Bar
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top) uu___5 in
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
                                FStar_Compiler_Effect.op_Less_Bar mk uu___8 in
                              mk_lam "_" uu___7 in
                            [uu___6] in
                          uu___4 :: uu___5 in
                        (uu___2, uu___3) in
                      FStar_Extraction_ML_Syntax.MLE_App uu___1 in
                    FStar_Compiler_Effect.op_Less_Bar mk uu___ in
                  mk_lam "args" body1
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
                            let uu___5 = as_name1 ([], "args") in [uu___5] in
                          (body, uu___4) in
                        FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                      FStar_Compiler_Effect.op_Less_Bar mk uu___2 in
                    (pattern, FStar_Pervasives_Native.None, uu___1) in
                  let default_branch =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = str_to_name "failwith" in
                          let uu___5 =
                            let uu___6 =
                              FStar_Compiler_Effect.op_Less_Bar mk
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_String
                                      "arity mismatch")) in
                            [uu___6] in
                          (uu___4, uu___5) in
                        FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                      FStar_Compiler_Effect.op_Less_Bar mk uu___2 in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu___1) in
                  let body1 =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = as_name1 ([], "args") in
                        (uu___3, [branch; default_branch]) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu___2 in
                    FStar_Compiler_Effect.op_Less_Bar mk uu___1 in
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
                            FStar_Compiler_Effect.op_Less_Bar
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top) uu___6 in
                          let uu___6 =
                            let uu___7 = mk_lam "_" body1 in [uu___7] in
                          uu___5 :: uu___6 in
                        (uu___3, uu___4) in
                      FStar_Extraction_ML_Syntax.MLE_App uu___2 in
                    FStar_Compiler_Effect.op_Less_Bar mk uu___1 in
                  mk_lam "args" body2 in
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
                                 FStar_Compiler_Effect.op_Less_Bar
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
                                   Prims.op_Hat "tv_" (Prims.string_of_int i))
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
                                  embedding_for tcenv loc tvar_context
                                    result_typ in
                                let fv_lid1 =
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                let uu___3 =
                                  FStar_Syntax_Util.is_pure_comp c1 in
                                if uu___3
                                then
                                  let cb = str_to_name "cb" in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity in
                                  let args =
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 = lid_to_name fv_lid1 in
                                        let uu___7 =
                                          let uu___8 =
                                            FStar_Compiler_Effect.op_Less_Bar
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              (FStar_Extraction_ML_Syntax.MLE_Const
                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                    ((Prims.string_of_int
                                                        tvar_arity),
                                                      FStar_Pervasives_Native.None))) in
                                          [uu___8; fv_lid_embedded; cb] in
                                        uu___6 :: uu___7 in
                                      res_embedding :: uu___5 in
                                    FStar_Compiler_List.op_At
                                      arg_unembeddings uu___4 in
                                  let fun_embedding =
                                    FStar_Compiler_Effect.op_Less_Bar mk
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (embed_fun_N, args)) in
                                  let tabs =
                                    abstract_tvars tvar_names fun_embedding in
                                  let cb_tabs = mk_lam "cb" tabs in
                                  let uu___4 =
                                    if loc = NBETerm
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs in
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
                                       FStar_Compiler_Effect.op_Less_Bar mk
                                         uu___6 in
                                     let psc = str_to_name "psc" in
                                     let ncb = str_to_name "ncb" in
                                     let all_args = str_to_name "args" in
                                     let args =
                                       FStar_Compiler_List.op_At [tac_fun]
                                         (FStar_Compiler_List.op_At
                                            arg_unembeddings
                                            [res_embedding; psc; ncb]) in
                                     let tabs =
                                       match tvar_names with
                                       | [] ->
                                           let uu___6 =
                                             FStar_Compiler_Effect.op_Less_Bar
                                               mk
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_Compiler_List.op_At
                                                       args [all_args]))) in
                                           mk_lam "args" uu___6
                                       | uu___6 ->
                                           let uu___7 =
                                             FStar_Compiler_Effect.op_Less_Bar
                                               mk
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args)) in
                                           abstract_tvars tvar_names uu___7 in
                                     let uu___6 =
                                       let uu___7 = mk_lam "ncb" tabs in
                                       mk_lam "psc" uu___7 in
                                     (uu___6, (arity + Prims.int_one), false)
                                   else
                                     (let uu___7 =
                                        let uu___8 =
                                          let uu___9 =
                                            FStar_Syntax_Print.term_to_string
                                              t1 in
                                          Prims.op_Hat
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
                                    embedding_for tcenv loc tvar_context
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
                                   FStar_Syntax_Print.fv_to_string fv in
                                 not_implemented_warning uu___5 uu___6 msg);
                                FStar_Pervasives_Native.None))))
let (mk_unembed :
  FStar_TypeChecker_Env.env ->
    FStar_Extraction_ML_Syntax.mlpath Prims.list
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun tcenv ->
    fun record_fields ->
      fun ctors ->
        let e_branches = FStar_Compiler_Util.mk_ref [] in
        let arg_v = fresh "tm" in
        FStar_Compiler_Effect.op_Bar_Greater ctors
          (FStar_Compiler_List.iter
             (fun ctor ->
                match ctor.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_datacon
                    { FStar_Syntax_Syntax.lid1 = lid;
                      FStar_Syntax_Syntax.us1 = us;
                      FStar_Syntax_Syntax.t1 = t;
                      FStar_Syntax_Syntax.ty_lid = ty_lid;
                      FStar_Syntax_Syntax.num_ty_params = num_ty_params;
                      FStar_Syntax_Syntax.mutuals1 = mutuals;_}
                    ->
                    let fv = fresh "fv" in
                    let uu___1 = FStar_Syntax_Util.arrow_formals t in
                    (match uu___1 with
                     | (bs, c) ->
                         let vs =
                           FStar_Compiler_List.map
                             (fun b ->
                                let uu___2 =
                                  let uu___3 =
                                    FStar_Ident.string_of_id
                                      (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname in
                                  fresh uu___3 in
                                (uu___2,
                                  ((b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort)))
                             bs in
                         let pat_s =
                           let uu___2 =
                             let uu___3 = FStar_Ident.string_of_lid lid in
                             FStar_Extraction_ML_Syntax.MLC_String uu___3 in
                           FStar_Extraction_ML_Syntax.MLP_Const uu___2 in
                         let pat_args =
                           let uu___2 =
                             FStar_Compiler_Effect.op_Bar_Greater vs
                               (FStar_Compiler_List.map
                                  (fun uu___3 ->
                                     match uu___3 with
                                     | (v, uu___4) ->
                                         FStar_Extraction_ML_Syntax.MLP_Var v)) in
                           FStar_Compiler_Effect.op_Bar_Greater uu___2
                             pats_to_list_pat in
                         let pat_both =
                           FStar_Extraction_ML_Syntax.MLP_Tuple
                             [pat_s; pat_args] in
                         let ret =
                           match record_fields with
                           | FStar_Pervasives_Native.Some fields ->
                               let uu___2 =
                                 FStar_Compiler_List.map2
                                   (fun uu___3 ->
                                      fun fld ->
                                        match uu___3 with
                                        | (v, uu___4) ->
                                            ((FStar_Pervasives_Native.snd fld),
                                              (mk
                                                 (FStar_Extraction_ML_Syntax.MLE_Var
                                                    v)))) vs fields in
                               ml_record lid uu___2
                           | FStar_Pervasives_Native.None ->
                               let uu___2 =
                                 FStar_Compiler_List.map
                                   (fun uu___3 ->
                                      match uu___3 with
                                      | (v, uu___4) ->
                                          mk
                                            (FStar_Extraction_ML_Syntax.MLE_Var
                                               v)) vs in
                               ml_ctor lid uu___2 in
                         let ret1 =
                           mk
                             (FStar_Extraction_ML_Syntax.MLE_App
                                (ml_some, [ret])) in
                         let body =
                           FStar_Compiler_List.fold_right
                             (fun uu___2 ->
                                fun body1 ->
                                  match uu___2 with
                                  | (v, ty) ->
                                      let body2 =
                                        mk
                                          (FStar_Extraction_ML_Syntax.MLE_Fun
                                             ([(v,
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)],
                                               body1)) in
                                      let uu___3 =
                                        let uu___4 =
                                          let uu___5 = ml_name bind_opt_lid in
                                          let uu___6 =
                                            let uu___7 =
                                              let uu___8 =
                                                let uu___9 =
                                                  let uu___10 =
                                                    ml_name unembed_lid in
                                                  let uu___11 =
                                                    let uu___12 =
                                                      embedding_for tcenv
                                                        SyntaxTerm [] ty in
                                                    [uu___12;
                                                    mk
                                                      (FStar_Extraction_ML_Syntax.MLE_Var
                                                         v)] in
                                                  (uu___10, uu___11) in
                                                FStar_Extraction_ML_Syntax.MLE_App
                                                  uu___9 in
                                              mk uu___8 in
                                            [uu___7; body2] in
                                          (uu___5, uu___6) in
                                        FStar_Extraction_ML_Syntax.MLE_App
                                          uu___4 in
                                      mk uu___3) vs ret1 in
                         let br =
                           (pat_both, FStar_Pervasives_Native.None, body) in
                         let uu___2 =
                           let uu___3 =
                             FStar_Compiler_Effect.op_Bang e_branches in
                           br :: uu___3 in
                         FStar_Compiler_Effect.op_Colon_Equals e_branches
                           uu___2)
                | uu___1 -> failwith "impossible, filter above"));
        (let nomatch =
           (FStar_Extraction_ML_Syntax.MLP_Wild,
             FStar_Pervasives_Native.None, ml_none) in
         let branches =
           let uu___1 =
             let uu___2 = FStar_Compiler_Effect.op_Bang e_branches in nomatch
               :: uu___2 in
           FStar_Compiler_List.rev uu___1 in
         let sc = mk (FStar_Extraction_ML_Syntax.MLE_Var arg_v) in
         let def = mk (FStar_Extraction_ML_Syntax.MLE_Match (sc, branches)) in
         let lam =
           mk
             (FStar_Extraction_ML_Syntax.MLE_Fun
                ([(arg_v, FStar_Extraction_ML_Syntax.MLTY_Top)], def)) in
         lam)
let (mk_embed :
  FStar_TypeChecker_Env.env ->
    FStar_Extraction_ML_Syntax.mlpath Prims.list
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun tcenv ->
    fun record_fields ->
      fun ctors ->
        let e_branches = FStar_Compiler_Util.mk_ref [] in
        let arg_v = fresh "tm" in
        FStar_Compiler_Effect.op_Bar_Greater ctors
          (FStar_Compiler_List.iter
             (fun ctor ->
                match ctor.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_datacon
                    { FStar_Syntax_Syntax.lid1 = lid;
                      FStar_Syntax_Syntax.us1 = us;
                      FStar_Syntax_Syntax.t1 = t;
                      FStar_Syntax_Syntax.ty_lid = ty_lid;
                      FStar_Syntax_Syntax.num_ty_params = num_ty_params;
                      FStar_Syntax_Syntax.mutuals1 = mutuals;_}
                    ->
                    let fv = fresh "fv" in
                    let uu___1 = FStar_Syntax_Util.arrow_formals t in
                    (match uu___1 with
                     | (bs, c) ->
                         let vs =
                           FStar_Compiler_List.map
                             (fun b ->
                                let uu___2 =
                                  let uu___3 =
                                    FStar_Ident.string_of_id
                                      (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname in
                                  fresh uu___3 in
                                (uu___2,
                                  ((b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort)))
                             bs in
                         let pat =
                           match record_fields with
                           | FStar_Pervasives_Native.Some fields ->
                               let uu___2 =
                                 let uu___3 =
                                   FStar_Compiler_List.map2
                                     (fun v ->
                                        fun fld ->
                                          ((FStar_Pervasives_Native.snd fld),
                                            (FStar_Extraction_ML_Syntax.MLP_Var
                                               (FStar_Pervasives_Native.fst v))))
                                     vs fields in
                                 ([], uu___3) in
                               FStar_Extraction_ML_Syntax.MLP_Record uu___2
                           | FStar_Pervasives_Native.None ->
                               let uu___2 =
                                 let uu___3 =
                                   let uu___4 = FStar_Ident.path_of_lid lid in
                                   splitlast uu___4 in
                                 let uu___4 =
                                   FStar_Compiler_List.map
                                     (fun v ->
                                        FStar_Extraction_ML_Syntax.MLP_Var
                                          (FStar_Pervasives_Native.fst v)) vs in
                                 (uu___3, uu___4) in
                               FStar_Extraction_ML_Syntax.MLP_CTor uu___2 in
                         let fvar = ml_name s_fvar_lid in
                         let lid_of_str = ml_name lid_of_str_lid in
                         let head =
                           let uu___2 =
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       let uu___8 =
                                         let uu___9 =
                                           let uu___10 =
                                             let uu___11 =
                                               let uu___12 =
                                                 FStar_Ident.string_of_lid
                                                   lid in
                                               FStar_Extraction_ML_Syntax.MLC_String
                                                 uu___12 in
                                             FStar_Extraction_ML_Syntax.MLE_Const
                                               uu___11 in
                                           mk uu___10 in
                                         [uu___9] in
                                       (lid_of_str, uu___8) in
                                     FStar_Extraction_ML_Syntax.MLE_App
                                       uu___7 in
                                   mk uu___6 in
                                 [uu___5; ml_none] in
                               (fvar, uu___4) in
                             FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                           mk uu___2 in
                         let mk_mk_app t1 ts =
                           let ts1 =
                             FStar_Compiler_List.map
                               (fun t2 ->
                                  mk
                                    (FStar_Extraction_ML_Syntax.MLE_Tuple
                                       [t2; ml_none])) ts in
                           let uu___2 =
                             let uu___3 =
                               let uu___4 = ml_name mk_app_lid in
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 = as_ml_list ts1 in [uu___7] in
                                 t1 :: uu___6 in
                               (uu___4, uu___5) in
                             FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                           mk uu___2 in
                         let args =
                           FStar_Compiler_Effect.op_Bar_Greater vs
                             (FStar_Compiler_List.map
                                (fun uu___2 ->
                                   match uu___2 with
                                   | (v, ty) ->
                                       let vt =
                                         mk
                                           (FStar_Extraction_ML_Syntax.MLE_Var
                                              v) in
                                       let uu___3 =
                                         let uu___4 =
                                           let uu___5 = ml_name embed_lid in
                                           let uu___6 =
                                             let uu___7 =
                                               embedding_for tcenv SyntaxTerm
                                                 [] ty in
                                             [uu___7; vt] in
                                           (uu___5, uu___6) in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu___4 in
                                       mk uu___3)) in
                         let ret = mk_mk_app head args in
                         let br = (pat, FStar_Pervasives_Native.None, ret) in
                         let uu___2 =
                           let uu___3 =
                             FStar_Compiler_Effect.op_Bang e_branches in
                           br :: uu___3 in
                         FStar_Compiler_Effect.op_Colon_Equals e_branches
                           uu___2)
                | uu___1 -> failwith "impossible, filter above"));
        (let branches =
           let uu___1 = FStar_Compiler_Effect.op_Bang e_branches in
           FStar_Compiler_List.rev uu___1 in
         let sc = mk (FStar_Extraction_ML_Syntax.MLE_Var arg_v) in
         let def = mk (FStar_Extraction_ML_Syntax.MLE_Match (sc, branches)) in
         let lam =
           mk
             (FStar_Extraction_ML_Syntax.MLE_Fun
                ([(arg_v, FStar_Extraction_ML_Syntax.MLTY_Top)], def)) in
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
                         FStar_Compiler_Effect.op_Less_Bar
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name register) in
                       let arity1 =
                         FStar_Extraction_ML_Syntax.MLE_Const
                           (FStar_Extraction_ML_Syntax.MLC_Int
                              ((Prims.string_of_int arity),
                                FStar_Pervasives_Native.None)) in
                       let app =
                         FStar_Compiler_Effect.op_Less_Bar
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_App
                              (h,
                                (FStar_Compiler_List.op_At
                                   [mk ml_name_str; mk arity1] args))) in
                       [FStar_Extraction_ML_Syntax.MLM_Top app])
              | FStar_Pervasives_Native.None -> [] in
            FStar_Compiler_List.collect mk_registration
              (FStar_Pervasives_Native.snd lbs)
        | FStar_Syntax_Syntax.Sig_bundle
            { FStar_Syntax_Syntax.ses = ses;
              FStar_Syntax_Syntax.lids = uu___;_}
            ->
            let typ_sigelt =
              let uu___1 =
                FStar_Compiler_List.filter
                  (fun se1 ->
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ uu___2 -> true
                     | uu___2 -> false) ses in
              match uu___1 with
              | se1::[] -> se1
              | uu___2 ->
                  FStar_Compiler_Effect.raise
                    (Unsupported "mutual inductives") in
            let uu___1 = typ_sigelt.FStar_Syntax_Syntax.sigel in
            (match uu___1 with
             | FStar_Syntax_Syntax.Sig_inductive_typ
                 { FStar_Syntax_Syntax.lid = tlid;
                   FStar_Syntax_Syntax.us = uu___2;
                   FStar_Syntax_Syntax.params = ps;
                   FStar_Syntax_Syntax.num_uniform_params = uu___3;
                   FStar_Syntax_Syntax.t = uu___4;
                   FStar_Syntax_Syntax.mutuals = uu___5;
                   FStar_Syntax_Syntax.ds = uu___6;_}
                 ->
                 (if (FStar_Compiler_List.length ps) > Prims.int_zero
                  then
                    FStar_Compiler_Effect.raise
                      (Unsupported "parameters on inductive")
                  else ();
                  (let ns = FStar_Ident.ns_of_lid tlid in
                   let name =
                     let uu___8 =
                       let uu___9 = FStar_Ident.ids_of_lid tlid in
                       FStar_Compiler_List.last uu___9 in
                     FStar_Ident.string_of_id uu___8 in
                   let ctors =
                     FStar_Compiler_List.filter
                       (fun se1 ->
                          match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon uu___8 -> true
                          | uu___8 -> false) ses in
                   let ml_name1 =
                     let uu___8 =
                       let uu___9 =
                         let uu___10 = FStar_Ident.string_of_lid tlid in
                         FStar_Extraction_ML_Syntax.MLC_String uu___10 in
                       FStar_Extraction_ML_Syntax.MLE_Const uu___9 in
                     mk uu___8 in
                   let record_fields =
                     let uu___8 =
                       FStar_Compiler_List.find
                         (fun uu___9 ->
                            match uu___9 with
                            | FStar_Syntax_Syntax.RecordType uu___10 -> true
                            | uu___10 -> false)
                         se.FStar_Syntax_Syntax.sigquals in
                     match uu___8 with
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Syntax.RecordType (uu___9, b)) ->
                         let uu___10 =
                           FStar_Compiler_List.map
                             (fun f ->
                                FStar_Extraction_ML_UEnv.lookup_record_field_name
                                  g (tlid, f)) b in
                         FStar_Pervasives_Native.Some uu___10
                     | uu___9 -> FStar_Pervasives_Native.None in
                   let tcenv = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                   let ml_unembed = mk_unembed tcenv record_fields ctors in
                   let ml_embed = mk_embed tcenv record_fields ctors in
                   let def =
                     mk
                       (FStar_Extraction_ML_Syntax.MLE_App
                          ((mk
                              (FStar_Extraction_ML_Syntax.MLE_Name
                                 (["FStar"; "Syntax"; "Embeddings"; "Base"],
                                   "mk_extracted_embedding"))),
                            [ml_name1; ml_unembed; ml_embed])) in
                   let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (Prims.op_Hat "e_" name);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = def;
                       FStar_Extraction_ML_Syntax.mllb_meta = [];
                       FStar_Extraction_ML_Syntax.print_typ = false
                     } in
                   (let uu___9 =
                      let uu___10 =
                        let uu___11 =
                          FStar_Ident.mk_ident
                            ((Prims.op_Hat "e_" name),
                              FStar_Compiler_Range_Type.dummyRange) in
                        FStar_Ident.lid_of_ns_and_id ns uu___11 in
                      {
                        arity = Prims.int_zero;
                        syn_emb = uu___10;
                        nbe_emb = FStar_Pervasives_Native.None
                      } in
                    register_embedding tlid uu___9);
                   [FStar_Extraction_ML_Syntax.MLM_Let
                      (FStar_Extraction_ML_Syntax.NonRec, [lb])])))
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
                let uu___3 =
                  let uu___4 = FStar_Syntax_Print.sigelt_to_string_short se in
                  FStar_Compiler_Util.format2
                    "Could not generate a plugin for %s, reason = %s" uu___4
                    msg in
                (FStar_Errors_Codes.Warning_PluginNotImplemented, uu___3) in
              FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu___2);
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
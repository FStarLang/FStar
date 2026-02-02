open Prims
exception NoEmbedding of Prims.string 
let uu___is_NoEmbedding (projectee : Prims.exn) : Prims.bool=
  match projectee with | NoEmbedding uu___ -> true | uu___ -> false
let __proj__NoEmbedding__item__uu___ (projectee : Prims.exn) : Prims.string=
  match projectee with | NoEmbedding uu___ -> uu___
exception Unsupported of Prims.string 
let uu___is_Unsupported (projectee : Prims.exn) : Prims.bool=
  match projectee with | Unsupported uu___ -> true | uu___ -> false
let __proj__Unsupported__item__uu___ (projectee : Prims.exn) : Prims.string=
  match projectee with | Unsupported uu___ -> uu___
let splitlast (s : 'uuuuu Prims.list) : ('uuuuu Prims.list * 'uuuuu)=
  let uu___ = FStarC_List.rev s in
  match uu___ with | x::xs -> ((FStarC_List.rev xs), x)
let mk (e : FStarC_Extraction_ML_Syntax.mlexpr') :
  FStarC_Extraction_ML_Syntax.mlexpr=
  FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.MLTY_Top e
let ml_name (l : FStarC_Ident.lid) : FStarC_Extraction_ML_Syntax.mlexpr=
  let s = FStarC_Ident.path_of_lid l in
  let uu___ = splitlast s in
  match uu___ with
  | (ns, id) -> mk (FStarC_Extraction_ML_Syntax.MLE_Name (ns, id))
let ml_name' (s : Prims.string) : FStarC_Extraction_ML_Syntax.mlexpr=
  let uu___ = FStarC_Ident.lid_of_str s in ml_name uu___
let ml_ctor (l : FStarC_Ident.lid)
  (args : FStarC_Extraction_ML_Syntax.mlexpr Prims.list) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  let s = FStarC_Ident.path_of_lid l in
  let uu___ = splitlast s in
  match uu___ with
  | (ns, id) -> mk (FStarC_Extraction_ML_Syntax.MLE_CTor ((ns, id), args))
let ml_record (l : FStarC_Ident.lid)
  (args : (Prims.string * FStarC_Extraction_ML_Syntax.mlexpr) Prims.list) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  let s = FStarC_Ident.path_of_lid l in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Ident.ident_of_lid l in
        FStarC_Ident.string_of_id uu___3 in
      ([], uu___2, args) in
    FStarC_Extraction_ML_Syntax.MLE_Record uu___1 in
  mk uu___
let mk_binder (x : FStarC_Extraction_ML_Syntax.mlident)
  (t : FStarC_Extraction_ML_Syntax.mlty) :
  FStarC_Extraction_ML_Syntax.mlbinder=
  {
    FStarC_Extraction_ML_Syntax.mlbinder_name = x;
    FStarC_Extraction_ML_Syntax.mlbinder_ty = t;
    FStarC_Extraction_ML_Syntax.mlbinder_attrs = []
  }
let ml_lam (nm : FStarC_Extraction_ML_Syntax.mlident)
  (e : FStarC_Extraction_ML_Syntax.mlexpr) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Fun
       ([mk_binder nm FStarC_Extraction_ML_Syntax.MLTY_Top], e))
let ml_none : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (["FStar"; "Pervasives"; "Native"], "None"))
let ml_some : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (["FStar"; "Pervasives"; "Native"], "Some"))
let s_tdataconstr : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (splitlast ["Fstarcompiler.FStarC"; "Syntax"; "Syntax"; "tdataconstr"]))
let mk_app : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (splitlast ["Fstarcompiler.FStarC"; "Syntax"; "Util"; "mk_app"]))
let tm_fvar : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (splitlast ["Fstarcompiler.FStarC"; "Syntax"; "Syntax"; "Tm_fvar"]))
let fv_eq_lid : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (splitlast ["Fstarcompiler.FStarC"; "Syntax"; "Syntax"; "fv_eq_lid"]))
let lid_of_str : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (splitlast ["Fstarcompiler.FStarC"; "Ident"; "lid_of_str"]))
let nil_lid : FStarC_Ident.lident= FStarC_Ident.lid_of_str "Prims.Nil"
let cons_lid : FStarC_Ident.lident= FStarC_Ident.lid_of_str "Prims.Cons"
let embed : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (splitlast
          ["Fstarcompiler.FStarC";
          "Syntax";
          "Embeddings";
          "Base";
          "extracted_embed"]))
let unembed : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (splitlast
          ["Fstarcompiler.FStarC";
          "Syntax";
          "Embeddings";
          "Base";
          "extracted_unembed"]))
let bind_opt : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Name
       (splitlast ["Fstarcompiler.FStarC"; "Option"; "bind"]))
let ml_nbe_unsupported : FStarC_Extraction_ML_Syntax.mlexpr=
  let hd =
    mk
      (FStarC_Extraction_ML_Syntax.MLE_Name
         (["Fstarcompiler.FStarC"; "TypeChecker"; "NBETerm"],
           "e_unsupported")) in
  mk
    (FStarC_Extraction_ML_Syntax.MLE_App
       (hd, [FStarC_Extraction_ML_Syntax.ml_unit]))
let ml_magic : FStarC_Extraction_ML_Syntax.mlexpr=
  mk
    (FStarC_Extraction_ML_Syntax.MLE_Coerce
       (FStarC_Extraction_ML_Syntax.ml_unit,
         FStarC_Extraction_ML_Syntax.MLTY_Top,
         FStarC_Extraction_ML_Syntax.MLTY_Top))
let as_name (mlp : FStarC_Extraction_ML_Syntax.mlpath) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.MLTY_Top
    (FStarC_Extraction_ML_Syntax.MLE_Name mlp)
let ml_failwith (s : Prims.string) : FStarC_Extraction_ML_Syntax.mlexpr=
  let uu___ =
    let uu___1 =
      let uu___2 = as_name ([], "failwith") in
      let uu___3 =
        let uu___4 =
          mk
            (FStarC_Extraction_ML_Syntax.MLE_Const
               (FStarC_Extraction_ML_Syntax.MLC_String s)) in
        [uu___4] in
      (uu___2, uu___3) in
    FStarC_Extraction_ML_Syntax.MLE_App uu___1 in
  mk uu___
let rec as_ml_list (ts : FStarC_Extraction_ML_Syntax.mlexpr Prims.list) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  match ts with
  | [] -> ml_ctor nil_lid []
  | t::ts1 ->
      let uu___ =
        let uu___1 = let uu___2 = as_ml_list ts1 in [uu___2] in t :: uu___1 in
      ml_ctor cons_lid uu___
let rec pats_to_list_pat
  (vs : FStarC_Extraction_ML_Syntax.mlpattern Prims.list) :
  FStarC_Extraction_ML_Syntax.mlpattern=
  match vs with
  | [] -> FStarC_Extraction_ML_Syntax.MLP_CTor ((["Prims"], "Nil"), [])
  | p::ps ->
      let uu___ =
        let uu___1 =
          let uu___2 = let uu___3 = pats_to_list_pat ps in [uu___3] in p ::
            uu___2 in
        ((["Prims"], "Cons"), uu___1) in
      FStarC_Extraction_ML_Syntax.MLP_CTor uu___
let fresh : Prims.string -> Prims.string=
  let r = FStarC_Effect.mk_ref Prims.int_zero in
  fun s ->
    let v = FStarC_Effect.op_Bang r in
    FStarC_Effect.op_Colon_Equals r (v + Prims.int_one);
    (let uu___1 =
       let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int v in
       Prims.strcat "_" uu___2 in
     Prims.strcat s uu___1)
let not_implemented_warning (r : FStarC_Range_Type.t) (t : Prims.string)
  (msg : Prims.string) : unit=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          FStarC_Format.fmt1 "Plugin `%s' can not run natively because:" t in
        FStarC_Errors_Msg.text uu___3 in
      let uu___3 = FStarC_Errors_Msg.text msg in
      FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one uu___2 uu___3 in
    let uu___2 =
      let uu___3 =
        let uu___4 = FStarC_Errors_Msg.text "Use --warn_error -" in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              let uu___8 =
                FStarC_Errors.lookup
                  FStarC_Errors_Codes.Warning_PluginNotImplemented in
              FStarC_Errors.error_number uu___8 in
            FStarC_Class_PP.pp FStarC_Class_PP.pp_int uu___7 in
          let uu___7 = FStarC_Errors_Msg.text "to carry on." in
          FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
        FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
      [uu___3] in
    uu___1 :: uu___2 in
  FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
    FStarC_Errors_Codes.Warning_PluginNotImplemented ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc) (Obj.magic uu___)
type embedding_data =
  {
  arity: Prims.int ;
  syn_emb: FStarC_Ident.lid ;
  nbe_emb: FStarC_Ident.lid FStar_Pervasives_Native.option }
let __proj__Mkembedding_data__item__arity (projectee : embedding_data) :
  Prims.int= match projectee with | { arity; syn_emb; nbe_emb;_} -> arity
let __proj__Mkembedding_data__item__syn_emb (projectee : embedding_data) :
  FStarC_Ident.lid=
  match projectee with | { arity; syn_emb; nbe_emb;_} -> syn_emb
let __proj__Mkembedding_data__item__nbe_emb (projectee : embedding_data) :
  FStarC_Ident.lid FStar_Pervasives_Native.option=
  match projectee with | { arity; syn_emb; nbe_emb;_} -> nbe_emb
let builtin_embeddings : (FStarC_Ident.lident * embedding_data) Prims.list=
  let syn_emb_lid s =
    FStarC_Ident.lid_of_path
      ["Fstarcompiler.FStarC"; "Syntax"; "Embeddings"; s]
      FStarC_Range_Type.dummyRange in
  let nbe_emb_lid s =
    FStarC_Ident.lid_of_path
      ["Fstarcompiler.FStarC"; "TypeChecker"; "NBETerm"; s]
      FStarC_Range_Type.dummyRange in
  let refl_emb_lid s =
    FStarC_Ident.lid_of_path
      ["Fstarcompiler.FStarC"; "Reflection"; "V2"; "Embeddings"; s]
      FStarC_Range_Type.dummyRange in
  let nbe_refl_emb_lid s =
    FStarC_Ident.lid_of_path
      ["Fstarcompiler.FStarC"; "Reflection"; "V2"; "NBEEmbeddings"; s]
      FStarC_Range_Type.dummyRange in
  let uu___ =
    let uu___1 =
      let uu___2 = syn_emb_lid "e_int" in
      let uu___3 =
        let uu___4 = nbe_emb_lid "e_int" in
        FStar_Pervasives_Native.Some uu___4 in
      { arity = Prims.int_zero; syn_emb = uu___2; nbe_emb = uu___3 } in
    (FStarC_Parser_Const.int_lid, uu___1) in
  let uu___1 =
    let uu___2 =
      let uu___3 =
        let uu___4 = syn_emb_lid "e_bool" in
        let uu___5 =
          let uu___6 = nbe_emb_lid "e_bool" in
          FStar_Pervasives_Native.Some uu___6 in
        { arity = Prims.int_zero; syn_emb = uu___4; nbe_emb = uu___5 } in
      (FStarC_Parser_Const.bool_lid, uu___3) in
    let uu___3 =
      let uu___4 =
        let uu___5 =
          let uu___6 = syn_emb_lid "e_unit" in
          let uu___7 =
            let uu___8 = nbe_emb_lid "e_unit" in
            FStar_Pervasives_Native.Some uu___8 in
          { arity = Prims.int_zero; syn_emb = uu___6; nbe_emb = uu___7 } in
        (FStarC_Parser_Const.unit_lid, uu___5) in
      let uu___5 =
        let uu___6 =
          let uu___7 =
            let uu___8 = syn_emb_lid "e_string" in
            let uu___9 =
              let uu___10 = nbe_emb_lid "e_string" in
              FStar_Pervasives_Native.Some uu___10 in
            { arity = Prims.int_zero; syn_emb = uu___8; nbe_emb = uu___9 } in
          (FStarC_Parser_Const.string_lid, uu___7) in
        let uu___7 =
          let uu___8 =
            let uu___9 =
              let uu___10 = syn_emb_lid "e_norm_step" in
              let uu___11 =
                let uu___12 = nbe_emb_lid "e_norm_step" in
                FStar_Pervasives_Native.Some uu___12 in
              { arity = Prims.int_zero; syn_emb = uu___10; nbe_emb = uu___11
              } in
            (FStarC_Parser_Const.norm_step_lid, uu___9) in
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
              (FStarC_Parser_Const.__range_lid, uu___11) in
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
                (FStarC_Parser_Const.vconfig_lid, uu___13) in
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
                  (FStarC_Parser_Const.list_lid, uu___15) in
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
                    (FStarC_Parser_Const.option_lid, uu___17) in
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
                      (FStarC_Parser_Const.sealed_lid, uu___19) in
                    let uu___19 =
                      let uu___20 =
                        let uu___21 =
                          FStarC_Parser_Const_Tuples.mk_tuple_lid
                            (Prims.of_int (2)) FStarC_Range_Type.dummyRange in
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
                            FStarC_Parser_Const_Tuples.mk_tuple_lid
                              (Prims.of_int (3)) FStarC_Range_Type.dummyRange in
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
                            (FStarC_Parser_Const.either_lid, uu___25) in
                          let uu___25 =
                            let uu___26 =
                              let uu___27 =
                                FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                  FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                    FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                      FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                        FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                          FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                            FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                              FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                                FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                                  FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                                    FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                                      FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                                        FStarC_Reflection_V2_Constants.fstar_refl_types_lid
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
                                                          FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                            FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                              FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                  FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
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
let dbg_plugin : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "Plugins"
let local_fv_embeddings :
  (FStarC_Ident.lident * embedding_data) Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let register_embedding (l : FStarC_Ident.lident) (d : embedding_data) : 
  unit=
  (let uu___1 = FStarC_Effect.op_Bang dbg_plugin in
   if uu___1
   then
     let uu___2 = FStarC_Ident.string_of_lid l in
     FStarC_Format.print1 "Registering local embedding for %s\n" uu___2
   else ());
  (let uu___1 =
     let uu___2 = FStarC_Effect.op_Bang local_fv_embeddings in (l, d) ::
       uu___2 in
   FStarC_Effect.op_Colon_Equals local_fv_embeddings uu___1)
let list_local (uu___ : unit) :
  (FStarC_Ident.lident * embedding_data) Prims.list=
  FStarC_Effect.op_Bang local_fv_embeddings
let find_fv_embedding' (l : FStarC_Ident.lident) :
  embedding_data FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Effect.op_Bang local_fv_embeddings in
      FStarC_List.op_At uu___2 builtin_embeddings in
    FStarC_List.find
      (fun uu___2 ->
         match uu___2 with | (l', uu___3) -> FStarC_Ident.lid_equals l l')
      uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, data) ->
      FStar_Pervasives_Native.Some data
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let find_fv_embedding (l : FStarC_Ident.lident) : embedding_data=
  let uu___ = find_fv_embedding' l in
  match uu___ with
  | FStar_Pervasives_Native.Some data -> data
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Ident.string_of_lid l in
          Prims.strcat "Embedding not defined for type " uu___3 in
        NoEmbedding uu___2 in
      FStarC_Effect.raise uu___1
type embedding_kind =
  | SyntaxTerm 
  | NBETerm 
let uu___is_SyntaxTerm (projectee : embedding_kind) : Prims.bool=
  match projectee with | SyntaxTerm -> true | uu___ -> false
let uu___is_NBETerm (projectee : embedding_kind) : Prims.bool=
  match projectee with | NBETerm -> true | uu___ -> false
let rec embedding_for (tcenv : FStarC_TypeChecker_Env.env)
  (mutuals : FStarC_Ident.lid Prims.list) (k : embedding_kind)
  (env : (FStarC_Syntax_Syntax.bv * Prims.string) Prims.list)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Extraction_ML_Syntax.mlexpr=
  let str_to_name s = as_name ([], s) in
  let emb_arrow e1 e2 =
    let comb =
      match k with
      | SyntaxTerm ->
          mk
            (FStarC_Extraction_ML_Syntax.MLE_Name
               (["Fstarcompiler.FStarC"; "Syntax"; "Embeddings"], "e_arrow"))
      | NBETerm ->
          mk
            (FStarC_Extraction_ML_Syntax.MLE_Name
               (["Fstarcompiler.FStarC"; "TypeChecker"; "NBETerm"],
                 "e_arrow")) in
    mk (FStarC_Extraction_ML_Syntax.MLE_App (comb, [e1; e2])) in
  let find_env_entry bv uu___ =
    match uu___ with | (bv', uu___1) -> FStarC_Syntax_Syntax.bv_eq bv bv' in
  let t1 = FStarC_TypeChecker_Normalize.unfold_whnf tcenv t in
  let t2 = FStarC_Syntax_Util.un_uinst t1 in
  let t3 = FStarC_Syntax_Subst.compress t2 in
  match t3.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_name bv when
      FStarC_Util.for_some (find_env_entry bv) env ->
      let comb =
        match k with
        | SyntaxTerm ->
            mk
              (FStarC_Extraction_ML_Syntax.MLE_Name
                 (["Fstarcompiler.FStarC"; "Syntax"; "Embeddings"],
                   "mk_any_emb"))
        | NBETerm ->
            mk
              (FStarC_Extraction_ML_Syntax.MLE_Name
                 (["Fstarcompiler.FStarC"; "TypeChecker"; "NBETerm"],
                   "mk_any_emb")) in
      let s =
        let uu___ =
          let uu___1 = FStarC_Option.find (find_env_entry bv) env in
          FStar_Pervasives_Native.__proj__Some__item__v uu___1 in
        FStar_Pervasives_Native.snd uu___ in
      let uu___ =
        let uu___1 =
          let uu___2 = let uu___3 = str_to_name s in [uu___3] in
          (comb, uu___2) in
        FStarC_Extraction_ML_Syntax.MLE_App uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_refine
      { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = uu___;_} ->
      embedding_for tcenv mutuals k env x.FStarC_Syntax_Syntax.sort
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = t4; FStarC_Syntax_Syntax.asc = uu___;
        FStarC_Syntax_Syntax.eff_opt = uu___1;_}
      -> embedding_for tcenv mutuals k env t4
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.bs1 = b::[]; FStarC_Syntax_Syntax.comp = c;_}
      when FStarC_Syntax_Util.is_pure_comp c ->
      let uu___ = FStarC_Syntax_Subst.open_comp [b] c in
      (match uu___ with
       | (b1::[], c1) ->
           let t0 =
             (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
           let t11 = FStarC_Syntax_Util.comp_result c1 in
           let uu___1 = embedding_for tcenv mutuals k env t0 in
           let uu___2 = embedding_for tcenv mutuals k env t11 in
           emb_arrow uu___1 uu___2)
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.bs1 = b::more::bs;
        FStarC_Syntax_Syntax.comp = c;_}
      ->
      let tail =
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_arrow
             {
               FStarC_Syntax_Syntax.bs1 = (more :: bs);
               FStarC_Syntax_Syntax.comp = c
             }) t3.FStarC_Syntax_Syntax.pos in
      let t4 =
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Syntax_Syntax.mk_Total tail in
            {
              FStarC_Syntax_Syntax.bs1 = [b];
              FStarC_Syntax_Syntax.comp = uu___2
            } in
          FStarC_Syntax_Syntax.Tm_arrow uu___1 in
        FStarC_Syntax_Syntax.mk uu___ t3.FStarC_Syntax_Syntax.pos in
      embedding_for tcenv mutuals k env t4
  | FStarC_Syntax_Syntax.Tm_app uu___ ->
      let uu___1 = FStarC_Syntax_Util.head_and_args t3 in
      (match uu___1 with
       | (head, args) ->
           let e_head = embedding_for tcenv mutuals k env head in
           let e_args =
             FStarC_List.map
               (fun uu___2 ->
                  match uu___2 with
                  | (t4, uu___3) -> embedding_for tcenv mutuals k env t4)
               args in
           mk (FStarC_Extraction_ML_Syntax.MLE_App (e_head, e_args)))
  | FStarC_Syntax_Syntax.Tm_fvar fv when
      FStarC_List.existsb
        (FStarC_Ident.lid_equals fv.FStarC_Syntax_Syntax.fv_name) mutuals
      ->
      let head =
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStarC_Ident.ident_of_lid fv.FStarC_Syntax_Syntax.fv_name in
              FStarC_Ident.string_of_id uu___3 in
            Prims.strcat "__knot_e_" uu___2 in
          FStarC_Extraction_ML_Syntax.MLE_Var uu___1 in
        mk uu___ in
      mk
        (FStarC_Extraction_ML_Syntax.MLE_App
           (head, [FStarC_Extraction_ML_Syntax.ml_unit]))
  | FStarC_Syntax_Syntax.Tm_fvar fv when
      let uu___ = find_fv_embedding' fv.FStarC_Syntax_Syntax.fv_name in
      FStar_Pervasives_Native.uu___is_Some uu___ ->
      let emb_data = find_fv_embedding fv.FStarC_Syntax_Syntax.fv_name in
      (match k with
       | SyntaxTerm -> ml_name emb_data.syn_emb
       | NBETerm ->
           (match emb_data.nbe_emb with
            | FStar_Pervasives_Native.Some lid -> ml_name lid
            | FStar_Pervasives_Native.None -> ml_nbe_unsupported))
  | FStarC_Syntax_Syntax.Tm_fvar fv when
      FStarC_TypeChecker_Env.fv_has_attr tcenv fv
        FStarC_Parser_Const.plugin_attr
      ->
      (match k with
       | SyntaxTerm ->
           let lid = fv.FStarC_Syntax_Syntax.fv_name in
           let uu___ =
             let uu___1 =
               let uu___2 = FStarC_Ident.ns_of_lid lid in
               FStarC_List.map FStarC_Ident.string_of_id uu___2 in
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStarC_Ident.ident_of_lid lid in
                 FStarC_Ident.string_of_id uu___4 in
               Prims.strcat "e_" uu___3 in
             (uu___1, uu___2) in
           as_name uu___
       | NBETerm -> ml_nbe_unsupported)
  | FStarC_Syntax_Syntax.Tm_fvar fv ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t3 in
          FStarC_Format.fmt1 "Embedding not defined for name `%s'" uu___2 in
        NoEmbedding uu___1 in
      FStarC_Effect.raise uu___
  | uu___ ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t3 in
          let uu___4 =
            FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t3 in
          FStarC_Format.fmt2 "Cannot embed type `%s' (%s)" uu___3 uu___4 in
        NoEmbedding uu___2 in
      FStarC_Effect.raise uu___1
type wrapped_term =
  (FStarC_Extraction_ML_Syntax.mlexpr * FStarC_Extraction_ML_Syntax.mlexpr *
    Prims.int * Prims.bool)
let interpret_plugin_as_term_fun (env : FStarC_Extraction_ML_UEnv.uenv)
  (fv : FStarC_Syntax_Syntax.fv) (t : FStarC_Syntax_Syntax.typ)
  (arity_opt : Prims.int FStar_Pervasives_Native.option)
  (ml_fv : FStarC_Extraction_ML_Syntax.mlexpr') :
  (FStarC_Extraction_ML_Syntax.mlexpr * FStarC_Extraction_ML_Syntax.mlexpr *
    Prims.int * Prims.bool) FStar_Pervasives_Native.option=
  let fv_lid = fv.FStarC_Syntax_Syntax.fv_name in
  let tcenv = FStarC_Extraction_ML_UEnv.tcenv_of_uenv env in
  let t1 =
    FStarC_TypeChecker_Normalize.normalize
      [FStarC_TypeChecker_Env.EraseUniverses;
      FStarC_TypeChecker_Env.AllowUnboundUniverses;
      FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant;
      FStarC_TypeChecker_Env.ForExtraction] tcenv t in
  let as_name1 mlp =
    FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.MLTY_Top
      (FStarC_Extraction_ML_Syntax.MLE_Name mlp) in
  let lid_to_name l =
    let uu___ =
      let uu___1 = FStarC_Extraction_ML_UEnv.mlpath_of_lident env l in
      FStarC_Extraction_ML_Syntax.MLE_Name uu___1 in
    FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.MLTY_Top
      uu___ in
  let str_to_name s = as_name1 ([], s) in
  let fv_lid_embedded =
    let uu___ =
      let uu___1 =
        let uu___2 = as_name1 (["Fstarcompiler.FStarC_Ident"], "lid_of_str") in
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_Ident.string_of_lid fv_lid in
                FStarC_Extraction_ML_Syntax.MLC_String uu___7 in
              FStarC_Extraction_ML_Syntax.MLE_Const uu___6 in
            FStarC_Extraction_ML_Syntax.with_ty
              FStarC_Extraction_ML_Syntax.MLTY_Top uu___5 in
          [uu___4] in
        (uu___2, uu___3) in
      FStarC_Extraction_ML_Syntax.MLE_App uu___1 in
    FStarC_Extraction_ML_Syntax.with_ty FStarC_Extraction_ML_Syntax.MLTY_Top
      uu___ in
  let mk_tactic_interpretation l arity =
    if arity > FStarC_Tactics_InterpFuns.max_tac_arity
    then
      FStarC_Effect.raise
        (NoEmbedding "tactic plugins can only take up to 20 arguments")
    else
      (let idroot =
         match l with
         | SyntaxTerm -> "mk_tactic_interpretation_"
         | NBETerm -> "mk_nbe_tactic_interpretation_" in
       let uu___1 =
         let uu___2 =
           let uu___3 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int arity in
           Prims.strcat idroot uu___3 in
         (["Fstarcompiler.FStarC_Tactics_InterpFuns"], uu___2) in
       as_name1 uu___1) in
  let mk_from_tactic l arity =
    let idroot =
      match l with
      | SyntaxTerm -> "from_tactic_"
      | NBETerm -> "from_nbe_tactic_" in
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_nat arity in
        Prims.strcat idroot uu___2 in
      (["Fstarcompiler.FStarC_Tactics_Native"], uu___1) in
    as_name1 uu___ in
  let mk_arrow_as_prim_step k arity =
    let modul =
      match k with
      | SyntaxTerm -> ["Fstarcompiler.FStarC"; "Syntax"; "Embeddings"]
      | NBETerm -> ["Fstarcompiler.FStarC"; "TypeChecker"; "NBETerm"] in
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int arity in
        Prims.strcat "arrow_as_prim_step_" uu___2 in
      (modul, uu___1) in
    as_name1 uu___ in
  let abstract_tvars tvar_names body =
    match tvar_names with
    | [] ->
        let body1 =
          let uu___ =
            let uu___1 =
              let uu___2 =
                as_name1
                  (["Fstarcompiler.FStarC_Syntax_Embeddings"], "debug_wrap") in
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 = FStarC_Ident.string_of_lid fv_lid in
                      FStarC_Extraction_ML_Syntax.MLC_String uu___7 in
                    FStarC_Extraction_ML_Syntax.MLE_Const uu___6 in
                  FStarC_Extraction_ML_Syntax.with_ty
                    FStarC_Extraction_ML_Syntax.MLTY_Top uu___5 in
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          let uu___10 =
                            let uu___11 = str_to_name "args" in [uu___11] in
                          (body, uu___10) in
                        FStarC_Extraction_ML_Syntax.MLE_App uu___9 in
                      mk uu___8 in
                    ml_lam "_" uu___7 in
                  [uu___6] in
                uu___4 :: uu___5 in
              (uu___2, uu___3) in
            FStarC_Extraction_ML_Syntax.MLE_App uu___1 in
          mk uu___ in
        ml_lam "args" body1
    | uu___ ->
        let args_tail = FStarC_Extraction_ML_Syntax.MLP_Var "args_tail" in
        let mk_cons hd_pat tail_pat =
          FStarC_Extraction_ML_Syntax.MLP_CTor
            ((["Prims"], "Cons"), [hd_pat; tail_pat]) in
        let fst_pat v =
          FStarC_Extraction_ML_Syntax.MLP_Tuple
            [FStarC_Extraction_ML_Syntax.MLP_Var v;
            FStarC_Extraction_ML_Syntax.MLP_Wild] in
        let pattern =
          FStarC_List.fold_right (fun hd_var -> mk_cons (fst_pat hd_var))
            tvar_names args_tail in
        let branch =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = as_name1 ([], "args_tail") in [uu___5] in
                (body, uu___4) in
              FStarC_Extraction_ML_Syntax.MLE_App uu___3 in
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
                      (FStarC_Extraction_ML_Syntax.MLE_Const
                         (FStarC_Extraction_ML_Syntax.MLC_String
                            "arity mismatch")) in
                  [uu___6] in
                (uu___4, uu___5) in
              FStarC_Extraction_ML_Syntax.MLE_App uu___3 in
            mk uu___2 in
          (FStarC_Extraction_ML_Syntax.MLP_Wild,
            FStar_Pervasives_Native.None, uu___1) in
        let body1 =
          let uu___1 =
            let uu___2 =
              let uu___3 = as_name1 ([], "args") in
              (uu___3, [branch; default_branch]) in
            FStarC_Extraction_ML_Syntax.MLE_Match uu___2 in
          mk uu___1 in
        let body2 =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                as_name1
                  (["Fstarcompiler.FStarC_Syntax_Embeddings"], "debug_wrap") in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = FStarC_Ident.string_of_lid fv_lid in
                      FStarC_Extraction_ML_Syntax.MLC_String uu___8 in
                    FStarC_Extraction_ML_Syntax.MLE_Const uu___7 in
                  FStarC_Extraction_ML_Syntax.with_ty
                    FStarC_Extraction_ML_Syntax.MLTY_Top uu___6 in
                let uu___6 = let uu___7 = ml_lam "_" body1 in [uu___7] in
                uu___5 :: uu___6 in
              (uu___3, uu___4) in
            FStarC_Extraction_ML_Syntax.MLE_App uu___2 in
          mk uu___1 in
        ml_lam "args" body2 in
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp t1 in
  match uu___ with
  | (bs, c) ->
      let uu___1 =
        match arity_opt with
        | FStar_Pervasives_Native.None -> (bs, c)
        | FStar_Pervasives_Native.Some n ->
            let n_bs = FStarC_List.length bs in
            if n = n_bs
            then (bs, c)
            else
              if n < n_bs
              then
                (let uu___3 = FStarC_Util.first_N n bs in
                 match uu___3 with
                 | (bs1, rest) ->
                     let c1 =
                       let uu___4 = FStarC_Syntax_Util.arrow rest c in
                       FStarC_Syntax_Syntax.mk_Total uu___4 in
                     (bs1, c1))
              else
                (let msg =
                   let uu___4 = FStarC_Ident.string_of_lid fv_lid in
                   let uu___5 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
                   let uu___6 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                       n_bs in
                   FStarC_Format.fmt3
                     "Embedding not defined for %s; expected arity at least %s; got %s"
                     uu___4 uu___5 uu___6 in
                 FStarC_Effect.raise (NoEmbedding msg)) in
      (match uu___1 with
       | (bs1, c1) ->
           let result_typ = FStarC_Syntax_Util.comp_result c1 in
           let arity = FStarC_List.length bs1 in
           let uu___2 =
             let uu___3 =
               FStarC_Util.prefix_until
                 (fun uu___4 ->
                    match uu___4 with
                    | { FStarC_Syntax_Syntax.binder_bv = b;
                        FStarC_Syntax_Syntax.binder_qual = uu___5;
                        FStarC_Syntax_Syntax.binder_positivity = uu___6;
                        FStarC_Syntax_Syntax.binder_attrs = uu___7;_} ->
                        let uu___8 =
                          let uu___9 =
                            FStarC_Syntax_Subst.compress
                              b.FStarC_Syntax_Syntax.sort in
                          uu___9.FStarC_Syntax_Syntax.n in
                        (match uu___8 with
                         | FStarC_Syntax_Syntax.Tm_type uu___9 -> false
                         | uu___9 -> true)) bs1 in
             match uu___3 with
             | FStar_Pervasives_Native.None -> (bs1, [])
             | FStar_Pervasives_Native.Some (tvars, x, rest) ->
                 (tvars, (x :: rest)) in
           (match uu___2 with
            | (type_vars, bs2) ->
                let tvar_arity = FStarC_List.length type_vars in
                let non_tvar_arity = FStarC_List.length bs2 in
                let tvar_names =
                  FStarC_List.mapi
                    (fun i tv ->
                       let uu___3 =
                         FStarC_Class_Show.show
                           FStarC_Class_Show.showable_int i in
                       Prims.strcat "tv_" uu___3) type_vars in
                let tvar_context =
                  FStarC_List.map2
                    (fun b nm -> ((b.FStarC_Syntax_Syntax.binder_bv), nm))
                    type_vars tvar_names in
                let rec aux loc accum_embeddings bs3 =
                  match bs3 with
                  | [] ->
                      let arg_unembeddings = FStarC_List.rev accum_embeddings in
                      let res_embedding =
                        embedding_for tcenv [] loc tvar_context result_typ in
                      let fv_lid1 = fv.FStarC_Syntax_Syntax.fv_name in
                      let uu___3 = FStarC_Syntax_Util.is_pure_comp c1 in
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
                          FStarC_List.op_At arg_unembeddings uu___4 in
                        let fun_embedding =
                          mk
                            (FStarC_Extraction_ML_Syntax.MLE_App
                               (embed_fun_N, args)) in
                        let tabs = abstract_tvars tvar_names fun_embedding in
                        let cb_tabs =
                          let uu___4 = ml_lam "us" tabs in ml_lam "cb" uu___4 in
                        let uu___4 =
                          if loc = NBETerm
                          then cb_tabs
                          else ml_lam "_psc" cb_tabs in
                        (uu___4, arity, true)
                      else
                        (let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               FStarC_Syntax_Util.comp_effect_name c1 in
                             FStarC_TypeChecker_Env.norm_eff_name tcenv
                               uu___7 in
                           FStarC_Ident.lid_equals uu___6
                             FStarC_Parser_Const.effect_TAC_lid in
                         if uu___5
                         then
                           let h =
                             mk_tactic_interpretation loc non_tvar_arity in
                           let tac_fun =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   mk_from_tactic loc non_tvar_arity in
                                 let uu___9 =
                                   let uu___10 = lid_to_name fv_lid1 in
                                   [uu___10] in
                                 (uu___8, uu___9) in
                               FStarC_Extraction_ML_Syntax.MLE_App uu___7 in
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
                                         FStarC_Ident.string_of_lid fv_lid1 in
                                       Prims.strcat uu___11 " (plugin)" in
                                     FStarC_Extraction_ML_Syntax.MLC_String
                                       uu___10 in
                                   FStarC_Extraction_ML_Syntax.MLE_Const
                                     uu___9 in
                                 mk uu___8 in
                               [uu___7] in
                             FStarC_List.op_At uu___6
                               (FStarC_List.op_At [tac_fun]
                                  (FStarC_List.op_At arg_unembeddings
                                     [res_embedding; psc; ncb; us])) in
                           let tabs =
                             match tvar_names with
                             | [] ->
                                 let uu___6 =
                                   mk
                                     (FStarC_Extraction_ML_Syntax.MLE_App
                                        (h,
                                          (FStarC_List.op_At args [all_args]))) in
                                 ml_lam "args" uu___6
                             | uu___6 ->
                                 let uu___7 =
                                   mk
                                     (FStarC_Extraction_ML_Syntax.MLE_App
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
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term t1 in
                                Prims.strcat "Plugins not defined for type "
                                  uu___9 in
                              NoEmbedding uu___8 in
                            FStarC_Effect.raise uu___7))
                  | { FStarC_Syntax_Syntax.binder_bv = b;
                      FStarC_Syntax_Syntax.binder_qual = uu___3;
                      FStarC_Syntax_Syntax.binder_positivity = uu___4;
                      FStarC_Syntax_Syntax.binder_attrs = uu___5;_}::bs4 ->
                      let uu___6 =
                        let uu___7 =
                          embedding_for tcenv [] loc tvar_context
                            b.FStarC_Syntax_Syntax.sort in
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
                         FStarC_Ident.range_of_lid
                           fv.FStarC_Syntax_Syntax.fv_name in
                       let uu___6 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Syntax.showable_fv fv in
                       not_implemented_warning uu___5 uu___6 msg);
                      FStar_Pervasives_Native.None))))
let mk_unembed (tcenv : FStarC_TypeChecker_Env.env)
  (mutuals : FStarC_Ident.lid Prims.list)
  (record_fields :
    FStarC_Extraction_ML_Syntax.mlpath Prims.list
      FStar_Pervasives_Native.option)
  (ctors : FStarC_Syntax_Syntax.sigelt Prims.list) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  let e_branches = FStarC_Effect.mk_ref [] in
  let arg_v = fresh "tm" in
  FStarC_List.iter
    (fun ctor ->
       match ctor.FStarC_Syntax_Syntax.sigel with
       | FStarC_Syntax_Syntax.Sig_datacon
           { FStarC_Syntax_Syntax.lid1 = lid; FStarC_Syntax_Syntax.us1 = us;
             FStarC_Syntax_Syntax.t1 = t;
             FStarC_Syntax_Syntax.ty_lid = ty_lid;
             FStarC_Syntax_Syntax.num_ty_params = num_ty_params;
             FStarC_Syntax_Syntax.mutuals1 = uu___1;
             FStarC_Syntax_Syntax.injective_type_params1 = uu___2;
             FStarC_Syntax_Syntax.proj_disc_lids = uu___3;_}
           ->
           let fv = fresh "fv" in
           let uu___4 = FStarC_Syntax_Util.arrow_formals t in
           (match uu___4 with
            | (bs, c) ->
                let vs =
                  FStarC_List.map
                    (fun b ->
                       let uu___5 =
                         let uu___6 =
                           FStarC_Ident.string_of_id
                             (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname in
                         fresh uu___6 in
                       (uu___5,
                         ((b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)))
                    bs in
                let pat_s =
                  let uu___5 =
                    let uu___6 = FStarC_Ident.string_of_lid lid in
                    FStarC_Extraction_ML_Syntax.MLC_String uu___6 in
                  FStarC_Extraction_ML_Syntax.MLP_Const uu___5 in
                let pat_args =
                  let uu___5 =
                    FStarC_List.map
                      (fun uu___6 ->
                         match uu___6 with
                         | (v, uu___7) ->
                             FStarC_Extraction_ML_Syntax.MLP_Var v) vs in
                  pats_to_list_pat uu___5 in
                let pat_both =
                  FStarC_Extraction_ML_Syntax.MLP_Tuple [pat_s; pat_args] in
                let ret =
                  match record_fields with
                  | FStar_Pervasives_Native.Some fields ->
                      let uu___5 =
                        FStarC_List.map2
                          (fun uu___6 fld ->
                             match uu___6 with
                             | (v, uu___7) ->
                                 let uu___8 =
                                   mk (FStarC_Extraction_ML_Syntax.MLE_Var v) in
                                 ((FStar_Pervasives_Native.snd fld), uu___8))
                          vs fields in
                      ml_record lid uu___5
                  | FStar_Pervasives_Native.None ->
                      let uu___5 =
                        FStarC_List.map
                          (fun uu___6 ->
                             match uu___6 with
                             | (v, uu___7) ->
                                 mk (FStarC_Extraction_ML_Syntax.MLE_Var v))
                          vs in
                      ml_ctor lid uu___5 in
                let ret1 =
                  mk (FStarC_Extraction_ML_Syntax.MLE_App (ml_some, [ret])) in
                let body =
                  FStarC_List.fold_right
                    (fun uu___5 body1 ->
                       match uu___5 with
                       | (v, ty) ->
                           let body2 =
                             mk
                               (FStarC_Extraction_ML_Syntax.MLE_Fun
                                  ([mk_binder v
                                      FStarC_Extraction_ML_Syntax.MLTY_Top],
                                    body1)) in
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 =
                                         let uu___13 =
                                           embedding_for tcenv mutuals
                                             SyntaxTerm [] ty in
                                         let uu___14 =
                                           let uu___15 =
                                             mk
                                               (FStarC_Extraction_ML_Syntax.MLE_Var
                                                  v) in
                                           [uu___15] in
                                         uu___13 :: uu___14 in
                                       (unembed, uu___12) in
                                     FStarC_Extraction_ML_Syntax.MLE_App
                                       uu___11 in
                                   mk uu___10 in
                                 [uu___9; body2] in
                               (bind_opt, uu___8) in
                             FStarC_Extraction_ML_Syntax.MLE_App uu___7 in
                           mk uu___6) vs ret1 in
                let br = (pat_both, FStar_Pervasives_Native.None, body) in
                let uu___5 =
                  let uu___6 = FStarC_Effect.op_Bang e_branches in br ::
                    uu___6 in
                FStarC_Effect.op_Colon_Equals e_branches uu___5)
       | uu___1 -> failwith "impossible, filter above") ctors;
  (let nomatch =
     (FStarC_Extraction_ML_Syntax.MLP_Wild, FStar_Pervasives_Native.None,
       ml_none) in
   let branches =
     let uu___1 =
       let uu___2 = FStarC_Effect.op_Bang e_branches in nomatch :: uu___2 in
     FStarC_List.rev uu___1 in
   let sc = mk (FStarC_Extraction_ML_Syntax.MLE_Var arg_v) in
   let def = mk (FStarC_Extraction_ML_Syntax.MLE_Match (sc, branches)) in
   let lam =
     mk
       (FStarC_Extraction_ML_Syntax.MLE_Fun
          ([mk_binder arg_v FStarC_Extraction_ML_Syntax.MLTY_Top], def)) in
   lam)
let mk_embed (tcenv : FStarC_TypeChecker_Env.env)
  (mutuals : FStarC_Ident.lid Prims.list)
  (record_fields :
    FStarC_Extraction_ML_Syntax.mlpath Prims.list
      FStar_Pervasives_Native.option)
  (ctors : FStarC_Syntax_Syntax.sigelt Prims.list) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  let e_branches = FStarC_Effect.mk_ref [] in
  let arg_v = fresh "tm" in
  FStarC_List.iter
    (fun ctor ->
       match ctor.FStarC_Syntax_Syntax.sigel with
       | FStarC_Syntax_Syntax.Sig_datacon
           { FStarC_Syntax_Syntax.lid1 = lid; FStarC_Syntax_Syntax.us1 = us;
             FStarC_Syntax_Syntax.t1 = t;
             FStarC_Syntax_Syntax.ty_lid = ty_lid;
             FStarC_Syntax_Syntax.num_ty_params = num_ty_params;
             FStarC_Syntax_Syntax.mutuals1 = uu___1;
             FStarC_Syntax_Syntax.injective_type_params1 = uu___2;
             FStarC_Syntax_Syntax.proj_disc_lids = uu___3;_}
           ->
           let fv = fresh "fv" in
           let uu___4 = FStarC_Syntax_Util.arrow_formals t in
           (match uu___4 with
            | (bs, c) ->
                let vs =
                  FStarC_List.map
                    (fun b ->
                       let uu___5 =
                         let uu___6 =
                           FStarC_Ident.string_of_id
                             (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname in
                         fresh uu___6 in
                       (uu___5,
                         ((b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)))
                    bs in
                let pat =
                  match record_fields with
                  | FStar_Pervasives_Native.Some fields ->
                      let uu___5 =
                        let uu___6 =
                          FStarC_List.map2
                            (fun v fld ->
                               ((FStar_Pervasives_Native.snd fld),
                                 (FStarC_Extraction_ML_Syntax.MLP_Var
                                    (FStar_Pervasives_Native.fst v)))) vs
                            fields in
                        ([], uu___6) in
                      FStarC_Extraction_ML_Syntax.MLP_Record uu___5
                  | FStar_Pervasives_Native.None ->
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = FStarC_Ident.path_of_lid lid in
                          splitlast uu___7 in
                        let uu___7 =
                          FStarC_List.map
                            (fun v ->
                               FStarC_Extraction_ML_Syntax.MLP_Var
                                 (FStar_Pervasives_Native.fst v)) vs in
                        (uu___6, uu___7) in
                      FStarC_Extraction_ML_Syntax.MLP_CTor uu___5 in
                let fvar = s_tdataconstr in
                let lid_of_str1 = lid_of_str in
                let head =
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
                                      let uu___15 =
                                        FStarC_Ident.string_of_lid lid in
                                      FStarC_Extraction_ML_Syntax.MLC_String
                                        uu___15 in
                                    FStarC_Extraction_ML_Syntax.MLE_Const
                                      uu___14 in
                                  mk uu___13 in
                                [uu___12] in
                              (lid_of_str1, uu___11) in
                            FStarC_Extraction_ML_Syntax.MLE_App uu___10 in
                          mk uu___9 in
                        [uu___8] in
                      (fvar, uu___7) in
                    FStarC_Extraction_ML_Syntax.MLE_App uu___6 in
                  mk uu___5 in
                let mk_mk_app t1 ts =
                  let ts1 =
                    FStarC_List.map
                      (fun t2 ->
                         mk
                           (FStarC_Extraction_ML_Syntax.MLE_Tuple
                              [t2; ml_none])) ts in
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        let uu___8 = let uu___9 = as_ml_list ts1 in [uu___9] in
                        t1 :: uu___8 in
                      (mk_app, uu___7) in
                    FStarC_Extraction_ML_Syntax.MLE_App uu___6 in
                  mk uu___5 in
                let args =
                  FStarC_List.map
                    (fun uu___5 ->
                       match uu___5 with
                       | (v, ty) ->
                           let vt =
                             mk (FStarC_Extraction_ML_Syntax.MLE_Var v) in
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 =
                                   embedding_for tcenv mutuals SyntaxTerm []
                                     ty in
                                 [uu___9; vt] in
                               (embed, uu___8) in
                             FStarC_Extraction_ML_Syntax.MLE_App uu___7 in
                           mk uu___6) vs in
                let ret = mk_mk_app head args in
                let br = (pat, FStar_Pervasives_Native.None, ret) in
                let uu___5 =
                  let uu___6 = FStarC_Effect.op_Bang e_branches in br ::
                    uu___6 in
                FStarC_Effect.op_Colon_Equals e_branches uu___5)
       | uu___1 -> failwith "impossible, filter above") ctors;
  (let branches =
     let uu___1 = FStarC_Effect.op_Bang e_branches in FStarC_List.rev uu___1 in
   let sc = mk (FStarC_Extraction_ML_Syntax.MLE_Var arg_v) in
   let def = mk (FStarC_Extraction_ML_Syntax.MLE_Match (sc, branches)) in
   let lam =
     mk
       (FStarC_Extraction_ML_Syntax.MLE_Fun
          ([mk_binder arg_v FStarC_Extraction_ML_Syntax.MLTY_Top], def)) in
   lam)
let __do_handle_plugin (g : FStarC_Extraction_ML_UEnv.uenv)
  (arity_opt : Prims.int FStar_Pervasives_Native.option)
  (se : FStarC_Syntax_Syntax.sigelt) :
  FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list=
  let r = se.FStarC_Syntax_Syntax.sigrng in
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_let
      { FStarC_Syntax_Syntax.lbs1 = lbs;
        FStarC_Syntax_Syntax.lids1 = uu___;_}
      ->
      let mk_registration lb =
        let fv =
          FStar_Pervasives.__proj__Inr__item__v
            lb.FStarC_Syntax_Syntax.lbname in
        let fv_lid = fv.FStarC_Syntax_Syntax.fv_name in
        let fv_t = lb.FStarC_Syntax_Syntax.lbtyp in
        let ml_name_str =
          let uu___1 =
            let uu___2 = FStarC_Ident.string_of_lid fv_lid in
            FStarC_Extraction_ML_Syntax.MLC_String uu___2 in
          FStarC_Extraction_ML_Syntax.MLE_Const uu___1 in
        let uu___1 =
          interpret_plugin_as_term_fun g fv fv_t arity_opt ml_name_str in
        match uu___1 with
        | FStar_Pervasives_Native.Some (interp, nbe_interp, arity, plugin) ->
            let uu___2 =
              if plugin
              then
                ((["Fstarcompiler.FStarC_Tactics_Native"], "register_plugin"),
                  [interp; nbe_interp])
              else
                ((["Fstarcompiler.FStarC_Tactics_Native"], "register_tactic"),
                  [interp]) in
            (match uu___2 with
             | (register, args) ->
                 let h =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.MLTY_Top
                     (FStarC_Extraction_ML_Syntax.MLE_Name register) in
                 let arity1 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Class_Show.show
                           FStarC_Class_Show.showable_int arity in
                       (uu___5, FStar_Pervasives_Native.None) in
                     FStarC_Extraction_ML_Syntax.MLC_Int uu___4 in
                   FStarC_Extraction_ML_Syntax.MLE_Const uu___3 in
                 let app =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = mk ml_name_str in
                           let uu___8 = let uu___9 = mk arity1 in [uu___9] in
                           uu___7 :: uu___8 in
                         FStarC_List.op_At uu___6 args in
                       (h, uu___5) in
                     FStarC_Extraction_ML_Syntax.MLE_App uu___4 in
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.MLTY_Top uu___3 in
                 let uu___3 =
                   FStarC_Extraction_ML_Syntax.mk_mlmodule1
                     (FStarC_Extraction_ML_Syntax.MLM_Top app) in
                 [uu___3])
        | FStar_Pervasives_Native.None -> [] in
      FStarC_List.collect mk_registration (FStar_Pervasives_Native.snd lbs)
  | FStarC_Syntax_Syntax.Sig_bundle
      { FStarC_Syntax_Syntax.ses = ses; FStarC_Syntax_Syntax.lids = uu___;_}
      ->
      let mutual_sigelts =
        FStarC_List.filter
          (fun se1 ->
             match se1.FStarC_Syntax_Syntax.sigel with
             | FStarC_Syntax_Syntax.Sig_inductive_typ uu___1 -> true
             | uu___1 -> false) ses in
      let mutual_lids =
        FStarC_List.map
          (fun se1 ->
             match se1.FStarC_Syntax_Syntax.sigel with
             | FStarC_Syntax_Syntax.Sig_inductive_typ
                 { FStarC_Syntax_Syntax.lid = lid;
                   FStarC_Syntax_Syntax.us = uu___1;
                   FStarC_Syntax_Syntax.params = uu___2;
                   FStarC_Syntax_Syntax.num_uniform_params = uu___3;
                   FStarC_Syntax_Syntax.t = uu___4;
                   FStarC_Syntax_Syntax.mutuals = uu___5;
                   FStarC_Syntax_Syntax.ds = uu___6;
                   FStarC_Syntax_Syntax.injective_type_params = uu___7;_}
                 -> lid) mutual_sigelts in
      let proc_one typ_sigelt =
        let uu___1 = typ_sigelt.FStarC_Syntax_Syntax.sigel in
        match uu___1 with
        | FStarC_Syntax_Syntax.Sig_inductive_typ
            { FStarC_Syntax_Syntax.lid = tlid;
              FStarC_Syntax_Syntax.us = uu___2;
              FStarC_Syntax_Syntax.params = ps;
              FStarC_Syntax_Syntax.num_uniform_params = uu___3;
              FStarC_Syntax_Syntax.t = uu___4;
              FStarC_Syntax_Syntax.mutuals = uu___5;
              FStarC_Syntax_Syntax.ds = uu___6;
              FStarC_Syntax_Syntax.injective_type_params = uu___7;_}
            ->
            (if (FStarC_List.length ps) > Prims.int_zero
             then FStarC_Effect.raise (Unsupported "parameters on inductive")
             else ();
             (let ns = FStarC_Ident.ns_of_lid tlid in
              let name =
                let uu___9 =
                  let uu___10 = FStarC_Ident.ids_of_lid tlid in
                  FStarC_List.last uu___10 in
                FStarC_Ident.string_of_id uu___9 in
              let ctors =
                FStarC_List.filter
                  (fun se1 ->
                     match se1.FStarC_Syntax_Syntax.sigel with
                     | FStarC_Syntax_Syntax.Sig_datacon
                         { FStarC_Syntax_Syntax.lid1 = uu___9;
                           FStarC_Syntax_Syntax.us1 = uu___10;
                           FStarC_Syntax_Syntax.t1 = uu___11;
                           FStarC_Syntax_Syntax.ty_lid = ty_lid;
                           FStarC_Syntax_Syntax.num_ty_params = uu___12;
                           FStarC_Syntax_Syntax.mutuals1 = uu___13;
                           FStarC_Syntax_Syntax.injective_type_params1 =
                             uu___14;
                           FStarC_Syntax_Syntax.proj_disc_lids = uu___15;_}
                         -> FStarC_Ident.lid_equals ty_lid tlid
                     | uu___9 -> false) ses in
              let ml_name1 =
                let uu___9 =
                  let uu___10 =
                    let uu___11 = FStarC_Ident.string_of_lid tlid in
                    FStarC_Extraction_ML_Syntax.MLC_String uu___11 in
                  FStarC_Extraction_ML_Syntax.MLE_Const uu___10 in
                mk uu___9 in
              let record_fields =
                let uu___9 =
                  FStarC_List.find
                    (fun uu___10 ->
                       match uu___10 with
                       | FStarC_Syntax_Syntax.RecordType uu___11 -> true
                       | uu___11 -> false)
                    typ_sigelt.FStarC_Syntax_Syntax.sigquals in
                match uu___9 with
                | FStar_Pervasives_Native.Some
                    (FStarC_Syntax_Syntax.RecordType (uu___10, b)) ->
                    let uu___11 =
                      FStarC_List.map
                        (fun f ->
                           FStarC_Extraction_ML_UEnv.lookup_record_field_name
                             g (tlid, f)) b in
                    FStar_Pervasives_Native.Some uu___11
                | uu___10 -> FStar_Pervasives_Native.None in
              let tcenv = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
              let ml_unembed =
                mk_unembed tcenv mutual_lids record_fields ctors in
              let ml_embed = mk_embed tcenv mutual_lids record_fields ctors in
              let def =
                let uu___9 =
                  let uu___10 =
                    let uu___11 =
                      mk
                        (FStarC_Extraction_ML_Syntax.MLE_Name
                           (["Fstarcompiler.FStarC";
                            "Syntax";
                            "Embeddings";
                            "Base"], "mk_extracted_embedding")) in
                    (uu___11, [ml_name1; ml_unembed; ml_embed]) in
                  FStarC_Extraction_ML_Syntax.MLE_App uu___10 in
                mk uu___9 in
              let def1 =
                mk
                  (FStarC_Extraction_ML_Syntax.MLE_Fun
                     ([mk_binder "_" FStarC_Extraction_ML_Syntax.MLTY_Erased],
                       def)) in
              let lb =
                {
                  FStarC_Extraction_ML_Syntax.mllb_name =
                    (Prims.strcat "__knot_e_" name);
                  FStarC_Extraction_ML_Syntax.mllb_tysc =
                    FStar_Pervasives_Native.None;
                  FStarC_Extraction_ML_Syntax.mllb_add_unit = false;
                  FStarC_Extraction_ML_Syntax.mllb_def = def1;
                  FStarC_Extraction_ML_Syntax.mllb_attrs = [];
                  FStarC_Extraction_ML_Syntax.mllb_meta = [];
                  FStarC_Extraction_ML_Syntax.print_typ = false
                } in
              (let uu___10 =
                 let uu___11 =
                   let uu___12 =
                     FStarC_Ident.mk_ident
                       ((Prims.strcat "e_" name),
                         FStarC_Range_Type.dummyRange) in
                   FStarC_Ident.lid_of_ns_and_id ns uu___12 in
                 {
                   arity = Prims.int_zero;
                   syn_emb = uu___11;
                   nbe_emb = FStar_Pervasives_Native.None
                 } in
               register_embedding tlid uu___10);
              [lb])) in
      let lbs = FStarC_List.concatMap proc_one mutual_sigelts in
      let unthunking =
        FStarC_List.concatMap
          (fun se1 ->
             let tlid =
               match se1.FStarC_Syntax_Syntax.sigel with
               | FStarC_Syntax_Syntax.Sig_inductive_typ
                   { FStarC_Syntax_Syntax.lid = tlid1;
                     FStarC_Syntax_Syntax.us = uu___1;
                     FStarC_Syntax_Syntax.params = uu___2;
                     FStarC_Syntax_Syntax.num_uniform_params = uu___3;
                     FStarC_Syntax_Syntax.t = uu___4;
                     FStarC_Syntax_Syntax.mutuals = uu___5;
                     FStarC_Syntax_Syntax.ds = uu___6;
                     FStarC_Syntax_Syntax.injective_type_params = uu___7;_}
                   -> tlid1 in
             let name =
               let uu___1 =
                 let uu___2 = FStarC_Ident.ids_of_lid tlid in
                 FStarC_List.last uu___2 in
               FStarC_Ident.string_of_id uu___1 in
             let app =
               let head =
                 mk
                   (FStarC_Extraction_ML_Syntax.MLE_Var
                      (Prims.strcat "__knot_e_" name)) in
               mk
                 (FStarC_Extraction_ML_Syntax.MLE_App
                    (head, [FStarC_Extraction_ML_Syntax.ml_unit])) in
             let lb =
               {
                 FStarC_Extraction_ML_Syntax.mllb_name =
                   (Prims.strcat "e_" name);
                 FStarC_Extraction_ML_Syntax.mllb_tysc =
                   FStar_Pervasives_Native.None;
                 FStarC_Extraction_ML_Syntax.mllb_add_unit = false;
                 FStarC_Extraction_ML_Syntax.mllb_def = app;
                 FStarC_Extraction_ML_Syntax.mllb_attrs = [];
                 FStarC_Extraction_ML_Syntax.mllb_meta = [];
                 FStarC_Extraction_ML_Syntax.print_typ = false
               } in
             let uu___1 =
               FStarC_Extraction_ML_Syntax.mk_mlmodule1
                 (FStarC_Extraction_ML_Syntax.MLM_Let
                    (FStarC_Extraction_ML_Syntax.NonRec, [lb])) in
             [uu___1]) mutual_sigelts in
      let uu___1 =
        let uu___2 =
          FStarC_Extraction_ML_Syntax.mk_mlmodule1
            (FStarC_Extraction_ML_Syntax.MLM_Let
               (FStarC_Extraction_ML_Syntax.Rec, lbs)) in
        [uu___2] in
      FStarC_List.op_At uu___1 unthunking
  | uu___ -> []
let do_handle_plugin (g : FStarC_Extraction_ML_UEnv.uenv)
  (arity_opt : Prims.int FStar_Pervasives_Native.option)
  (se : FStarC_Syntax_Syntax.sigelt) :
  FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list=
  try
    (fun uu___ -> match () with | () -> __do_handle_plugin g arity_opt se) ()
  with
  | Unsupported msg ->
      ((let uu___2 =
          let uu___3 = FStarC_Syntax_Print.sigelt_to_string_short se in
          FStarC_Format.fmt2
            "Could not generate a plugin for %s, reason = %s" uu___3 msg in
        FStarC_Errors.log_issue FStarC_Syntax_Syntax.has_range_sigelt se
          FStarC_Errors_Codes.Warning_PluginNotImplemented ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic uu___2));
       [])
  | NoEmbedding msg ->
      ((let uu___2 = FStarC_Syntax_Print.sigelt_to_string_short se in
        not_implemented_warning se.FStarC_Syntax_Syntax.sigrng uu___2 msg);
       [])
let maybe_register_plugin (g : FStarC_Extraction_ML_UEnv.uenv)
  (se : FStarC_Syntax_Syntax.sigelt) :
  FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list=
  let plugin_with_arity attrs =
    FStarC_Util.find_map attrs
      (fun t ->
         let uu___ = FStarC_Syntax_Util.head_and_args t in
         match uu___ with
         | (head, args) ->
             let uu___1 =
               let uu___2 =
                 FStarC_Syntax_Util.is_fvar FStarC_Parser_Const.plugin_attr
                   head in
               Prims.op_Negation uu___2 in
             if uu___1
             then FStar_Pervasives_Native.None
             else
               (match args with
                | (a, uu___3)::[] ->
                    let nopt =
                      FStarC_Syntax_Embeddings_Base.unembed
                        FStarC_Syntax_Embeddings.e_int a
                        FStarC_Syntax_Embeddings_Base.id_norm_cb in
                    FStar_Pervasives_Native.Some nopt
                | uu___3 ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None)) in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Options.codegen () in
      FStarC_List.mem uu___2
        [FStar_Pervasives_Native.Some FStarC_Options.Plugin;
        FStar_Pervasives_Native.Some FStarC_Options.PluginNoLib] in
    Prims.op_Negation uu___1 in
  if uu___
  then []
  else
    (let uu___2 = plugin_with_arity se.FStarC_Syntax_Syntax.sigattrs in
     match uu___2 with
     | FStar_Pervasives_Native.None -> []
     | FStar_Pervasives_Native.Some uu___3 when
         FStarC_List.existsb
           (fun uu___4 ->
              match uu___4 with
              | FStarC_Syntax_Syntax.Projector uu___5 -> true
              | FStarC_Syntax_Syntax.Discriminator uu___5 -> true
              | uu___5 -> false) se.FStarC_Syntax_Syntax.sigquals
         -> []
     | FStar_Pervasives_Native.Some arity_opt ->
         do_handle_plugin g arity_opt se)

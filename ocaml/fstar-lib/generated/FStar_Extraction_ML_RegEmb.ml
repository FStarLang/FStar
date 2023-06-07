open Prims
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
let (embedding_for :
  FStar_Syntax_Syntax.typ -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun a -> ml_magic
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
let (mk_unembed :
  Prims.string Prims.list FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Extraction_ML_Syntax.mlexpr)
  =
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
                    FStar_Syntax_Syntax.us1 = us; FStar_Syntax_Syntax.t1 = t;
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
                                          (fld,
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
                                                    embedding_for ty in
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
         (FStar_Extraction_ML_Syntax.MLP_Wild, FStar_Pervasives_Native.None,
           ml_none) in
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
  Prims.string Prims.list FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Extraction_ML_Syntax.mlexpr)
  =
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
                    FStar_Syntax_Syntax.us1 = us; FStar_Syntax_Syntax.t1 = t;
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
                                        (fld,
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
                                               FStar_Ident.string_of_lid lid in
                                             FStar_Extraction_ML_Syntax.MLC_String
                                               uu___12 in
                                           FStar_Extraction_ML_Syntax.MLE_Const
                                             uu___11 in
                                         mk uu___10 in
                                       [uu___9] in
                                     (lid_of_str, uu___8) in
                                   FStar_Extraction_ML_Syntax.MLE_App uu___7 in
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
                                           let uu___7 = embedding_for ty in
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
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NoTacticEmbedding uu___ -> true | uu___ -> false
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | NoTacticEmbedding uu___ -> uu___
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
              "Plugin %s can not run natively because %s (use --warn_error -%s to carry on)."
              t msg uu___2 in
          (FStar_Errors_Codes.Warning_PluginNotImplemented, uu___1) in
        FStar_Errors.log_issue r uu___
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee ->
    match projectee with | Syntax_term -> true | uu___ -> false
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee -> match projectee with | Refl_emb -> true | uu___ -> false
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee -> match projectee with | NBE_t -> true | uu___ -> false
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee ->
    match projectee with | NBERefl_emb -> true | uu___ -> false
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
let (known_embeddings :
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
                  let uu___13 = syn_emb_lid "e_list" in
                  let uu___14 =
                    let uu___15 = nbe_emb_lid "e_list" in
                    FStar_Pervasives_Native.Some uu___15 in
                  {
                    arity = Prims.int_one;
                    syn_emb = uu___13;
                    nbe_emb = uu___14
                  } in
                (FStar_Parser_Const.list_lid, uu___12) in
              let uu___12 =
                let uu___13 =
                  let uu___14 =
                    let uu___15 = syn_emb_lid "e_option" in
                    let uu___16 =
                      let uu___17 = nbe_emb_lid "e_option" in
                      FStar_Pervasives_Native.Some uu___17 in
                    {
                      arity = Prims.int_one;
                      syn_emb = uu___15;
                      nbe_emb = uu___16
                    } in
                  (FStar_Parser_Const.option_lid, uu___14) in
                let uu___14 =
                  let uu___15 =
                    let uu___16 =
                      let uu___17 = syn_emb_lid "e_sealed" in
                      let uu___18 =
                        let uu___19 = nbe_emb_lid "e_sealed" in
                        FStar_Pervasives_Native.Some uu___19 in
                      {
                        arity = Prims.int_one;
                        syn_emb = uu___17;
                        nbe_emb = uu___18
                      } in
                    (FStar_Parser_Const.sealed_lid, uu___16) in
                  let uu___16 =
                    let uu___17 =
                      let uu___18 =
                        FStar_Parser_Const.mk_tuple_lid (Prims.of_int (2))
                          FStar_Compiler_Range_Type.dummyRange in
                      let uu___19 =
                        let uu___20 = syn_emb_lid "e_tuple2" in
                        let uu___21 =
                          let uu___22 = nbe_emb_lid "e_tuple2" in
                          FStar_Pervasives_Native.Some uu___22 in
                        {
                          arity = Prims.int_one;
                          syn_emb = uu___20;
                          nbe_emb = uu___21
                        } in
                      (uu___18, uu___19) in
                    let uu___18 =
                      let uu___19 =
                        let uu___20 =
                          FStar_Reflection_Constants.fstar_refl_types_lid
                            "term" in
                        let uu___21 =
                          let uu___22 = refl_emb_lid "e_term" in
                          let uu___23 =
                            let uu___24 = nbe_refl_emb_lid "e_term" in
                            FStar_Pervasives_Native.Some uu___24 in
                          {
                            arity = Prims.int_zero;
                            syn_emb = uu___22;
                            nbe_emb = uu___23
                          } in
                        (uu___20, uu___21) in
                      let uu___20 =
                        let uu___21 =
                          let uu___22 =
                            FStar_Reflection_Constants.fstar_refl_types_lid
                              "fv" in
                          let uu___23 =
                            let uu___24 = refl_emb_lid "e_fv" in
                            let uu___25 =
                              let uu___26 = nbe_refl_emb_lid "e_fv" in
                              FStar_Pervasives_Native.Some uu___26 in
                            {
                              arity = Prims.int_zero;
                              syn_emb = uu___24;
                              nbe_emb = uu___25
                            } in
                          (uu___22, uu___23) in
                        let uu___22 =
                          let uu___23 =
                            let uu___24 =
                              FStar_Reflection_Constants.fstar_refl_types_lid
                                "sigelt" in
                            let uu___25 =
                              let uu___26 = refl_emb_lid "e_sigelt" in
                              let uu___27 =
                                let uu___28 = nbe_refl_emb_lid "e_sigelt" in
                                FStar_Pervasives_Native.Some uu___28 in
                              {
                                arity = Prims.int_zero;
                                syn_emb = uu___26;
                                nbe_emb = uu___27
                              } in
                            (uu___24, uu___25) in
                          let uu___24 =
                            let uu___25 =
                              let uu___26 =
                                FStar_Reflection_Constants.fstar_refl_types_lid
                                  "env" in
                              let uu___27 =
                                let uu___28 = refl_emb_lid "e_env" in
                                let uu___29 =
                                  let uu___30 = nbe_refl_emb_lid "e_env" in
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
                                    "binders" in
                                let uu___29 =
                                  let uu___30 = refl_emb_lid "e_binders" in
                                  let uu___31 =
                                    let uu___32 =
                                      nbe_refl_emb_lid "e_binders" in
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
                                  [uu___31] in
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
        let uu___1 = FStar_Compiler_Effect.op_Bang known_embeddings in 
          (l, d) :: uu___1 in
      FStar_Compiler_Effect.op_Colon_Equals known_embeddings uu___
let (find_embedding' :
  FStar_Ident.lident -> embedding_data FStar_Pervasives_Native.option) =
  fun l ->
    let uu___ =
      let uu___1 = FStar_Compiler_Effect.op_Bang known_embeddings in
      FStar_Compiler_List.find
        (fun uu___2 ->
           match uu___2 with | (l', uu___3) -> FStar_Ident.lid_equals l l')
        uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some (uu___1, data) ->
        FStar_Pervasives_Native.Some data
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (find_embedding : FStar_Ident.lident -> embedding_data) =
  fun l ->
    let uu___ = find_embedding' l in
    match uu___ with
    | FStar_Pervasives_Native.Some data -> data
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Ident.string_of_lid l in
            Prims.op_Hat "Embedding not defined for type " uu___3 in
          NoTacticEmbedding uu___2 in
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
            let w =
              FStar_Extraction_ML_Syntax.with_ty
                FStar_Extraction_ML_Syntax.MLTY_Top in
            let as_name mlp =
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
            let str_to_name s = as_name ([], s) in
            let fstar_tc_nbe_prefix s =
              as_name (["FStar_TypeChecker_NBETerm"], s) in
            let fstar_syn_emb_prefix s =
              as_name (["FStar_Syntax_Embeddings"], s) in
            let fstar_refl_emb_prefix s =
              as_name (["FStar_Reflection_Embeddings"], s) in
            let fstar_refl_nbeemb_prefix s =
              as_name (["FStar_Reflection_NBEEmbeddings"], s) in
            let fv_lid_embedded =
              let uu___ =
                let uu___1 =
                  let uu___2 = as_name (["FStar_Ident"], "lid_of_str") in
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
            let emb_prefix uu___ =
              match uu___ with
              | Syntax_term -> fstar_syn_emb_prefix
              | Refl_emb -> fstar_refl_emb_prefix
              | NBE_t -> fstar_tc_nbe_prefix
              | NBERefl_emb -> fstar_refl_nbeemb_prefix in
            let mk_tactic_interpretation l arity =
              if arity > FStar_Tactics_InterpFuns.max_tac_arity
              then
                FStar_Compiler_Effect.raise
                  (NoTacticEmbedding
                     "tactic plugins can only take up to 20 arguments")
              else
                (let idroot =
                   match l with
                   | Syntax_term -> "mk_tactic_interpretation_"
                   | uu___1 -> "mk_nbe_tactic_interpretation_" in
                 as_name
                   (["FStar_Tactics_InterpFuns"],
                     (Prims.op_Hat idroot (Prims.string_of_int arity)))) in
            let mk_from_tactic l arity =
              let idroot =
                match l with
                | Syntax_term -> "from_tactic_"
                | uu___ -> "from_nbe_tactic_" in
              as_name
                (["FStar_Tactics_Native"],
                  (Prims.op_Hat idroot (Prims.string_of_int arity))) in
            let mk_arrow_as_prim_step l arity =
              emb_prefix l
                (Prims.op_Hat "arrow_as_prim_step_"
                   (Prims.string_of_int arity)) in
            let mk_any_embedding l s =
              let uu___ =
                let uu___1 =
                  let uu___2 = emb_prefix l "mk_any_emb" in
                  let uu___3 = let uu___4 = str_to_name s in [uu___4] in
                  (uu___2, uu___3) in
                FStar_Extraction_ML_Syntax.MLE_App uu___1 in
              FStar_Compiler_Effect.op_Less_Bar w uu___ in
            let mk_lam nm e =
              FStar_Compiler_Effect.op_Less_Bar w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e)) in
            let emb_arrow l e1 e2 =
              let uu___ =
                let uu___1 =
                  let uu___2 = emb_prefix l "e_arrow" in (uu___2, [e1; e2]) in
                FStar_Extraction_ML_Syntax.MLE_App uu___1 in
              FStar_Compiler_Effect.op_Less_Bar w uu___ in
            let find_env_entry bv uu___ =
              match uu___ with
              | (bv', uu___1) -> FStar_Syntax_Syntax.bv_eq bv bv' in
            let rec mk_embedding l env1 t2 =
              let t3 =
                FStar_TypeChecker_Normalize.unfold_whnf'
                  [FStar_TypeChecker_Env.ForExtraction] tcenv t2 in
              let uu___ =
                let uu___1 = FStar_Syntax_Subst.compress t3 in
                uu___1.FStar_Syntax_Syntax.n in
              match uu___ with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Compiler_Util.for_some (find_env_entry bv) env1 ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        FStar_Compiler_Util.find_opt (find_env_entry bv) env1 in
                      FStar_Compiler_Util.must uu___3 in
                    FStar_Pervasives_Native.snd uu___2 in
                  FStar_Compiler_Effect.op_Less_Bar (mk_any_embedding l)
                    uu___1
              | FStar_Syntax_Syntax.Tm_refine
                  { FStar_Syntax_Syntax.b = x;
                    FStar_Syntax_Syntax.phi = uu___1;_}
                  -> mk_embedding l env1 x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed
                  { FStar_Syntax_Syntax.tm = t4;
                    FStar_Syntax_Syntax.asc = uu___1;
                    FStar_Syntax_Syntax.eff_opt = uu___2;_}
                  -> mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_arrow
                  { FStar_Syntax_Syntax.bs1 = b::[];
                    FStar_Syntax_Syntax.comp = c;_}
                  when FStar_Syntax_Util.is_pure_comp c ->
                  let uu___1 = FStar_Syntax_Subst.open_comp [b] c in
                  (match uu___1 with
                   | (bs, c1) ->
                       let t0 =
                         let uu___2 =
                           let uu___3 = FStar_Compiler_List.hd bs in
                           uu___3.FStar_Syntax_Syntax.binder_bv in
                         uu___2.FStar_Syntax_Syntax.sort in
                       let t11 = FStar_Syntax_Util.comp_result c1 in
                       let uu___2 = mk_embedding l env1 t0 in
                       let uu___3 = mk_embedding l env1 t11 in
                       emb_arrow l uu___2 uu___3)
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
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = FStar_Syntax_Syntax.mk_Total tail in
                        {
                          FStar_Syntax_Syntax.bs1 = [b];
                          FStar_Syntax_Syntax.comp = uu___3
                        } in
                      FStar_Syntax_Syntax.Tm_arrow uu___2 in
                    FStar_Syntax_Syntax.mk uu___1 t3.FStar_Syntax_Syntax.pos in
                  mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_fvar uu___1 ->
                  let uu___2 = FStar_Syntax_Util.head_and_args t3 in
                  (match uu___2 with
                   | (head, args) ->
                       let n_args = FStar_Compiler_List.length args in
                       let uu___3 =
                         let uu___4 = FStar_Syntax_Util.un_uinst head in
                         uu___4.FStar_Syntax_Syntax.n in
                       (match uu___3 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            let uu___4 =
                              find_embedding'
                                (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Pervasives_Native.uu___is_Some uu___4 ->
                            let arg_embeddings =
                              FStar_Compiler_Effect.op_Bar_Greater args
                                (FStar_Compiler_List.map
                                   (fun uu___4 ->
                                      match uu___4 with
                                      | (t4, uu___5) ->
                                          mk_embedding l env1 t4)) in
                            let emb_data =
                              find_embedding
                                (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let t_arity = emb_data.arity in
                            let head1 =
                              match l with
                              | Syntax_term -> ml_name emb_data.syn_emb
                              | NBE_t ->
                                  (match emb_data.nbe_emb with
                                   | FStar_Pervasives_Native.Some lid ->
                                       ml_name lid
                                   | FStar_Pervasives_Native.None -> ml_magic)
                              | uu___4 -> failwith "blah" in
                            if t_arity = Prims.int_zero
                            then head1
                            else
                              FStar_Compiler_Effect.op_Less_Bar w
                                (FStar_Extraction_ML_Syntax.MLE_App
                                   (head1, arg_embeddings))
                        | uu___4 ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Print.term_to_string t3 in
                                Prims.op_Hat
                                  "Embedding not defined for type " uu___7 in
                              NoTacticEmbedding uu___6 in
                            FStar_Compiler_Effect.raise uu___5))
              | FStar_Syntax_Syntax.Tm_uinst uu___1 ->
                  let uu___2 = FStar_Syntax_Util.head_and_args t3 in
                  (match uu___2 with
                   | (head, args) ->
                       let n_args = FStar_Compiler_List.length args in
                       let uu___3 =
                         let uu___4 = FStar_Syntax_Util.un_uinst head in
                         uu___4.FStar_Syntax_Syntax.n in
                       (match uu___3 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            let uu___4 =
                              find_embedding'
                                (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Pervasives_Native.uu___is_Some uu___4 ->
                            let arg_embeddings =
                              FStar_Compiler_Effect.op_Bar_Greater args
                                (FStar_Compiler_List.map
                                   (fun uu___4 ->
                                      match uu___4 with
                                      | (t4, uu___5) ->
                                          mk_embedding l env1 t4)) in
                            let emb_data =
                              find_embedding
                                (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let t_arity = emb_data.arity in
                            let head1 =
                              match l with
                              | Syntax_term -> ml_name emb_data.syn_emb
                              | NBE_t ->
                                  (match emb_data.nbe_emb with
                                   | FStar_Pervasives_Native.Some lid ->
                                       ml_name lid
                                   | FStar_Pervasives_Native.None -> ml_magic)
                              | uu___4 -> failwith "blah" in
                            if t_arity = Prims.int_zero
                            then head1
                            else
                              FStar_Compiler_Effect.op_Less_Bar w
                                (FStar_Extraction_ML_Syntax.MLE_App
                                   (head1, arg_embeddings))
                        | uu___4 ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Print.term_to_string t3 in
                                Prims.op_Hat
                                  "Embedding not defined for type " uu___7 in
                              NoTacticEmbedding uu___6 in
                            FStar_Compiler_Effect.raise uu___5))
              | FStar_Syntax_Syntax.Tm_app uu___1 ->
                  let uu___2 = FStar_Syntax_Util.head_and_args t3 in
                  (match uu___2 with
                   | (head, args) ->
                       let n_args = FStar_Compiler_List.length args in
                       let uu___3 =
                         let uu___4 = FStar_Syntax_Util.un_uinst head in
                         uu___4.FStar_Syntax_Syntax.n in
                       (match uu___3 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            let uu___4 =
                              find_embedding'
                                (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Pervasives_Native.uu___is_Some uu___4 ->
                            let arg_embeddings =
                              FStar_Compiler_Effect.op_Bar_Greater args
                                (FStar_Compiler_List.map
                                   (fun uu___4 ->
                                      match uu___4 with
                                      | (t4, uu___5) ->
                                          mk_embedding l env1 t4)) in
                            let emb_data =
                              find_embedding
                                (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let t_arity = emb_data.arity in
                            let head1 =
                              match l with
                              | Syntax_term -> ml_name emb_data.syn_emb
                              | NBE_t ->
                                  (match emb_data.nbe_emb with
                                   | FStar_Pervasives_Native.Some lid ->
                                       ml_name lid
                                   | FStar_Pervasives_Native.None -> ml_magic)
                              | uu___4 -> failwith "blah" in
                            if t_arity = Prims.int_zero
                            then head1
                            else
                              FStar_Compiler_Effect.op_Less_Bar w
                                (FStar_Extraction_ML_Syntax.MLE_App
                                   (head1, arg_embeddings))
                        | uu___4 ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Print.term_to_string t3 in
                                Prims.op_Hat
                                  "Embedding not defined for type " uu___7 in
                              NoTacticEmbedding uu___6 in
                            FStar_Compiler_Effect.raise uu___5))
              | uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Print.term_to_string t3 in
                      Prims.op_Hat "Embedding not defined for type " uu___4 in
                    NoTacticEmbedding uu___3 in
                  FStar_Compiler_Effect.raise uu___2 in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          as_name (["FStar_Syntax_Embeddings"], "debug_wrap") in
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
                                FStar_Compiler_Effect.op_Less_Bar w uu___8 in
                              mk_lam "_" uu___7 in
                            [uu___6] in
                          uu___4 :: uu___5 in
                        (uu___2, uu___3) in
                      FStar_Extraction_ML_Syntax.MLE_App uu___1 in
                    FStar_Compiler_Effect.op_Less_Bar w uu___ in
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
                            let uu___5 = as_name ([], "args") in [uu___5] in
                          (body, uu___4) in
                        FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                      FStar_Compiler_Effect.op_Less_Bar w uu___2 in
                    (pattern, FStar_Pervasives_Native.None, uu___1) in
                  let default_branch =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = str_to_name "failwith" in
                          let uu___5 =
                            let uu___6 =
                              FStar_Compiler_Effect.op_Less_Bar w
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_String
                                      "arity mismatch")) in
                            [uu___6] in
                          (uu___4, uu___5) in
                        FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                      FStar_Compiler_Effect.op_Less_Bar w uu___2 in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu___1) in
                  let body1 =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = as_name ([], "args") in
                        (uu___3, [branch; default_branch]) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu___2 in
                    FStar_Compiler_Effect.op_Less_Bar w uu___1 in
                  let body2 =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          as_name (["FStar_Syntax_Embeddings"], "debug_wrap") in
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
                    FStar_Compiler_Effect.op_Less_Bar w uu___1 in
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
                           FStar_Compiler_Effect.raise
                             (NoTacticEmbedding msg)) in
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
                                  mk_embedding loc tvar_context result_typ in
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
                                    FStar_Compiler_Effect.op_Less_Bar w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (embed_fun_N, args)) in
                                  let tabs =
                                    abstract_tvars tvar_names fun_embedding in
                                  let cb_tabs = mk_lam "cb" tabs in
                                  let uu___4 =
                                    if loc = NBE_t
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
                                       FStar_Compiler_Effect.op_Less_Bar w
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
                                               w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_Compiler_List.op_At
                                                       args [all_args]))) in
                                           mk_lam "args" uu___6
                                       | uu___6 ->
                                           let uu___7 =
                                             FStar_Compiler_Effect.op_Less_Bar
                                               w
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
                                        NoTacticEmbedding uu___8 in
                                      FStar_Compiler_Effect.raise uu___7))
                            | { FStar_Syntax_Syntax.binder_bv = b;
                                FStar_Syntax_Syntax.binder_qual = uu___3;
                                FStar_Syntax_Syntax.binder_positivity =
                                  uu___4;
                                FStar_Syntax_Syntax.binder_attrs = uu___5;_}::bs4
                                ->
                                let uu___6 =
                                  let uu___7 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort in
                                  uu___7 :: accum_embeddings in
                                aux loc uu___6 bs4 in
                          (try
                             (fun uu___3 ->
                                match () with
                                | () ->
                                    let uu___4 = aux Syntax_term [] bs2 in
                                    (match uu___4 with
                                     | (w1, a, b) ->
                                         let uu___5 = aux NBE_t [] bs2 in
                                         (match uu___5 with
                                          | (w', uu___6, uu___7) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu___5 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 let uu___6 =
                                   FStar_Syntax_Print.fv_to_string fv in
                                 not_implemented_warning uu___5 uu___6 msg);
                                FStar_Pervasives_Native.None))))
let (__do_handle_plugin :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.int FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.sigelt ->
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g ->
    fun arity_opt ->
      fun se ->
        let w =
          FStar_Extraction_ML_Syntax.with_ty
            FStar_Extraction_ML_Syntax.MLTY_Top in
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
                                   [w ml_name_str; w arity1] args))) in
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
                         (FStar_Syntax_Syntax.RecordType (a, b)) ->
                         let uu___9 =
                           FStar_Compiler_List.map FStar_Ident.string_of_id b in
                         FStar_Pervasives_Native.Some uu___9
                     | uu___9 -> FStar_Pervasives_Native.None in
                   let ml_unembed = mk_unembed record_fields ctors in
                   let ml_embed = mk_embed record_fields ctors in
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
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s, uu___3));
                         FStar_Syntax_Syntax.pos = uu___4;
                         FStar_Syntax_Syntax.vars = uu___5;
                         FStar_Syntax_Syntax.hash_code = uu___6;_},
                       uu___7)::[] ->
                        let uu___8 =
                          let uu___9 = FStar_Compiler_Util.int_of_string s in
                          FStar_Pervasives_Native.Some uu___9 in
                        FStar_Pervasives_Native.Some uu___8
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
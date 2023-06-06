open Prims
exception Unsupported of Prims.string 
let (uu___is_Unsupported : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Unsupported uu___ -> true | uu___ -> false
let (__proj__Unsupported__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Unsupported uu___ -> uu___
let (mk :
  FStar_Extraction_ML_Syntax.mlexpr' -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e ->
    FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top e
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
  FStar_Ident.lid_of_str "Ident.lid_of_str"
let (fresh : Prims.string -> Prims.string) =
  let r = FStar_Compiler_Util.mk_ref Prims.int_zero in
  fun s ->
    let v = FStar_Compiler_Effect.op_Bang r in
    FStar_Compiler_Effect.op_Colon_Equals r (v + Prims.int_one);
    Prims.op_Hat s (Prims.op_Hat "_" (Prims.string_of_int v))
let splitlast : 'uuuuu . 'uuuuu Prims.list -> ('uuuuu Prims.list * 'uuuuu) =
  fun s ->
    let uu___ = FStar_Compiler_List.rev s in
    match uu___ with | x::xs -> ((FStar_Compiler_List.rev xs), x)
let (mk_unembed :
  FStar_Syntax_Syntax.sigelt Prims.list -> FStar_Extraction_ML_Syntax.mlexpr)
  =
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
                     let pat_s =
                       let uu___2 =
                         let uu___3 = FStar_Ident.string_of_lid lid in
                         FStar_Extraction_ML_Syntax.MLC_String uu___3 in
                       FStar_Extraction_ML_Syntax.MLP_Const uu___2 in
                     let pat_args =
                       FStar_Extraction_ML_Syntax.MLP_CTor
                         ((["Prims"], "Nil"), []) in
                     let pat_both =
                       FStar_Extraction_ML_Syntax.MLP_Tuple [pat_s; pat_args] in
                     let ret =
                       let uu___2 =
                         let uu___3 =
                           let uu___4 = FStar_Ident.path_of_lid lid in
                           splitlast uu___4 in
                         FStar_Extraction_ML_Syntax.MLE_Name uu___3 in
                       mk uu___2 in
                     let ret1 =
                       mk
                         (FStar_Extraction_ML_Syntax.MLE_App (ml_some, [ret])) in
                     let br = (pat_both, FStar_Pervasives_Native.None, ret1) in
                     let uu___2 =
                       let uu___3 = FStar_Compiler_Effect.op_Bang e_branches in
                       br :: uu___3 in
                     FStar_Compiler_Effect.op_Colon_Equals e_branches uu___2)
            | uu___1 -> failwith "impossible, filter above"));
    (let nomatch =
       (FStar_Extraction_ML_Syntax.MLP_Wild, FStar_Pervasives_Native.None,
         ml_none) in
     let branches =
       let uu___1 =
         let uu___2 = FStar_Compiler_Effect.op_Bang e_branches in nomatch ::
           uu___2 in
       FStar_Compiler_List.rev uu___1 in
     let sc = mk (FStar_Extraction_ML_Syntax.MLE_Var arg_v) in
     let def = mk (FStar_Extraction_ML_Syntax.MLE_Match (sc, branches)) in
     let lam =
       mk
         (FStar_Extraction_ML_Syntax.MLE_Fun
            ([(arg_v, FStar_Extraction_ML_Syntax.MLTY_Top)], def)) in
     lam)
let (mk_embed :
  FStar_Syntax_Syntax.sigelt Prims.list -> FStar_Extraction_ML_Syntax.mlexpr)
  =
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
                     let pat =
                       let uu___2 =
                         let uu___3 =
                           let uu___4 = FStar_Ident.path_of_lid lid in
                           splitlast uu___4 in
                         (uu___3, []) in
                       FStar_Extraction_ML_Syntax.MLP_CTor uu___2 in
                     let fvar =
                       let uu___2 =
                         let uu___3 =
                           let uu___4 = FStar_Ident.path_of_lid s_fvar_lid in
                           splitlast uu___4 in
                         FStar_Extraction_ML_Syntax.MLE_Name uu___3 in
                       mk uu___2 in
                     let lid_of_str =
                       let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             FStar_Ident.path_of_lid lid_of_str_lid in
                           splitlast uu___4 in
                         FStar_Extraction_ML_Syntax.MLE_Name uu___3 in
                       mk uu___2 in
                     let ret =
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
                             [uu___5] in
                           (fvar, uu___4) in
                         FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                       mk uu___2 in
                     let br = (pat, FStar_Pervasives_Native.None, ret) in
                     let uu___2 =
                       let uu___3 = FStar_Compiler_Effect.op_Bang e_branches in
                       br :: uu___3 in
                     FStar_Compiler_Effect.op_Colon_Equals e_branches uu___2)
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
                FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g fv
                  fv_t arity_opt ml_name_str in
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
                   FStar_Syntax_Syntax.params = uu___3;
                   FStar_Syntax_Syntax.num_uniform_params = uu___4;
                   FStar_Syntax_Syntax.t = uu___5;
                   FStar_Syntax_Syntax.mutuals = uu___6;
                   FStar_Syntax_Syntax.ds = uu___7;_}
                 ->
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
                 let ml_name =
                   let uu___8 =
                     let uu___9 =
                       let uu___10 = FStar_Ident.string_of_lid tlid in
                       FStar_Extraction_ML_Syntax.MLC_String uu___10 in
                     FStar_Extraction_ML_Syntax.MLE_Const uu___9 in
                   mk uu___8 in
                 let ml_unembed = mk_unembed ctors in
                 let ml_embed = mk_embed ctors in
                 let def =
                   mk
                     (FStar_Extraction_ML_Syntax.MLE_App
                        ((mk
                            (FStar_Extraction_ML_Syntax.MLE_Name
                               (["FStar"; "Syntax"; "Embeddings"; "Base"],
                                 "mk_extracted_embedding"))),
                          [ml_name; ml_unembed; ml_embed])) in
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
                 [FStar_Extraction_ML_Syntax.MLM_Let
                    (FStar_Extraction_ML_Syntax.NonRec, [lb])])
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
open Prims
let (maybe_register_plugin :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g ->
    fun se ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top in
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
         | FStar_Pervasives_Native.Some arity_opt ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_let
                  { FStar_Syntax_Syntax.lbs1 = lbs;
                    FStar_Syntax_Syntax.lids1 = uu___3;_}
                  ->
                  let mk_registration lb =
                    let fv =
                      FStar_Compiler_Util.right lb.FStar_Syntax_Syntax.lbname in
                    let fv_lid =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp in
                    let ml_name_str =
                      let uu___4 =
                        let uu___5 = FStar_Ident.string_of_lid fv_lid in
                        FStar_Extraction_ML_Syntax.MLC_String uu___5 in
                      FStar_Extraction_ML_Syntax.MLE_Const uu___4 in
                    let uu___4 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g
                        fv fv_t arity_opt ml_name_str in
                    match uu___4 with
                    | FStar_Pervasives_Native.Some
                        (interp, nbe_interp, arity, plugin) ->
                        let uu___5 =
                          if plugin
                          then
                            ((["FStar_Tactics_Native"], "register_plugin"),
                              [interp; nbe_interp])
                          else
                            ((["FStar_Tactics_Native"], "register_tactic"),
                              [interp]) in
                        (match uu___5 with
                         | (register, args) ->
                             let h =
                               FStar_Compiler_Effect.op_Less_Bar
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_Name
                                    register) in
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
              | uu___3 -> []))
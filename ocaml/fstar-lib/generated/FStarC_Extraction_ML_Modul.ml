open Prims
let (dbg_ExtractionReify : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "ExtractionReify"
type tydef_declaration =
  (FStarC_Extraction_ML_Syntax.mlsymbol *
    FStarC_Extraction_ML_Syntax.metadata * Prims.int)
type iface =
  {
  iface_module_name: FStarC_Extraction_ML_Syntax.mlpath ;
  iface_bindings:
    (FStarC_Syntax_Syntax.fv * FStarC_Extraction_ML_UEnv.exp_binding)
      Prims.list
    ;
  iface_tydefs:
    (FStarC_Extraction_ML_UEnv.tydef, tydef_declaration)
      FStar_Pervasives.either Prims.list
    ;
  iface_type_names:
    (FStarC_Syntax_Syntax.fv * FStarC_Extraction_ML_Syntax.mlpath) Prims.list }
let (__proj__Mkiface__item__iface_module_name :
  iface -> FStarC_Extraction_ML_Syntax.mlpath) =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_module_name
let (__proj__Mkiface__item__iface_bindings :
  iface ->
    (FStarC_Syntax_Syntax.fv * FStarC_Extraction_ML_UEnv.exp_binding)
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_bindings
let (__proj__Mkiface__item__iface_tydefs :
  iface ->
    (FStarC_Extraction_ML_UEnv.tydef, tydef_declaration)
      FStar_Pervasives.either Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_tydefs
let (__proj__Mkiface__item__iface_type_names :
  iface ->
    (FStarC_Syntax_Syntax.fv * FStarC_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_type_names
type extension_sigelt_extractor =
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.sigelt ->
      FStarC_Dyn.dyn ->
        (FStarC_Extraction_ML_Syntax.mlmodule, Prims.string)
          FStar_Pervasives.either
type extension_sigelt_iface_extractor =
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.sigelt ->
      FStarC_Dyn.dyn ->
        ((FStarC_Extraction_ML_UEnv.uenv * iface), Prims.string)
          FStar_Pervasives.either
type extension_extractor =
  {
  extract_sigelt: extension_sigelt_extractor ;
  extract_sigelt_iface: extension_sigelt_iface_extractor }
let (__proj__Mkextension_extractor__item__extract_sigelt :
  extension_extractor -> extension_sigelt_extractor) =
  fun projectee ->
    match projectee with
    | { extract_sigelt; extract_sigelt_iface;_} -> extract_sigelt
let (__proj__Mkextension_extractor__item__extract_sigelt_iface :
  extension_extractor -> extension_sigelt_iface_extractor) =
  fun projectee ->
    match projectee with
    | { extract_sigelt; extract_sigelt_iface;_} -> extract_sigelt_iface
let (extension_extractor_table :
  extension_extractor FStarC_Compiler_Util.smap) =
  FStarC_Compiler_Util.smap_create (Prims.of_int (20))
let (register_extension_extractor :
  Prims.string -> extension_extractor -> unit) =
  fun ext ->
    fun callback ->
      FStarC_Compiler_Util.smap_add extension_extractor_table ext callback
let (lookup_extension_extractor :
  Prims.string -> extension_extractor FStar_Pervasives_Native.option) =
  fun ext ->
    let do1 uu___ =
      FStarC_Compiler_Util.smap_try_find extension_extractor_table ext in
    let uu___ = do1 () in
    match uu___ with
    | FStar_Pervasives_Native.None ->
        let uu___1 = FStarC_Compiler_Plugins.autoload_plugin ext in
        if uu___1 then do1 () else FStar_Pervasives_Native.None
    | r -> r
type env_t = FStarC_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun lid ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Parser_Const.failwith_lid () in
            FStarC_Syntax_Syntax.fvar uu___3 FStar_Pervasives_Native.None in
          let uu___3 =
            let uu___4 = FStarC_Syntax_Syntax.iarg t in
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 =
                          let uu___12 =
                            FStarC_Class_Show.show
                              FStarC_Ident.showable_lident lid in
                          Prims.strcat "Not yet implemented: " uu___12 in
                        (uu___11, FStarC_Compiler_Range_Type.dummyRange) in
                      FStarC_Const.Const_string uu___10 in
                    FStarC_Syntax_Syntax.Tm_constant uu___9 in
                  FStarC_Syntax_Syntax.mk uu___8
                    FStarC_Compiler_Range_Type.dummyRange in
                FStarC_Syntax_Syntax.as_arg uu___7 in
              [uu___6] in
            uu___4 :: uu___5 in
          {
            FStarC_Syntax_Syntax.hd = uu___2;
            FStarC_Syntax_Syntax.args = uu___3
          } in
        FStarC_Syntax_Syntax.Tm_app uu___1 in
      FStarC_Syntax_Syntax.mk uu___ FStarC_Compiler_Range_Type.dummyRange
let (always_fail :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.letbinding)
  =
  fun lid ->
    fun t ->
      let imp =
        let uu___ = FStarC_Syntax_Util.arrow_formals t in
        match uu___ with
        | ([], t1) ->
            let b =
              let uu___1 =
                FStarC_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1 in
              FStarC_Syntax_Syntax.mk_binder uu___1 in
            let uu___1 = fail_exp lid t1 in
            FStarC_Syntax_Util.abs [b] uu___1 FStar_Pervasives_Native.None
        | (bs, t1) ->
            let uu___1 = fail_exp lid t1 in
            FStarC_Syntax_Util.abs bs uu___1 FStar_Pervasives_Native.None in
      let lb =
        let uu___ =
          let uu___1 =
            FStarC_Syntax_Syntax.lid_as_fv lid FStar_Pervasives_Native.None in
          FStar_Pervasives.Inr uu___1 in
        let uu___1 = FStarC_Parser_Const.effect_ML_lid () in
        {
          FStarC_Syntax_Syntax.lbname = uu___;
          FStarC_Syntax_Syntax.lbunivs = [];
          FStarC_Syntax_Syntax.lbtyp = t;
          FStarC_Syntax_Syntax.lbeff = uu___1;
          FStarC_Syntax_Syntax.lbdef = imp;
          FStarC_Syntax_Syntax.lbattrs = [];
          FStarC_Syntax_Syntax.lbpos = (imp.FStarC_Syntax_Syntax.pos)
        } in
      lb
let as_pair : 'uuuuu . 'uuuuu Prims.list -> ('uuuuu * 'uuuuu) =
  fun uu___ ->
    match uu___ with
    | a::b::[] -> (a, b)
    | uu___1 -> failwith "Expected a list with 2 elements"
let (flag_of_qual :
  FStarC_Syntax_Syntax.qualifier ->
    FStarC_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.Assumption ->
        FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.Assumed
    | FStarC_Syntax_Syntax.Private ->
        FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.Private
    | FStarC_Syntax_Syntax.NoExtract ->
        FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.NoExtract
    | uu___1 -> FStar_Pervasives_Native.None
let rec (extract_meta :
  FStarC_Syntax_Syntax.term ->
    FStarC_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x ->
    let uu___ = FStarC_Syntax_Subst.compress x in
    match uu___ with
    | { FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
        FStarC_Syntax_Syntax.pos = uu___1;
        FStarC_Syntax_Syntax.vars = uu___2;
        FStarC_Syntax_Syntax.hash_code = uu___3;_} ->
        let uu___4 =
          let uu___5 = FStarC_Syntax_Syntax.lid_of_fv fv in
          FStarC_Ident.string_of_lid uu___5 in
        (match uu___4 with
         | "FStar.Pervasives.PpxDerivingShow" ->
             FStar_Pervasives_Native.Some
               FStarC_Extraction_ML_Syntax.PpxDerivingShow
         | "FStar.Pervasives.PpxDerivingYoJson" ->
             FStar_Pervasives_Native.Some
               FStarC_Extraction_ML_Syntax.PpxDerivingYoJson
         | "FStar.Pervasives.CInline" ->
             FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.CInline
         | "FStar.Pervasives.CNoInline" ->
             FStar_Pervasives_Native.Some
               FStarC_Extraction_ML_Syntax.CNoInline
         | "FStar.Pervasives.Substitute" ->
             FStar_Pervasives_Native.Some
               FStarC_Extraction_ML_Syntax.Substitute
         | "FStar.Pervasives.Gc" ->
             FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.GCType
         | "FStar.Pervasives.CAbstractStruct" ->
             FStar_Pervasives_Native.Some
               FStarC_Extraction_ML_Syntax.CAbstract
         | "FStar.Pervasives.CIfDef" ->
             FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.CIfDef
         | "FStar.Pervasives.CMacro" ->
             FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.CMacro
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStarC_Extraction_ML_Syntax.Deprecated "")
         | uu___5 -> FStar_Pervasives_Native.None)
    | {
        FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_app
          {
            FStarC_Syntax_Syntax.hd =
              { FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
                FStarC_Syntax_Syntax.pos = uu___1;
                FStarC_Syntax_Syntax.vars = uu___2;
                FStarC_Syntax_Syntax.hash_code = uu___3;_};
            FStarC_Syntax_Syntax.args =
              ({
                 FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                   (FStarC_Const.Const_string (s, uu___4));
                 FStarC_Syntax_Syntax.pos = uu___5;
                 FStarC_Syntax_Syntax.vars = uu___6;
                 FStarC_Syntax_Syntax.hash_code = uu___7;_},
               uu___8)::[];_};
        FStarC_Syntax_Syntax.pos = uu___9;
        FStarC_Syntax_Syntax.vars = uu___10;
        FStarC_Syntax_Syntax.hash_code = uu___11;_} ->
        let uu___12 =
          let uu___13 = FStarC_Syntax_Syntax.lid_of_fv fv in
          FStarC_Ident.string_of_lid uu___13 in
        (match uu___12 with
         | "FStar.Pervasives.PpxDerivingShowConstant" ->
             FStar_Pervasives_Native.Some
               (FStarC_Extraction_ML_Syntax.PpxDerivingShowConstant s)
         | "FStar.Pervasives.Comment" ->
             FStar_Pervasives_Native.Some
               (FStarC_Extraction_ML_Syntax.Comment s)
         | "FStar.Pervasives.CPrologue" ->
             FStar_Pervasives_Native.Some
               (FStarC_Extraction_ML_Syntax.CPrologue s)
         | "FStar.Pervasives.CEpilogue" ->
             FStar_Pervasives_Native.Some
               (FStarC_Extraction_ML_Syntax.CEpilogue s)
         | "FStar.Pervasives.CConst" ->
             FStar_Pervasives_Native.Some
               (FStarC_Extraction_ML_Syntax.CConst s)
         | "FStar.Pervasives.CCConv" ->
             FStar_Pervasives_Native.Some
               (FStarC_Extraction_ML_Syntax.CCConv s)
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStarC_Extraction_ML_Syntax.Deprecated s)
         | uu___13 -> FStar_Pervasives_Native.None)
    | {
        FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
          (FStarC_Const.Const_string ("KrmlPrivate", uu___1));
        FStarC_Syntax_Syntax.pos = uu___2;
        FStarC_Syntax_Syntax.vars = uu___3;
        FStarC_Syntax_Syntax.hash_code = uu___4;_} ->
        FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.Private
    | {
        FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
          (FStarC_Const.Const_string ("c_inline", uu___1));
        FStarC_Syntax_Syntax.pos = uu___2;
        FStarC_Syntax_Syntax.vars = uu___3;
        FStarC_Syntax_Syntax.hash_code = uu___4;_} ->
        FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.CInline
    | {
        FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
          (FStarC_Const.Const_string ("substitute", uu___1));
        FStarC_Syntax_Syntax.pos = uu___2;
        FStarC_Syntax_Syntax.vars = uu___3;
        FStarC_Syntax_Syntax.hash_code = uu___4;_} ->
        FStar_Pervasives_Native.Some FStarC_Extraction_ML_Syntax.Substitute
    | {
        FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = x1;
            FStarC_Syntax_Syntax.meta = uu___1;_};
        FStarC_Syntax_Syntax.pos = uu___2;
        FStarC_Syntax_Syntax.vars = uu___3;
        FStarC_Syntax_Syntax.hash_code = uu___4;_} -> extract_meta x1
    | uu___1 ->
        let uu___2 = FStarC_Syntax_Util.head_and_args x in
        (match uu___2 with
         | (head, args) ->
             let uu___3 =
               let uu___4 =
                 let uu___5 = FStarC_Syntax_Subst.compress head in
                 uu___5.FStarC_Syntax_Syntax.n in
               (uu___4, args) in
             (match uu___3 with
              | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___4::[]) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.remove_unused_type_parameters_lid
                  ->
                  let uu___5 =
                    let uu___6 =
                      FStarC_ToSyntax_ToSyntax.parse_attr_with_list false x
                        FStarC_Parser_Const.remove_unused_type_parameters_lid in
                    FStar_Pervasives_Native.fst uu___6 in
                  (match uu___5 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some l ->
                       let uu___6 =
                         let uu___7 =
                           let uu___8 = FStarC_Syntax_Syntax.range_of_fv fv in
                           (l, uu___8) in
                         FStarC_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                           uu___7 in
                       FStar_Pervasives_Native.Some uu___6)
              | uu___4 -> FStar_Pervasives_Native.None))
let (extract_metadata :
  FStarC_Syntax_Syntax.term Prims.list ->
    FStarC_Extraction_ML_Syntax.meta Prims.list)
  = fun metas -> FStarC_Compiler_List.choose extract_meta metas
let (binders_as_mlty_binders :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.binder Prims.list ->
      (FStarC_Extraction_ML_UEnv.uenv * FStarC_Extraction_ML_Syntax.ty_param
        Prims.list))
  =
  fun env ->
    fun bs ->
      FStarC_Compiler_Util.fold_map
        (fun env1 ->
           fun uu___ ->
             match uu___ with
             | { FStarC_Syntax_Syntax.binder_bv = bv;
                 FStarC_Syntax_Syntax.binder_qual = uu___1;
                 FStarC_Syntax_Syntax.binder_positivity = uu___2;
                 FStarC_Syntax_Syntax.binder_attrs = binder_attrs;_} ->
                 let env2 = FStarC_Extraction_ML_UEnv.extend_ty env1 bv false in
                 let ty_param_name =
                   let uu___3 = FStarC_Extraction_ML_UEnv.lookup_bv env2 bv in
                   match uu___3 with
                   | FStar_Pervasives.Inl ty ->
                       ty.FStarC_Extraction_ML_UEnv.ty_b_name
                   | uu___4 -> failwith "Impossible" in
                 let ty_param_attrs =
                   FStarC_Compiler_List.map
                     (fun attr ->
                        let uu___3 =
                          FStarC_Extraction_ML_Term.term_as_mlexpr env2 attr in
                        match uu___3 with | (e, uu___4, uu___5) -> e)
                     binder_attrs in
                 (env2,
                   {
                     FStarC_Extraction_ML_Syntax.ty_param_name =
                       ty_param_name;
                     FStarC_Extraction_ML_Syntax.ty_param_attrs =
                       ty_param_attrs
                   })) env bs
type data_constructor =
  {
  dname: FStarC_Ident.lident ;
  dtyp: FStarC_Syntax_Syntax.typ }
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStarC_Ident.lident) =
  fun projectee -> match projectee with | { dname; dtyp;_} -> dname
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStarC_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | { dname; dtyp;_} -> dtyp
type inductive_family =
  {
  ifv: FStarC_Syntax_Syntax.fv ;
  iname: FStarC_Ident.lident ;
  iparams: FStarC_Syntax_Syntax.binders ;
  ityp: FStarC_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStarC_Syntax_Syntax.qualifier Prims.list ;
  imetadata: FStarC_Extraction_ML_Syntax.metadata }
let (__proj__Mkinductive_family__item__ifv :
  inductive_family -> FStarC_Syntax_Syntax.fv) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ifv
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iname
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStarC_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iparams
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStarC_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ityp
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> idatas
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStarC_Syntax_Syntax.qualifier Prims.list) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iquals
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStarC_Extraction_ML_Syntax.metadata) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> imetadata
let (print_ifamily : inductive_family -> unit) =
  fun i ->
    let uu___ = FStarC_Class_Show.show FStarC_Ident.showable_lident i.iname in
    let uu___1 =
      FStarC_Class_Show.show
        (FStarC_Class_Show.show_list FStarC_Syntax_Print.showable_binder)
        i.iparams in
    let uu___2 =
      FStarC_Class_Show.show FStarC_Syntax_Print.showable_term i.ityp in
    let uu___3 =
      let uu___4 =
        FStarC_Compiler_List.map
          (fun d ->
             let uu___5 =
               FStarC_Class_Show.show FStarC_Ident.showable_lident d.dname in
             let uu___6 =
               let uu___7 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                   d.dtyp in
               Prims.strcat " : " uu___7 in
             Prims.strcat uu___5 uu___6) i.idatas in
      FStarC_Compiler_String.concat "\n\t\t" uu___4 in
    FStarC_Compiler_Util.print4 "\n\t%s %s : %s { %s }\n" uu___ uu___1 uu___2
      uu___3
let (bundle_as_inductive_families :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.sigelt Prims.list ->
      FStarC_Syntax_Syntax.qualifier Prims.list ->
        (FStarC_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        let uu___ =
          FStarC_Compiler_Util.fold_map
            (fun env1 ->
               fun se ->
                 match se.FStarC_Syntax_Syntax.sigel with
                 | FStarC_Syntax_Syntax.Sig_inductive_typ
                     { FStarC_Syntax_Syntax.lid = l;
                       FStarC_Syntax_Syntax.us = us;
                       FStarC_Syntax_Syntax.params = bs;
                       FStarC_Syntax_Syntax.num_uniform_params = uu___1;
                       FStarC_Syntax_Syntax.t = t;
                       FStarC_Syntax_Syntax.mutuals = uu___2;
                       FStarC_Syntax_Syntax.ds = datas;
                       FStarC_Syntax_Syntax.injective_type_params = uu___3;_}
                     ->
                     let uu___4 = FStarC_Syntax_Subst.open_univ_vars us t in
                     (match uu___4 with
                      | (_us, t1) ->
                          let uu___5 = FStarC_Syntax_Subst.open_term bs t1 in
                          (match uu___5 with
                           | (bs1, t2) ->
                               let datas1 =
                                 FStarC_Compiler_List.collect
                                   (fun se1 ->
                                      match se1.FStarC_Syntax_Syntax.sigel
                                      with
                                      | FStarC_Syntax_Syntax.Sig_datacon
                                          { FStarC_Syntax_Syntax.lid1 = d;
                                            FStarC_Syntax_Syntax.us1 = us1;
                                            FStarC_Syntax_Syntax.t1 = t3;
                                            FStarC_Syntax_Syntax.ty_lid = l';
                                            FStarC_Syntax_Syntax.num_ty_params
                                              = nparams;
                                            FStarC_Syntax_Syntax.mutuals1 =
                                              uu___6;
                                            FStarC_Syntax_Syntax.injective_type_params1
                                              = uu___7;_}
                                          when FStarC_Ident.lid_equals l l'
                                          ->
                                          let uu___8 =
                                            FStarC_Syntax_Subst.open_univ_vars
                                              us1 t3 in
                                          (match uu___8 with
                                           | (_us1, t4) ->
                                               let uu___9 =
                                                 FStarC_Syntax_Util.arrow_formals
                                                   t4 in
                                               (match uu___9 with
                                                | (bs', body) ->
                                                    let uu___10 =
                                                      FStarC_Compiler_Util.first_N
                                                        (FStarC_Compiler_List.length
                                                           bs1) bs' in
                                                    (match uu___10 with
                                                     | (bs_params, rest) ->
                                                         let subst =
                                                           FStarC_Compiler_List.map2
                                                             (fun uu___11 ->
                                                                fun uu___12
                                                                  ->
                                                                  match 
                                                                    (uu___11,
                                                                    uu___12)
                                                                  with
                                                                  | ({
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b';
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___13;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___14;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___15;_},
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___16;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___17;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___18;_})
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    (b',
                                                                    uu___20) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___19)
                                                             bs_params bs1 in
                                                         let t5 =
                                                           let uu___11 =
                                                             let uu___12 =
                                                               FStarC_Syntax_Syntax.mk_Total
                                                                 body in
                                                             FStarC_Syntax_Util.arrow
                                                               rest uu___12 in
                                                           FStarC_Syntax_Subst.subst
                                                             subst uu___11 in
                                                         [{
                                                            dname = d;
                                                            dtyp = t5
                                                          }])))
                                      | uu___6 -> []) ses in
                               let metadata =
                                 let uu___6 =
                                   extract_metadata
                                     se.FStarC_Syntax_Syntax.sigattrs in
                                 let uu___7 =
                                   FStarC_Compiler_List.choose flag_of_qual
                                     quals in
                                 FStarC_Compiler_List.op_At uu___6 uu___7 in
                               let fv =
                                 FStarC_Syntax_Syntax.lid_as_fv l
                                   FStar_Pervasives_Native.None in
                               let uu___6 =
                                 FStarC_Extraction_ML_UEnv.extend_type_name
                                   env1 fv in
                               (match uu___6 with
                                | (uu___7, env2) ->
                                    (env2,
                                      [{
                                         ifv = fv;
                                         iname = l;
                                         iparams = bs1;
                                         ityp = t2;
                                         idatas = datas1;
                                         iquals =
                                           (se.FStarC_Syntax_Syntax.sigquals);
                                         imetadata = metadata
                                       }]))))
                 | uu___1 -> (env1, [])) env ses in
        match uu___ with
        | (env1, ifams) -> (env1, (FStarC_Compiler_List.flatten ifams))
let (empty_iface : iface) =
  {
    iface_module_name = ([], "");
    iface_bindings = [];
    iface_tydefs = [];
    iface_type_names = []
  }
let (iface_of_bindings :
  (FStarC_Syntax_Syntax.fv * FStarC_Extraction_ML_UEnv.exp_binding)
    Prims.list -> iface)
  =
  fun fvs ->
    {
      iface_module_name = (empty_iface.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (empty_iface.iface_tydefs);
      iface_type_names = (empty_iface.iface_type_names)
    }
let (iface_of_tydefs : FStarC_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds ->
    let uu___ =
      FStarC_Compiler_List.map (fun uu___1 -> FStar_Pervasives.Inl uu___1)
        tds in
    let uu___1 =
      FStarC_Compiler_List.map
        (fun td ->
           let uu___2 = FStarC_Extraction_ML_UEnv.tydef_fv td in
           let uu___3 = FStarC_Extraction_ML_UEnv.tydef_mlpath td in
           (uu___2, uu___3)) tds in
    {
      iface_module_name = (empty_iface.iface_module_name);
      iface_bindings = (empty_iface.iface_bindings);
      iface_tydefs = uu___;
      iface_type_names = uu___1
    }
let (iface_of_type_names :
  (FStarC_Syntax_Syntax.fv * FStarC_Extraction_ML_Syntax.mlpath) Prims.list
    -> iface)
  =
  fun fvs ->
    {
      iface_module_name = (empty_iface.iface_module_name);
      iface_bindings = (empty_iface.iface_bindings);
      iface_tydefs = (empty_iface.iface_tydefs);
      iface_type_names = fvs
    }
let (iface_union : iface -> iface -> iface) =
  fun if1 ->
    fun if2 ->
      let uu___ = if1.iface_module_name in
      {
        iface_module_name = uu___;
        iface_bindings =
          (FStarC_Compiler_List.op_At if1.iface_bindings if2.iface_bindings);
        iface_tydefs =
          (FStarC_Compiler_List.op_At if1.iface_tydefs if2.iface_tydefs);
        iface_type_names =
          (FStarC_Compiler_List.op_At if1.iface_type_names
             if2.iface_type_names)
      }
let (iface_union_l : iface Prims.list -> iface) =
  fun ifs -> FStarC_Compiler_List.fold_right iface_union ifs empty_iface
let (string_of_mlpath : FStarC_Extraction_ML_Syntax.mlpath -> Prims.string) =
  fun p ->
    FStarC_Compiler_String.concat ". "
      (FStarC_Compiler_List.op_At (FStar_Pervasives_Native.fst p)
         [FStar_Pervasives_Native.snd p])
let tscheme_to_string :
  'uuuuu .
    FStarC_Extraction_ML_Syntax.mlpath ->
      ('uuuuu * FStarC_Extraction_ML_Syntax.mlty) -> Prims.string
  =
  fun cm ->
    fun ts ->
      FStarC_Extraction_ML_Code.string_of_mlty cm
        (FStar_Pervasives_Native.snd ts)
let (print_exp_binding :
  FStarC_Extraction_ML_Syntax.mlpath ->
    FStarC_Extraction_ML_UEnv.exp_binding -> Prims.string)
  =
  fun cm ->
    fun e ->
      let uu___ =
        FStarC_Extraction_ML_Code.string_of_mlexpr cm
          e.FStarC_Extraction_ML_UEnv.exp_b_expr in
      let uu___1 =
        tscheme_to_string cm e.FStarC_Extraction_ML_UEnv.exp_b_tscheme in
      FStarC_Compiler_Util.format3
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s }"
        e.FStarC_Extraction_ML_UEnv.exp_b_name uu___ uu___1
let (print_binding :
  FStarC_Extraction_ML_Syntax.mlpath ->
    (FStarC_Syntax_Syntax.fv * FStarC_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm ->
    fun uu___ ->
      match uu___ with
      | (fv, exp_binding) ->
          let uu___1 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_fv fv in
          let uu___2 = print_exp_binding cm exp_binding in
          FStarC_Compiler_Util.format2 "(%s, %s)" uu___1 uu___2
let print_tydef :
  'uuuuu 'uuuuu1 .
    FStarC_Extraction_ML_Syntax.mlpath ->
      (FStarC_Extraction_ML_UEnv.tydef, (Prims.string * 'uuuuu * 'uuuuu1))
        FStar_Pervasives.either -> Prims.string
  =
  fun cm ->
    fun tydef ->
      let uu___ =
        match tydef with
        | FStar_Pervasives.Inl tydef1 ->
            let uu___1 =
              let uu___2 = FStarC_Extraction_ML_UEnv.tydef_fv tydef1 in
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_fv uu___2 in
            let uu___2 =
              let uu___3 = FStarC_Extraction_ML_UEnv.tydef_def tydef1 in
              tscheme_to_string cm uu___3 in
            (uu___1, uu___2)
        | FStar_Pervasives.Inr (p, uu___1, uu___2) -> (p, "None") in
      match uu___ with
      | (name, defn) -> FStarC_Compiler_Util.format2 "(%s, %s)" name defn
let (iface_to_string : iface -> Prims.string) =
  fun iface1 ->
    let cm = iface1.iface_module_name in
    let print_type_name uu___ =
      match uu___ with
      | (tn, uu___1) ->
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_fv tn in
    let uu___ =
      let uu___1 =
        FStarC_Compiler_List.map (print_binding cm) iface1.iface_bindings in
      FStarC_Compiler_String.concat "\n" uu___1 in
    let uu___1 =
      let uu___2 =
        FStarC_Compiler_List.map (print_tydef cm) iface1.iface_tydefs in
      FStarC_Compiler_String.concat "\n" uu___2 in
    let uu___2 =
      let uu___3 =
        FStarC_Compiler_List.map print_type_name iface1.iface_type_names in
      FStarC_Compiler_String.concat "\n" uu___3 in
    FStarC_Compiler_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (string_of_mlpath iface1.iface_module_name) uu___ uu___1 uu___2
let (gamma_to_string : FStarC_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env ->
    let cm = FStarC_Extraction_ML_UEnv.current_module_of_uenv env in
    let gamma =
      let uu___ = FStarC_Extraction_ML_UEnv.bindings_of_uenv env in
      FStarC_Compiler_List.collect
        (fun uu___1 ->
           match uu___1 with
           | FStarC_Extraction_ML_UEnv.Fv (b, e) -> [(b, e)]
           | uu___2 -> []) uu___ in
    let uu___ =
      let uu___1 = FStarC_Compiler_List.map (print_binding cm) gamma in
      FStarC_Compiler_String.concat "\n" uu___1 in
    FStarC_Compiler_Util.format1 "Gamma = {\n %s }" uu___
let (extract_attrs :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.attribute Prims.list ->
      FStarC_Extraction_ML_Syntax.mlattribute Prims.list)
  =
  fun env ->
    fun attrs ->
      FStarC_Compiler_List.map
        (fun attr ->
           let uu___ = FStarC_Extraction_ML_Term.term_as_mlexpr env attr in
           match uu___ with | (e, uu___1, uu___2) -> e) attrs
let (extract_typ_abbrev :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.qualifier Prims.list ->
      FStarC_Syntax_Syntax.attribute Prims.list ->
        FStarC_Syntax_Syntax.letbinding ->
          (env_t * iface * FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun quals ->
      fun attrs ->
        fun lb ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv env in
              FStarC_TypeChecker_Env.open_universes_in uu___2
                lb.FStarC_Syntax_Syntax.lbunivs
                [lb.FStarC_Syntax_Syntax.lbdef;
                lb.FStarC_Syntax_Syntax.lbtyp] in
            match uu___1 with
            | (tcenv, uu___2, def_typ) ->
                let uu___3 = as_pair def_typ in (tcenv, uu___3) in
          match uu___ with
          | (tcenv, (lbdef, lbtyp)) ->
              let lbtyp1 =
                FStarC_TypeChecker_Normalize.normalize
                  [FStarC_TypeChecker_Env.Beta;
                  FStarC_TypeChecker_Env.UnfoldUntil
                    FStarC_Syntax_Syntax.delta_constant;
                  FStarC_TypeChecker_Env.ForExtraction] tcenv lbtyp in
              let lbdef1 =
                FStarC_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef
                  lbtyp1 in
              let fv =
                FStarC_Compiler_Util.right lb.FStarC_Syntax_Syntax.lbname in
              let lid =
                (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
              let def =
                let uu___1 =
                  let uu___2 = FStarC_Syntax_Subst.compress lbdef1 in
                  FStarC_Syntax_Util.unmeta uu___2 in
                FStarC_Syntax_Util.un_uinst uu___1 in
              let def1 =
                match def.FStarC_Syntax_Syntax.n with
                | FStarC_Syntax_Syntax.Tm_abs uu___1 ->
                    FStarC_Extraction_ML_Term.normalize_abs def
                | uu___1 -> def in
              let uu___1 =
                match def1.FStarC_Syntax_Syntax.n with
                | FStarC_Syntax_Syntax.Tm_abs
                    { FStarC_Syntax_Syntax.bs = bs;
                      FStarC_Syntax_Syntax.body = body;
                      FStarC_Syntax_Syntax.rc_opt = uu___2;_}
                    -> FStarC_Syntax_Subst.open_term bs body
                | uu___2 -> ([], def1) in
              (match uu___1 with
               | (bs, body) ->
                   let assumed =
                     FStarC_Compiler_Util.for_some
                       (fun uu___2 ->
                          match uu___2 with
                          | FStarC_Syntax_Syntax.Assumption -> true
                          | uu___3 -> false) quals in
                   let uu___2 = binders_as_mlty_binders env bs in
                   (match uu___2 with
                    | (env1, ml_bs) ->
                        let body1 =
                          let uu___3 =
                            FStarC_Extraction_ML_Term.term_as_mlty env1 body in
                          FStarC_Extraction_ML_Util.eraseTypeDeep
                            (FStarC_Extraction_ML_Util.udelta_unfold env1)
                            uu___3 in
                        let metadata =
                          let has_val_decl =
                            FStarC_Extraction_ML_UEnv.has_tydef_declaration
                              env lid in
                          let meta =
                            let uu___3 = extract_metadata attrs in
                            let uu___4 =
                              FStarC_Compiler_List.choose flag_of_qual quals in
                            FStarC_Compiler_List.op_At uu___3 uu___4 in
                          if has_val_decl
                          then
                            let uu___3 =
                              let uu___4 = FStarC_Ident.range_of_lid lid in
                              FStarC_Extraction_ML_Syntax.HasValDecl uu___4 in
                            uu___3 :: meta
                          else meta in
                        let tyscheme = (ml_bs, body1) in
                        let uu___3 =
                          let uu___4 =
                            FStarC_Compiler_Util.for_some
                              (fun uu___5 ->
                                 match uu___5 with
                                 | FStarC_Syntax_Syntax.Assumption -> true
                                 | FStarC_Syntax_Syntax.New -> true
                                 | uu___6 -> false) quals in
                          if uu___4
                          then
                            let uu___5 =
                              FStarC_Extraction_ML_UEnv.extend_type_name env
                                fv in
                            match uu___5 with
                            | (mlp, env2) ->
                                (mlp, (iface_of_type_names [(fv, mlp)]),
                                  env2)
                          else
                            (let uu___6 =
                               FStarC_Extraction_ML_UEnv.extend_tydef env fv
                                 tyscheme metadata in
                             match uu___6 with
                             | (td, mlp, env2) ->
                                 let uu___7 = iface_of_tydefs [td] in
                                 (mlp, uu___7, env2)) in
                        (match uu___3 with
                         | (mlpath, iface1, env2) ->
                             let td =
                               {
                                 FStarC_Extraction_ML_Syntax.tydecl_assumed =
                                   assumed;
                                 FStarC_Extraction_ML_Syntax.tydecl_name =
                                   (FStar_Pervasives_Native.snd mlpath);
                                 FStarC_Extraction_ML_Syntax.tydecl_ignored =
                                   FStar_Pervasives_Native.None;
                                 FStarC_Extraction_ML_Syntax.tydecl_parameters
                                   = ml_bs;
                                 FStarC_Extraction_ML_Syntax.tydecl_meta =
                                   metadata;
                                 FStarC_Extraction_ML_Syntax.tydecl_defn =
                                   (FStar_Pervasives_Native.Some
                                      (FStarC_Extraction_ML_Syntax.MLTD_Abbrev
                                         body1))
                               } in
                             let loc_mlmodule1 =
                               let uu___4 =
                                 let uu___5 = FStarC_Ident.range_of_lid lid in
                                 FStarC_Extraction_ML_Util.mlloc_of_range
                                   uu___5 in
                               FStarC_Extraction_ML_Syntax.MLM_Loc uu___4 in
                             let ty_mlmodule1 =
                               FStarC_Extraction_ML_Syntax.MLM_Ty [td] in
                             let def2 =
                               let uu___4 =
                                 FStarC_Extraction_ML_Syntax.mk_mlmodule1
                                   loc_mlmodule1 in
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 = extract_attrs env2 attrs in
                                   FStarC_Extraction_ML_Syntax.mk_mlmodule1_with_attrs
                                     ty_mlmodule1 uu___7 in
                                 [uu___6] in
                               uu___4 :: uu___5 in
                             (env2, iface1, def2))))
let (extract_let_rec_type :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.qualifier Prims.list ->
      FStarC_Syntax_Syntax.attribute Prims.list ->
        FStarC_Syntax_Syntax.letbinding ->
          (env_t * iface * FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun quals ->
      fun attrs ->
        fun lb ->
          let lbtyp =
            let uu___ = FStarC_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStarC_TypeChecker_Normalize.normalize
              [FStarC_TypeChecker_Env.Beta;
              FStarC_TypeChecker_Env.AllowUnboundUniverses;
              FStarC_TypeChecker_Env.EraseUniverses;
              FStarC_TypeChecker_Env.UnfoldUntil
                FStarC_Syntax_Syntax.delta_constant;
              FStarC_TypeChecker_Env.ForExtraction] uu___
              lb.FStarC_Syntax_Syntax.lbtyp in
          let uu___ = FStarC_Syntax_Util.arrow_formals lbtyp in
          match uu___ with
          | (bs, uu___1) ->
              let uu___2 = binders_as_mlty_binders env bs in
              (match uu___2 with
               | (env1, ml_bs) ->
                   let fv =
                     FStarC_Compiler_Util.right
                       lb.FStarC_Syntax_Syntax.lbname in
                   let lid =
                     (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                   let body = FStarC_Extraction_ML_Syntax.MLTY_Top in
                   let metadata =
                     let uu___3 = extract_metadata attrs in
                     let uu___4 =
                       FStarC_Compiler_List.choose flag_of_qual quals in
                     FStarC_Compiler_List.op_At uu___3 uu___4 in
                   let assumed = false in
                   let tscheme = (ml_bs, body) in
                   let uu___3 =
                     FStarC_Extraction_ML_UEnv.extend_tydef env fv tscheme
                       metadata in
                   (match uu___3 with
                    | (tydef, mlp, env2) ->
                        let td =
                          {
                            FStarC_Extraction_ML_Syntax.tydecl_assumed =
                              assumed;
                            FStarC_Extraction_ML_Syntax.tydecl_name =
                              (FStar_Pervasives_Native.snd mlp);
                            FStarC_Extraction_ML_Syntax.tydecl_ignored =
                              FStar_Pervasives_Native.None;
                            FStarC_Extraction_ML_Syntax.tydecl_parameters =
                              ml_bs;
                            FStarC_Extraction_ML_Syntax.tydecl_meta =
                              metadata;
                            FStarC_Extraction_ML_Syntax.tydecl_defn =
                              (FStar_Pervasives_Native.Some
                                 (FStarC_Extraction_ML_Syntax.MLTD_Abbrev
                                    body))
                          } in
                        let loc_mlmodule1 =
                          let uu___4 =
                            let uu___5 = FStarC_Ident.range_of_lid lid in
                            FStarC_Extraction_ML_Util.mlloc_of_range uu___5 in
                          FStarC_Extraction_ML_Syntax.MLM_Loc uu___4 in
                        let td_mlmodule1 =
                          FStarC_Extraction_ML_Syntax.MLM_Ty [td] in
                        let def =
                          let uu___4 =
                            FStarC_Extraction_ML_Syntax.mk_mlmodule1
                              loc_mlmodule1 in
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = extract_attrs env2 attrs in
                              FStarC_Extraction_ML_Syntax.mk_mlmodule1_with_attrs
                                td_mlmodule1 uu___7 in
                            [uu___6] in
                          uu___4 :: uu___5 in
                        let iface1 = iface_of_tydefs [tydef] in
                        (env2, iface1, def)))
let (extract_bundle_iface :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env ->
    fun se ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu___ =
            FStarC_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStarC_Extraction_ML_Util.eraseTypeDeep
            (FStarC_Extraction_ML_Util.udelta_unfold env_iparams) uu___ in
        let tys = (ml_tyvars, mlt) in
        let fvv =
          FStarC_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Pervasives_Native.None in
        let uu___ = FStarC_Extraction_ML_UEnv.extend_fv env1 fvv tys false in
        match uu___ with | (env2, uu___1, b) -> (env2, (fvv, b)) in
      let extract_one_family env1 ind =
        let uu___ = binders_as_mlty_binders env1 ind.iparams in
        match uu___ with
        | (env_iparams, vars) ->
            let uu___1 =
              FStarC_Compiler_Util.fold_map (extract_ctor env_iparams vars)
                env1 ind.idatas in
            (match uu___1 with
             | (env2, ctors) ->
                 let env3 =
                   let uu___2 =
                     FStarC_Compiler_Util.find_opt
                       (fun uu___3 ->
                          match uu___3 with
                          | FStarC_Syntax_Syntax.RecordType uu___4 -> true
                          | uu___4 -> false) ind.iquals in
                   match uu___2 with
                   | FStar_Pervasives_Native.Some
                       (FStarC_Syntax_Syntax.RecordType (ns, ids)) ->
                       let g =
                         FStarC_Compiler_List.fold_right
                           (fun id ->
                              fun g1 ->
                                let uu___3 =
                                  FStarC_Extraction_ML_UEnv.extend_record_field_name
                                    g1 ((ind.iname), id) in
                                match uu___3 with | (uu___4, g2) -> g2) ids
                           env2 in
                       g
                   | uu___3 -> env2 in
                 (env3, ctors)) in
      match ((se.FStarC_Syntax_Syntax.sigel),
              (se.FStarC_Syntax_Syntax.sigquals))
      with
      | (FStarC_Syntax_Syntax.Sig_bundle
         {
           FStarC_Syntax_Syntax.ses =
             {
               FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
                 { FStarC_Syntax_Syntax.lid1 = l;
                   FStarC_Syntax_Syntax.us1 = uu___;
                   FStarC_Syntax_Syntax.t1 = t;
                   FStarC_Syntax_Syntax.ty_lid = uu___1;
                   FStarC_Syntax_Syntax.num_ty_params = uu___2;
                   FStarC_Syntax_Syntax.mutuals1 = uu___3;
                   FStarC_Syntax_Syntax.injective_type_params1 = uu___4;_};
               FStarC_Syntax_Syntax.sigrng = uu___5;
               FStarC_Syntax_Syntax.sigquals = uu___6;
               FStarC_Syntax_Syntax.sigmeta = uu___7;
               FStarC_Syntax_Syntax.sigattrs = uu___8;
               FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
               FStarC_Syntax_Syntax.sigopts = uu___10;_}::[];
           FStarC_Syntax_Syntax.lids = uu___11;_},
         (FStarC_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu___12 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu___12 with
           | (env1, ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStarC_Syntax_Syntax.Sig_bundle
         { FStarC_Syntax_Syntax.ses = ses;
           FStarC_Syntax_Syntax.lids = uu___;_},
         quals) ->
          let uu___1 =
            FStarC_Syntax_Util.has_attribute se.FStarC_Syntax_Syntax.sigattrs
              FStarC_Parser_Const.erasable_attr in
          if uu___1
          then (env, empty_iface)
          else
            (let uu___3 = bundle_as_inductive_families env ses quals in
             match uu___3 with
             | (env1, ifams) ->
                 let uu___4 =
                   FStarC_Compiler_Util.fold_map extract_one_family env1
                     ifams in
                 (match uu___4 with
                  | (env2, td) ->
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            FStarC_Compiler_List.map
                              (fun x ->
                                 let uu___8 =
                                   FStarC_Extraction_ML_UEnv.mlpath_of_lident
                                     env2 x.iname in
                                 ((x.ifv), uu___8)) ifams in
                          iface_of_type_names uu___7 in
                        iface_union uu___6
                          (iface_of_bindings
                             (FStarC_Compiler_List.flatten td)) in
                      (env2, uu___5)))
      | uu___ -> failwith "Unexpected signature element"
let (extract_type_declaration :
  FStarC_Extraction_ML_UEnv.uenv ->
    Prims.bool ->
      FStarC_Ident.lident ->
        FStarC_Syntax_Syntax.qualifier Prims.list ->
          FStarC_Syntax_Syntax.term Prims.list ->
            FStarC_Syntax_Syntax.univ_name Prims.list ->
              FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
                (env_t * iface * FStarC_Extraction_ML_Syntax.mlmodule1
                  Prims.list))
  =
  fun g ->
    fun is_interface_val ->
      fun lid ->
        fun quals ->
          fun attrs ->
            fun univs ->
              fun t ->
                let uu___ =
                  let uu___1 =
                    FStarC_Compiler_Util.for_some
                      (fun uu___2 ->
                         match uu___2 with
                         | FStarC_Syntax_Syntax.Assumption -> true
                         | uu___3 -> false) quals in
                  Prims.op_Negation uu___1 in
                if uu___
                then
                  let g1 =
                    FStarC_Extraction_ML_UEnv.extend_with_tydef_declaration g
                      lid in
                  (g1, empty_iface, [])
                else
                  (let uu___2 = FStarC_Syntax_Util.arrow_formals t in
                   match uu___2 with
                   | (bs, uu___3) ->
                       let fv =
                         FStarC_Syntax_Syntax.lid_as_fv lid
                           FStar_Pervasives_Native.None in
                       let lb =
                         let uu___4 =
                           FStarC_Syntax_Util.abs bs
                             FStarC_Syntax_Syntax.t_unit
                             FStar_Pervasives_Native.None in
                         {
                           FStarC_Syntax_Syntax.lbname =
                             (FStar_Pervasives.Inr fv);
                           FStarC_Syntax_Syntax.lbunivs = univs;
                           FStarC_Syntax_Syntax.lbtyp = t;
                           FStarC_Syntax_Syntax.lbeff =
                             FStarC_Parser_Const.effect_Tot_lid;
                           FStarC_Syntax_Syntax.lbdef = uu___4;
                           FStarC_Syntax_Syntax.lbattrs = attrs;
                           FStarC_Syntax_Syntax.lbpos =
                             (t.FStarC_Syntax_Syntax.pos)
                         } in
                       let uu___4 = extract_typ_abbrev g quals attrs lb in
                       (match uu___4 with
                        | (g1, iface1, mods) ->
                            let iface2 =
                              if is_interface_val
                              then
                                let mlp =
                                  FStarC_Extraction_ML_UEnv.mlpath_of_lident
                                    g1 lid in
                                let meta = extract_metadata attrs in
                                {
                                  iface_module_name =
                                    (empty_iface.iface_module_name);
                                  iface_bindings =
                                    (empty_iface.iface_bindings);
                                  iface_tydefs =
                                    [FStar_Pervasives.Inr
                                       ((FStar_Pervasives_Native.snd mlp),
                                         meta,
                                         (FStarC_Compiler_List.length bs))];
                                  iface_type_names =
                                    (empty_iface.iface_type_names)
                                }
                              else iface1 in
                            (g1, iface2, mods)))
let (extract_reifiable_effect :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.eff_decl ->
      (FStarC_Extraction_ML_UEnv.uenv * iface *
        FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun ed ->
      let extend_iface lid mlp exp exp_binding =
        let fv =
          FStarC_Syntax_Syntax.lid_as_fv lid FStar_Pervasives_Native.None in
        let lb =
          {
            FStarC_Extraction_ML_Syntax.mllb_name =
              (FStar_Pervasives_Native.snd mlp);
            FStarC_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.None;
            FStarC_Extraction_ML_Syntax.mllb_add_unit = false;
            FStarC_Extraction_ML_Syntax.mllb_def = exp;
            FStarC_Extraction_ML_Syntax.mllb_attrs = [];
            FStarC_Extraction_ML_Syntax.mllb_meta = [];
            FStarC_Extraction_ML_Syntax.print_typ = false
          } in
        let uu___ =
          FStarC_Extraction_ML_Syntax.mk_mlmodule1
            (FStarC_Extraction_ML_Syntax.MLM_Let
               (FStarC_Extraction_ML_Syntax.NonRec, [lb])) in
        ((iface_of_bindings [(fv, exp_binding)]), uu___) in
      let rec extract_fv tm =
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_ExtractionReify in
         if uu___1
         then
           let uu___2 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
           FStarC_Compiler_Util.print1 "extract_fv term: %s\n" uu___2
         else ());
        (let uu___1 =
           let uu___2 = FStarC_Syntax_Subst.compress tm in
           uu___2.FStarC_Syntax_Syntax.n in
         match uu___1 with
         | FStarC_Syntax_Syntax.Tm_uinst (tm1, uu___2) -> extract_fv tm1
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStarC_Extraction_ML_UEnv.mlpath_of_lident g
                 (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
             let uu___2 =
               FStarC_Extraction_ML_UEnv.lookup_fv
                 tm.FStarC_Syntax_Syntax.pos g fv in
             (match uu___2 with
              | { FStarC_Extraction_ML_UEnv.exp_b_name = uu___3;
                  FStarC_Extraction_ML_UEnv.exp_b_expr = uu___4;
                  FStarC_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStarC_Extraction_ML_UEnv.exp_b_eff = uu___5;_} ->
                  let uu___6 =
                    FStarC_Extraction_ML_Syntax.with_ty
                      FStarC_Extraction_ML_Syntax.MLTY_Top
                      (FStarC_Extraction_ML_Syntax.MLE_Name mlp) in
                  (uu___6, tysc))
         | uu___2 ->
             let uu___3 =
               let uu___4 =
                 FStarC_Compiler_Range_Ops.string_of_range
                   tm.FStarC_Syntax_Syntax.pos in
               let uu___5 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
               FStarC_Compiler_Util.format2 "(%s) Not an fv: %s" uu___4
                 uu___5 in
             failwith uu___3) in
      let extract_action g1 a =
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_ExtractionReify in
         if uu___1
         then
           let uu___2 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
               a.FStarC_Syntax_Syntax.action_typ in
           let uu___3 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
               a.FStarC_Syntax_Syntax.action_defn in
           FStarC_Compiler_Util.print2 "Action type %s and term %s\n" uu___2
             uu___3
         else ());
        (let lbname =
           let uu___1 =
             FStarC_Syntax_Syntax.new_bv
               (FStar_Pervasives_Native.Some
                  ((a.FStarC_Syntax_Syntax.action_defn).FStarC_Syntax_Syntax.pos))
               FStarC_Syntax_Syntax.tun in
           FStar_Pervasives.Inl uu___1 in
         let lb =
           FStarC_Syntax_Syntax.mk_lb
             (lbname, (a.FStarC_Syntax_Syntax.action_univs),
               FStarC_Parser_Const.effect_Tot_lid,
               (a.FStarC_Syntax_Syntax.action_typ),
               (a.FStarC_Syntax_Syntax.action_defn), [],
               ((a.FStarC_Syntax_Syntax.action_defn).FStarC_Syntax_Syntax.pos)) in
         let lbs = (false, [lb]) in
         let action_lb =
           FStarC_Syntax_Syntax.mk
             (FStarC_Syntax_Syntax.Tm_let
                {
                  FStarC_Syntax_Syntax.lbs = lbs;
                  FStarC_Syntax_Syntax.body1 =
                    FStarC_Syntax_Util.exp_false_bool
                })
             (a.FStarC_Syntax_Syntax.action_defn).FStarC_Syntax_Syntax.pos in
         let uu___1 = FStarC_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
         match uu___1 with
         | (a_let, uu___2, ty) ->
             let uu___3 =
               match a_let.FStarC_Extraction_ML_Syntax.expr with
               | FStarC_Extraction_ML_Syntax.MLE_Let
                   ((uu___4, mllb::[]), uu___5) ->
                   (match mllb.FStarC_Extraction_ML_Syntax.mllb_tysc with
                    | FStar_Pervasives_Native.Some tysc ->
                        ((mllb.FStarC_Extraction_ML_Syntax.mllb_def), tysc)
                    | FStar_Pervasives_Native.None ->
                        failwith "No type scheme")
               | uu___4 -> failwith "Impossible" in
             (match uu___3 with
              | (exp, tysc) ->
                  let uu___4 =
                    FStarC_Extraction_ML_UEnv.extend_with_action_name g1 ed a
                      tysc in
                  (match uu___4 with
                   | (a_nm, a_lid, exp_b, g2) ->
                       ((let uu___6 =
                           FStarC_Compiler_Effect.op_Bang dbg_ExtractionReify in
                         if uu___6
                         then
                           let uu___7 =
                             FStarC_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStarC_Compiler_Util.print1
                             "Extracted action term: %s\n" uu___7
                         else ());
                        (let uu___7 =
                           FStarC_Compiler_Effect.op_Bang dbg_ExtractionReify in
                         if uu___7
                         then
                           ((let uu___9 =
                               FStarC_Extraction_ML_Code.string_of_mlty a_nm
                                 (FStar_Pervasives_Native.snd tysc) in
                             FStarC_Compiler_Util.print1
                               "Extracted action type: %s\n" uu___9);
                            (let uu___9 =
                               FStarC_Extraction_ML_Syntax.ty_param_names
                                 (FStar_Pervasives_Native.fst tysc) in
                             FStarC_Compiler_List.iter
                               (fun x ->
                                  FStarC_Compiler_Util.print1
                                    "and binders: %s\n" x) uu___9))
                         else ());
                        (let uu___7 = extend_iface a_lid a_nm exp exp_b in
                         match uu___7 with
                         | (iface1, impl) -> (g2, (iface1, impl))))))) in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Syntax_Util.get_return_repr ed in
              FStarC_Compiler_Util.must uu___4 in
            FStar_Pervasives_Native.snd uu___3 in
          extract_fv uu___2 in
        match uu___1 with
        | (return_tm, ty_sc) ->
            let uu___2 =
              FStarC_Extraction_ML_UEnv.extend_with_monad_op_name g ed
                "return" ty_sc in
            (match uu___2 with
             | (return_nm, return_lid, return_b, g1) ->
                 let uu___3 =
                   extend_iface return_lid return_nm return_tm return_b in
                 (match uu___3 with | (iface1, impl) -> (g1, iface1, impl))) in
      match uu___ with
      | (g1, return_iface, return_decl) ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Util.get_bind_repr ed in
                  FStarC_Compiler_Util.must uu___5 in
                FStar_Pervasives_Native.snd uu___4 in
              extract_fv uu___3 in
            match uu___2 with
            | (bind_tm, ty_sc) ->
                let uu___3 =
                  FStarC_Extraction_ML_UEnv.extend_with_monad_op_name g1 ed
                    "bind" ty_sc in
                (match uu___3 with
                 | (bind_nm, bind_lid, bind_b, g2) ->
                     let uu___4 =
                       extend_iface bind_lid bind_nm bind_tm bind_b in
                     (match uu___4 with
                      | (iface1, impl) -> (g2, iface1, impl))) in
          (match uu___1 with
           | (g2, bind_iface, bind_decl) ->
               let uu___2 =
                 FStarC_Compiler_Util.fold_map extract_action g2
                   ed.FStarC_Syntax_Syntax.actions in
               (match uu___2 with
                | (g3, actions) ->
                    let uu___3 = FStarC_Compiler_List.unzip actions in
                    (match uu___3 with
                     | (actions_iface, actions1) ->
                         let uu___4 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface) in
                         (g3, uu___4, (return_decl :: bind_decl :: actions1)))))
let (should_split_let_rec_types_and_terms :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.letbinding Prims.list -> Prims.bool)
  =
  fun env ->
    fun lbs ->
      let rec is_homogeneous out lbs1 =
        match lbs1 with
        | [] -> true
        | lb::lbs_tail ->
            let is_type =
              FStarC_Extraction_ML_Term.is_arity env
                lb.FStarC_Syntax_Syntax.lbtyp in
            (match out with
             | FStar_Pervasives_Native.None ->
                 is_homogeneous (FStar_Pervasives_Native.Some is_type)
                   lbs_tail
             | FStar_Pervasives_Native.Some b when b = is_type ->
                 is_homogeneous (FStar_Pervasives_Native.Some is_type)
                   lbs_tail
             | uu___ -> false) in
      let uu___ = is_homogeneous FStar_Pervasives_Native.None lbs in
      Prims.op_Negation uu___
let (split_let_rec_types_and_terms :
  FStarC_Syntax_Syntax.sigelt ->
    FStarC_Extraction_ML_UEnv.uenv ->
      FStarC_Syntax_Syntax.letbinding Prims.list ->
        FStarC_Syntax_Syntax.sigelt Prims.list)
  =
  fun se ->
    fun env ->
      fun lbs ->
        let rec aux out mutuals lbs1 =
          match lbs1 with
          | [] -> (out, mutuals)
          | lb::lbs_tail ->
              let uu___ = aux out mutuals lbs_tail in
              (match uu___ with
               | (out1, mutuals1) ->
                   let uu___1 =
                     let uu___2 =
                       FStarC_Extraction_ML_Term.is_arity env
                         lb.FStarC_Syntax_Syntax.lbtyp in
                     Prims.op_Negation uu___2 in
                   if uu___1
                   then (out1, (lb :: mutuals1))
                   else
                     (let uu___3 =
                        FStarC_Syntax_Util.abs_formals_maybe_unascribe_body
                          true lb.FStarC_Syntax_Syntax.lbdef in
                      match uu___3 with
                      | (formals, body, rc_opt) ->
                          let body1 =
                            FStarC_Syntax_Syntax.tconst
                              FStarC_Parser_Const.c_true_lid in
                          let lbdef =
                            FStarC_Syntax_Util.abs formals body1
                              FStar_Pervasives_Native.None in
                          let lb1 =
                            {
                              FStarC_Syntax_Syntax.lbname =
                                (lb.FStarC_Syntax_Syntax.lbname);
                              FStarC_Syntax_Syntax.lbunivs =
                                (lb.FStarC_Syntax_Syntax.lbunivs);
                              FStarC_Syntax_Syntax.lbtyp =
                                (lb.FStarC_Syntax_Syntax.lbtyp);
                              FStarC_Syntax_Syntax.lbeff =
                                (lb.FStarC_Syntax_Syntax.lbeff);
                              FStarC_Syntax_Syntax.lbdef = lbdef;
                              FStarC_Syntax_Syntax.lbattrs =
                                (lb.FStarC_Syntax_Syntax.lbattrs);
                              FStarC_Syntax_Syntax.lbpos =
                                (lb.FStarC_Syntax_Syntax.lbpos)
                            } in
                          let se1 =
                            {
                              FStarC_Syntax_Syntax.sigel =
                                (FStarC_Syntax_Syntax.Sig_let
                                   {
                                     FStarC_Syntax_Syntax.lbs1 =
                                       (false, [lb1]);
                                     FStarC_Syntax_Syntax.lids1 = []
                                   });
                              FStarC_Syntax_Syntax.sigrng =
                                (se.FStarC_Syntax_Syntax.sigrng);
                              FStarC_Syntax_Syntax.sigquals =
                                (se.FStarC_Syntax_Syntax.sigquals);
                              FStarC_Syntax_Syntax.sigmeta =
                                (se.FStarC_Syntax_Syntax.sigmeta);
                              FStarC_Syntax_Syntax.sigattrs =
                                (se.FStarC_Syntax_Syntax.sigattrs);
                              FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                              FStarC_Syntax_Syntax.sigopts =
                                (se.FStarC_Syntax_Syntax.sigopts)
                            } in
                          ((se1 :: out1), mutuals1))) in
        let uu___ = aux [] [] lbs in
        match uu___ with
        | (sigs, lbs1) ->
            let lb =
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStarC_Compiler_List.map
                      (fun lb1 ->
                         let uu___4 =
                           FStarC_Compiler_Util.right
                             lb1.FStarC_Syntax_Syntax.lbname in
                         FStarC_Syntax_Syntax.lid_of_fv uu___4) lbs1 in
                  {
                    FStarC_Syntax_Syntax.lbs1 = (true, lbs1);
                    FStarC_Syntax_Syntax.lids1 = uu___3
                  } in
                FStarC_Syntax_Syntax.Sig_let uu___2 in
              {
                FStarC_Syntax_Syntax.sigel = uu___1;
                FStarC_Syntax_Syntax.sigrng =
                  (se.FStarC_Syntax_Syntax.sigrng);
                FStarC_Syntax_Syntax.sigquals =
                  (se.FStarC_Syntax_Syntax.sigquals);
                FStarC_Syntax_Syntax.sigmeta =
                  (se.FStarC_Syntax_Syntax.sigmeta);
                FStarC_Syntax_Syntax.sigattrs =
                  (se.FStarC_Syntax_Syntax.sigattrs);
                FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                  (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                FStarC_Syntax_Syntax.sigopts =
                  (se.FStarC_Syntax_Syntax.sigopts)
              } in
            let sigs1 = FStarC_Compiler_List.op_At sigs [lb] in sigs1
let (extract_let_rec_types :
  FStarC_Syntax_Syntax.sigelt ->
    FStarC_Extraction_ML_UEnv.uenv ->
      FStarC_Syntax_Syntax.letbinding Prims.list ->
        (FStarC_Extraction_ML_UEnv.uenv * iface *
          FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun se ->
    fun env ->
      fun lbs ->
        let uu___ =
          FStarC_Compiler_Util.for_some
            (fun lb ->
               let uu___1 =
                 FStarC_Extraction_ML_Term.is_arity env
                   lb.FStarC_Syntax_Syntax.lbtyp in
               Prims.op_Negation uu___1) lbs in
        if uu___
        then failwith "Impossible: mixed mutual types and terms"
        else
          (let uu___2 =
             FStarC_Compiler_List.fold_left
               (fun uu___3 ->
                  fun lb ->
                    match uu___3 with
                    | (env1, iface_opt, impls) ->
                        let uu___4 =
                          extract_let_rec_type env1
                            se.FStarC_Syntax_Syntax.sigquals
                            se.FStarC_Syntax_Syntax.sigattrs lb in
                        (match uu___4 with
                         | (env2, iface1, impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu___5 = iface_union iface' iface1 in
                                   FStar_Pervasives_Native.Some uu___5 in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs in
           match uu___2 with
           | (env1, iface_opt, impls) ->
               let uu___3 = FStarC_Compiler_Option.get iface_opt in
               (env1, uu___3,
                 (FStarC_Compiler_List.flatten
                    (FStarC_Compiler_List.rev impls))))
let (get_noextract_to :
  FStarC_Syntax_Syntax.sigelt ->
    FStarC_Options.codegen_t FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun se ->
    fun backend ->
      FStarC_Compiler_Util.for_some
        (fun uu___ ->
           let uu___1 = FStarC_Syntax_Util.head_and_args uu___ in
           match uu___1 with
           | (hd, args) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Syntax_Subst.compress hd in
                   uu___4.FStarC_Syntax_Syntax.n in
                 (uu___3, args) in
               (match uu___2 with
                | (FStarC_Syntax_Syntax.Tm_fvar fv, (a, uu___3)::[]) when
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.noextract_to_attr
                    ->
                    let uu___4 =
                      FStarC_Syntax_Embeddings_Base.try_unembed
                        FStarC_Syntax_Embeddings.e_string a
                        FStarC_Syntax_Embeddings_Base.id_norm_cb in
                    (match uu___4 with
                     | FStar_Pervasives_Native.Some s ->
                         (FStarC_Compiler_Option.isSome backend) &&
                           (let uu___5 = FStarC_Options.parse_codegen s in
                            uu___5 = backend)
                     | FStar_Pervasives_Native.None -> false)
                | uu___3 -> false)) se.FStarC_Syntax_Syntax.sigattrs
let (sigelt_has_noextract : FStarC_Syntax_Syntax.sigelt -> Prims.bool) =
  fun se ->
    let has_noextract_qualifier =
      FStarC_Compiler_List.contains FStarC_Syntax_Syntax.NoExtract
        se.FStarC_Syntax_Syntax.sigquals in
    let has_noextract_attribute =
      let uu___ = FStarC_Options.codegen () in get_noextract_to se uu___ in
    let uu___ = FStarC_Options.codegen () in
    match uu___ with
    | FStar_Pervasives_Native.Some (FStarC_Options.Krml) ->
        has_noextract_qualifier && has_noextract_attribute
    | uu___1 -> has_noextract_qualifier || has_noextract_attribute
let (karamel_fixup_qual :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.sigelt) =
  fun se ->
    let uu___ =
      ((let uu___1 = FStarC_Options.codegen () in
        uu___1 = (FStar_Pervasives_Native.Some FStarC_Options.Krml)) &&
         (get_noextract_to se
            (FStar_Pervasives_Native.Some FStarC_Options.Krml)))
        &&
        (Prims.op_Negation
           (FStarC_Compiler_List.contains FStarC_Syntax_Syntax.NoExtract
              se.FStarC_Syntax_Syntax.sigquals)) in
    if uu___
    then
      {
        FStarC_Syntax_Syntax.sigel = (se.FStarC_Syntax_Syntax.sigel);
        FStarC_Syntax_Syntax.sigrng = (se.FStarC_Syntax_Syntax.sigrng);
        FStarC_Syntax_Syntax.sigquals = (FStarC_Syntax_Syntax.NoExtract ::
          (se.FStarC_Syntax_Syntax.sigquals));
        FStarC_Syntax_Syntax.sigmeta = (se.FStarC_Syntax_Syntax.sigmeta);
        FStarC_Syntax_Syntax.sigattrs = (se.FStarC_Syntax_Syntax.sigattrs);
        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
          (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
        FStarC_Syntax_Syntax.sigopts = (se.FStarC_Syntax_Syntax.sigopts)
      }
    else se
let (mark_sigelt_erased :
  FStarC_Syntax_Syntax.sigelt ->
    FStarC_Extraction_ML_UEnv.uenv -> FStarC_Extraction_ML_UEnv.uenv)
  =
  fun se ->
    fun g ->
      FStarC_Extraction_ML_UEnv.debug g
        (fun u ->
           let uu___1 = FStarC_Syntax_Print.sigelt_to_string_short se in
           FStarC_Compiler_Util.print1 ">>>> NOT extracting %s \n" uu___1);
      FStarC_Compiler_List.fold_right
        (fun lid ->
           fun g1 ->
             let uu___1 =
               FStarC_Syntax_Syntax.lid_as_fv lid
                 FStar_Pervasives_Native.None in
             FStarC_Extraction_ML_UEnv.extend_erased_fv g1 uu___1)
        (FStarC_Syntax_Util.lids_of_sigelt se) g
let (fixup_sigelt_extract_as :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.sigelt) =
  fun se ->
    let uu___ =
      let uu___1 =
        FStarC_Compiler_Util.find_map se.FStarC_Syntax_Syntax.sigattrs
          FStarC_TypeChecker_Normalize.is_extract_as_attr in
      ((se.FStarC_Syntax_Syntax.sigel), uu___1) in
    match uu___ with
    | (FStarC_Syntax_Syntax.Sig_let
       { FStarC_Syntax_Syntax.lbs1 = (uu___1, lb::[]);
         FStarC_Syntax_Syntax.lids1 = lids;_},
       FStar_Pervasives_Native.Some impl) ->
        {
          FStarC_Syntax_Syntax.sigel =
            (FStarC_Syntax_Syntax.Sig_let
               {
                 FStarC_Syntax_Syntax.lbs1 =
                   (true,
                     [{
                        FStarC_Syntax_Syntax.lbname =
                          (lb.FStarC_Syntax_Syntax.lbname);
                        FStarC_Syntax_Syntax.lbunivs =
                          (lb.FStarC_Syntax_Syntax.lbunivs);
                        FStarC_Syntax_Syntax.lbtyp =
                          (lb.FStarC_Syntax_Syntax.lbtyp);
                        FStarC_Syntax_Syntax.lbeff =
                          (lb.FStarC_Syntax_Syntax.lbeff);
                        FStarC_Syntax_Syntax.lbdef = impl;
                        FStarC_Syntax_Syntax.lbattrs =
                          (lb.FStarC_Syntax_Syntax.lbattrs);
                        FStarC_Syntax_Syntax.lbpos =
                          (lb.FStarC_Syntax_Syntax.lbpos)
                      }]);
                 FStarC_Syntax_Syntax.lids1 = lids
               });
          FStarC_Syntax_Syntax.sigrng = (se.FStarC_Syntax_Syntax.sigrng);
          FStarC_Syntax_Syntax.sigquals = (se.FStarC_Syntax_Syntax.sigquals);
          FStarC_Syntax_Syntax.sigmeta = (se.FStarC_Syntax_Syntax.sigmeta);
          FStarC_Syntax_Syntax.sigattrs = (se.FStarC_Syntax_Syntax.sigattrs);
          FStarC_Syntax_Syntax.sigopens_and_abbrevs =
            (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
          FStarC_Syntax_Syntax.sigopts = (se.FStarC_Syntax_Syntax.sigopts)
        }
    | uu___1 -> se
let rec (extract_sigelt_iface :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.sigelt -> (FStarC_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun se ->
      let uu___ = sigelt_has_noextract se in
      if uu___
      then let g1 = mark_sigelt_erased se g in (g1, empty_iface)
      else
        (let se1 = karamel_fixup_qual se in
         let se2 = fixup_sigelt_extract_as se1 in
         match se2.FStarC_Syntax_Syntax.sigel with
         | FStarC_Syntax_Syntax.Sig_bundle uu___2 ->
             extract_bundle_iface g se2
         | FStarC_Syntax_Syntax.Sig_inductive_typ uu___2 ->
             extract_bundle_iface g se2
         | FStarC_Syntax_Syntax.Sig_datacon uu___2 ->
             extract_bundle_iface g se2
         | FStarC_Syntax_Syntax.Sig_declare_typ
             { FStarC_Syntax_Syntax.lid2 = lid;
               FStarC_Syntax_Syntax.us2 = univs;
               FStarC_Syntax_Syntax.t2 = t;_}
             when FStarC_Extraction_ML_Term.is_arity g t ->
             let uu___2 =
               extract_type_declaration g true lid
                 se2.FStarC_Syntax_Syntax.sigquals
                 se2.FStarC_Syntax_Syntax.sigattrs univs t in
             (match uu___2 with | (env, iface1, uu___3) -> (env, iface1))
         | FStarC_Syntax_Syntax.Sig_let
             { FStarC_Syntax_Syntax.lbs1 = (false, lb::[]);
               FStarC_Syntax_Syntax.lids1 = uu___2;_}
             when
             FStarC_Extraction_ML_Term.is_arity g
               lb.FStarC_Syntax_Syntax.lbtyp
             ->
             let uu___3 =
               FStarC_Compiler_Util.for_some
                 (fun uu___4 ->
                    match uu___4 with
                    | FStarC_Syntax_Syntax.Projector uu___5 -> true
                    | uu___5 -> false) se2.FStarC_Syntax_Syntax.sigquals in
             if uu___3
             then (g, empty_iface)
             else
               (let uu___5 =
                  extract_typ_abbrev g se2.FStarC_Syntax_Syntax.sigquals
                    se2.FStarC_Syntax_Syntax.sigattrs lb in
                match uu___5 with | (env, iface1, uu___6) -> (env, iface1))
         | FStarC_Syntax_Syntax.Sig_let
             { FStarC_Syntax_Syntax.lbs1 = (true, lbs);
               FStarC_Syntax_Syntax.lids1 = uu___2;_}
             when should_split_let_rec_types_and_terms g lbs ->
             let ses = split_let_rec_types_and_terms se2 g lbs in
             let iface1 =
               let uu___3 =
                 FStarC_Extraction_ML_UEnv.current_module_of_uenv g in
               {
                 iface_module_name = uu___3;
                 iface_bindings = (empty_iface.iface_bindings);
                 iface_tydefs = (empty_iface.iface_tydefs);
                 iface_type_names = (empty_iface.iface_type_names)
               } in
             FStarC_Compiler_List.fold_left
               (fun uu___3 ->
                  fun se3 ->
                    match uu___3 with
                    | (g1, out) ->
                        let uu___4 = extract_sigelt_iface g1 se3 in
                        (match uu___4 with
                         | (g2, mls) ->
                             let uu___5 = iface_union out mls in (g2, uu___5)))
               (g, iface1) ses
         | FStarC_Syntax_Syntax.Sig_let
             { FStarC_Syntax_Syntax.lbs1 = (true, lbs);
               FStarC_Syntax_Syntax.lids1 = uu___2;_}
             when
             FStarC_Compiler_Util.for_some
               (fun lb ->
                  FStarC_Extraction_ML_Term.is_arity g
                    lb.FStarC_Syntax_Syntax.lbtyp) lbs
             ->
             let uu___3 = extract_let_rec_types se2 g lbs in
             (match uu___3 with | (env, iface1, uu___4) -> (env, iface1))
         | FStarC_Syntax_Syntax.Sig_declare_typ
             { FStarC_Syntax_Syntax.lid2 = lid;
               FStarC_Syntax_Syntax.us2 = uu___2;
               FStarC_Syntax_Syntax.t2 = t;_}
             ->
             let quals = se2.FStarC_Syntax_Syntax.sigquals in
             let uu___3 =
               (FStarC_Compiler_List.contains FStarC_Syntax_Syntax.Assumption
                  quals)
                 &&
                 (let uu___4 =
                    let uu___5 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStarC_TypeChecker_Util.must_erase_for_extraction uu___5
                      t in
                  Prims.op_Negation uu___4) in
             if uu___3
             then
               let uu___4 =
                 let uu___5 =
                   let uu___6 = let uu___7 = always_fail lid t in [uu___7] in
                   (false, uu___6) in
                 FStarC_Extraction_ML_Term.extract_lb_iface g uu___5 in
               (match uu___4 with
                | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
             else (g, empty_iface)
         | FStarC_Syntax_Syntax.Sig_let
             { FStarC_Syntax_Syntax.lbs1 = (false, lb::[]);
               FStarC_Syntax_Syntax.lids1 = uu___2;_}
             when
             Prims.uu___is_Cons
               (se2.FStarC_Syntax_Syntax.sigmeta).FStarC_Syntax_Syntax.sigmeta_extension_data
             ->
             let uu___3 =
               FStarC_Compiler_List.tryPick
                 (fun uu___4 ->
                    match uu___4 with
                    | (ext, blob) ->
                        let uu___5 = lookup_extension_extractor ext in
                        (match uu___5 with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some extractor ->
                             FStar_Pervasives_Native.Some
                               (ext, blob, extractor)))
                 (se2.FStarC_Syntax_Syntax.sigmeta).FStarC_Syntax_Syntax.sigmeta_extension_data in
             (match uu___3 with
              | FStar_Pervasives_Native.None ->
                  let uu___4 =
                    FStarC_Extraction_ML_Term.extract_lb_iface g
                      (false, [lb]) in
                  (match uu___4 with
                   | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
              | FStar_Pervasives_Native.Some (ext, blob, extractor) ->
                  let res = extractor.extract_sigelt_iface g se2 blob in
                  (match res with
                   | FStar_Pervasives.Inl res1 -> res1
                   | FStar_Pervasives.Inr err ->
                       let uu___4 =
                         FStarC_Compiler_Util.format2
                           "Extension %s failed to extract iface: %s" ext err in
                       FStarC_Errors.raise_error
                         FStarC_Syntax_Syntax.has_range_sigelt se2
                         FStarC_Errors_Codes.Fatal_ExtractionUnsupported ()
                         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                         (Obj.magic uu___4)))
         | FStarC_Syntax_Syntax.Sig_let
             { FStarC_Syntax_Syntax.lbs1 = lbs;
               FStarC_Syntax_Syntax.lids1 = uu___2;_}
             ->
             let uu___3 = FStarC_Extraction_ML_Term.extract_lb_iface g lbs in
             (match uu___3 with
              | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
         | FStarC_Syntax_Syntax.Sig_assume uu___2 -> (g, empty_iface)
         | FStarC_Syntax_Syntax.Sig_sub_effect uu___2 -> (g, empty_iface)
         | FStarC_Syntax_Syntax.Sig_effect_abbrev uu___2 -> (g, empty_iface)
         | FStarC_Syntax_Syntax.Sig_polymonadic_bind uu___2 ->
             (g, empty_iface)
         | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp uu___2 ->
             (g, empty_iface)
         | FStarC_Syntax_Syntax.Sig_pragma p ->
             (FStarC_Syntax_Util.process_pragma p
                se2.FStarC_Syntax_Syntax.sigrng;
              (g, empty_iface))
         | FStarC_Syntax_Syntax.Sig_splice uu___2 ->
             failwith "impossible: trying to extract splice"
         | FStarC_Syntax_Syntax.Sig_fail uu___2 ->
             failwith "impossible: trying to extract Sig_fail"
         | FStarC_Syntax_Syntax.Sig_new_effect ed ->
             let uu___2 =
               (let uu___3 =
                  let uu___4 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
                  FStarC_TypeChecker_Util.effect_extraction_mode uu___4
                    ed.FStarC_Syntax_Syntax.mname in
                uu___3 = FStarC_Syntax_Syntax.Extract_reify) &&
                 (FStarC_Compiler_List.isEmpty
                    ed.FStarC_Syntax_Syntax.binders) in
             if uu___2
             then
               let uu___3 = extract_reifiable_effect g ed in
               (match uu___3 with | (env, iface1, uu___4) -> (env, iface1))
             else (g, empty_iface))
let (extract_iface' :
  env_t ->
    FStarC_Syntax_Syntax.modul -> (FStarC_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu___ = FStarC_Options.interactive () in
      if uu___
      then (g, empty_iface)
      else
        (let uu___2 = FStarC_Options.restore_cmd_line_options true in
         let decls = modul.FStarC_Syntax_Syntax.declarations in
         let iface1 =
           let uu___3 = FStarC_Extraction_ML_UEnv.current_module_of_uenv g in
           {
             iface_module_name = uu___3;
             iface_bindings = (empty_iface.iface_bindings);
             iface_tydefs = (empty_iface.iface_tydefs);
             iface_type_names = (empty_iface.iface_type_names)
           } in
         let res =
           FStarC_Compiler_List.fold_left
             (fun uu___3 ->
                fun se ->
                  match uu___3 with
                  | (g1, iface2) ->
                      let uu___4 = extract_sigelt_iface g1 se in
                      (match uu___4 with
                       | (g2, iface') ->
                           let uu___5 = iface_union iface2 iface' in
                           (g2, uu___5))) (g, iface1) decls in
         (let uu___4 = FStarC_Options.restore_cmd_line_options true in ());
         res)
let (extract_iface :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.modul -> (FStarC_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu___ =
        FStarC_Syntax_Unionfind.with_uf_enabled
          (fun uu___1 ->
             let uu___2 = FStarC_Compiler_Debug.any () in
             if uu___2
             then
               let uu___3 =
                 let uu___4 =
                   FStarC_Ident.string_of_lid modul.FStarC_Syntax_Syntax.name in
                 FStarC_Compiler_Util.format1 "Extracted interface of %s"
                   uu___4 in
               FStarC_Compiler_Util.measure_execution_time uu___3
                 (fun uu___4 -> extract_iface' g modul)
             else extract_iface' g modul) in
      match uu___ with
      | (g1, iface1) ->
          let uu___1 =
            FStarC_Extraction_ML_UEnv.with_typars_env g1
              (fun e ->
                 let iface_tydefs =
                   FStarC_Compiler_List.map
                     (fun uu___2 ->
                        match uu___2 with
                        | FStar_Pervasives.Inl td ->
                            let uu___3 =
                              let uu___4 =
                                FStarC_Extraction_ML_UEnv.tydef_mlpath td in
                              FStar_Pervasives_Native.snd uu___4 in
                            let uu___4 =
                              FStarC_Extraction_ML_UEnv.tydef_meta td in
                            let uu___5 =
                              let uu___6 =
                                FStarC_Extraction_ML_UEnv.tydef_def td in
                              FStar_Pervasives.Inl uu___6 in
                            (uu___3, uu___4, uu___5)
                        | FStar_Pervasives.Inr (p, m, n) ->
                            (p, m, (FStar_Pervasives.Inr n)))
                     iface1.iface_tydefs in
                 let uu___2 =
                   FStarC_Extraction_ML_UEnv.extend_with_module_name g1
                     modul.FStarC_Syntax_Syntax.name in
                 match uu___2 with
                 | (module_name, uu___3) ->
                     let e1 =
                       FStarC_Extraction_ML_RemoveUnusedParameters.set_current_module
                         e module_name in
                     FStarC_Extraction_ML_RemoveUnusedParameters.elim_tydefs
                       e1 iface_tydefs) in
          (match uu___1 with
           | (g2, uu___2) ->
               let uu___3 = FStarC_Extraction_ML_UEnv.exit_module g2 in
               (uu___3, iface1))
let (extract_bundle :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.sigelt ->
      (FStarC_Extraction_ML_UEnv.uenv * FStarC_Extraction_ML_Syntax.mlmodule1
        Prims.list))
  =
  fun env ->
    fun se ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu___ =
            FStarC_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStarC_Extraction_ML_Util.eraseTypeDeep
            (FStarC_Extraction_ML_Util.udelta_unfold env_iparams) uu___ in
        let steps =
          [FStarC_TypeChecker_Env.Inlining;
          FStarC_TypeChecker_Env.UnfoldUntil
            FStarC_Syntax_Syntax.delta_constant;
          FStarC_TypeChecker_Env.EraseUniverses;
          FStarC_TypeChecker_Env.AllowUnboundUniverses;
          FStarC_TypeChecker_Env.ForExtraction] in
        let names =
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStarC_Extraction_ML_UEnv.tcenv_of_uenv env_iparams in
                FStarC_TypeChecker_Normalize.normalize steps uu___3 ctor.dtyp in
              FStarC_Syntax_Subst.compress uu___2 in
            uu___1.FStarC_Syntax_Syntax.n in
          match uu___ with
          | FStarC_Syntax_Syntax.Tm_arrow
              { FStarC_Syntax_Syntax.bs1 = bs;
                FStarC_Syntax_Syntax.comp = uu___1;_}
              ->
              FStarC_Compiler_List.map
                (fun uu___2 ->
                   match uu___2 with
                   | {
                       FStarC_Syntax_Syntax.binder_bv =
                         { FStarC_Syntax_Syntax.ppname = ppname;
                           FStarC_Syntax_Syntax.index = uu___3;
                           FStarC_Syntax_Syntax.sort = uu___4;_};
                       FStarC_Syntax_Syntax.binder_qual = uu___5;
                       FStarC_Syntax_Syntax.binder_positivity = uu___6;
                       FStarC_Syntax_Syntax.binder_attrs = uu___7;_} ->
                       FStarC_Ident.string_of_id ppname) bs
          | uu___1 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv =
          FStarC_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Pervasives_Native.None in
        let uu___ = FStarC_Extraction_ML_UEnv.extend_fv env1 fvv tys false in
        match uu___ with
        | (env2, mls, uu___1) ->
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_Extraction_ML_Util.argTypes mlt in
                FStarC_Compiler_List.zip names uu___4 in
              (mls, uu___3) in
            (env2, uu___2) in
      let extract_one_family env1 ind =
        let uu___ = binders_as_mlty_binders env1 ind.iparams in
        match uu___ with
        | (env_iparams, vars) ->
            let uu___1 =
              FStarC_Compiler_Util.fold_map (extract_ctor env_iparams vars)
                env1 ind.idatas in
            (match uu___1 with
             | (env2, ctors) ->
                 let uu___2 = FStarC_Syntax_Util.arrow_formals ind.ityp in
                 (match uu___2 with
                  | (indices, uu___3) ->
                      let ml_params =
                        let uu___4 =
                          FStarC_Compiler_List.mapi
                            (fun i ->
                               fun uu___5 ->
                                 let uu___6 =
                                   let uu___7 =
                                     FStarC_Compiler_Util.string_of_int i in
                                   Prims.strcat "'dummyV" uu___7 in
                                 {
                                   FStarC_Extraction_ML_Syntax.ty_param_name
                                     = uu___6;
                                   FStarC_Extraction_ML_Syntax.ty_param_attrs
                                     = []
                                 }) indices in
                        FStarC_Compiler_List.append vars uu___4 in
                      let uu___4 =
                        let uu___5 =
                          FStarC_Compiler_Util.find_opt
                            (fun uu___6 ->
                               match uu___6 with
                               | FStarC_Syntax_Syntax.RecordType uu___7 ->
                                   true
                               | uu___7 -> false) ind.iquals in
                        match uu___5 with
                        | FStar_Pervasives_Native.Some
                            (FStarC_Syntax_Syntax.RecordType (ns, ids)) ->
                            let uu___6 = FStarC_Compiler_List.hd ctors in
                            (match uu___6 with
                             | (uu___7, c_ty) ->
                                 let uu___8 =
                                   FStarC_Compiler_List.fold_right2
                                     (fun id ->
                                        fun uu___9 ->
                                          fun uu___10 ->
                                            match (uu___9, uu___10) with
                                            | ((uu___11, ty), (fields, g)) ->
                                                let uu___12 =
                                                  FStarC_Extraction_ML_UEnv.extend_record_field_name
                                                    g ((ind.iname), id) in
                                                (match uu___12 with
                                                 | (mlid, g1) ->
                                                     (((mlid, ty) :: fields),
                                                       g1))) ids c_ty
                                     ([], env2) in
                                 (match uu___8 with
                                  | (fields, g) ->
                                      ((FStar_Pervasives_Native.Some
                                          (FStarC_Extraction_ML_Syntax.MLTD_Record
                                             fields)), g)))
                        | uu___6 when
                            (FStarC_Compiler_List.length ctors) =
                              Prims.int_zero
                            -> (FStar_Pervasives_Native.None, env2)
                        | uu___6 ->
                            ((FStar_Pervasives_Native.Some
                                (FStarC_Extraction_ML_Syntax.MLTD_DType ctors)),
                              env2) in
                      (match uu___4 with
                       | (tbody, env3) ->
                           let td =
                             let uu___5 =
                               let uu___6 =
                                 FStarC_Extraction_ML_UEnv.mlpath_of_lident
                                   env3 ind.iname in
                               FStar_Pervasives_Native.snd uu___6 in
                             {
                               FStarC_Extraction_ML_Syntax.tydecl_assumed =
                                 false;
                               FStarC_Extraction_ML_Syntax.tydecl_name =
                                 uu___5;
                               FStarC_Extraction_ML_Syntax.tydecl_ignored =
                                 FStar_Pervasives_Native.None;
                               FStarC_Extraction_ML_Syntax.tydecl_parameters
                                 = ml_params;
                               FStarC_Extraction_ML_Syntax.tydecl_meta =
                                 (ind.imetadata);
                               FStarC_Extraction_ML_Syntax.tydecl_defn =
                                 tbody
                             } in
                           (env3, td)))) in
      let mlattrs = extract_attrs env se.FStarC_Syntax_Syntax.sigattrs in
      match ((se.FStarC_Syntax_Syntax.sigel),
              (se.FStarC_Syntax_Syntax.sigquals))
      with
      | (FStarC_Syntax_Syntax.Sig_bundle
         {
           FStarC_Syntax_Syntax.ses =
             {
               FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
                 { FStarC_Syntax_Syntax.lid1 = l;
                   FStarC_Syntax_Syntax.us1 = uu___;
                   FStarC_Syntax_Syntax.t1 = t;
                   FStarC_Syntax_Syntax.ty_lid = uu___1;
                   FStarC_Syntax_Syntax.num_ty_params = uu___2;
                   FStarC_Syntax_Syntax.mutuals1 = uu___3;
                   FStarC_Syntax_Syntax.injective_type_params1 = uu___4;_};
               FStarC_Syntax_Syntax.sigrng = uu___5;
               FStarC_Syntax_Syntax.sigquals = uu___6;
               FStarC_Syntax_Syntax.sigmeta = uu___7;
               FStarC_Syntax_Syntax.sigattrs = uu___8;
               FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
               FStarC_Syntax_Syntax.sigopts = uu___10;_}::[];
           FStarC_Syntax_Syntax.lids = uu___11;_},
         (FStarC_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu___12 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu___12 with
           | (env1, ctor) ->
               let uu___13 =
                 let uu___14 =
                   FStarC_Extraction_ML_Syntax.mk_mlmodule1_with_attrs
                     (FStarC_Extraction_ML_Syntax.MLM_Exn ctor) mlattrs in
                 [uu___14] in
               (env1, uu___13))
      | (FStarC_Syntax_Syntax.Sig_bundle
         { FStarC_Syntax_Syntax.ses = ses;
           FStarC_Syntax_Syntax.lids = uu___;_},
         quals) ->
          let uu___1 =
            FStarC_Syntax_Util.has_attribute se.FStarC_Syntax_Syntax.sigattrs
              FStarC_Parser_Const.erasable_attr in
          if uu___1
          then (env, [])
          else
            (let uu___3 = bundle_as_inductive_families env ses quals in
             match uu___3 with
             | (env1, ifams) ->
                 let uu___4 =
                   FStarC_Compiler_Util.fold_map extract_one_family env1
                     ifams in
                 (match uu___4 with
                  | (env2, td) ->
                      let uu___5 =
                        let uu___6 =
                          FStarC_Extraction_ML_Syntax.mk_mlmodule1_with_attrs
                            (FStarC_Extraction_ML_Syntax.MLM_Ty td) mlattrs in
                        [uu___6] in
                      (env2, uu___5)))
      | uu___ -> failwith "Unexpected signature element"
let (lb_is_irrelevant :
  env_t -> FStarC_Syntax_Syntax.letbinding -> Prims.bool) =
  fun g ->
    fun lb ->
      ((let uu___ = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
        FStarC_TypeChecker_Env.non_informative uu___
          lb.FStarC_Syntax_Syntax.lbtyp)
         &&
         (let uu___ =
            FStarC_Extraction_ML_Term.is_arity g
              lb.FStarC_Syntax_Syntax.lbtyp in
          Prims.op_Negation uu___))
        &&
        (FStarC_Syntax_Util.is_pure_or_ghost_effect
           lb.FStarC_Syntax_Syntax.lbeff)
let (lb_is_tactic : env_t -> FStarC_Syntax_Syntax.letbinding -> Prims.bool) =
  fun g ->
    fun lb ->
      let uu___ =
        FStarC_Syntax_Util.is_pure_effect lb.FStarC_Syntax_Syntax.lbeff in
      if uu___
      then
        let uu___1 =
          FStarC_Syntax_Util.arrow_formals_comp_ln
            lb.FStarC_Syntax_Syntax.lbtyp in
        match uu___1 with
        | (bs, c) ->
            let c_eff_name =
              let uu___2 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
              FStarC_TypeChecker_Env.norm_eff_name uu___2
                (FStarC_Syntax_Util.comp_effect_name c) in
            FStarC_Ident.lid_equals c_eff_name
              FStarC_Parser_Const.effect_TAC_lid
      else false
let rec (extract_sig :
  env_t ->
    FStarC_Syntax_Syntax.sigelt ->
      (env_t * FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun se ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Print.sigelt_to_string_short se in
        FStarC_Compiler_Util.format1
          "While extracting top-level definition `%s`" uu___1 in
      FStarC_Errors.with_ctx uu___
        (fun uu___1 ->
           FStarC_Extraction_ML_UEnv.debug g
             (fun u ->
                let uu___3 = FStarC_Syntax_Print.sigelt_to_string_short se in
                FStarC_Compiler_Util.print1 ">>>> extract_sig %s \n" uu___3);
           (let uu___3 = sigelt_has_noextract se in
            if uu___3
            then let g1 = mark_sigelt_erased se g in (g1, [])
            else
              (let se1 = karamel_fixup_qual se in
               let se2 = fixup_sigelt_extract_as se1 in
               match se2.FStarC_Syntax_Syntax.sigel with
               | FStarC_Syntax_Syntax.Sig_bundle uu___5 ->
                   let uu___6 = extract_bundle g se2 in
                   (match uu___6 with
                    | (g1, ses) ->
                        let uu___7 =
                          let uu___8 =
                            FStarC_Extraction_ML_RegEmb.maybe_register_plugin
                              g1 se2 in
                          FStarC_Compiler_List.op_At ses uu___8 in
                        (g1, uu___7))
               | FStarC_Syntax_Syntax.Sig_inductive_typ uu___5 ->
                   let uu___6 = extract_bundle g se2 in
                   (match uu___6 with
                    | (g1, ses) ->
                        let uu___7 =
                          let uu___8 =
                            FStarC_Extraction_ML_RegEmb.maybe_register_plugin
                              g1 se2 in
                          FStarC_Compiler_List.op_At ses uu___8 in
                        (g1, uu___7))
               | FStarC_Syntax_Syntax.Sig_datacon uu___5 ->
                   let uu___6 = extract_bundle g se2 in
                   (match uu___6 with
                    | (g1, ses) ->
                        let uu___7 =
                          let uu___8 =
                            FStarC_Extraction_ML_RegEmb.maybe_register_plugin
                              g1 se2 in
                          FStarC_Compiler_List.op_At ses uu___8 in
                        (g1, uu___7))
               | FStarC_Syntax_Syntax.Sig_new_effect ed when
                   let uu___5 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
                   FStarC_TypeChecker_Env.is_reifiable_effect uu___5
                     ed.FStarC_Syntax_Syntax.mname
                   ->
                   let uu___5 = extract_reifiable_effect g ed in
                   (match uu___5 with | (env, _iface, impl) -> (env, impl))
               | FStarC_Syntax_Syntax.Sig_splice uu___5 ->
                   failwith "impossible: trying to extract splice"
               | FStarC_Syntax_Syntax.Sig_fail uu___5 ->
                   failwith "impossible: trying to extract Sig_fail"
               | FStarC_Syntax_Syntax.Sig_new_effect uu___5 -> (g, [])
               | FStarC_Syntax_Syntax.Sig_let
                   { FStarC_Syntax_Syntax.lbs1 = (uu___5, lbs);
                     FStarC_Syntax_Syntax.lids1 = uu___6;_}
                   when FStarC_Compiler_List.for_all (lb_is_irrelevant g) lbs
                   -> (g, [])
               | FStarC_Syntax_Syntax.Sig_let
                   { FStarC_Syntax_Syntax.lbs1 = (uu___5, lbs);
                     FStarC_Syntax_Syntax.lids1 = uu___6;_}
                   when
                   (let uu___7 = FStarC_Options.codegen () in
                    uu___7 <>
                      (FStar_Pervasives_Native.Some FStarC_Options.Plugin))
                     && (FStarC_Compiler_List.for_all (lb_is_tactic g) lbs)
                   -> (g, [])
               | FStarC_Syntax_Syntax.Sig_declare_typ
                   { FStarC_Syntax_Syntax.lid2 = lid;
                     FStarC_Syntax_Syntax.us2 = univs;
                     FStarC_Syntax_Syntax.t2 = t;_}
                   when FStarC_Extraction_ML_Term.is_arity g t ->
                   let uu___5 =
                     extract_type_declaration g false lid
                       se2.FStarC_Syntax_Syntax.sigquals
                       se2.FStarC_Syntax_Syntax.sigattrs univs t in
                   (match uu___5 with | (env, uu___6, impl) -> (env, impl))
               | FStarC_Syntax_Syntax.Sig_let
                   { FStarC_Syntax_Syntax.lbs1 = (false, lb::[]);
                     FStarC_Syntax_Syntax.lids1 = uu___5;_}
                   when
                   FStarC_Extraction_ML_Term.is_arity g
                     lb.FStarC_Syntax_Syntax.lbtyp
                   ->
                   let uu___6 =
                     FStarC_Compiler_Util.for_some
                       (fun uu___7 ->
                          match uu___7 with
                          | FStarC_Syntax_Syntax.Projector uu___8 -> true
                          | uu___8 -> false)
                       se2.FStarC_Syntax_Syntax.sigquals in
                   if uu___6
                   then (g, [])
                   else
                     (let uu___8 =
                        extract_typ_abbrev g
                          se2.FStarC_Syntax_Syntax.sigquals
                          se2.FStarC_Syntax_Syntax.sigattrs lb in
                      match uu___8 with | (env, uu___9, impl) -> (env, impl))
               | FStarC_Syntax_Syntax.Sig_let
                   { FStarC_Syntax_Syntax.lbs1 = (true, lbs);
                     FStarC_Syntax_Syntax.lids1 = uu___5;_}
                   when should_split_let_rec_types_and_terms g lbs ->
                   let ses = split_let_rec_types_and_terms se2 g lbs in
                   FStarC_Compiler_List.fold_left
                     (fun uu___6 ->
                        fun se3 ->
                          match uu___6 with
                          | (g1, out) ->
                              let uu___7 = extract_sig g1 se3 in
                              (match uu___7 with
                               | (g2, mls) ->
                                   (g2, (FStarC_Compiler_List.op_At out mls))))
                     (g, []) ses
               | FStarC_Syntax_Syntax.Sig_let
                   { FStarC_Syntax_Syntax.lbs1 = (true, lbs);
                     FStarC_Syntax_Syntax.lids1 = uu___5;_}
                   when
                   FStarC_Compiler_Util.for_some
                     (fun lb ->
                        FStarC_Extraction_ML_Term.is_arity g
                          lb.FStarC_Syntax_Syntax.lbtyp) lbs
                   ->
                   let uu___6 = extract_let_rec_types se2 g lbs in
                   (match uu___6 with | (env, uu___7, impl) -> (env, impl))
               | FStarC_Syntax_Syntax.Sig_let
                   { FStarC_Syntax_Syntax.lbs1 = (false, lb::[]);
                     FStarC_Syntax_Syntax.lids1 = uu___5;_}
                   when
                   Prims.uu___is_Cons
                     (se2.FStarC_Syntax_Syntax.sigmeta).FStarC_Syntax_Syntax.sigmeta_extension_data
                   ->
                   let uu___6 =
                     FStarC_Compiler_List.tryPick
                       (fun uu___7 ->
                          match uu___7 with
                          | (ext, blob) ->
                              let uu___8 = lookup_extension_extractor ext in
                              (match uu___8 with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some extractor ->
                                   FStar_Pervasives_Native.Some
                                     (ext, blob, extractor)))
                       (se2.FStarC_Syntax_Syntax.sigmeta).FStarC_Syntax_Syntax.sigmeta_extension_data in
                   (match uu___6 with
                    | FStar_Pervasives_Native.None -> extract_sig_let g se2
                    | FStar_Pervasives_Native.Some (ext, blob, extractor) ->
                        let uu___7 = extractor.extract_sigelt g se2 blob in
                        (match uu___7 with
                         | FStar_Pervasives.Inl decls ->
                             let meta =
                               extract_metadata
                                 se2.FStarC_Syntax_Syntax.sigattrs in
                             let mlattrs =
                               extract_attrs g
                                 se2.FStarC_Syntax_Syntax.sigattrs in
                             FStarC_Compiler_List.fold_left
                               (fun uu___8 ->
                                  fun d ->
                                    match uu___8 with
                                    | (g1, decls1) ->
                                        (match d.FStarC_Extraction_ML_Syntax.mlmodule1_m
                                         with
                                         | FStarC_Extraction_ML_Syntax.MLM_Let
                                             (maybe_rec, mllb::[]) ->
                                             let uu___9 =
                                               let uu___10 =
                                                 FStarC_Compiler_Util.must
                                                   mllb.FStarC_Extraction_ML_Syntax.mllb_tysc in
                                               FStarC_Extraction_ML_UEnv.extend_lb
                                                 g1
                                                 lb.FStarC_Syntax_Syntax.lbname
                                                 lb.FStarC_Syntax_Syntax.lbtyp
                                                 uu___10
                                                 mllb.FStarC_Extraction_ML_Syntax.mllb_add_unit in
                                             (match uu___9 with
                                              | (g2, mlid, uu___10) ->
                                                  let mllb1 =
                                                    {
                                                      FStarC_Extraction_ML_Syntax.mllb_name
                                                        = mlid;
                                                      FStarC_Extraction_ML_Syntax.mllb_tysc
                                                        =
                                                        (mllb.FStarC_Extraction_ML_Syntax.mllb_tysc);
                                                      FStarC_Extraction_ML_Syntax.mllb_add_unit
                                                        =
                                                        (mllb.FStarC_Extraction_ML_Syntax.mllb_add_unit);
                                                      FStarC_Extraction_ML_Syntax.mllb_def
                                                        =
                                                        (mllb.FStarC_Extraction_ML_Syntax.mllb_def);
                                                      FStarC_Extraction_ML_Syntax.mllb_attrs
                                                        = mlattrs;
                                                      FStarC_Extraction_ML_Syntax.mllb_meta
                                                        = meta;
                                                      FStarC_Extraction_ML_Syntax.print_typ
                                                        =
                                                        (mllb.FStarC_Extraction_ML_Syntax.print_typ)
                                                    } in
                                                  let uu___11 =
                                                    let uu___12 =
                                                      let uu___13 =
                                                        FStarC_Extraction_ML_Syntax.mk_mlmodule1_with_attrs
                                                          (FStarC_Extraction_ML_Syntax.MLM_Let
                                                             (maybe_rec,
                                                               [mllb1]))
                                                          mlattrs in
                                                      [uu___13] in
                                                    FStarC_Compiler_List.op_At
                                                      decls1 uu___12 in
                                                  (g2, uu___11))
                                         | uu___9 ->
                                             let uu___10 =
                                               let uu___11 =
                                                 FStarC_Class_Show.show
                                                   FStarC_Extraction_ML_Syntax.showable_mlmodule1
                                                   d in
                                               FStarC_Compiler_Util.format1
                                                 "Unexpected ML decl returned by the extension: %s"
                                                 uu___11 in
                                             failwith uu___10)) (g, []) decls
                         | FStar_Pervasives.Inr err ->
                             let uu___8 =
                               FStarC_Compiler_Util.format2
                                 "Extension %s failed to extract term: %s"
                                 ext err in
                             FStarC_Errors.raise_error
                               FStarC_Syntax_Syntax.has_range_sigelt se2
                               FStarC_Errors_Codes.Fatal_ExtractionUnsupported
                               ()
                               (Obj.magic
                                  FStarC_Errors_Msg.is_error_message_string)
                               (Obj.magic uu___8)))
               | FStarC_Syntax_Syntax.Sig_let uu___5 -> extract_sig_let g se2
               | FStarC_Syntax_Syntax.Sig_declare_typ
                   { FStarC_Syntax_Syntax.lid2 = lid;
                     FStarC_Syntax_Syntax.us2 = uu___5;
                     FStarC_Syntax_Syntax.t2 = t;_}
                   ->
                   let quals = se2.FStarC_Syntax_Syntax.sigquals in
                   let uu___6 =
                     (FStarC_Compiler_List.contains
                        FStarC_Syntax_Syntax.Assumption quals)
                       &&
                       (let uu___7 =
                          let uu___8 =
                            FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
                          FStarC_TypeChecker_Util.must_erase_for_extraction
                            uu___8 t in
                        Prims.op_Negation uu___7) in
                   if uu___6
                   then
                     let always_fail1 =
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               let uu___11 = always_fail lid t in [uu___11] in
                             (false, uu___10) in
                           {
                             FStarC_Syntax_Syntax.lbs1 = uu___9;
                             FStarC_Syntax_Syntax.lids1 = []
                           } in
                         FStarC_Syntax_Syntax.Sig_let uu___8 in
                       {
                         FStarC_Syntax_Syntax.sigel = uu___7;
                         FStarC_Syntax_Syntax.sigrng =
                           (se2.FStarC_Syntax_Syntax.sigrng);
                         FStarC_Syntax_Syntax.sigquals =
                           (se2.FStarC_Syntax_Syntax.sigquals);
                         FStarC_Syntax_Syntax.sigmeta =
                           (se2.FStarC_Syntax_Syntax.sigmeta);
                         FStarC_Syntax_Syntax.sigattrs =
                           (se2.FStarC_Syntax_Syntax.sigattrs);
                         FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                           (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                         FStarC_Syntax_Syntax.sigopts =
                           (se2.FStarC_Syntax_Syntax.sigopts)
                       } in
                     let uu___7 = extract_sig g always_fail1 in
                     (match uu___7 with
                      | (g1, mlm) ->
                          let uu___8 =
                            FStarC_Compiler_Util.find_map quals
                              (fun uu___9 ->
                                 match uu___9 with
                                 | FStarC_Syntax_Syntax.Discriminator l ->
                                     FStar_Pervasives_Native.Some l
                                 | uu___10 -> FStar_Pervasives_Native.None) in
                          (match uu___8 with
                           | FStar_Pervasives_Native.Some l ->
                               let uu___9 =
                                 let uu___10 =
                                   let uu___11 =
                                     let uu___12 =
                                       FStarC_Extraction_ML_Util.mlloc_of_range
                                         se2.FStarC_Syntax_Syntax.sigrng in
                                     FStarC_Extraction_ML_Syntax.MLM_Loc
                                       uu___12 in
                                   FStarC_Extraction_ML_Syntax.mk_mlmodule1
                                     uu___11 in
                                 let uu___11 =
                                   let uu___12 =
                                     FStarC_Extraction_ML_Term.ind_discriminator_body
                                       g1 lid l in
                                   [uu___12] in
                                 uu___10 :: uu___11 in
                               (g1, uu___9)
                           | uu___9 ->
                               let uu___10 =
                                 FStarC_Compiler_Util.find_map quals
                                   (fun uu___11 ->
                                      match uu___11 with
                                      | FStarC_Syntax_Syntax.Projector
                                          (l, uu___12) ->
                                          FStar_Pervasives_Native.Some l
                                      | uu___12 ->
                                          FStar_Pervasives_Native.None) in
                               (match uu___10 with
                                | FStar_Pervasives_Native.Some uu___11 ->
                                    (g1, [])
                                | uu___11 -> (g1, mlm))))
                   else (g, [])
               | FStarC_Syntax_Syntax.Sig_assume uu___5 -> (g, [])
               | FStarC_Syntax_Syntax.Sig_sub_effect uu___5 -> (g, [])
               | FStarC_Syntax_Syntax.Sig_effect_abbrev uu___5 -> (g, [])
               | FStarC_Syntax_Syntax.Sig_polymonadic_bind uu___5 -> (g, [])
               | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp uu___5 ->
                   (g, [])
               | FStarC_Syntax_Syntax.Sig_pragma p ->
                   (FStarC_Syntax_Util.process_pragma p
                      se2.FStarC_Syntax_Syntax.sigrng;
                    (g, [])))))
and (extract_sig_let :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.sigelt ->
      (FStarC_Extraction_ML_UEnv.uenv * FStarC_Extraction_ML_Syntax.mlmodule1
        Prims.list))
  =
  fun g ->
    fun se ->
      if
        Prims.op_Negation
          (FStarC_Syntax_Syntax.uu___is_Sig_let se.FStarC_Syntax_Syntax.sigel)
      then failwith "Impossible: should only be called with Sig_let"
      else
        (let uu___1 = se.FStarC_Syntax_Syntax.sigel in
         match uu___1 with
         | FStarC_Syntax_Syntax.Sig_let
             { FStarC_Syntax_Syntax.lbs1 = lbs;
               FStarC_Syntax_Syntax.lids1 = uu___2;_}
             ->
             let attrs = se.FStarC_Syntax_Syntax.sigattrs in
             let quals = se.FStarC_Syntax_Syntax.sigquals in
             let maybe_postprocess_lbs lbs1 =
               let post_tau =
                 let uu___3 =
                   FStarC_Syntax_Util.extract_attr'
                     FStarC_Parser_Const.postprocess_extr_with attrs in
                 match uu___3 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some
                     (uu___4, (tau, FStar_Pervasives_Native.None)::uu___5) ->
                     FStar_Pervasives_Native.Some tau
                 | FStar_Pervasives_Native.Some uu___4 ->
                     (FStarC_Errors.log_issue
                        FStarC_Syntax_Syntax.has_range_sigelt se
                        FStarC_Errors_Codes.Warning_UnrecognizedAttribute ()
                        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                        (Obj.magic
                           "Ill-formed application of 'postprocess_for_extraction_with'");
                      FStar_Pervasives_Native.None) in
               let postprocess_lb tau lb =
                 let env = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
                 let lbdef =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStarC_TypeChecker_Env.current_module env in
                       FStarC_Ident.string_of_lid uu___5 in
                     FStar_Pervasives_Native.Some uu___4 in
                   FStarC_Profiling.profile
                     (fun uu___4 ->
                        FStarC_TypeChecker_Env.postprocess env tau
                          lb.FStarC_Syntax_Syntax.lbtyp
                          lb.FStarC_Syntax_Syntax.lbdef) uu___3
                     "FStarC.Extraction.ML.Module.post_process_for_extraction" in
                 {
                   FStarC_Syntax_Syntax.lbname =
                     (lb.FStarC_Syntax_Syntax.lbname);
                   FStarC_Syntax_Syntax.lbunivs =
                     (lb.FStarC_Syntax_Syntax.lbunivs);
                   FStarC_Syntax_Syntax.lbtyp =
                     (lb.FStarC_Syntax_Syntax.lbtyp);
                   FStarC_Syntax_Syntax.lbeff =
                     (lb.FStarC_Syntax_Syntax.lbeff);
                   FStarC_Syntax_Syntax.lbdef = lbdef;
                   FStarC_Syntax_Syntax.lbattrs =
                     (lb.FStarC_Syntax_Syntax.lbattrs);
                   FStarC_Syntax_Syntax.lbpos =
                     (lb.FStarC_Syntax_Syntax.lbpos)
                 } in
               match post_tau with
               | FStar_Pervasives_Native.None -> lbs1
               | FStar_Pervasives_Native.Some tau ->
                   let uu___3 =
                     FStarC_Compiler_List.map (postprocess_lb tau)
                       (FStar_Pervasives_Native.snd lbs1) in
                   ((FStar_Pervasives_Native.fst lbs1), uu___3) in
             let maybe_normalize_for_extraction lbs1 =
               let norm_steps =
                 let uu___3 =
                   FStarC_Syntax_Util.extract_attr'
                     FStarC_Parser_Const.normalize_for_extraction_lid attrs in
                 match uu___3 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some
                     (uu___4, (steps, FStar_Pervasives_Native.None)::uu___5)
                     ->
                     let steps1 =
                       let uu___6 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
                       FStarC_TypeChecker_Normalize.normalize
                         [FStarC_TypeChecker_Env.UnfoldUntil
                            FStarC_Syntax_Syntax.delta_constant;
                         FStarC_TypeChecker_Env.Zeta;
                         FStarC_TypeChecker_Env.Iota;
                         FStarC_TypeChecker_Env.Primops] uu___6 steps in
                     let uu___6 =
                       FStarC_TypeChecker_Primops_Base.try_unembed_simple
                         (FStarC_Syntax_Embeddings.e_list
                            FStarC_Syntax_Embeddings.e_norm_step) steps1 in
                     (match uu___6 with
                      | FStar_Pervasives_Native.Some steps2 ->
                          let uu___7 =
                            FStarC_TypeChecker_Cfg.translate_norm_steps
                              steps2 in
                          FStar_Pervasives_Native.Some uu___7
                      | uu___7 ->
                          ((let uu___9 =
                              let uu___10 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term steps1 in
                              FStarC_Compiler_Util.format1
                                "Ill-formed application of 'normalize_for_extraction': normalization steps '%s' could not be interpreted"
                                uu___10 in
                            FStarC_Errors.log_issue
                              FStarC_Syntax_Syntax.has_range_sigelt se
                              FStarC_Errors_Codes.Warning_UnrecognizedAttribute
                              ()
                              (Obj.magic
                                 FStarC_Errors_Msg.is_error_message_string)
                              (Obj.magic uu___9));
                           FStar_Pervasives_Native.None))
                 | FStar_Pervasives_Native.Some uu___4 ->
                     (FStarC_Errors.log_issue
                        FStarC_Syntax_Syntax.has_range_sigelt se
                        FStarC_Errors_Codes.Warning_UnrecognizedAttribute ()
                        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                        (Obj.magic
                           "Ill-formed application of 'normalize_for_extraction'");
                      FStar_Pervasives_Native.None) in
               let norm_one_lb steps lb =
                 let env = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g in
                 let env1 =
                   {
                     FStarC_TypeChecker_Env.solver =
                       (env.FStarC_TypeChecker_Env.solver);
                     FStarC_TypeChecker_Env.range =
                       (env.FStarC_TypeChecker_Env.range);
                     FStarC_TypeChecker_Env.curmodule =
                       (env.FStarC_TypeChecker_Env.curmodule);
                     FStarC_TypeChecker_Env.gamma =
                       (env.FStarC_TypeChecker_Env.gamma);
                     FStarC_TypeChecker_Env.gamma_sig =
                       (env.FStarC_TypeChecker_Env.gamma_sig);
                     FStarC_TypeChecker_Env.gamma_cache =
                       (env.FStarC_TypeChecker_Env.gamma_cache);
                     FStarC_TypeChecker_Env.modules =
                       (env.FStarC_TypeChecker_Env.modules);
                     FStarC_TypeChecker_Env.expected_typ =
                       (env.FStarC_TypeChecker_Env.expected_typ);
                     FStarC_TypeChecker_Env.sigtab =
                       (env.FStarC_TypeChecker_Env.sigtab);
                     FStarC_TypeChecker_Env.attrtab =
                       (env.FStarC_TypeChecker_Env.attrtab);
                     FStarC_TypeChecker_Env.instantiate_imp =
                       (env.FStarC_TypeChecker_Env.instantiate_imp);
                     FStarC_TypeChecker_Env.effects =
                       (env.FStarC_TypeChecker_Env.effects);
                     FStarC_TypeChecker_Env.generalize =
                       (env.FStarC_TypeChecker_Env.generalize);
                     FStarC_TypeChecker_Env.letrecs =
                       (env.FStarC_TypeChecker_Env.letrecs);
                     FStarC_TypeChecker_Env.top_level =
                       (env.FStarC_TypeChecker_Env.top_level);
                     FStarC_TypeChecker_Env.check_uvars =
                       (env.FStarC_TypeChecker_Env.check_uvars);
                     FStarC_TypeChecker_Env.use_eq_strict =
                       (env.FStarC_TypeChecker_Env.use_eq_strict);
                     FStarC_TypeChecker_Env.is_iface =
                       (env.FStarC_TypeChecker_Env.is_iface);
                     FStarC_TypeChecker_Env.admit =
                       (env.FStarC_TypeChecker_Env.admit);
                     FStarC_TypeChecker_Env.lax_universes =
                       (env.FStarC_TypeChecker_Env.lax_universes);
                     FStarC_TypeChecker_Env.phase1 =
                       (env.FStarC_TypeChecker_Env.phase1);
                     FStarC_TypeChecker_Env.failhard =
                       (env.FStarC_TypeChecker_Env.failhard);
                     FStarC_TypeChecker_Env.flychecking =
                       (env.FStarC_TypeChecker_Env.flychecking);
                     FStarC_TypeChecker_Env.uvar_subtyping =
                       (env.FStarC_TypeChecker_Env.uvar_subtyping);
                     FStarC_TypeChecker_Env.intactics =
                       (env.FStarC_TypeChecker_Env.intactics);
                     FStarC_TypeChecker_Env.nocoerce =
                       (env.FStarC_TypeChecker_Env.nocoerce);
                     FStarC_TypeChecker_Env.tc_term =
                       (env.FStarC_TypeChecker_Env.tc_term);
                     FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                       (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.universe_of =
                       (env.FStarC_TypeChecker_Env.universe_of);
                     FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                       =
                       (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.teq_nosmt_force =
                       (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                     FStarC_TypeChecker_Env.subtype_nosmt_force =
                       (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                     FStarC_TypeChecker_Env.qtbl_name_and_index =
                       (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                     FStarC_TypeChecker_Env.normalized_eff_names =
                       (env.FStarC_TypeChecker_Env.normalized_eff_names);
                     FStarC_TypeChecker_Env.fv_delta_depths =
                       (env.FStarC_TypeChecker_Env.fv_delta_depths);
                     FStarC_TypeChecker_Env.proof_ns =
                       (env.FStarC_TypeChecker_Env.proof_ns);
                     FStarC_TypeChecker_Env.synth_hook =
                       (env.FStarC_TypeChecker_Env.synth_hook);
                     FStarC_TypeChecker_Env.try_solve_implicits_hook =
                       (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                     FStarC_TypeChecker_Env.splice =
                       (env.FStarC_TypeChecker_Env.splice);
                     FStarC_TypeChecker_Env.mpreprocess =
                       (env.FStarC_TypeChecker_Env.mpreprocess);
                     FStarC_TypeChecker_Env.postprocess =
                       (env.FStarC_TypeChecker_Env.postprocess);
                     FStarC_TypeChecker_Env.identifier_info =
                       (env.FStarC_TypeChecker_Env.identifier_info);
                     FStarC_TypeChecker_Env.tc_hooks =
                       (env.FStarC_TypeChecker_Env.tc_hooks);
                     FStarC_TypeChecker_Env.dsenv =
                       (env.FStarC_TypeChecker_Env.dsenv);
                     FStarC_TypeChecker_Env.nbe =
                       (env.FStarC_TypeChecker_Env.nbe);
                     FStarC_TypeChecker_Env.strict_args_tab =
                       (env.FStarC_TypeChecker_Env.strict_args_tab);
                     FStarC_TypeChecker_Env.erasable_types_tab =
                       (env.FStarC_TypeChecker_Env.erasable_types_tab);
                     FStarC_TypeChecker_Env.enable_defer_to_tac =
                       (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                     FStarC_TypeChecker_Env.unif_allow_ref_guards =
                       (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                     FStarC_TypeChecker_Env.erase_erasable_args = true;
                     FStarC_TypeChecker_Env.core_check =
                       (env.FStarC_TypeChecker_Env.core_check);
                     FStarC_TypeChecker_Env.missing_decl =
                       (env.FStarC_TypeChecker_Env.missing_decl)
                   } in
                 let lbd =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_TypeChecker_Env.current_module env1 in
                       FStarC_Ident.string_of_lid uu___5 in
                     FStar_Pervasives_Native.Some uu___4 in
                   FStarC_Profiling.profile
                     (fun uu___4 ->
                        FStarC_TypeChecker_Normalize.normalize steps env1
                          lb.FStarC_Syntax_Syntax.lbdef) uu___3
                     "FStarC.Extraction.ML.Module.normalize_for_extraction" in
                 {
                   FStarC_Syntax_Syntax.lbname =
                     (lb.FStarC_Syntax_Syntax.lbname);
                   FStarC_Syntax_Syntax.lbunivs =
                     (lb.FStarC_Syntax_Syntax.lbunivs);
                   FStarC_Syntax_Syntax.lbtyp =
                     (lb.FStarC_Syntax_Syntax.lbtyp);
                   FStarC_Syntax_Syntax.lbeff =
                     (lb.FStarC_Syntax_Syntax.lbeff);
                   FStarC_Syntax_Syntax.lbdef = lbd;
                   FStarC_Syntax_Syntax.lbattrs =
                     (lb.FStarC_Syntax_Syntax.lbattrs);
                   FStarC_Syntax_Syntax.lbpos =
                     (lb.FStarC_Syntax_Syntax.lbpos)
                 } in
               match norm_steps with
               | FStar_Pervasives_Native.None -> lbs1
               | FStar_Pervasives_Native.Some steps ->
                   let uu___3 =
                     FStarC_Compiler_List.map (norm_one_lb steps)
                       (FStar_Pervasives_Native.snd lbs1) in
                   ((FStar_Pervasives_Native.fst lbs1), uu___3) in
             let uu___3 =
               let lbs1 =
                 let uu___4 = maybe_postprocess_lbs lbs in
                 maybe_normalize_for_extraction uu___4 in
               let uu___4 =
                 FStarC_Syntax_Syntax.mk
                   (FStarC_Syntax_Syntax.Tm_let
                      {
                        FStarC_Syntax_Syntax.lbs = lbs1;
                        FStarC_Syntax_Syntax.body1 =
                          FStarC_Syntax_Util.exp_false_bool
                      }) se.FStarC_Syntax_Syntax.sigrng in
               FStarC_Extraction_ML_Term.term_as_mlexpr g uu___4 in
             (match uu___3 with
              | (ml_let, uu___4, uu___5) ->
                  let mlattrs =
                    extract_attrs g se.FStarC_Syntax_Syntax.sigattrs in
                  (match ml_let.FStarC_Extraction_ML_Syntax.expr with
                   | FStarC_Extraction_ML_Syntax.MLE_Let
                       ((flavor, bindings), uu___6) ->
                       let flags =
                         FStarC_Compiler_List.choose flag_of_qual quals in
                       let flags' = extract_metadata attrs in
                       let uu___7 =
                         FStarC_Compiler_List.fold_left2
                           (fun uu___8 ->
                              fun ml_lb ->
                                fun uu___9 ->
                                  match (uu___8, uu___9) with
                                  | ((env, ml_lbs),
                                     { FStarC_Syntax_Syntax.lbname = lbname;
                                       FStarC_Syntax_Syntax.lbunivs = uu___10;
                                       FStarC_Syntax_Syntax.lbtyp = t;
                                       FStarC_Syntax_Syntax.lbeff = uu___11;
                                       FStarC_Syntax_Syntax.lbdef = uu___12;
                                       FStarC_Syntax_Syntax.lbattrs = uu___13;
                                       FStarC_Syntax_Syntax.lbpos = uu___14;_})
                                      ->
                                      if
                                        FStarC_Compiler_List.contains
                                          FStarC_Extraction_ML_Syntax.Erased
                                          ml_lb.FStarC_Extraction_ML_Syntax.mllb_meta
                                      then (env, ml_lbs)
                                      else
                                        (let lb_lid =
                                           let uu___16 =
                                             let uu___17 =
                                               FStarC_Compiler_Util.right
                                                 lbname in
                                             uu___17.FStarC_Syntax_Syntax.fv_name in
                                           uu___16.FStarC_Syntax_Syntax.v in
                                         let flags'' =
                                           let uu___16 =
                                             let uu___17 =
                                               FStarC_Syntax_Subst.compress t in
                                             uu___17.FStarC_Syntax_Syntax.n in
                                           match uu___16 with
                                           | FStarC_Syntax_Syntax.Tm_arrow
                                               {
                                                 FStarC_Syntax_Syntax.bs1 =
                                                   uu___17;
                                                 FStarC_Syntax_Syntax.comp =
                                                   {
                                                     FStarC_Syntax_Syntax.n =
                                                       FStarC_Syntax_Syntax.Comp
                                                       {
                                                         FStarC_Syntax_Syntax.comp_univs
                                                           = uu___18;
                                                         FStarC_Syntax_Syntax.effect_name
                                                           = e;
                                                         FStarC_Syntax_Syntax.result_typ
                                                           = uu___19;
                                                         FStarC_Syntax_Syntax.effect_args
                                                           = uu___20;
                                                         FStarC_Syntax_Syntax.flags
                                                           = uu___21;_};
                                                     FStarC_Syntax_Syntax.pos
                                                       = uu___22;
                                                     FStarC_Syntax_Syntax.vars
                                                       = uu___23;
                                                     FStarC_Syntax_Syntax.hash_code
                                                       = uu___24;_};_}
                                               when
                                               let uu___25 =
                                                 FStarC_Ident.string_of_lid e in
                                               uu___25 =
                                                 "FStar.HyperStack.ST.StackInline"
                                               ->
                                               [FStarC_Extraction_ML_Syntax.StackInline]
                                           | uu___17 -> [] in
                                         let meta =
                                           FStarC_Compiler_List.op_At flags
                                             (FStarC_Compiler_List.op_At
                                                flags' flags'') in
                                         let ml_lb1 =
                                           {
                                             FStarC_Extraction_ML_Syntax.mllb_name
                                               =
                                               (ml_lb.FStarC_Extraction_ML_Syntax.mllb_name);
                                             FStarC_Extraction_ML_Syntax.mllb_tysc
                                               =
                                               (ml_lb.FStarC_Extraction_ML_Syntax.mllb_tysc);
                                             FStarC_Extraction_ML_Syntax.mllb_add_unit
                                               =
                                               (ml_lb.FStarC_Extraction_ML_Syntax.mllb_add_unit);
                                             FStarC_Extraction_ML_Syntax.mllb_def
                                               =
                                               (ml_lb.FStarC_Extraction_ML_Syntax.mllb_def);
                                             FStarC_Extraction_ML_Syntax.mllb_attrs
                                               = mlattrs;
                                             FStarC_Extraction_ML_Syntax.mllb_meta
                                               = meta;
                                             FStarC_Extraction_ML_Syntax.print_typ
                                               =
                                               (ml_lb.FStarC_Extraction_ML_Syntax.print_typ)
                                           } in
                                         let uu___16 =
                                           let uu___17 =
                                             FStarC_Compiler_Util.for_some
                                               (fun uu___18 ->
                                                  match uu___18 with
                                                  | FStarC_Syntax_Syntax.Projector
                                                      uu___19 -> true
                                                  | uu___19 -> false) quals in
                                           if uu___17
                                           then
                                             let uu___18 =
                                               let uu___19 =
                                                 FStarC_Compiler_Util.right
                                                   lbname in
                                               let uu___20 =
                                                 FStarC_Compiler_Util.must
                                                   ml_lb1.FStarC_Extraction_ML_Syntax.mllb_tysc in
                                               FStarC_Extraction_ML_UEnv.extend_fv
                                                 env uu___19 uu___20
                                                 ml_lb1.FStarC_Extraction_ML_Syntax.mllb_add_unit in
                                             match uu___18 with
                                             | (env1, mls, uu___19) ->
                                                 (env1,
                                                   {
                                                     FStarC_Extraction_ML_Syntax.mllb_name
                                                       = mls;
                                                     FStarC_Extraction_ML_Syntax.mllb_tysc
                                                       =
                                                       (ml_lb1.FStarC_Extraction_ML_Syntax.mllb_tysc);
                                                     FStarC_Extraction_ML_Syntax.mllb_add_unit
                                                       =
                                                       (ml_lb1.FStarC_Extraction_ML_Syntax.mllb_add_unit);
                                                     FStarC_Extraction_ML_Syntax.mllb_def
                                                       =
                                                       (ml_lb1.FStarC_Extraction_ML_Syntax.mllb_def);
                                                     FStarC_Extraction_ML_Syntax.mllb_attrs
                                                       =
                                                       (ml_lb1.FStarC_Extraction_ML_Syntax.mllb_attrs);
                                                     FStarC_Extraction_ML_Syntax.mllb_meta
                                                       =
                                                       (ml_lb1.FStarC_Extraction_ML_Syntax.mllb_meta);
                                                     FStarC_Extraction_ML_Syntax.print_typ
                                                       =
                                                       (ml_lb1.FStarC_Extraction_ML_Syntax.print_typ)
                                                   })
                                           else
                                             (let uu___19 =
                                                let uu___20 =
                                                  FStarC_Compiler_Util.must
                                                    ml_lb1.FStarC_Extraction_ML_Syntax.mllb_tysc in
                                                FStarC_Extraction_ML_UEnv.extend_lb
                                                  env lbname t uu___20
                                                  ml_lb1.FStarC_Extraction_ML_Syntax.mllb_add_unit in
                                              match uu___19 with
                                              | (env1, uu___20, uu___21) ->
                                                  (env1, ml_lb1)) in
                                         match uu___16 with
                                         | (g1, ml_lb2) ->
                                             (g1, (ml_lb2 :: ml_lbs))))
                           (g, []) bindings (FStar_Pervasives_Native.snd lbs) in
                       (match uu___7 with
                        | (g1, ml_lbs') ->
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      FStarC_Extraction_ML_Util.mlloc_of_range
                                        se.FStarC_Syntax_Syntax.sigrng in
                                    FStarC_Extraction_ML_Syntax.MLM_Loc
                                      uu___12 in
                                  FStarC_Extraction_ML_Syntax.mk_mlmodule1
                                    uu___11 in
                                let uu___11 =
                                  let uu___12 =
                                    FStarC_Extraction_ML_Syntax.mk_mlmodule1_with_attrs
                                      (FStarC_Extraction_ML_Syntax.MLM_Let
                                         (flavor,
                                           (FStarC_Compiler_List.rev ml_lbs')))
                                      mlattrs in
                                  [uu___12] in
                                uu___10 :: uu___11 in
                              let uu___10 =
                                FStarC_Extraction_ML_RegEmb.maybe_register_plugin
                                  g1 se in
                              FStarC_Compiler_List.op_At uu___9 uu___10 in
                            (g1, uu___8))
                   | uu___6 ->
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             FStarC_Extraction_ML_UEnv.current_module_of_uenv
                               g in
                           FStarC_Extraction_ML_Code.string_of_mlexpr uu___9
                             ml_let in
                         FStarC_Compiler_Util.format1
                           "Impossible: Translated a let to a non-let: %s"
                           uu___8 in
                       failwith uu___7)))
let (extract' :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.modul ->
      (FStarC_Extraction_ML_UEnv.uenv * FStarC_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      let uu___ = FStarC_Options.restore_cmd_line_options true in
      let uu___1 =
        FStarC_Extraction_ML_UEnv.extend_with_module_name g
          m.FStarC_Syntax_Syntax.name in
      match uu___1 with
      | (name, g1) ->
          let g2 =
            let uu___2 =
              let uu___3 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv g1 in
              FStarC_TypeChecker_Env.set_current_module uu___3
                m.FStarC_Syntax_Syntax.name in
            FStarC_Extraction_ML_UEnv.set_tcenv g1 uu___2 in
          let g3 = FStarC_Extraction_ML_UEnv.set_current_module g2 name in
          let uu___2 =
            FStarC_Compiler_Util.fold_map
              (fun g4 ->
                 fun se ->
                   let uu___3 = FStarC_Compiler_Debug.any () in
                   if uu___3
                   then
                     let nm =
                       let uu___4 =
                         FStarC_Compiler_List.map FStarC_Ident.string_of_lid
                           (FStarC_Syntax_Util.lids_of_sigelt se) in
                       FStarC_Compiler_String.concat ", " uu___4 in
                     (FStarC_Compiler_Util.print1
                        "+++About to extract {%s}\n" nm;
                      (let r =
                         let uu___5 =
                           FStarC_Compiler_Util.format1 "---Extracted {%s}"
                             nm in
                         FStarC_Compiler_Util.measure_execution_time uu___5
                           (fun uu___6 -> extract_sig g4 se) in
                       (let uu___6 =
                          FStarC_Class_Show.show
                            FStarC_Extraction_ML_Syntax.showable_mlmodule
                            (FStar_Pervasives_Native.snd r) in
                        FStarC_Compiler_Util.print1 "Extraction result: %s\n"
                          uu___6);
                       r))
                   else extract_sig g4 se) g3
              m.FStarC_Syntax_Syntax.declarations in
          (match uu___2 with
           | (g4, sigs) ->
               let mlm = FStarC_Compiler_List.flatten sigs in
               let is_karamel =
                 let uu___3 = FStarC_Options.codegen () in
                 uu___3 = (FStar_Pervasives_Native.Some FStarC_Options.Krml) in
               let uu___3 =
                 (let uu___4 =
                    FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
                  uu___4 <> "Prims") &&
                   (is_karamel ||
                      (Prims.op_Negation m.FStarC_Syntax_Syntax.is_interface)) in
               if uu___3
               then
                 ((let uu___5 =
                     let uu___6 = FStarC_Options.silent () in
                     Prims.op_Negation uu___6 in
                   if uu___5
                   then
                     let uu___6 =
                       FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
                     FStarC_Compiler_Util.print1 "Extracted module %s\n"
                       uu___6
                   else ());
                  (g4,
                    (FStar_Pervasives_Native.Some
                       (FStarC_Extraction_ML_Syntax.MLLib
                          [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                             (FStarC_Extraction_ML_Syntax.MLLib []))]))))
               else (g4, FStar_Pervasives_Native.None))
let (extract :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.modul ->
      (FStarC_Extraction_ML_UEnv.uenv * FStarC_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      (let uu___1 = FStarC_Options.restore_cmd_line_options true in ());
      (let tgt =
         let uu___1 = FStarC_Options.codegen () in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             failwith "Impossible: We're in extract, codegen must be set!"
         | FStar_Pervasives_Native.Some t -> t in
       (let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
            FStarC_Options.should_extract uu___4 tgt in
          Prims.op_Negation uu___3 in
        if uu___2
        then
          let uu___3 =
            let uu___4 =
              FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
            FStarC_Compiler_Util.format1
              "Extract called on a module %s that should not be extracted"
              uu___4 in
          failwith uu___3
        else ());
       (let uu___2 = FStarC_Options.interactive () in
        if uu___2
        then (g, FStar_Pervasives_Native.None)
        else
          (let nm = FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
           let uu___4 =
             FStarC_Syntax_Unionfind.with_uf_enabled
               (fun uu___5 ->
                  FStarC_Errors.with_ctx
                    (Prims.strcat "While extracting module " nm)
                    (fun uu___6 ->
                       FStarC_Profiling.profile (fun uu___7 -> extract' g m)
                         (FStar_Pervasives_Native.Some nm)
                         "FStarC.Extraction.ML.Modul.extract")) in
           match uu___4 with
           | (g1, mllib) ->
               let uu___5 =
                 match mllib with
                 | FStar_Pervasives_Native.None -> (g1, mllib)
                 | FStar_Pervasives_Native.Some mllib1 ->
                     let uu___6 =
                       FStarC_Extraction_ML_UEnv.with_typars_env g1
                         (fun e ->
                            FStarC_Extraction_ML_RemoveUnusedParameters.elim_mllib
                              e mllib1) in
                     (match uu___6 with
                      | (g2, mllib2) ->
                          (g2, (FStar_Pervasives_Native.Some mllib2))) in
               (match uu___5 with
                | (g2, mllib1) ->
                    ((let uu___7 =
                        FStarC_Options.restore_cmd_line_options true in
                      ());
                     (let uu___7 = FStarC_Extraction_ML_UEnv.exit_module g2 in
                      (uu___7, mllib1)))))))
open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          let uu___3 =
            let uu___4 = FStar_Syntax_Syntax.iarg t in
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 =
                          let uu___12 = FStar_Syntax_Print.lid_to_string lid in
                          Prims.op_Hat "Not yet implemented:" uu___12 in
                        (uu___11, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu___10 in
                    FStar_Syntax_Syntax.Tm_constant uu___9 in
                  FStar_Syntax_Syntax.mk uu___8 FStar_Range.dummyRange in
                FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu___7 in
              [uu___6] in
            uu___4 :: uu___5 in
          (uu___2, uu___3) in
        FStar_Syntax_Syntax.Tm_app uu___1 in
      FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid ->
    fun t ->
      let imp =
        let uu___ = FStar_Syntax_Util.arrow_formals t in
        match uu___ with
        | ([], t1) ->
            let b =
              let uu___1 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu___1 in
            let uu___1 = fail_exp lid t1 in
            FStar_Syntax_Util.abs [b] uu___1 FStar_Pervasives_Native.None
        | (bs, t1) ->
            let uu___1 = fail_exp lid t1 in
            FStar_Syntax_Util.abs bs uu___1 FStar_Pervasives_Native.None in
      let lb =
        let uu___ =
          let uu___1 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Pervasives.Inr uu___1 in
        {
          FStar_Syntax_Syntax.lbname = uu___;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid;
          FStar_Syntax_Syntax.lbdef = imp;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = (imp.FStar_Syntax_Syntax.pos)
        } in
      lb
let as_pair : 'uuuuu . 'uuuuu Prims.list -> ('uuuuu * 'uuuuu) =
  fun uu___ ->
    match uu___ with
    | a::b::[] -> (a, b)
    | uu___1 -> failwith "Expected a list with 2 elements"
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Assumption ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu___1 -> FStar_Pervasives_Native.None
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x ->
    let uu___ = FStar_Syntax_Subst.compress x in
    match uu___ with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu___1;
        FStar_Syntax_Syntax.vars = uu___2;_} ->
        let uu___3 =
          let uu___4 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu___4 in
        (match uu___3 with
         | "FStar.Pervasives.PpxDerivingShow" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingShow
         | "FStar.Pervasives.PpxDerivingYoJson" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingYoJson
         | "FStar.Pervasives.CInline" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
         | "FStar.Pervasives.Substitute" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.Substitute
         | "FStar.Pervasives.Gc" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
         | "FStar.Pervasives.CAbstractStruct" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.CAbstract
         | "FStar.Pervasives.CIfDef" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CIfDef
         | "FStar.Pervasives.CMacro" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CMacro
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated "")
         | uu___4 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu___1;
             FStar_Syntax_Syntax.vars = uu___2;_},
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, uu___3));
              FStar_Syntax_Syntax.pos = uu___4;
              FStar_Syntax_Syntax.vars = uu___5;_},
            uu___6)::[]);
        FStar_Syntax_Syntax.pos = uu___7;
        FStar_Syntax_Syntax.vars = uu___8;_} ->
        let uu___9 =
          let uu___10 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu___10 in
        (match uu___9 with
         | "FStar.Pervasives.PpxDerivingShowConstant" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
         | "FStar.Pervasives.Comment" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Comment s)
         | "FStar.Pervasives.CPrologue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CPrologue s)
         | "FStar.Pervasives.CEpilogue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CEpilogue s)
         | "FStar.Pervasives.CConst" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CConst s)
         | "FStar.Pervasives.CCConv" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CCConv s)
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated s)
         | uu___10 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate", uu___1));
        FStar_Syntax_Syntax.pos = uu___2;
        FStar_Syntax_Syntax.vars = uu___3;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline", uu___1));
        FStar_Syntax_Syntax.pos = uu___2;
        FStar_Syntax_Syntax.vars = uu___3;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute", uu___1));
        FStar_Syntax_Syntax.pos = uu___2;
        FStar_Syntax_Syntax.vars = uu___3;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu___1);
        FStar_Syntax_Syntax.pos = uu___2;
        FStar_Syntax_Syntax.vars = uu___3;_} -> extract_meta x1
    | uu___1 ->
        let uu___2 = FStar_Syntax_Util.head_and_args x in
        (match uu___2 with
         | (head, args) ->
             let uu___3 =
               let uu___4 =
                 let uu___5 = FStar_Syntax_Subst.compress head in
                 uu___5.FStar_Syntax_Syntax.n in
               (uu___4, args) in
             (match uu___3 with
              | (FStar_Syntax_Syntax.Tm_fvar fv, uu___4::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.remove_unused_type_parameters_lid
                  ->
                  let uu___5 =
                    let uu___6 =
                      FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                        FStar_Parser_Const.remove_unused_type_parameters_lid in
                    FStar_Pervasives_Native.fst uu___6 in
                  (match uu___5 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some l ->
                       let uu___6 =
                         let uu___7 =
                           let uu___8 = FStar_Syntax_Syntax.range_of_fv fv in
                           (l, uu___8) in
                         FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                           uu___7 in
                       FStar_Pervasives_Native.Some uu___6)
              | uu___4 -> FStar_Pervasives_Native.None))
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas -> FStar_List.choose extract_meta metas
let (binders_as_mlty_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binder Prims.list ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlident
        Prims.list))
  =
  fun env ->
    fun bs ->
      FStar_Util.fold_map
        (fun env1 ->
           fun uu___ ->
             match uu___ with
             | { FStar_Syntax_Syntax.binder_bv = bv;
                 FStar_Syntax_Syntax.binder_qual = uu___1;
                 FStar_Syntax_Syntax.binder_attrs = uu___2;_} ->
                 let env2 = FStar_Extraction_ML_UEnv.extend_ty env1 bv false in
                 let name =
                   let uu___3 = FStar_Extraction_ML_UEnv.lookup_bv env2 bv in
                   match uu___3 with
                   | FStar_Pervasives.Inl ty ->
                       ty.FStar_Extraction_ML_UEnv.ty_b_name
                   | uu___4 -> failwith "Impossible" in
                 (env2, name)) env bs
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee -> match projectee with | { dname; dtyp;_} -> dname
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | { dname; dtyp;_} -> dtyp
type inductive_family =
  {
  ifv: FStar_Syntax_Syntax.fv ;
  iname: FStar_Ident.lident ;
  iparams: FStar_Syntax_Syntax.binders ;
  ityp: FStar_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list ;
  imetadata: FStar_Extraction_ML_Syntax.metadata }
let (__proj__Mkinductive_family__item__ifv :
  inductive_family -> FStar_Syntax_Syntax.fv) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ifv
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iname
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iparams
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ityp
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> idatas
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iquals
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> imetadata
let (print_ifamily : inductive_family -> unit) =
  fun i ->
    let uu___ = FStar_Syntax_Print.lid_to_string i.iname in
    let uu___1 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu___2 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu___3 =
      let uu___4 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d ->
                let uu___5 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu___6 =
                  let uu___7 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.op_Hat " : " uu___7 in
                Prims.op_Hat uu___5 uu___6)) in
      FStar_All.pipe_right uu___4 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu___ uu___1 uu___2 uu___3
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        let uu___ =
          FStar_Util.fold_map
            (fun env1 ->
               fun se ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l, us, bs, t, _mut_i, datas) ->
                     let uu___1 = FStar_Syntax_Subst.open_univ_vars us t in
                     (match uu___1 with
                      | (_us, t1) ->
                          let uu___2 = FStar_Syntax_Subst.open_term bs t1 in
                          (match uu___2 with
                           | (bs1, t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1 ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d, us1, t3, l', nparams,
                                              uu___3)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu___4 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3 in
                                             (match uu___4 with
                                              | (_us1, t4) ->
                                                  let uu___5 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4 in
                                                  (match uu___5 with
                                                   | (bs', body) ->
                                                       let uu___6 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs' in
                                                       (match uu___6 with
                                                        | (bs_params, rest)
                                                            ->
                                                            let subst =
                                                              FStar_List.map2
                                                                (fun uu___7
                                                                   ->
                                                                   fun uu___8
                                                                    ->
                                                                    match 
                                                                    (uu___7,
                                                                    uu___8)
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = b';
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___9;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___10;_},
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___11;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___12;_})
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    (b',
                                                                    uu___14) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu___13)
                                                                bs_params bs1 in
                                                            let t5 =
                                                              let uu___7 =
                                                                let uu___8 =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body in
                                                                FStar_Syntax_Util.arrow
                                                                  rest uu___8 in
                                                              FStar_All.pipe_right
                                                                uu___7
                                                                (FStar_Syntax_Subst.subst
                                                                   subst) in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu___3 -> [])) in
                               let metadata =
                                 let uu___3 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs in
                                 let uu___4 =
                                   FStar_List.choose flag_of_qual quals in
                                 FStar_List.append uu___3 uu___4 in
                               let fv =
                                 FStar_Syntax_Syntax.lid_as_fv l
                                   FStar_Syntax_Syntax.delta_constant
                                   FStar_Pervasives_Native.None in
                               let uu___3 =
                                 FStar_Extraction_ML_UEnv.extend_type_name
                                   env1 fv in
                               (match uu___3 with
                                | (uu___4, env2) ->
                                    (env2,
                                      [{
                                         ifv = fv;
                                         iname = l;
                                         iparams = bs1;
                                         ityp = t2;
                                         idatas = datas1;
                                         iquals =
                                           (se.FStar_Syntax_Syntax.sigquals);
                                         imetadata = metadata
                                       }]))))
                 | uu___1 -> (env1, [])) env ses in
        match uu___ with
        | (env1, ifams) -> (env1, (FStar_List.flatten ifams))
type tydef_declaration =
  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.metadata
    * Prims.int)
type iface =
  {
  iface_module_name: FStar_Extraction_ML_Syntax.mlpath ;
  iface_bindings:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list
    ;
  iface_tydefs:
    (FStar_Extraction_ML_UEnv.tydef, tydef_declaration)
      FStar_Pervasives.either Prims.list
    ;
  iface_type_names:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list }
let (__proj__Mkiface__item__iface_module_name :
  iface -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_module_name
let (__proj__Mkiface__item__iface_bindings :
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_bindings
let (__proj__Mkiface__item__iface_tydefs :
  iface ->
    (FStar_Extraction_ML_UEnv.tydef, tydef_declaration)
      FStar_Pervasives.either Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_tydefs
let (__proj__Mkiface__item__iface_type_names :
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_type_names
let (empty_iface : iface) =
  {
    iface_module_name = ([], "");
    iface_bindings = [];
    iface_tydefs = [];
    iface_type_names = []
  }
let (iface_of_bindings :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list
    -> iface)
  =
  fun fvs ->
    let uu___ = empty_iface in
    {
      iface_module_name = (uu___.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___.iface_tydefs);
      iface_type_names = (uu___.iface_type_names)
    }
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds ->
    let uu___ = empty_iface in
    let uu___1 =
      FStar_List.map (fun uu___2 -> FStar_Pervasives.Inl uu___2) tds in
    let uu___2 =
      FStar_List.map
        (fun td ->
           let uu___3 = FStar_Extraction_ML_UEnv.tydef_fv td in
           let uu___4 = FStar_Extraction_ML_UEnv.tydef_mlpath td in
           (uu___3, uu___4)) tds in
    {
      iface_module_name = (uu___.iface_module_name);
      iface_bindings = (uu___.iface_bindings);
      iface_tydefs = uu___1;
      iface_type_names = uu___2
    }
let (iface_of_type_names :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list ->
    iface)
  =
  fun fvs ->
    let uu___ = empty_iface in
    {
      iface_module_name = (uu___.iface_module_name);
      iface_bindings = (uu___.iface_bindings);
      iface_tydefs = (uu___.iface_tydefs);
      iface_type_names = fvs
    }
let (iface_union : iface -> iface -> iface) =
  fun if1 ->
    fun if2 ->
      let uu___ =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name in
      {
        iface_module_name = uu___;
        iface_bindings =
          (FStar_List.append if1.iface_bindings if2.iface_bindings);
        iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs);
        iface_type_names =
          (FStar_List.append if1.iface_type_names if2.iface_type_names)
      }
let (iface_union_l : iface Prims.list -> iface) =
  fun ifs -> FStar_List.fold_right iface_union ifs empty_iface
let (mlpath_to_string : FStar_Extraction_ML_Syntax.mlpath -> Prims.string) =
  fun p ->
    FStar_String.concat ". "
      (FStar_List.append (FStar_Pervasives_Native.fst p)
         [FStar_Pervasives_Native.snd p])
let tscheme_to_string :
  'uuuuu .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('uuuuu * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
  =
  fun cm ->
    fun ts ->
      FStar_Extraction_ML_Code.string_of_mlty cm
        (FStar_Pervasives_Native.snd ts)
let (print_exp_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.exp_binding -> Prims.string)
  =
  fun cm ->
    fun e ->
      let uu___ =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr in
      let uu___1 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme in
      FStar_Util.format3
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu___ uu___1
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm ->
    fun uu___ ->
      match uu___ with
      | (fv, exp_binding) ->
          let uu___1 = FStar_Syntax_Print.fv_to_string fv in
          let uu___2 = print_exp_binding cm exp_binding in
          FStar_Util.format2 "(%s, %s)" uu___1 uu___2
let print_tydef :
  'uuuuu 'uuuuu1 .
    FStar_Extraction_ML_Syntax.mlpath ->
      (FStar_Extraction_ML_UEnv.tydef, (Prims.string * 'uuuuu * 'uuuuu1))
        FStar_Pervasives.either -> Prims.string
  =
  fun cm ->
    fun tydef ->
      let uu___ =
        match tydef with
        | FStar_Pervasives.Inl tydef1 ->
            let uu___1 =
              let uu___2 = FStar_Extraction_ML_UEnv.tydef_fv tydef1 in
              FStar_Syntax_Print.fv_to_string uu___2 in
            let uu___2 =
              let uu___3 = FStar_Extraction_ML_UEnv.tydef_def tydef1 in
              tscheme_to_string cm uu___3 in
            (uu___1, uu___2)
        | FStar_Pervasives.Inr (p, uu___1, uu___2) -> (p, "None") in
      match uu___ with
      | (name, defn) -> FStar_Util.format2 "(%s, %s)" name defn
let (iface_to_string : iface -> Prims.string) =
  fun iface1 ->
    let cm = iface1.iface_module_name in
    let print_type_name uu___ =
      match uu___ with | (tn, uu___1) -> FStar_Syntax_Print.fv_to_string tn in
    let uu___ =
      let uu___1 = FStar_List.map (print_binding cm) iface1.iface_bindings in
      FStar_All.pipe_right uu___1 (FStar_String.concat "\n") in
    let uu___1 =
      let uu___2 = FStar_List.map (print_tydef cm) iface1.iface_tydefs in
      FStar_All.pipe_right uu___2 (FStar_String.concat "\n") in
    let uu___2 =
      let uu___3 = FStar_List.map print_type_name iface1.iface_type_names in
      FStar_All.pipe_right uu___3 (FStar_String.concat "\n") in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu___ uu___1 uu___2
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env ->
    let cm = FStar_Extraction_ML_UEnv.current_module_of_uenv env in
    let gamma =
      let uu___ = FStar_Extraction_ML_UEnv.bindings_of_uenv env in
      FStar_List.collect
        (fun uu___1 ->
           match uu___1 with
           | FStar_Extraction_ML_UEnv.Fv (b, e) -> [(b, e)]
           | uu___2 -> []) uu___ in
    let uu___ =
      let uu___1 = FStar_List.map (print_binding cm) gamma in
      FStar_All.pipe_right uu___1 (FStar_String.concat "\n") in
    FStar_Util.format1 "Gamma = {\n %s }" uu___
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun quals ->
      fun attrs ->
        fun lb ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
              FStar_TypeChecker_Env.open_universes_in uu___2
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
            match uu___1 with
            | (tcenv, uu___2, def_typ) ->
                let uu___3 = as_pair def_typ in (tcenv, uu___3) in
          match uu___ with
          | (tcenv, (lbdef, lbtyp)) ->
              let lbtyp1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant;
                  FStar_TypeChecker_Env.ForExtraction] tcenv lbtyp in
              let lbdef1 =
                FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef
                  lbtyp1 in
              let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let def =
                let uu___1 =
                  let uu___2 = FStar_Syntax_Subst.compress lbdef1 in
                  FStar_All.pipe_right uu___2 FStar_Syntax_Util.unmeta in
                FStar_All.pipe_right uu___1 FStar_Syntax_Util.un_uinst in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu___1 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu___1 -> def in
              let uu___1 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs, body, uu___2) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu___2 -> ([], def1) in
              (match uu___1 with
               | (bs, body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___2 ->
                          match uu___2 with
                          | FStar_Syntax_Syntax.Assumption -> true
                          | uu___3 -> false) quals in
                   let uu___2 = binders_as_mlty_binders env bs in
                   (match uu___2 with
                    | (env1, ml_bs) ->
                        let body1 =
                          let uu___3 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body in
                          FStar_All.pipe_right uu___3
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                        let metadata =
                          let has_val_decl =
                            FStar_Extraction_ML_UEnv.has_tydef_declaration
                              env lid in
                          let meta =
                            let uu___3 = extract_metadata attrs in
                            let uu___4 = FStar_List.choose flag_of_qual quals in
                            FStar_List.append uu___3 uu___4 in
                          if has_val_decl
                          then
                            let uu___3 =
                              let uu___4 = FStar_Ident.range_of_lid lid in
                              FStar_Extraction_ML_Syntax.HasValDecl uu___4 in
                            uu___3 :: meta
                          else meta in
                        let tyscheme = (ml_bs, body1) in
                        let uu___3 =
                          let uu___4 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5 ->
                                    match uu___5 with
                                    | FStar_Syntax_Syntax.Assumption -> true
                                    | FStar_Syntax_Syntax.New -> true
                                    | uu___6 -> false)) in
                          if uu___4
                          then
                            let uu___5 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv in
                            match uu___5 with
                            | (mlp, env2) ->
                                (mlp, (iface_of_type_names [(fv, mlp)]),
                                  env2)
                          else
                            (let uu___6 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 tyscheme metadata in
                             match uu___6 with
                             | (td, mlp, env2) ->
                                 let uu___7 = iface_of_tydefs [td] in
                                 (mlp, uu___7, env2)) in
                        (match uu___3 with
                         | (mlpath, iface1, env2) ->
                             let td =
                               {
                                 FStar_Extraction_ML_Syntax.tydecl_assumed =
                                   assumed;
                                 FStar_Extraction_ML_Syntax.tydecl_name =
                                   (FStar_Pervasives_Native.snd mlpath);
                                 FStar_Extraction_ML_Syntax.tydecl_ignored =
                                   FStar_Pervasives_Native.None;
                                 FStar_Extraction_ML_Syntax.tydecl_parameters
                                   = ml_bs;
                                 FStar_Extraction_ML_Syntax.tydecl_meta =
                                   metadata;
                                 FStar_Extraction_ML_Syntax.tydecl_defn =
                                   (FStar_Pervasives_Native.Some
                                      (FStar_Extraction_ML_Syntax.MLTD_Abbrev
                                         body1))
                               } in
                             let def2 =
                               let uu___4 =
                                 let uu___5 =
                                   let uu___6 = FStar_Ident.range_of_lid lid in
                                   FStar_Extraction_ML_Util.mlloc_of_range
                                     uu___6 in
                                 FStar_Extraction_ML_Syntax.MLM_Loc uu___5 in
                               [uu___4;
                               FStar_Extraction_ML_Syntax.MLM_Ty [td]] in
                             (env2, iface1, def2))))
let (extract_let_rec_type :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun quals ->
      fun attrs ->
        fun lb ->
          let lbtyp =
            let uu___ = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.ForExtraction] uu___
              lb.FStar_Syntax_Syntax.lbtyp in
          let uu___ = FStar_Syntax_Util.arrow_formals lbtyp in
          match uu___ with
          | (bs, uu___1) ->
              let uu___2 = binders_as_mlty_binders env bs in
              (match uu___2 with
               | (env1, ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top in
                   let metadata =
                     let uu___3 = extract_metadata attrs in
                     let uu___4 = FStar_List.choose flag_of_qual quals in
                     FStar_List.append uu___3 uu___4 in
                   let assumed = false in
                   let tscheme = (ml_bs, body) in
                   let uu___3 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv tscheme
                       metadata in
                   (match uu___3 with
                    | (tydef, mlp, env2) ->
                        let td =
                          {
                            FStar_Extraction_ML_Syntax.tydecl_assumed =
                              assumed;
                            FStar_Extraction_ML_Syntax.tydecl_name =
                              (FStar_Pervasives_Native.snd mlp);
                            FStar_Extraction_ML_Syntax.tydecl_ignored =
                              FStar_Pervasives_Native.None;
                            FStar_Extraction_ML_Syntax.tydecl_parameters =
                              ml_bs;
                            FStar_Extraction_ML_Syntax.tydecl_meta = metadata;
                            FStar_Extraction_ML_Syntax.tydecl_defn =
                              (FStar_Pervasives_Native.Some
                                 (FStar_Extraction_ML_Syntax.MLTD_Abbrev body))
                          } in
                        let def =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 = FStar_Ident.range_of_lid lid in
                              FStar_Extraction_ML_Util.mlloc_of_range uu___6 in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu___5 in
                          [uu___4; FStar_Extraction_ML_Syntax.MLM_Ty [td]] in
                        let iface1 = iface_of_tydefs [tydef] in
                        (env2, iface1, def)))
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env ->
    fun se ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu___ =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu___ in
        let tys = (ml_tyvars, mlt) in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu___ = FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false in
        match uu___ with | (env2, uu___1, b) -> (env2, (fvv, b)) in
      let extract_one_family env1 ind =
        let uu___ = binders_as_mlty_binders env1 ind.iparams in
        match uu___ with
        | (env_iparams, vars) ->
            let uu___1 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1) in
            (match uu___1 with
             | (env2, ctors) ->
                 let env3 =
                   let uu___2 =
                     FStar_Util.find_opt
                       (fun uu___3 ->
                          match uu___3 with
                          | FStar_Syntax_Syntax.RecordType uu___4 -> true
                          | uu___4 -> false) ind.iquals in
                   match uu___2 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.RecordType (ns, ids)) ->
                       let g =
                         FStar_List.fold_right
                           (fun id ->
                              fun g1 ->
                                let uu___3 =
                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                    g1 ((ind.iname), id) in
                                match uu___3 with | (uu___4, g2) -> g2) ids
                           env2 in
                       g
                   | uu___3 -> env2 in
                 (env3, ctors)) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu___, t, uu___1, uu___2, uu___3);
            FStar_Syntax_Syntax.sigrng = uu___4;
            FStar_Syntax_Syntax.sigquals = uu___5;
            FStar_Syntax_Syntax.sigmeta = uu___6;
            FStar_Syntax_Syntax.sigattrs = uu___7;
            FStar_Syntax_Syntax.sigopts = uu___8;_}::[],
          uu___9),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu___10 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu___10 with
           | (env1, ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu___), quals) ->
          let uu___1 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr in
          if uu___1
          then (env, empty_iface)
          else
            (let uu___3 = bundle_as_inductive_families env ses quals in
             match uu___3 with
             | (env1, ifams) ->
                 let uu___4 =
                   FStar_Util.fold_map extract_one_family env1 ifams in
                 (match uu___4 with
                  | (env2, td) ->
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            FStar_List.map
                              (fun x ->
                                 let uu___8 =
                                   FStar_Extraction_ML_UEnv.mlpath_of_lident
                                     env2 x.iname in
                                 ((x.ifv), uu___8)) ifams in
                          iface_of_type_names uu___7 in
                        iface_union uu___6
                          (iface_of_bindings (FStar_List.flatten td)) in
                      (env2, uu___5)))
      | uu___ -> failwith "Unexpected signature element"
let (extract_type_declaration :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.bool ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Syntax_Syntax.term Prims.list ->
            FStar_Syntax_Syntax.univ_name Prims.list ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
                (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1
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
                    FStar_All.pipe_right quals
                      (FStar_Util.for_some
                         (fun uu___2 ->
                            match uu___2 with
                            | FStar_Syntax_Syntax.Assumption -> true
                            | uu___3 -> false)) in
                  Prims.op_Negation uu___1 in
                if uu___
                then
                  let g1 =
                    FStar_Extraction_ML_UEnv.extend_with_tydef_declaration g
                      lid in
                  (g1, empty_iface, [])
                else
                  (let uu___2 = FStar_Syntax_Util.arrow_formals t in
                   match uu___2 with
                   | (bs, uu___3) ->
                       let fv =
                         FStar_Syntax_Syntax.lid_as_fv lid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       let lb =
                         let uu___4 =
                           FStar_Syntax_Util.abs bs
                             FStar_Syntax_Syntax.t_unit
                             FStar_Pervasives_Native.None in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (FStar_Pervasives.Inr fv);
                           FStar_Syntax_Syntax.lbunivs = univs;
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_Tot_lid;
                           FStar_Syntax_Syntax.lbdef = uu___4;
                           FStar_Syntax_Syntax.lbattrs = attrs;
                           FStar_Syntax_Syntax.lbpos =
                             (t.FStar_Syntax_Syntax.pos)
                         } in
                       let uu___4 = extract_typ_abbrev g quals attrs lb in
                       (match uu___4 with
                        | (g1, iface1, mods) ->
                            let iface2 =
                              if is_interface_val
                              then
                                let mlp =
                                  FStar_Extraction_ML_UEnv.mlpath_of_lident
                                    g1 lid in
                                let meta = extract_metadata attrs in
                                let uu___5 = empty_iface in
                                {
                                  iface_module_name =
                                    (uu___5.iface_module_name);
                                  iface_bindings = (uu___5.iface_bindings);
                                  iface_tydefs =
                                    [FStar_Pervasives.Inr
                                       ((FStar_Pervasives_Native.snd mlp),
                                         meta, (FStar_List.length bs))];
                                  iface_type_names =
                                    (uu___5.iface_type_names)
                                }
                              else iface1 in
                            (g1, iface2, mods)))
let (extract_reifiable_effect :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Extraction_ML_UEnv.uenv * iface *
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun ed ->
      let extend_iface lid mlp exp exp_binding =
        let fv =
          FStar_Syntax_Syntax.lid_as_fv lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
        let lb =
          {
            FStar_Extraction_ML_Syntax.mllb_name =
              (FStar_Pervasives_Native.snd mlp);
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.None;
            FStar_Extraction_ML_Syntax.mllb_add_unit = false;
            FStar_Extraction_ML_Syntax.mllb_def = exp;
            FStar_Extraction_ML_Syntax.mllb_meta = [];
            FStar_Extraction_ML_Syntax.print_typ = false
          } in
        ((iface_of_bindings [(fv, exp_binding)]),
          (FStar_Extraction_ML_Syntax.MLM_Let
             (FStar_Extraction_ML_Syntax.NonRec, [lb]))) in
      let rec extract_fv tm =
        (let uu___1 =
           let uu___2 =
             let uu___3 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
             FStar_TypeChecker_Env.debug uu___3 in
           FStar_All.pipe_left uu___2 (FStar_Options.Other "ExtractionReify") in
         if uu___1
         then
           let uu___2 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "extract_fv term: %s\n" uu___2
         else ());
        (let uu___1 =
           let uu___2 = FStar_Syntax_Subst.compress tm in
           uu___2.FStar_Syntax_Syntax.n in
         match uu___1 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1, uu___2) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_UEnv.mlpath_of_lident g
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             let uu___2 =
               FStar_Extraction_ML_UEnv.lookup_fv tm.FStar_Syntax_Syntax.pos
                 g fv in
             (match uu___2 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu___3;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu___4;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;_} ->
                  let uu___5 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                  (uu___5, tysc))
         | uu___2 ->
             let uu___3 =
               let uu___4 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos in
               let uu___5 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format2 "(%s) Not an fv: %s" uu___4 uu___5 in
             failwith uu___3) in
      let extract_action g1 a =
        (let uu___2 =
           let uu___3 =
             let uu___4 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
             FStar_TypeChecker_Env.debug uu___4 in
           FStar_All.pipe_left uu___3 (FStar_Options.Other "ExtractionReify") in
         if uu___2
         then
           let uu___3 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ in
           let uu___4 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn in
           FStar_Util.print2 "Action type %s and term %s\n" uu___3 uu___4
         else ());
        (let lbname =
           let uu___2 =
             FStar_Syntax_Syntax.new_bv
               (FStar_Pervasives_Native.Some
                  ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
               FStar_Syntax_Syntax.tun in
           FStar_Pervasives.Inl uu___2 in
         let lb =
           FStar_Syntax_Syntax.mk_lb
             (lbname, (a.FStar_Syntax_Syntax.action_univs),
               FStar_Parser_Const.effect_Tot_lid,
               (a.FStar_Syntax_Syntax.action_typ),
               (a.FStar_Syntax_Syntax.action_defn), [],
               ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos)) in
         let lbs = (false, [lb]) in
         let action_lb =
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_let
                (lbs, FStar_Syntax_Util.exp_false_bool))
             (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
         let uu___2 = FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
         match uu___2 with
         | (a_let, uu___3, ty) ->
             let uu___4 =
               match a_let.FStar_Extraction_ML_Syntax.expr with
               | FStar_Extraction_ML_Syntax.MLE_Let
                   ((uu___5, mllb::[]), uu___6) ->
                   (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc with
                    | FStar_Pervasives_Native.Some tysc ->
                        ((mllb.FStar_Extraction_ML_Syntax.mllb_def), tysc)
                    | FStar_Pervasives_Native.None ->
                        failwith "No type scheme")
               | uu___5 -> failwith "Impossible" in
             (match uu___4 with
              | (exp, tysc) ->
                  let uu___5 =
                    FStar_Extraction_ML_UEnv.extend_with_action_name g1 ed a
                      tysc in
                  (match uu___5 with
                   | (a_nm, a_lid, exp_b, g2) ->
                       ((let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2 in
                             FStar_TypeChecker_Env.debug uu___9 in
                           FStar_All.pipe_left uu___8
                             (FStar_Options.Other "ExtractionReify") in
                         if uu___7
                         then
                           let uu___8 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu___8
                         else ());
                        (let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2 in
                             FStar_TypeChecker_Env.debug uu___10 in
                           FStar_All.pipe_left uu___9
                             (FStar_Options.Other "ExtractionReify") in
                         if uu___8
                         then
                           ((let uu___10 =
                               FStar_Extraction_ML_Code.string_of_mlty a_nm
                                 (FStar_Pervasives_Native.snd tysc) in
                             FStar_Util.print1 "Extracted action type: %s\n"
                               uu___10);
                            FStar_List.iter
                              (fun x ->
                                 FStar_Util.print1 "and binders: %s\n" x)
                              (FStar_Pervasives_Native.fst tysc))
                         else ());
                        (let uu___8 = extend_iface a_lid a_nm exp exp_b in
                         match uu___8 with
                         | (iface1, impl) -> (g2, (iface1, impl))))))) in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr in
              FStar_All.pipe_right uu___4 FStar_Util.must in
            FStar_All.pipe_right uu___3 FStar_Pervasives_Native.snd in
          extract_fv uu___2 in
        match uu___1 with
        | (return_tm, ty_sc) ->
            let uu___2 =
              FStar_Extraction_ML_UEnv.extend_with_monad_op_name g ed
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
                  let uu___5 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr in
                  FStar_All.pipe_right uu___5 FStar_Util.must in
                FStar_All.pipe_right uu___4 FStar_Pervasives_Native.snd in
              extract_fv uu___3 in
            match uu___2 with
            | (bind_tm, ty_sc) ->
                let uu___3 =
                  FStar_Extraction_ML_UEnv.extend_with_monad_op_name g1 ed
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
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions in
               (match uu___2 with
                | (g3, actions) ->
                    let uu___3 = FStar_List.unzip actions in
                    (match uu___3 with
                     | (actions_iface, actions1) ->
                         let uu___4 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface) in
                         (g3, uu___4, (return_decl :: bind_decl :: actions1)))))
let (extract_let_rec_types :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * iface *
          FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun se ->
    fun env ->
      fun lbs ->
        let uu___ =
          FStar_Util.for_some
            (fun lb ->
               let uu___1 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp in
               Prims.op_Negation uu___1) lbs in
        if uu___
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu___2 =
             FStar_List.fold_left
               (fun uu___3 ->
                  fun lb ->
                    match uu___3 with
                    | (env1, iface_opt, impls) ->
                        let uu___4 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb in
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
               let uu___3 = FStar_Option.get iface_opt in
               let uu___4 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten in
               (env1, uu___3, uu___4))
let (get_noextract_to :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Options.codegen_t FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun se ->
    fun backend ->
      FStar_Util.for_some
        (fun uu___ ->
           let uu___1 = FStar_Syntax_Util.head_and_args uu___ in
           match uu___1 with
           | (hd, args) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Syntax_Subst.compress hd in
                   uu___4.FStar_Syntax_Syntax.n in
                 (uu___3, args) in
               (match uu___2 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, (a, uu___3)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.noextract_to_attr
                    ->
                    let uu___4 =
                      let uu___5 =
                        FStar_Syntax_Embeddings.unembed
                          FStar_Syntax_Embeddings.e_string a in
                      uu___5 false FStar_Syntax_Embeddings.id_norm_cb in
                    (match uu___4 with
                     | FStar_Pervasives_Native.Some s ->
                         (FStar_Option.isSome backend) &&
                           (let uu___5 = FStar_Options.parse_codegen s in
                            uu___5 = backend)
                     | FStar_Pervasives_Native.None -> false)
                | uu___3 -> false)) se.FStar_Syntax_Syntax.sigattrs
let (sigelt_has_noextract : FStar_Syntax_Syntax.sigelt -> Prims.bool) =
  fun se ->
    let has_noextract_qualifier =
      FStar_List.contains FStar_Syntax_Syntax.NoExtract
        se.FStar_Syntax_Syntax.sigquals in
    let has_noextract_attribute =
      let uu___ = FStar_Options.codegen () in get_noextract_to se uu___ in
    let uu___ = FStar_Options.codegen () in
    match uu___ with
    | FStar_Pervasives_Native.Some (FStar_Options.Kremlin) ->
        has_noextract_qualifier && has_noextract_attribute
    | uu___1 -> has_noextract_qualifier || has_noextract_attribute
let (kremlin_fixup_qual :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun se ->
    let uu___ =
      ((let uu___1 = FStar_Options.codegen () in
        uu___1 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)) &&
         (get_noextract_to se
            (FStar_Pervasives_Native.Some FStar_Options.Kremlin)))
        &&
        (Prims.op_Negation
           (FStar_List.contains FStar_Syntax_Syntax.NoExtract
              se.FStar_Syntax_Syntax.sigquals)) in
    if uu___
    then
      let uu___1 = se in
      {
        FStar_Syntax_Syntax.sigel = (uu___1.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng = (uu___1.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.NoExtract ::
          (se.FStar_Syntax_Syntax.sigquals));
        FStar_Syntax_Syntax.sigmeta = (uu___1.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = (uu___1.FStar_Syntax_Syntax.sigattrs);
        FStar_Syntax_Syntax.sigopts = (uu___1.FStar_Syntax_Syntax.sigopts)
      }
    else se
let (mark_sigelt_erased :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Extraction_ML_UEnv.uenv -> FStar_Extraction_ML_UEnv.uenv)
  =
  fun se ->
    fun g ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u ->
           let uu___1 = FStar_Syntax_Print.sigelt_to_string_short se in
           FStar_Util.print1 ">>>> NOT extracting %s \n" uu___1);
      FStar_List.fold_right
        (fun lid ->
           fun g1 ->
             let uu___1 =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None in
             FStar_Extraction_ML_UEnv.extend_erased_fv g1 uu___1)
        (FStar_Syntax_Util.lids_of_sigelt se) g
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun se ->
      let uu___ = sigelt_has_noextract se in
      if uu___
      then let g1 = mark_sigelt_erased se g in (g1, empty_iface)
      else
        (let se1 = kremlin_fixup_qual se in
         match se1.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_bundle uu___2 ->
             extract_bundle_iface g se1
         | FStar_Syntax_Syntax.Sig_inductive_typ uu___2 ->
             extract_bundle_iface g se1
         | FStar_Syntax_Syntax.Sig_datacon uu___2 ->
             extract_bundle_iface g se1
         | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t) when
             FStar_Extraction_ML_Term.is_arity g t ->
             let uu___2 =
               extract_type_declaration g true lid
                 se1.FStar_Syntax_Syntax.sigquals
                 se1.FStar_Syntax_Syntax.sigattrs univs t in
             (match uu___2 with | (env, iface1, uu___3) -> (env, iface1))
         | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu___2) when
             FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
             ->
             let uu___3 =
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___4 ->
                       match uu___4 with
                       | FStar_Syntax_Syntax.Projector uu___5 -> true
                       | uu___5 -> false)) in
             if uu___3
             then (g, empty_iface)
             else
               (let uu___5 =
                  extract_typ_abbrev g se1.FStar_Syntax_Syntax.sigquals
                    se1.FStar_Syntax_Syntax.sigattrs lb in
                match uu___5 with | (env, iface1, uu___6) -> (env, iface1))
         | FStar_Syntax_Syntax.Sig_let ((true, lbs), uu___2) when
             FStar_Util.for_some
               (fun lb ->
                  FStar_Extraction_ML_Term.is_arity g
                    lb.FStar_Syntax_Syntax.lbtyp) lbs
             ->
             let uu___3 = extract_let_rec_types se1 g lbs in
             (match uu___3 with | (env, iface1, uu___4) -> (env, iface1))
         | FStar_Syntax_Syntax.Sig_declare_typ (lid, _univs, t) ->
             let quals = se1.FStar_Syntax_Syntax.sigquals in
             let uu___2 =
               (FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                 &&
                 (let uu___3 =
                    let uu___4 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Util.must_erase_for_extraction uu___4 t in
                  Prims.op_Negation uu___3) in
             if uu___2
             then
               let uu___3 =
                 let uu___4 =
                   let uu___5 = let uu___6 = always_fail lid t in [uu___6] in
                   (false, uu___5) in
                 FStar_Extraction_ML_Term.extract_lb_iface g uu___4 in
               (match uu___3 with
                | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
             else (g, empty_iface)
         | FStar_Syntax_Syntax.Sig_let (lbs, uu___2) ->
             let uu___3 = FStar_Extraction_ML_Term.extract_lb_iface g lbs in
             (match uu___3 with
              | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
         | FStar_Syntax_Syntax.Sig_assume uu___2 -> (g, empty_iface)
         | FStar_Syntax_Syntax.Sig_sub_effect uu___2 -> (g, empty_iface)
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu___2 -> (g, empty_iface)
         | FStar_Syntax_Syntax.Sig_polymonadic_bind uu___2 ->
             (g, empty_iface)
         | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu___2 ->
             (g, empty_iface)
         | FStar_Syntax_Syntax.Sig_pragma p ->
             (FStar_Syntax_Util.process_pragma p
                se1.FStar_Syntax_Syntax.sigrng;
              (g, empty_iface))
         | FStar_Syntax_Syntax.Sig_splice uu___2 ->
             failwith "impossible: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_fail uu___2 ->
             failwith "impossible: trying to extract Sig_fail"
         | FStar_Syntax_Syntax.Sig_new_effect ed ->
             let uu___2 =
               (let uu___3 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                FStar_TypeChecker_Env.is_reifiable_effect uu___3
                  ed.FStar_Syntax_Syntax.mname)
                 && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders) in
             if uu___2
             then
               let uu___3 = extract_reifiable_effect g ed in
               (match uu___3 with | (env, iface1, uu___4) -> (env, iface1))
             else (g, empty_iface))
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu___ = FStar_Options.interactive () in
      if uu___
      then (g, empty_iface)
      else
        (let uu___2 = FStar_Options.restore_cmd_line_options true in
         let decls = modul.FStar_Syntax_Syntax.declarations in
         let iface1 =
           let uu___3 = empty_iface in
           let uu___4 = FStar_Extraction_ML_UEnv.current_module_of_uenv g in
           {
             iface_module_name = uu___4;
             iface_bindings = (uu___3.iface_bindings);
             iface_tydefs = (uu___3.iface_tydefs);
             iface_type_names = (uu___3.iface_type_names)
           } in
         let res =
           FStar_List.fold_left
             (fun uu___3 ->
                fun se ->
                  match uu___3 with
                  | (g1, iface2) ->
                      let uu___4 = extract_sigelt_iface g1 se in
                      (match uu___4 with
                       | (g2, iface') ->
                           let uu___5 = iface_union iface2 iface' in
                           (g2, uu___5))) (g, iface1) decls in
         (let uu___4 = FStar_Options.restore_cmd_line_options true in
          FStar_All.pipe_left (fun uu___5 -> ()) uu___4);
         res)
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu___ =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu___1 ->
             let uu___2 = FStar_Options.debug_any () in
             if uu___2
             then
               let uu___3 =
                 let uu___4 =
                   FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
                 FStar_Util.format1 "Extracted interface of %s" uu___4 in
               FStar_Util.measure_execution_time uu___3
                 (fun uu___4 -> extract_iface' g modul)
             else extract_iface' g modul) in
      match uu___ with
      | (g1, iface1) ->
          let uu___1 =
            FStar_Extraction_ML_UEnv.with_typars_env g1
              (fun e ->
                 let iface_tydefs =
                   FStar_List.map
                     (fun uu___2 ->
                        match uu___2 with
                        | FStar_Pervasives.Inl td ->
                            let uu___3 =
                              let uu___4 =
                                FStar_Extraction_ML_UEnv.tydef_mlpath td in
                              FStar_Pervasives_Native.snd uu___4 in
                            let uu___4 =
                              FStar_Extraction_ML_UEnv.tydef_meta td in
                            let uu___5 =
                              let uu___6 =
                                FStar_Extraction_ML_UEnv.tydef_def td in
                              FStar_Pervasives.Inl uu___6 in
                            (uu___3, uu___4, uu___5)
                        | FStar_Pervasives.Inr (p, m, n) ->
                            (p, m, (FStar_Pervasives.Inr n)))
                     iface1.iface_tydefs in
                 let uu___2 =
                   FStar_Extraction_ML_UEnv.extend_with_module_name g1
                     modul.FStar_Syntax_Syntax.name in
                 match uu___2 with
                 | (module_name, uu___3) ->
                     let e1 =
                       FStar_Extraction_ML_RemoveUnusedParameters.set_current_module
                         e module_name in
                     FStar_Extraction_ML_RemoveUnusedParameters.elim_tydefs
                       e1 iface_tydefs) in
          (match uu___1 with
           | (g2, uu___2) ->
               let uu___3 = FStar_Extraction_ML_UEnv.exit_module g2 in
               (uu___3, iface1))
let (extract_bundle :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlmodule1
        Prims.list))
  =
  fun env ->
    fun se ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu___ =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu___ in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.ForExtraction] in
        let names =
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStar_Extraction_ML_UEnv.tcenv_of_uenv env_iparams in
                FStar_TypeChecker_Normalize.normalize steps uu___3 ctor.dtyp in
              FStar_Syntax_Subst.compress uu___2 in
            uu___1.FStar_Syntax_Syntax.n in
          match uu___ with
          | FStar_Syntax_Syntax.Tm_arrow (bs, uu___1) ->
              FStar_List.map
                (fun uu___2 ->
                   match uu___2 with
                   | {
                       FStar_Syntax_Syntax.binder_bv =
                         { FStar_Syntax_Syntax.ppname = ppname;
                           FStar_Syntax_Syntax.index = uu___3;
                           FStar_Syntax_Syntax.sort = uu___4;_};
                       FStar_Syntax_Syntax.binder_qual = uu___5;
                       FStar_Syntax_Syntax.binder_attrs = uu___6;_} ->
                       FStar_Ident.string_of_id ppname) bs
          | uu___1 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu___ = FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false in
        match uu___ with
        | (env2, mls, uu___1) ->
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Extraction_ML_Util.argTypes mlt in
                FStar_List.zip names uu___4 in
              (mls, uu___3) in
            (env2, uu___2) in
      let extract_one_family env1 ind =
        let uu___ = binders_as_mlty_binders env1 ind.iparams in
        match uu___ with
        | (env_iparams, vars) ->
            let uu___1 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1) in
            (match uu___1 with
             | (env2, ctors) ->
                 let uu___2 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu___2 with
                  | (indices, uu___3) ->
                      let ml_params =
                        let uu___4 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i ->
                                  fun uu___5 ->
                                    let uu___6 = FStar_Util.string_of_int i in
                                    Prims.op_Hat "'dummyV" uu___6)) in
                        FStar_List.append vars uu___4 in
                      let uu___4 =
                        let uu___5 =
                          FStar_Util.find_opt
                            (fun uu___6 ->
                               match uu___6 with
                               | FStar_Syntax_Syntax.RecordType uu___7 ->
                                   true
                               | uu___7 -> false) ind.iquals in
                        match uu___5 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns, ids)) ->
                            let uu___6 = FStar_List.hd ctors in
                            (match uu___6 with
                             | (uu___7, c_ty) ->
                                 let uu___9 =
                                   FStar_List.fold_right2
                                     (fun id ->
                                        fun uu___10 ->
                                          fun uu___11 ->
                                            match (uu___10, uu___11) with
                                            | ((uu___12, ty), (fields, g)) ->
                                                let uu___13 =
                                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                                    g ((ind.iname), id) in
                                                (match uu___13 with
                                                 | (mlid, g1) ->
                                                     (((mlid, ty) :: fields),
                                                       g1))) ids c_ty
                                     ([], env2) in
                                 (match uu___9 with
                                  | (fields, g) ->
                                      ((FStar_Pervasives_Native.Some
                                          (FStar_Extraction_ML_Syntax.MLTD_Record
                                             fields)), g)))
                        | uu___6 when
                            (FStar_List.length ctors) = Prims.int_zero ->
                            (FStar_Pervasives_Native.None, env2)
                        | uu___6 ->
                            ((FStar_Pervasives_Native.Some
                                (FStar_Extraction_ML_Syntax.MLTD_DType ctors)),
                              env2) in
                      (match uu___4 with
                       | (tbody, env3) ->
                           let td =
                             let uu___5 =
                               let uu___6 =
                                 FStar_Extraction_ML_UEnv.mlpath_of_lident
                                   env3 ind.iname in
                               FStar_Pervasives_Native.snd uu___6 in
                             {
                               FStar_Extraction_ML_Syntax.tydecl_assumed =
                                 false;
                               FStar_Extraction_ML_Syntax.tydecl_name =
                                 uu___5;
                               FStar_Extraction_ML_Syntax.tydecl_ignored =
                                 FStar_Pervasives_Native.None;
                               FStar_Extraction_ML_Syntax.tydecl_parameters =
                                 ml_params;
                               FStar_Extraction_ML_Syntax.tydecl_meta =
                                 (ind.imetadata);
                               FStar_Extraction_ML_Syntax.tydecl_defn = tbody
                             } in
                           (env3, td)))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu___, t, uu___1, uu___2, uu___3);
            FStar_Syntax_Syntax.sigrng = uu___4;
            FStar_Syntax_Syntax.sigquals = uu___5;
            FStar_Syntax_Syntax.sigmeta = uu___6;
            FStar_Syntax_Syntax.sigattrs = uu___7;
            FStar_Syntax_Syntax.sigopts = uu___8;_}::[],
          uu___9),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu___10 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu___10 with
           | (env1, ctor) ->
               (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu___), quals) ->
          let uu___1 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr in
          if uu___1
          then (env, [])
          else
            (let uu___3 = bundle_as_inductive_families env ses quals in
             match uu___3 with
             | (env1, ifams) ->
                 let uu___4 =
                   FStar_Util.fold_map extract_one_family env1 ifams in
                 (match uu___4 with
                  | (env2, td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu___ -> failwith "Unexpected signature element"
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g ->
    fun se ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top in
      let plugin_with_arity attrs =
        FStar_Util.find_map attrs
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
                         FStar_Syntax_Syntax.vars = uu___5;_},
                       uu___6)::[] ->
                        let uu___7 =
                          let uu___8 = FStar_Util.int_of_string s in
                          FStar_Pervasives_Native.Some uu___8 in
                        FStar_Pervasives_Native.Some uu___7
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
              | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
                  let mk_registration lb =
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                    let fv_lid =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp in
                    let ml_name_str =
                      let uu___3 =
                        let uu___4 = FStar_Ident.string_of_lid fv_lid in
                        FStar_Extraction_ML_Syntax.MLC_String uu___4 in
                      FStar_Extraction_ML_Syntax.MLE_Const uu___3 in
                    let uu___3 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g
                        fv fv_t arity_opt ml_name_str in
                    match uu___3 with
                    | FStar_Pervasives_Native.Some
                        (interp, nbe_interp, arity, plugin) ->
                        let uu___4 =
                          if plugin
                          then
                            ((["FStar_Tactics_Native"], "register_plugin"),
                              [interp; nbe_interp])
                          else
                            ((["FStar_Tactics_Native"], "register_tactic"),
                              [interp]) in
                        (match uu___4 with
                         | (register, args) ->
                             let h =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_Name
                                    register) in
                             let arity1 =
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     FStar_Util.string_of_int arity in
                                   (uu___7, FStar_Pervasives_Native.None) in
                                 FStar_Extraction_ML_Syntax.MLC_Int uu___6 in
                               FStar_Extraction_ML_Syntax.MLE_Const uu___5 in
                             let app =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (h,
                                      (FStar_List.append
                                         [w ml_name_str; w arity1] args))) in
                             [FStar_Extraction_ML_Syntax.MLM_Top app])
                    | FStar_Pervasives_Native.None -> [] in
                  FStar_List.collect mk_registration
                    (FStar_Pervasives_Native.snd lbs)
              | uu___3 -> []))
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun se ->
      let uu___ =
        let uu___1 = FStar_Syntax_Print.sigelt_to_string_short se in
        FStar_Util.format1 "While extracting top-level definition `%s`"
          uu___1 in
      FStar_Errors.with_ctx uu___
        (fun uu___1 ->
           FStar_Extraction_ML_UEnv.debug g
             (fun u ->
                let uu___3 = FStar_Syntax_Print.sigelt_to_string_short se in
                FStar_Util.print1 ">>>> extract_sig %s \n" uu___3);
           (let uu___3 = sigelt_has_noextract se in
            if uu___3
            then let g1 = mark_sigelt_erased se g in (g1, [])
            else
              (let se1 = kremlin_fixup_qual se in
               match se1.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_bundle uu___5 ->
                   extract_bundle g se1
               | FStar_Syntax_Syntax.Sig_inductive_typ uu___5 ->
                   extract_bundle g se1
               | FStar_Syntax_Syntax.Sig_datacon uu___5 ->
                   extract_bundle g se1
               | FStar_Syntax_Syntax.Sig_new_effect ed when
                   let uu___5 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                   FStar_TypeChecker_Env.is_reifiable_effect uu___5
                     ed.FStar_Syntax_Syntax.mname
                   ->
                   let uu___5 = extract_reifiable_effect g ed in
                   (match uu___5 with | (env, _iface, impl) -> (env, impl))
               | FStar_Syntax_Syntax.Sig_splice uu___5 ->
                   failwith "impossible: trying to extract splice"
               | FStar_Syntax_Syntax.Sig_fail uu___5 ->
                   failwith "impossible: trying to extract Sig_fail"
               | FStar_Syntax_Syntax.Sig_new_effect uu___5 -> (g, [])
               | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t) when
                   FStar_Extraction_ML_Term.is_arity g t ->
                   let uu___5 =
                     extract_type_declaration g false lid
                       se1.FStar_Syntax_Syntax.sigquals
                       se1.FStar_Syntax_Syntax.sigattrs univs t in
                   (match uu___5 with | (env, uu___6, impl) -> (env, impl))
               | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu___5) when
                   FStar_Extraction_ML_Term.is_arity g
                     lb.FStar_Syntax_Syntax.lbtyp
                   ->
                   let uu___6 =
                     FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___7 ->
                             match uu___7 with
                             | FStar_Syntax_Syntax.Projector uu___8 -> true
                             | uu___8 -> false)) in
                   if uu___6
                   then (g, [])
                   else
                     (let uu___8 =
                        extract_typ_abbrev g se1.FStar_Syntax_Syntax.sigquals
                          se1.FStar_Syntax_Syntax.sigattrs lb in
                      match uu___8 with | (env, uu___9, impl) -> (env, impl))
               | FStar_Syntax_Syntax.Sig_let ((true, lbs), uu___5) when
                   FStar_Util.for_some
                     (fun lb ->
                        FStar_Extraction_ML_Term.is_arity g
                          lb.FStar_Syntax_Syntax.lbtyp) lbs
                   ->
                   let uu___6 = extract_let_rec_types se1 g lbs in
                   (match uu___6 with | (env, uu___7, impl) -> (env, impl))
               | FStar_Syntax_Syntax.Sig_let (lbs, uu___5) ->
                   let attrs = se1.FStar_Syntax_Syntax.sigattrs in
                   let quals = se1.FStar_Syntax_Syntax.sigquals in
                   let uu___6 =
                     let uu___7 =
                       FStar_Syntax_Util.extract_attr'
                         FStar_Parser_Const.postprocess_extr_with attrs in
                     match uu___7 with
                     | FStar_Pervasives_Native.None ->
                         (attrs, FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (ats, (tau, FStar_Pervasives_Native.None)::uu___8)
                         -> (ats, (FStar_Pervasives_Native.Some tau))
                     | FStar_Pervasives_Native.Some (ats, args) ->
                         (FStar_Errors.log_issue
                            se1.FStar_Syntax_Syntax.sigrng
                            (FStar_Errors.Warning_UnrecognizedAttribute,
                              "Ill-formed application of `postprocess_for_extraction_with`");
                          (attrs, FStar_Pervasives_Native.None)) in
                   (match uu___6 with
                    | (attrs1, post_tau) ->
                        let postprocess_lb tau lb =
                          let lbdef =
                            let uu___7 =
                              FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                            FStar_TypeChecker_Env.postprocess uu___7 tau
                              lb.FStar_Syntax_Syntax.lbtyp
                              lb.FStar_Syntax_Syntax.lbdef in
                          let uu___7 = lb in
                          {
                            FStar_Syntax_Syntax.lbname =
                              (uu___7.FStar_Syntax_Syntax.lbname);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___7.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___7.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___7.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef = lbdef;
                            FStar_Syntax_Syntax.lbattrs =
                              (uu___7.FStar_Syntax_Syntax.lbattrs);
                            FStar_Syntax_Syntax.lbpos =
                              (uu___7.FStar_Syntax_Syntax.lbpos)
                          } in
                        let lbs1 =
                          let uu___7 =
                            match post_tau with
                            | FStar_Pervasives_Native.Some tau ->
                                FStar_List.map (postprocess_lb tau)
                                  (FStar_Pervasives_Native.snd lbs)
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.snd lbs in
                          ((FStar_Pervasives_Native.fst lbs), uu___7) in
                        let uu___7 =
                          let uu___8 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 (lbs1, FStar_Syntax_Util.exp_false_bool))
                              se1.FStar_Syntax_Syntax.sigrng in
                          FStar_Extraction_ML_Term.term_as_mlexpr g uu___8 in
                        (match uu___7 with
                         | (ml_let, uu___8, uu___9) ->
                             (match ml_let.FStar_Extraction_ML_Syntax.expr
                              with
                              | FStar_Extraction_ML_Syntax.MLE_Let
                                  ((flavor, bindings), uu___10) ->
                                  let flags =
                                    FStar_List.choose flag_of_qual quals in
                                  let flags' = extract_metadata attrs1 in
                                  let uu___11 =
                                    FStar_List.fold_left2
                                      (fun uu___12 ->
                                         fun ml_lb ->
                                           fun uu___13 ->
                                             match (uu___12, uu___13) with
                                             | ((env, ml_lbs),
                                                {
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu___14;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu___15;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu___16;
                                                  FStar_Syntax_Syntax.lbattrs
                                                    = uu___17;
                                                  FStar_Syntax_Syntax.lbpos =
                                                    uu___18;_})
                                                 ->
                                                 let uu___19 =
                                                   FStar_All.pipe_right
                                                     ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                                     (FStar_List.contains
                                                        FStar_Extraction_ML_Syntax.Erased) in
                                                 if uu___19
                                                 then (env, ml_lbs)
                                                 else
                                                   (let lb_lid =
                                                      let uu___21 =
                                                        let uu___22 =
                                                          FStar_Util.right
                                                            lbname in
                                                        uu___22.FStar_Syntax_Syntax.fv_name in
                                                      uu___21.FStar_Syntax_Syntax.v in
                                                    let flags'' =
                                                      let uu___21 =
                                                        let uu___22 =
                                                          FStar_Syntax_Subst.compress
                                                            t in
                                                        uu___22.FStar_Syntax_Syntax.n in
                                                      match uu___21 with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (uu___22,
                                                           {
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Comp
                                                               {
                                                                 FStar_Syntax_Syntax.comp_univs
                                                                   = uu___23;
                                                                 FStar_Syntax_Syntax.effect_name
                                                                   = e;
                                                                 FStar_Syntax_Syntax.result_typ
                                                                   = uu___24;
                                                                 FStar_Syntax_Syntax.effect_args
                                                                   = uu___25;
                                                                 FStar_Syntax_Syntax.flags
                                                                   = uu___26;_};
                                                             FStar_Syntax_Syntax.pos
                                                               = uu___27;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu___28;_})
                                                          when
                                                          let uu___29 =
                                                            FStar_Ident.string_of_lid
                                                              e in
                                                          uu___29 =
                                                            "FStar.HyperStack.ST.StackInline"
                                                          ->
                                                          [FStar_Extraction_ML_Syntax.StackInline]
                                                      | uu___22 -> [] in
                                                    let meta =
                                                      FStar_List.append flags
                                                        (FStar_List.append
                                                           flags' flags'') in
                                                    let ml_lb1 =
                                                      let uu___21 = ml_lb in
                                                      {
                                                        FStar_Extraction_ML_Syntax.mllb_name
                                                          =
                                                          (uu___21.FStar_Extraction_ML_Syntax.mllb_name);
                                                        FStar_Extraction_ML_Syntax.mllb_tysc
                                                          =
                                                          (uu___21.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                        FStar_Extraction_ML_Syntax.mllb_add_unit
                                                          =
                                                          (uu___21.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                        FStar_Extraction_ML_Syntax.mllb_def
                                                          =
                                                          (uu___21.FStar_Extraction_ML_Syntax.mllb_def);
                                                        FStar_Extraction_ML_Syntax.mllb_meta
                                                          = meta;
                                                        FStar_Extraction_ML_Syntax.print_typ
                                                          =
                                                          (uu___21.FStar_Extraction_ML_Syntax.print_typ)
                                                      } in
                                                    let uu___21 =
                                                      let uu___22 =
                                                        FStar_All.pipe_right
                                                          quals
                                                          (FStar_Util.for_some
                                                             (fun uu___23 ->
                                                                match uu___23
                                                                with
                                                                | FStar_Syntax_Syntax.Projector
                                                                    uu___24
                                                                    -> true
                                                                | uu___24 ->
                                                                    false)) in
                                                      if uu___22
                                                      then
                                                        let uu___23 =
                                                          let uu___24 =
                                                            FStar_Util.right
                                                              lbname in
                                                          let uu___25 =
                                                            FStar_Util.must
                                                              ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                                          FStar_Extraction_ML_UEnv.extend_fv
                                                            env uu___24
                                                            uu___25
                                                            ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit in
                                                        match uu___23 with
                                                        | (env1, mls,
                                                           uu___24) ->
                                                            (env1,
                                                              (let uu___25 =
                                                                 ml_lb1 in
                                                               {
                                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                                   = mls;
                                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                                   =
                                                                   (uu___25.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                                   =
                                                                   (uu___25.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                                   =
                                                                   (uu___25.FStar_Extraction_ML_Syntax.mllb_def);
                                                                 FStar_Extraction_ML_Syntax.mllb_meta
                                                                   =
                                                                   (uu___25.FStar_Extraction_ML_Syntax.mllb_meta);
                                                                 FStar_Extraction_ML_Syntax.print_typ
                                                                   =
                                                                   (uu___25.FStar_Extraction_ML_Syntax.print_typ)
                                                               }))
                                                      else
                                                        (let uu___24 =
                                                           let uu___25 =
                                                             FStar_Util.must
                                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                                           FStar_Extraction_ML_UEnv.extend_lb
                                                             env lbname t
                                                             uu___25
                                                             ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit in
                                                         match uu___24 with
                                                         | (env1, uu___25,
                                                            uu___26) ->
                                                             (env1, ml_lb1)) in
                                                    match uu___21 with
                                                    | (g1, ml_lb2) ->
                                                        (g1, (ml_lb2 ::
                                                          ml_lbs)))) 
                                      (g, []) bindings
                                      (FStar_Pervasives_Native.snd lbs1) in
                                  (match uu___11 with
                                   | (g1, ml_lbs') ->
                                       let uu___12 =
                                         let uu___13 =
                                           let uu___14 =
                                             let uu___15 =
                                               FStar_Extraction_ML_Util.mlloc_of_range
                                                 se1.FStar_Syntax_Syntax.sigrng in
                                             FStar_Extraction_ML_Syntax.MLM_Loc
                                               uu___15 in
                                           [uu___14;
                                           FStar_Extraction_ML_Syntax.MLM_Let
                                             (flavor,
                                               (FStar_List.rev ml_lbs'))] in
                                         let uu___14 =
                                           maybe_register_plugin g1 se1 in
                                         FStar_List.append uu___13 uu___14 in
                                       (g1, uu___12))
                              | uu___10 ->
                                  let uu___11 =
                                    let uu___12 =
                                      let uu___13 =
                                        FStar_Extraction_ML_UEnv.current_module_of_uenv
                                          g in
                                      FStar_Extraction_ML_Code.string_of_mlexpr
                                        uu___13 ml_let in
                                    FStar_Util.format1
                                      "Impossible: Translated a let to a non-let: %s"
                                      uu___12 in
                                  failwith uu___11)))
               | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu___5, t) ->
                   let quals = se1.FStar_Syntax_Syntax.sigquals in
                   let uu___6 =
                     (FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       &&
                       (let uu___7 =
                          let uu___8 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                          FStar_TypeChecker_Util.must_erase_for_extraction
                            uu___8 t in
                        Prims.op_Negation uu___7) in
                   if uu___6
                   then
                     let always_fail1 =
                       let uu___7 = se1 in
                       let uu___8 =
                         let uu___9 =
                           let uu___10 =
                             let uu___11 =
                               let uu___12 = always_fail lid t in [uu___12] in
                             (false, uu___11) in
                           (uu___10, []) in
                         FStar_Syntax_Syntax.Sig_let uu___9 in
                       {
                         FStar_Syntax_Syntax.sigel = uu___8;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___7.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___7.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___7.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___7.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___7.FStar_Syntax_Syntax.sigopts)
                       } in
                     let uu___7 = extract_sig g always_fail1 in
                     (match uu___7 with
                      | (g1, mlm) ->
                          let uu___8 =
                            FStar_Util.find_map quals
                              (fun uu___9 ->
                                 match uu___9 with
                                 | FStar_Syntax_Syntax.Discriminator l ->
                                     FStar_Pervasives_Native.Some l
                                 | uu___10 -> FStar_Pervasives_Native.None) in
                          (match uu___8 with
                           | FStar_Pervasives_Native.Some l ->
                               let uu___9 =
                                 let uu___10 =
                                   let uu___11 =
                                     FStar_Extraction_ML_Util.mlloc_of_range
                                       se1.FStar_Syntax_Syntax.sigrng in
                                   FStar_Extraction_ML_Syntax.MLM_Loc uu___11 in
                                 let uu___11 =
                                   let uu___12 =
                                     FStar_Extraction_ML_Term.ind_discriminator_body
                                       g1 lid l in
                                   [uu___12] in
                                 uu___10 :: uu___11 in
                               (g1, uu___9)
                           | uu___9 ->
                               let uu___10 =
                                 FStar_Util.find_map quals
                                   (fun uu___11 ->
                                      match uu___11 with
                                      | FStar_Syntax_Syntax.Projector
                                          (l, uu___12) ->
                                          FStar_Pervasives_Native.Some l
                                      | uu___12 ->
                                          FStar_Pervasives_Native.None) in
                               (match uu___10 with
                                | FStar_Pervasives_Native.Some uu___11 ->
                                    (g1, [])
                                | uu___11 -> (g1, mlm))))
                   else (g, [])
               | FStar_Syntax_Syntax.Sig_assume uu___5 -> (g, [])
               | FStar_Syntax_Syntax.Sig_sub_effect uu___5 -> (g, [])
               | FStar_Syntax_Syntax.Sig_effect_abbrev uu___5 -> (g, [])
               | FStar_Syntax_Syntax.Sig_polymonadic_bind uu___5 -> (g, [])
               | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu___5 ->
                   (g, [])
               | FStar_Syntax_Syntax.Sig_pragma p ->
                   (FStar_Syntax_Util.process_pragma p
                      se1.FStar_Syntax_Syntax.sigrng;
                    (g, [])))))
let (extract' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      let uu___ = FStar_Options.restore_cmd_line_options true in
      let uu___1 =
        FStar_Extraction_ML_UEnv.extend_with_module_name g
          m.FStar_Syntax_Syntax.name in
      match uu___1 with
      | (name, g1) ->
          let g2 =
            let uu___2 =
              let uu___3 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
              FStar_TypeChecker_Env.set_current_module uu___3
                m.FStar_Syntax_Syntax.name in
            FStar_Extraction_ML_UEnv.set_tcenv g1 uu___2 in
          let g3 = FStar_Extraction_ML_UEnv.set_current_module g2 name in
          let uu___2 =
            FStar_Util.fold_map
              (fun g4 ->
                 fun se ->
                   let uu___3 =
                     let uu___4 =
                       FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                     FStar_Options.debug_module uu___4 in
                   if uu___3
                   then
                     let nm =
                       let uu___4 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lids_of_sigelt se)
                           (FStar_List.map FStar_Ident.string_of_lid) in
                       FStar_All.pipe_right uu___4 (FStar_String.concat ", ") in
                     (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                      (let uu___5 = FStar_Util.format1 "---Extracted {%s}" nm in
                       FStar_Util.measure_execution_time uu___5
                         (fun uu___6 -> extract_sig g4 se)))
                   else extract_sig g4 se) g3
              m.FStar_Syntax_Syntax.declarations in
          (match uu___2 with
           | (g4, sigs) ->
               let mlm = FStar_List.flatten sigs in
               let is_kremlin =
                 let uu___3 = FStar_Options.codegen () in
                 uu___3 =
                   (FStar_Pervasives_Native.Some FStar_Options.Kremlin) in
               let uu___3 =
                 (let uu___4 =
                    FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                  uu___4 <> "Prims") &&
                   (is_kremlin ||
                      (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)) in
               if uu___3
               then
                 ((let uu___5 =
                     let uu___6 = FStar_Options.silent () in
                     Prims.op_Negation uu___6 in
                   if uu___5
                   then
                     let uu___6 =
                       FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                     FStar_Util.print1 "Extracted module %s\n" uu___6
                   else ());
                  (g4,
                    (FStar_Pervasives_Native.Some
                       (FStar_Extraction_ML_Syntax.MLLib
                          [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                             (FStar_Extraction_ML_Syntax.MLLib []))]))))
               else (g4, FStar_Pervasives_Native.None))
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      (let uu___1 = FStar_Options.restore_cmd_line_options true in
       FStar_All.pipe_left (fun uu___2 -> ()) uu___1);
      (let uu___2 =
         let uu___3 =
           let uu___4 = FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Options.should_extract uu___4 in
         Prims.op_Negation uu___3 in
       if uu___2
       then
         let uu___3 =
           let uu___4 = FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu___4 in
         failwith uu___3
       else ());
      (let uu___2 = FStar_Options.interactive () in
       if uu___2
       then (g, FStar_Pervasives_Native.None)
       else
         (let nm = FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          let uu___4 =
            FStar_Syntax_Unionfind.with_uf_enabled
              (fun uu___5 ->
                 FStar_Errors.with_ctx
                   (Prims.op_Hat "While extracting module " nm)
                   (fun uu___6 ->
                      let uu___7 = FStar_Options.debug_any () in
                      if uu___7
                      then
                        let msg =
                          FStar_Util.format1 "Extracting module %s" nm in
                        FStar_Util.measure_execution_time msg
                          (fun uu___8 -> extract' g m)
                      else extract' g m)) in
          match uu___4 with
          | (g1, mllib) ->
              let uu___5 =
                match mllib with
                | FStar_Pervasives_Native.None -> (g1, mllib)
                | FStar_Pervasives_Native.Some mllib1 ->
                    let uu___6 =
                      FStar_Extraction_ML_UEnv.with_typars_env g1
                        (fun e ->
                           FStar_Extraction_ML_RemoveUnusedParameters.elim_mllib
                             e mllib1) in
                    (match uu___6 with
                     | (g2, mllib2) ->
                         (g2, (FStar_Pervasives_Native.Some mllib2))) in
              (match uu___5 with
               | (g2, mllib1) ->
                   ((let uu___7 = FStar_Options.restore_cmd_line_options true in
                     FStar_All.pipe_left (fun uu___8 -> ()) uu___7);
                    (let uu___7 = FStar_Extraction_ML_UEnv.exit_module g2 in
                     (uu___7, mllib1))))))
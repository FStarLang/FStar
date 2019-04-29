open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid ->
    fun t ->
      let uu____25 =
        let uu____32 =
          let uu____33 =
            let uu____50 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            let uu____53 =
              let uu____64 = FStar_Syntax_Syntax.iarg t in
              let uu____73 =
                let uu____84 =
                  let uu____93 =
                    let uu____94 =
                      let uu____101 =
                        let uu____102 =
                          let uu____103 =
                            let uu____109 =
                              let uu____111 =
                                FStar_Syntax_Print.lid_to_string lid in
                              Prims.op_Hat "Not yet implemented:" uu____111 in
                            (uu____109, FStar_Range.dummyRange) in
                          FStar_Const.Const_string uu____103 in
                        FStar_Syntax_Syntax.Tm_constant uu____102 in
                      FStar_Syntax_Syntax.mk uu____101 in
                    uu____94 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____93 in
                [uu____84] in
              uu____64 :: uu____73 in
            (uu____50, uu____53) in
          FStar_Syntax_Syntax.Tm_app uu____33 in
        FStar_Syntax_Syntax.mk uu____32 in
      uu____25 FStar_Pervasives_Native.None FStar_Range.dummyRange
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid ->
    fun t ->
      let imp =
        let uu____177 = FStar_Syntax_Util.arrow_formals t in
        match uu____177 with
        | ([], t1) ->
            let b =
              let uu____220 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____220 in
            let uu____228 = fail_exp lid t1 in
            FStar_Syntax_Util.abs [b] uu____228 FStar_Pervasives_Native.None
        | (bs, t1) ->
            let uu____265 = fail_exp lid t1 in
            FStar_Syntax_Util.abs bs uu____265 FStar_Pervasives_Native.None in
      let lb =
        let uu____269 =
          let uu____274 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Util.Inr uu____274 in
        {
          FStar_Syntax_Syntax.lbname = uu____269;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid;
          FStar_Syntax_Syntax.lbdef = imp;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = (imp.FStar_Syntax_Syntax.pos)
        } in
      lb
let (mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident) =
  fun x -> x
let (lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun id1 ->
    FStar_Extraction_ML_Syntax.avoid_keyword
      (id1.FStar_Ident.ident).FStar_Ident.idText
let as_pair :
  'Auu____296 . 'Auu____296 Prims.list -> ('Auu____296 * 'Auu____296) =
  fun uu___0_307 ->
    match uu___0_307 with
    | a::b::[] -> (a, b)
    | uu____312 -> failwith "Expected a list with 2 elements"
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_327 ->
    match uu___1_327 with
    | FStar_Syntax_Syntax.Assumption ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____330 -> FStar_Pervasives_Native.None
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x ->
    let uu____339 = FStar_Syntax_Subst.compress x in
    match uu____339 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____343;
        FStar_Syntax_Syntax.vars = uu____344;_} ->
        let uu____347 =
          let uu____349 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____349 in
        (match uu____347 with
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
         | uu____359 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____362;
             FStar_Syntax_Syntax.vars = uu____363;_},
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, uu____365));
              FStar_Syntax_Syntax.pos = uu____366;
              FStar_Syntax_Syntax.vars = uu____367;_},
            uu____368)::[]);
        FStar_Syntax_Syntax.pos = uu____369;
        FStar_Syntax_Syntax.vars = uu____370;_} ->
        let uu____413 =
          let uu____415 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____415 in
        (match uu____413 with
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
         | uu____424 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate", uu____426));
        FStar_Syntax_Syntax.pos = uu____427;
        FStar_Syntax_Syntax.vars = uu____428;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline", uu____433));
        FStar_Syntax_Syntax.pos = uu____434;
        FStar_Syntax_Syntax.vars = uu____435;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute", uu____440));
        FStar_Syntax_Syntax.pos = uu____441;
        FStar_Syntax_Syntax.vars = uu____442;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____448);
        FStar_Syntax_Syntax.pos = uu____449;
        FStar_Syntax_Syntax.vars = uu____450;_} -> extract_meta x1
    | uu____457 -> FStar_Pervasives_Native.None
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas -> FStar_List.choose extract_meta metas
let binders_as_mlty_binders :
  'Auu____477 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____477) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env ->
    fun bs ->
      FStar_Util.fold_map
        (fun env1 ->
           fun uu____519 ->
             match uu____519 with
             | (bv, uu____530) ->
                 let uu____531 =
                   let uu____532 =
                     let uu____535 =
                       let uu____536 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____536 in
                     FStar_Pervasives_Native.Some uu____535 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____532 in
                 let uu____538 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____531, uu____538)) env bs
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
    let uu____739 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____741 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____744 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____746 =
      let uu____748 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d ->
                let uu____762 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____764 =
                  let uu____766 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.op_Hat " : " uu____766 in
                Prims.op_Hat uu____762 uu____764)) in
      FStar_All.pipe_right uu____748 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____739 uu____741 uu____744
      uu____746
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun attrs ->
          let uu____820 =
            FStar_Util.fold_map
              (fun env1 ->
                 fun se ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l, _us, bs, t, _mut_i, datas) ->
                       let uu____868 = FStar_Syntax_Subst.open_term bs t in
                       (match uu____868 with
                        | (bs1, t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1 ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d, uu____907, t2, l', nparams,
                                           uu____911)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____918 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2 in
                                          (match uu____918 with
                                           | (bs', body) ->
                                               let uu____957 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
                                               (match uu____957 with
                                                | (bs_params, rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____1048 ->
                                                           fun uu____1049 ->
                                                             match (uu____1048,
                                                                    uu____1049)
                                                             with
                                                             | ((b',
                                                                 uu____1075),
                                                                (b,
                                                                 uu____1077))
                                                                 ->
                                                                 let uu____1098
                                                                   =
                                                                   let uu____1105
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                   (b',
                                                                    uu____1105) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1098)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____1111 =
                                                        let uu____1112 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1112 in
                                                      FStar_All.pipe_right
                                                        uu____1111
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1115 -> [])) in
                            let metadata =
                              let uu____1119 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs) in
                              let uu____1122 =
                                FStar_List.choose flag_of_qual quals in
                              FStar_List.append uu____1119 uu____1122 in
                            let fv =
                              FStar_Syntax_Syntax.lid_as_fv l
                                FStar_Syntax_Syntax.delta_constant
                                FStar_Pervasives_Native.None in
                            let env2 =
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                fv in
                            (env2,
                              [{
                                 ifv = fv;
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____1129 -> (env1, [])) env ses in
          match uu____820 with
          | (env1, ifams) -> (env1, (FStar_List.flatten ifams))
type iface =
  {
  iface_module_name: FStar_Extraction_ML_Syntax.mlpath ;
  iface_bindings:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list
    ;
  iface_tydefs: FStar_Extraction_ML_UEnv.tydef Prims.list ;
  iface_type_names: FStar_Syntax_Syntax.fv Prims.list }
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
  iface -> FStar_Extraction_ML_UEnv.tydef Prims.list) =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_tydefs
let (__proj__Mkiface__item__iface_type_names :
  iface -> FStar_Syntax_Syntax.fv Prims.list) =
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
    let uu___208_1309 = empty_iface in
    {
      iface_module_name = (uu___208_1309.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___208_1309.iface_tydefs);
      iface_type_names = (uu___208_1309.iface_type_names)
    }
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds ->
    let uu___211_1320 = empty_iface in
    let uu____1321 =
      FStar_List.map (fun td -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds in
    {
      iface_module_name = (uu___211_1320.iface_module_name);
      iface_bindings = (uu___211_1320.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1321
    }
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs ->
    let uu___215_1336 = empty_iface in
    {
      iface_module_name = (uu___215_1336.iface_module_name);
      iface_bindings = (uu___215_1336.iface_bindings);
      iface_tydefs = (uu___215_1336.iface_tydefs);
      iface_type_names = fvs
    }
let (iface_union : iface -> iface -> iface) =
  fun if1 ->
    fun if2 ->
      let uu____1348 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name in
      {
        iface_module_name = uu____1348;
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
  'Auu____1393 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1393 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____1425 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr in
      let uu____1427 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme in
      let uu____1429 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1425 uu____1427
        uu____1429
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm ->
    fun uu____1447 ->
      match uu____1447 with
      | (fv, exp_binding) ->
          let uu____1455 = FStar_Syntax_Print.fv_to_string fv in
          let uu____1457 = print_exp_binding cm exp_binding in
          FStar_Util.format2 "(%s, %s)" uu____1455 uu____1457
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm ->
    fun tydef ->
      let uu____1472 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv in
      let uu____1474 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def in
      FStar_Util.format2 "(%s, %s)" uu____1472 uu____1474
let (iface_to_string : iface -> Prims.string) =
  fun iface1 ->
    let cm = iface1.iface_module_name in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn in
    let uu____1492 =
      let uu____1494 =
        FStar_List.map (print_binding cm) iface1.iface_bindings in
      FStar_All.pipe_right uu____1494 (FStar_String.concat "\n") in
    let uu____1508 =
      let uu____1510 = FStar_List.map (print_tydef cm) iface1.iface_tydefs in
      FStar_All.pipe_right uu____1510 (FStar_String.concat "\n") in
    let uu____1520 =
      let uu____1522 = FStar_List.map print_type_name iface1.iface_type_names in
      FStar_All.pipe_right uu____1522 (FStar_String.concat "\n") in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1492 uu____1508
      uu____1520
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule in
    let gamma =
      FStar_List.collect
        (fun uu___2_1555 ->
           match uu___2_1555 with
           | FStar_Extraction_ML_UEnv.Fv (b, e) -> [(b, e)]
           | uu____1572 -> []) env.FStar_Extraction_ML_UEnv.env_bindings in
    let uu____1577 =
      let uu____1579 = FStar_List.map (print_binding cm) gamma in
      FStar_All.pipe_right uu____1579 (FStar_String.concat "\n") in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1577
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
          let uu____1639 =
            let uu____1648 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
            match uu____1648 with
            | (tcenv, uu____1666, def_typ) ->
                let uu____1672 = as_pair def_typ in (tcenv, uu____1672) in
          match uu____1639 with
          | (tcenv, (lbdef, lbtyp)) ->
              let lbtyp1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant] tcenv lbtyp in
              let lbdef1 =
                FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef
                  lbtyp1 in
              let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let def =
                let uu____1703 =
                  let uu____1704 = FStar_Syntax_Subst.compress lbdef1 in
                  FStar_All.pipe_right uu____1704 FStar_Syntax_Util.unmeta in
                FStar_All.pipe_right uu____1703 FStar_Syntax_Util.un_uinst in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1712 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1731 -> def in
              let uu____1732 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1743) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1768 -> ([], def1) in
              (match uu____1732 with
               | (bs, body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1788 ->
                          match uu___3_1788 with
                          | FStar_Syntax_Syntax.Assumption -> true
                          | uu____1791 -> false) quals in
                   let uu____1793 = binders_as_mlty_binders env bs in
                   (match uu____1793 with
                    | (env1, ml_bs) ->
                        let body1 =
                          let uu____1820 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body in
                          FStar_All.pipe_right uu____1820
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                        let mangled_projector =
                          let uu____1825 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1832 ->
                                    match uu___4_1832 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1834 -> true
                                    | uu____1840 -> false)) in
                          if uu____1825
                          then
                            let mname = mangle_projector_lid lid in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None in
                        let metadata =
                          let uu____1854 = extract_metadata attrs in
                          let uu____1857 =
                            FStar_List.choose flag_of_qual quals in
                          FStar_List.append uu____1854 uu____1857 in
                        let td =
                          let uu____1880 = lident_as_mlsymbol lid in
                          (assumed, uu____1880, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                        let def2 =
                          let uu____1892 =
                            let uu____1893 =
                              let uu____1894 = FStar_Ident.range_of_lid lid in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1894 in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1893 in
                          [uu____1892;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]] in
                        let uu____1895 =
                          let uu____1900 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_1906 ->
                                    match uu___5_1906 with
                                    | FStar_Syntax_Syntax.Assumption -> true
                                    | FStar_Syntax_Syntax.New -> true
                                    | uu____1910 -> false)) in
                          if uu____1900
                          then
                            let uu____1917 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv in
                            (uu____1917, (iface_of_type_names [fv]))
                          else
                            (let uu____1920 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td in
                             match uu____1920 with
                             | (env2, tydef) ->
                                 let uu____1931 = iface_of_tydefs [tydef] in
                                 (env2, uu____1931)) in
                        (match uu____1895 with
                         | (env2, iface1) -> (env2, iface1, def2))))
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
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.env_tcenv
              lb.FStar_Syntax_Syntax.lbtyp in
          let uu____1990 = FStar_Syntax_Util.arrow_formals lbtyp in
          match uu____1990 with
          | (bs, uu____2014) ->
              let uu____2035 = binders_as_mlty_binders env bs in
              (match uu____2035 with
               | (env1, ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top in
                   let metadata =
                     let uu____2067 = extract_metadata attrs in
                     let uu____2070 = FStar_List.choose flag_of_qual quals in
                     FStar_List.append uu____2067 uu____2070 in
                   let assumed = false in
                   let td =
                     let uu____2096 = lident_as_mlsymbol lid in
                     (assumed, uu____2096, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body))) in
                   let def =
                     let uu____2109 =
                       let uu____2110 =
                         let uu____2111 = FStar_Ident.range_of_lid lid in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____2111 in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____2110 in
                     [uu____2109; FStar_Extraction_ML_Syntax.MLM_Ty [td]] in
                   let uu____2112 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td in
                   (match uu____2112 with
                    | (env2, tydef) ->
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
          let uu____2193 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2193 in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____2200 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
        match uu____2200 with | (env2, uu____2219, b) -> (env2, (fvv, b)) in
      let extract_one_family env1 ind =
        let uu____2258 = binders_as_mlty_binders env1 ind.iparams in
        match uu____2258 with
        | (env_iparams, vars) ->
            let uu____2286 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1) in
            (match uu____2286 with | (env2, ctors) -> (env2, ctors)) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu____2350, t, uu____2352, uu____2353, uu____2354);
            FStar_Syntax_Syntax.sigrng = uu____2355;
            FStar_Syntax_Syntax.sigquals = uu____2356;
            FStar_Syntax_Syntax.sigmeta = uu____2357;
            FStar_Syntax_Syntax.sigattrs = uu____2358;_}::[],
          uu____2359),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu____2378 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu____2378 with
           | (env1, ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu____2411), quals) ->
          let uu____2425 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____2425 with
           | (env1, ifams) ->
               let uu____2442 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____2442 with
                | (env2, td) ->
                    let uu____2483 =
                      let uu____2484 =
                        let uu____2485 =
                          FStar_List.map (fun x -> x.ifv) ifams in
                        iface_of_type_names uu____2485 in
                      iface_union uu____2484
                        (iface_of_bindings (FStar_List.flatten td)) in
                    (env2, uu____2483)))
      | uu____2494 -> failwith "Unexpected signature element"
let (extract_type_declaration :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.univ_name Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1
                Prims.list))
  =
  fun g ->
    fun lid ->
      fun quals ->
        fun attrs ->
          fun univs1 ->
            fun t ->
              let uu____2569 =
                let uu____2571 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2577 ->
                          match uu___6_2577 with
                          | FStar_Syntax_Syntax.Assumption -> true
                          | uu____2580 -> false)) in
                Prims.op_Negation uu____2571 in
              if uu____2569
              then (g, empty_iface, [])
              else
                (let uu____2595 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2595 with
                 | (bs, uu____2619) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     let lb =
                       let uu____2642 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2642;
                         FStar_Syntax_Syntax.lbattrs = attrs;
                         FStar_Syntax_Syntax.lbpos =
                           (t.FStar_Syntax_Syntax.pos)
                       } in
                     extract_typ_abbrev g quals attrs lb)
let (extract_reifiable_effect :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Extraction_ML_UEnv.uenv * iface *
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun ed ->
      let extend_env g1 lid ml_name tm tysc =
        let fv =
          FStar_Syntax_Syntax.lid_as_fv lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
        let uu____2705 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false in
        match uu____2705 with
        | (g2, mangled_name, exp_binding) ->
            ((let uu____2727 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2727
              then FStar_Util.print1 "Mangled name: %s\n" mangled_name
              else ());
             (let lb =
                {
                  FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                  FStar_Extraction_ML_Syntax.mllb_tysc =
                    FStar_Pervasives_Native.None;
                  FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                  FStar_Extraction_ML_Syntax.mllb_def = tm;
                  FStar_Extraction_ML_Syntax.mllb_meta = [];
                  FStar_Extraction_ML_Syntax.print_typ = false
                } in
              (g2, (iface_of_bindings [(fv, exp_binding)]),
                (FStar_Extraction_ML_Syntax.MLM_Let
                   (FStar_Extraction_ML_Syntax.NonRec, [lb]))))) in
      let rec extract_fv tm =
        (let uu____2763 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify") in
         if uu____2763
         then
           let uu____2768 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2768
         else ());
        (let uu____2773 =
           let uu____2774 = FStar_Syntax_Subst.compress tm in
           uu____2774.FStar_Syntax_Syntax.n in
         match uu____2773 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1, uu____2782) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             let uu____2789 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
             (match uu____2789 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2794;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2795;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2797;_} ->
                  let uu____2800 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                  (uu____2800, tysc))
         | uu____2801 ->
             let uu____2802 =
               let uu____2804 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos in
               let uu____2806 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2804 uu____2806 in
             failwith uu____2802) in
      let extract_action g1 a =
        (let uu____2834 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify") in
         if uu____2834
         then
           let uu____2839 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ in
           let uu____2841 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2839
             uu____2841
         else ());
        (let uu____2846 = FStar_Extraction_ML_UEnv.action_name ed a in
         match uu____2846 with
         | (a_nm, a_lid) ->
             let lbname =
               let uu____2866 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun in
               FStar_Util.Inl uu____2866 in
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
                 FStar_Pervasives_Native.None
                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
             let uu____2896 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
             (match uu____2896 with
              | (a_let, uu____2912, ty) ->
                  ((let uu____2915 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify") in
                    if uu____2915
                    then
                      let uu____2920 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2920
                    else ());
                   (let uu____2925 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2948, mllb::[]), uu____2950) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None ->
                               failwith "No type scheme")
                      | uu____2990 -> failwith "Impossible" in
                    match uu____2925 with
                    | (exp, tysc) ->
                        ((let uu____3028 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify") in
                          if uu____3028
                          then
                            ((let uu____3034 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc) in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____3034);
                             FStar_List.iter
                               (fun x ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____3050 = extend_env g1 a_lid a_nm exp tysc in
                          match uu____3050 with
                          | (env, iface1, impl) -> (env, (iface1, impl)))))))) in
      let uu____3072 =
        let uu____3079 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr) in
        match uu____3079 with
        | (return_tm, ty_sc) ->
            let uu____3096 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
            (match uu____3096 with
             | (return_nm, return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc) in
      match uu____3072 with
      | (g1, return_iface, return_decl) ->
          let uu____3121 =
            let uu____3128 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr) in
            match uu____3128 with
            | (bind_tm, ty_sc) ->
                let uu____3145 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                (match uu____3145 with
                 | (bind_nm, bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
          (match uu____3121 with
           | (g2, bind_iface, bind_decl) ->
               let uu____3170 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions in
               (match uu____3170 with
                | (g3, actions) ->
                    let uu____3207 = FStar_List.unzip actions in
                    (match uu____3207 with
                     | (actions_iface, actions1) ->
                         let uu____3234 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface) in
                         (g3, uu____3234, (return_decl :: bind_decl ::
                           actions1)))))
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
        let uu____3265 =
          FStar_Util.for_some
            (fun lb ->
               let uu____3270 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp in
               Prims.op_Negation uu____3270) lbs in
        if uu____3265
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3293 =
             FStar_List.fold_left
               (fun uu____3328 ->
                  fun lb ->
                    match uu____3328 with
                    | (env1, iface_opt, impls) ->
                        let uu____3369 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb in
                        (match uu____3369 with
                         | (env2, iface1, impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3403 = iface_union iface' iface1 in
                                   FStar_Pervasives_Native.Some uu____3403 in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs in
           match uu____3293 with
           | (env1, iface_opt, impls) ->
               let uu____3443 = FStar_Option.get iface_opt in
               let uu____3444 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten in
               (env1, uu____3443, uu____3444))
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3476 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3485 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3502 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3521 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t in
          (match uu____3521 with | (env, iface1, uu____3536) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____3542) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3551 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb in
          (match uu____3551 with | (env, iface1, uu____3566) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true, lbs), uu____3572) when
          FStar_Util.for_some
            (fun lb ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3585 = extract_let_rec_types se g lbs in
          (match uu____3585 with | (env, iface1, uu____3600) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, _univs, t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____3611 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3617 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t in
               Prims.op_Negation uu____3617) in
          if uu____3611
          then
            let uu____3624 =
              let uu____3635 =
                let uu____3636 =
                  let uu____3639 = always_fail lid t in [uu____3639] in
                (false, uu____3636) in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3635 in
            (match uu____3624 with
             | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____3665) ->
          let uu____3670 = FStar_Extraction_ML_Term.extract_lb_iface g lbs in
          (match uu____3670 with
           | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3699 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3700 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3701 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3708 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3709 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3724 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3737 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders) in
          if uu____3737
          then
            let uu____3750 = extract_reifiable_effect g ed in
            (match uu____3750 with
             | (env, iface1, uu____3765) -> (env, iface1))
          else (g, empty_iface)
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu____3787 = FStar_Options.interactive () in
      if uu____3787
      then (g, empty_iface)
      else
        (let uu____3796 = FStar_Options.restore_cmd_line_options true in
         let decls = modul.FStar_Syntax_Syntax.declarations in
         let iface1 =
           let uu___609_3800 = empty_iface in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___609_3800.iface_bindings);
             iface_tydefs = (uu___609_3800.iface_tydefs);
             iface_type_names = (uu___609_3800.iface_type_names)
           } in
         let res =
           FStar_List.fold_left
             (fun uu____3818 ->
                fun se ->
                  match uu____3818 with
                  | (g1, iface2) ->
                      let uu____3830 = extract_sigelt_iface g1 se in
                      (match uu____3830 with
                       | (g2, iface') ->
                           let uu____3841 = iface_union iface2 iface' in
                           (g2, uu____3841))) (g, iface1) decls in
         (let uu____3843 = FStar_Options.restore_cmd_line_options true in
          FStar_All.pipe_left (fun a1 -> ()) uu____3843);
         res)
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu____3860 = FStar_Options.debug_any () in
      if uu____3860
      then
        let uu____3867 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
        FStar_Util.measure_execution_time uu____3867
          (fun uu____3875 -> extract_iface' g modul)
      else extract_iface' g modul
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g ->
    fun iface1 ->
      let uu___627_3889 = g in
      let uu____3890 =
        let uu____3893 =
          FStar_List.map (fun _3900 -> FStar_Extraction_ML_UEnv.Fv _3900)
            iface1.iface_bindings in
        FStar_List.append uu____3893 g.FStar_Extraction_ML_UEnv.env_bindings in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___627_3889.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____3890;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___627_3889.FStar_Extraction_ML_UEnv.currentModule)
      }
let (extract_bundle :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun se ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____3978 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____3978 in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses] in
        let names1 =
          let uu____3986 =
            let uu____3987 =
              let uu____3990 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____3990 in
            uu____3987.FStar_Syntax_Syntax.n in
          match uu____3986 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, uu____3995) ->
              FStar_List.map
                (fun uu____4028 ->
                   match uu____4028 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4037;
                        FStar_Syntax_Syntax.sort = uu____4038;_},
                      uu____4039) -> ppname.FStar_Ident.idText) bs
          | uu____4047 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____4055 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
        match uu____4055 with
        | (env2, uu____4082, uu____4083) ->
            let uu____4086 =
              let uu____4099 = lident_as_mlsymbol ctor.dname in
              let uu____4101 =
                let uu____4109 = FStar_Extraction_ML_Util.argTypes mlt in
                FStar_List.zip names1 uu____4109 in
              (uu____4099, uu____4101) in
            (env2, uu____4086) in
      let extract_one_family env1 ind =
        let uu____4170 = binders_as_mlty_binders env1 ind.iparams in
        match uu____4170 with
        | (env_iparams, vars) ->
            let uu____4214 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1) in
            (match uu____4214 with
             | (env2, ctors) ->
                 let uu____4321 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____4321 with
                  | (indices, uu____4363) ->
                      let ml_params =
                        let uu____4388 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i ->
                                  fun uu____4414 ->
                                    let uu____4422 =
                                      FStar_Util.string_of_int i in
                                    Prims.op_Hat "'dummyV" uu____4422)) in
                        FStar_List.append vars uu____4388 in
                      let tbody =
                        let uu____4427 =
                          FStar_Util.find_opt
                            (fun uu___7_4432 ->
                               match uu___7_4432 with
                               | FStar_Syntax_Syntax.RecordType uu____4434 ->
                                   true
                               | uu____4444 -> false) ind.iquals in
                        match uu____4427 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns, ids)) ->
                            let uu____4456 = FStar_List.hd ctors in
                            (match uu____4456 with
                             | (uu____4481, c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1 ->
                                        fun uu____4525 ->
                                          match uu____4525 with
                                          | (uu____4536, ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1]) in
                                              let uu____4541 =
                                                lident_as_mlsymbol lid in
                                              (uu____4541, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4544 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____4547 =
                        let uu____4570 = lident_as_mlsymbol ind.iname in
                        (false, uu____4570, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env2, uu____4547))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu____4615, t, uu____4617, uu____4618, uu____4619);
            FStar_Syntax_Syntax.sigrng = uu____4620;
            FStar_Syntax_Syntax.sigquals = uu____4621;
            FStar_Syntax_Syntax.sigmeta = uu____4622;
            FStar_Syntax_Syntax.sigattrs = uu____4623;_}::[],
          uu____4624),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu____4643 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu____4643 with
           | (env1, ctor) ->
               (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu____4696), quals) ->
          let uu____4710 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____4710 with
           | (env1, ifams) ->
               let uu____4729 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____4729 with
                | (env2, td) ->
                    (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____4838 -> failwith "Unexpected signature element"
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
             let uu____4896 = FStar_Syntax_Util.head_and_args t in
             match uu____4896 with
             | (head1, args) ->
                 let uu____4944 =
                   let uu____4946 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1 in
                   Prims.op_Negation uu____4946 in
                 if uu____4944
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s, uu____4965));
                         FStar_Syntax_Syntax.pos = uu____4966;
                         FStar_Syntax_Syntax.vars = uu____4967;_},
                       uu____4968)::[] ->
                        let uu____5007 =
                          let uu____5011 = FStar_Util.int_of_string s in
                          FStar_Pervasives_Native.Some uu____5011 in
                        FStar_Pervasives_Native.Some uu____5007
                    | uu____5017 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None)) in
      let uu____5032 =
        let uu____5034 = FStar_Options.codegen () in
        uu____5034 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin) in
      if uu____5032
      then []
      else
        (let uu____5044 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs in
         match uu____5044 with
         | FStar_Pervasives_Native.None -> []
         | FStar_Pervasives_Native.Some arity_opt ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
                  let mk_registration lb =
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                    let fv_lid1 =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp in
                    let ml_name_str =
                      let uu____5086 =
                        let uu____5087 = FStar_Ident.string_of_lid fv_lid1 in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5087 in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5086 in
                    let uu____5089 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str in
                    match uu____5089 with
                    | FStar_Pervasives_Native.Some
                        (interp, nbe_interp, arity, plugin1) ->
                        let uu____5122 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp]) in
                        (match uu____5122 with
                         | (register, args) ->
                             let h =
                               let uu____5159 =
                                 let uu____5160 =
                                   let uu____5161 =
                                     FStar_Ident.lid_of_str register in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____5161 in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____5160 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____5159 in
                             let arity1 =
                               let uu____5163 =
                                 let uu____5164 =
                                   let uu____5176 =
                                     FStar_Util.string_of_int arity in
                                   (uu____5176, FStar_Pervasives_Native.None) in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5164 in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5163 in
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
              | uu____5205 -> []))
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun se ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u ->
           let uu____5233 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5233);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5242 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5251 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5268 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5285 = extract_reifiable_effect g ed in
           (match uu____5285 with | (env, _iface, impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5309 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5323 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5329 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t in
           (match uu____5329 with | (env, uu____5345, impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____5354) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5363 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb in
           (match uu____5363 with | (env, uu____5379, impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true, lbs), uu____5388) when
           FStar_Util.for_some
             (fun lb ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5401 = extract_let_rec_types se g lbs in
           (match uu____5401 with | (env, uu____5417, impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs, uu____5426) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____5437 =
             let uu____5446 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs in
             match uu____5446 with
             | FStar_Pervasives_Native.None ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats, (tau, FStar_Pervasives_Native.None)::uu____5475) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats, args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None)) in
           (match uu____5437 with
            | (attrs1, post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef in
                  let uu___857_5561 = lb in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___857_5561.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___857_5561.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___857_5561.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___857_5561.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___857_5561.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___857_5561.FStar_Syntax_Syntax.lbpos)
                  } in
                let lbs1 =
                  let uu____5570 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.snd lbs in
                  ((FStar_Pervasives_Native.fst lbs), uu____5570) in
                let uu____5588 =
                  let uu____5595 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5595 in
                (match uu____5588 with
                 | (ml_let, uu____5612, uu____5613) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor, bindings), uu____5622) ->
                          let flags = FStar_List.choose flag_of_qual quals in
                          let flags' = extract_metadata attrs1 in
                          let uu____5639 =
                            FStar_List.fold_left2
                              (fun uu____5665 ->
                                 fun ml_lb ->
                                   fun uu____5667 ->
                                     match (uu____5665, uu____5667) with
                                     | ((env, ml_lbs),
                                        {
                                          FStar_Syntax_Syntax.lbname = lbname;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____5689;
                                          FStar_Syntax_Syntax.lbtyp = t;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____5691;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____5692;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____5693;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____5694;_})
                                         ->
                                         let uu____5719 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased) in
                                         if uu____5719
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5736 =
                                                let uu____5739 =
                                                  FStar_Util.right lbname in
                                                uu____5739.FStar_Syntax_Syntax.fv_name in
                                              uu____5736.FStar_Syntax_Syntax.v in
                                            let flags'' =
                                              let uu____5743 =
                                                let uu____5744 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____5744.FStar_Syntax_Syntax.n in
                                              match uu____5743 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5749,
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       FStar_Syntax_Syntax.Comp
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____5750;
                                                         FStar_Syntax_Syntax.effect_name
                                                           = e;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = uu____5752;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____5753;
                                                         FStar_Syntax_Syntax.flags
                                                           = uu____5754;_};
                                                     FStar_Syntax_Syntax.pos
                                                       = uu____5755;
                                                     FStar_Syntax_Syntax.vars
                                                       = uu____5756;_})
                                                  when
                                                  let uu____5791 =
                                                    FStar_Ident.string_of_lid
                                                      e in
                                                  uu____5791 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____5795 -> [] in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'') in
                                            let ml_lb1 =
                                              let uu___905_5800 = ml_lb in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___905_5800.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___905_5800.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___905_5800.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___905_5800.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___905_5800.FStar_Extraction_ML_Syntax.print_typ)
                                              } in
                                            let uu____5801 =
                                              let uu____5806 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_5813 ->
                                                        match uu___8_5813
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____5815 ->
                                                            true
                                                        | uu____5821 -> false)) in
                                              if uu____5806
                                              then
                                                let mname =
                                                  let uu____5837 =
                                                    mangle_projector_lid
                                                      lb_lid in
                                                  FStar_All.pipe_right
                                                    uu____5837
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                                let uu____5846 =
                                                  let uu____5854 =
                                                    FStar_Util.right lbname in
                                                  let uu____5855 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____5854 mname
                                                    uu____5855
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false in
                                                match uu____5846 with
                                                | (env1, uu____5862,
                                                   uu____5863) ->
                                                    (env1,
                                                      (let uu___918_5867 =
                                                         ml_lb1 in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___918_5867.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___918_5867.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___918_5867.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___918_5867.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___918_5867.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____5874 =
                                                   let uu____5882 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____5882
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false in
                                                 match uu____5874 with
                                                 | (env1, uu____5889,
                                                    uu____5890) ->
                                                     (env1, ml_lb1)) in
                                            match uu____5801 with
                                            | (g1, ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1) in
                          (match uu____5639 with
                           | (g1, ml_lbs') ->
                               let uu____5920 =
                                 let uu____5923 =
                                   let uu____5926 =
                                     let uu____5927 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____5927 in
                                   [uu____5926;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))] in
                                 let uu____5930 = maybe_register_plugin g1 se in
                                 FStar_List.append uu____5923 uu____5930 in
                               (g1, uu____5920))
                      | uu____5935 ->
                          let uu____5936 =
                            let uu____5938 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____5938 in
                          failwith uu____5936)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____5948, t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____5953 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____5959 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t in
                Prims.op_Negation uu____5959) in
           if uu____5953
           then
             let always_fail1 =
               let uu___938_5969 = se in
               let uu____5970 =
                 let uu____5971 =
                   let uu____5978 =
                     let uu____5979 =
                       let uu____5982 = always_fail lid t in [uu____5982] in
                     (false, uu____5979) in
                   (uu____5978, []) in
                 FStar_Syntax_Syntax.Sig_let uu____5971 in
               {
                 FStar_Syntax_Syntax.sigel = uu____5970;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___938_5969.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___938_5969.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___938_5969.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___938_5969.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____5989 = extract_sig g always_fail1 in
             (match uu____5989 with
              | (g1, mlm) ->
                  let uu____6008 =
                    FStar_Util.find_map quals
                      (fun uu___9_6013 ->
                         match uu___9_6013 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6017 -> FStar_Pervasives_Native.None) in
                  (match uu____6008 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6025 =
                         let uu____6028 =
                           let uu____6029 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6029 in
                         let uu____6030 =
                           let uu____6033 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____6033] in
                         uu____6028 :: uu____6030 in
                       (g1, uu____6025)
                   | uu____6036 ->
                       let uu____6039 =
                         FStar_Util.find_map quals
                           (fun uu___10_6045 ->
                              match uu___10_6045 with
                              | FStar_Syntax_Syntax.Projector (l, uu____6049)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6050 -> FStar_Pervasives_Native.None) in
                       (match uu____6039 with
                        | FStar_Pervasives_Native.Some uu____6057 -> (g1, [])
                        | uu____6060 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6070 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____6070 with
            | (ml_main, uu____6084, uu____6085) ->
                let uu____6086 =
                  let uu____6089 =
                    let uu____6090 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6090 in
                  [uu____6089; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____6086))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6093 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____6101 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6110 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6113 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
let (extract' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      let uu____6155 = FStar_Options.restore_cmd_line_options true in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name in
      let g1 =
        let uu___981_6159 = g in
        let uu____6160 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____6160;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___981_6159.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___981_6159.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___981_6159.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        } in
      let uu____6161 =
        FStar_Util.fold_map
          (fun g2 ->
             fun se ->
               let uu____6180 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
               if uu____6180
               then
                 let nm =
                   let uu____6191 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid) in
                   FStar_All.pipe_right uu____6191 (FStar_String.concat ", ") in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____6208 = FStar_Util.format1 "---Extracted {%s}" nm in
                   FStar_Util.measure_execution_time uu____6208
                     (fun uu____6218 -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations in
      match uu____6161 with
      | (g2, sigs) ->
          let mlm = FStar_List.flatten sigs in
          let is_kremlin =
            let uu____6240 = FStar_Options.codegen () in
            uu____6240 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin) in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____6255 =
                let uu____6257 = FStar_Options.silent () in
                Prims.op_Negation uu____6257 in
              if uu____6255
              then
                let uu____6260 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                FStar_Util.print1 "Extracted module %s\n" uu____6260
              else ());
             (g2,
               (FStar_Pervasives_Native.Some
                  (FStar_Extraction_ML_Syntax.MLLib
                     [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                        (FStar_Extraction_ML_Syntax.MLLib []))]))))
          else (g2, FStar_Pervasives_Native.None)
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      (let uu____6335 = FStar_Options.restore_cmd_line_options true in
       FStar_All.pipe_left (fun a2 -> ()) uu____6335);
      (let uu____6338 =
         let uu____6340 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
         Prims.op_Negation uu____6340 in
       if uu____6338
       then
         let uu____6343 =
           let uu____6345 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6345 in
         failwith uu____6343
       else ());
      (let uu____6350 = FStar_Options.interactive () in
       if uu____6350
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____6370 = FStar_Options.debug_any () in
            if uu____6370
            then
              let msg =
                let uu____6381 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
                FStar_Util.format1 "Extracting module %s\n" uu____6381 in
              FStar_Util.measure_execution_time msg
                (fun uu____6391 -> extract' g m)
            else extract' g m in
          (let uu____6395 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_left (fun a3 -> ()) uu____6395);
          res))
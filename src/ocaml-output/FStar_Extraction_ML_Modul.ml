open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____25 =
        let uu____32 =
          let uu____33 =
            let uu____50 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____53 =
              let uu____64 = FStar_Syntax_Syntax.iarg t  in
              let uu____73 =
                let uu____84 =
                  let uu____93 =
                    let uu____94 =
                      let uu____101 =
                        let uu____102 =
                          let uu____103 =
                            let uu____109 =
                              let uu____111 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____111
                               in
                            (uu____109, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____103  in
                        FStar_Syntax_Syntax.Tm_constant uu____102  in
                      FStar_Syntax_Syntax.mk uu____101  in
                    uu____94 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____93  in
                [uu____84]  in
              uu____64 :: uu____73  in
            (uu____50, uu____53)  in
          FStar_Syntax_Syntax.Tm_app uu____33  in
        FStar_Syntax_Syntax.mk uu____32  in
      uu____25 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____177 = FStar_Syntax_Util.arrow_formals t  in
        match uu____177 with
        | ([],t1) ->
            let b =
              let uu____204 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____204  in
            let uu____212 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____212 FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____233 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____233 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____237 =
          let uu____242 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____242  in
        {
          FStar_Syntax_Syntax.lbname = uu____237;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid;
          FStar_Syntax_Syntax.lbdef = imp;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = (imp.FStar_Syntax_Syntax.pos)
        }  in
      lb
  
let (mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident) =
  fun x  -> x 
let (lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun id1  ->
    FStar_Extraction_ML_Syntax.avoid_keyword
      (id1.FStar_Ident.ident).FStar_Ident.idText
  
let as_pair :
  'Auu____264 . 'Auu____264 Prims.list -> ('Auu____264 * 'Auu____264) =
  fun uu___0_275  ->
    match uu___0_275 with
    | a::b::[] -> (a, b)
    | uu____280 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_295  ->
    match uu___1_295 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____298 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____307 = FStar_Syntax_Subst.compress x  in
    match uu____307 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____311;
        FStar_Syntax_Syntax.vars = uu____312;_} ->
        let uu____315 =
          let uu____317 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____317  in
        (match uu____315 with
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
         | uu____330 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____333;
             FStar_Syntax_Syntax.vars = uu____334;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____336));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____337;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____338;_},uu____339)::[]);
        FStar_Syntax_Syntax.pos = uu____340;
        FStar_Syntax_Syntax.vars = uu____341;_} ->
        let uu____384 =
          let uu____386 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____386  in
        (match uu____384 with
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
         | uu____396 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____398));
        FStar_Syntax_Syntax.pos = uu____399;
        FStar_Syntax_Syntax.vars = uu____400;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____405));
        FStar_Syntax_Syntax.pos = uu____406;
        FStar_Syntax_Syntax.vars = uu____407;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____412));
        FStar_Syntax_Syntax.pos = uu____413;
        FStar_Syntax_Syntax.vars = uu____414;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____420);
        FStar_Syntax_Syntax.pos = uu____421;
        FStar_Syntax_Syntax.vars = uu____422;_} -> extract_meta x1
    | uu____429 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____449 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____449) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____491  ->
             match uu____491 with
             | (bv,uu____502) ->
                 let uu____503 =
                   let uu____504 =
                     let uu____507 =
                       let uu____508 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____508  in
                     FStar_Pervasives_Native.Some uu____507  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____504  in
                 let uu____510 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____503, uu____510)) env bs
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | { dname; dtyp;_} -> dname 
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | { dname; dtyp;_} -> dtyp 
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
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ifv
  
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iname
  
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iparams
  
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ityp
  
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> idatas
  
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iquals
  
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> imetadata
  
let (print_ifamily : inductive_family -> unit) =
  fun i  ->
    let uu____711 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____713 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____716 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____718 =
      let uu____720 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____734 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____736 =
                  let uu____738 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____738  in
                Prims.op_Hat uu____734 uu____736))
         in
      FStar_All.pipe_right uu____720 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____711 uu____713 uu____716
      uu____718
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        let uu____783 =
          FStar_Util.fold_map
            (fun env1  ->
               fun se  ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l,us,bs,t,_mut_i,datas) ->
                     let uu____834 = FStar_Syntax_Subst.open_univ_vars us t
                        in
                     (match uu____834 with
                      | (_us,t1) ->
                          let uu____847 = FStar_Syntax_Subst.open_term bs t1
                             in
                          (match uu____847 with
                           | (bs1,t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1  ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d,us1,t3,l',nparams,uu____893)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____900 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3
                                                in
                                             (match uu____900 with
                                              | (_us1,t4) ->
                                                  let uu____909 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4
                                                     in
                                                  (match uu____909 with
                                                   | (bs',body) ->
                                                       let uu____924 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs'
                                                          in
                                                       (match uu____924 with
                                                        | (bs_params,rest) ->
                                                            let subst1 =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____1015
                                                                    ->
                                                                   fun
                                                                    uu____1016
                                                                     ->
                                                                    match 
                                                                    (uu____1015,
                                                                    uu____1016)
                                                                    with
                                                                    | 
                                                                    ((b',uu____1042),
                                                                    (b,uu____1044))
                                                                    ->
                                                                    let uu____1065
                                                                    =
                                                                    let uu____1072
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                    (b',
                                                                    uu____1072)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____1065)
                                                                bs_params bs1
                                                               in
                                                            let t5 =
                                                              let uu____1078
                                                                =
                                                                let uu____1079
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____1079
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____1078
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1)
                                                               in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____1082 -> []))
                                  in
                               let metadata =
                                 let uu____1086 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs
                                    in
                                 let uu____1089 =
                                   FStar_List.choose flag_of_qual quals  in
                                 FStar_List.append uu____1086 uu____1089  in
                               let fv =
                                 FStar_Syntax_Syntax.lid_as_fv l
                                   FStar_Syntax_Syntax.delta_constant
                                   FStar_Pervasives_Native.None
                                  in
                               let env2 =
                                 FStar_Extraction_ML_UEnv.extend_type_name
                                   env1 fv
                                  in
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
                                  }])))
                 | uu____1096 -> (env1, [])) env ses
           in
        match uu____783 with
        | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
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
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_module_name
  
let (__proj__Mkiface__item__iface_bindings :
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_bindings
  
let (__proj__Mkiface__item__iface_tydefs :
  iface -> FStar_Extraction_ML_UEnv.tydef Prims.list) =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_tydefs
  
let (__proj__Mkiface__item__iface_type_names :
  iface -> FStar_Syntax_Syntax.fv Prims.list) =
  fun projectee  ->
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
  fun fvs  ->
    let uu___216_1276 = empty_iface  in
    {
      iface_module_name = (uu___216_1276.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___216_1276.iface_tydefs);
      iface_type_names = (uu___216_1276.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___219_1287 = empty_iface  in
    let uu____1288 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___219_1287.iface_module_name);
      iface_bindings = (uu___219_1287.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1288
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___223_1303 = empty_iface  in
    {
      iface_module_name = (uu___223_1303.iface_module_name);
      iface_bindings = (uu___223_1303.iface_bindings);
      iface_tydefs = (uu___223_1303.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1315 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1315;
        iface_bindings =
          (FStar_List.append if1.iface_bindings if2.iface_bindings);
        iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs);
        iface_type_names =
          (FStar_List.append if1.iface_type_names if2.iface_type_names)
      }
  
let (iface_union_l : iface Prims.list -> iface) =
  fun ifs  -> FStar_List.fold_right iface_union ifs empty_iface 
let (mlpath_to_string : FStar_Extraction_ML_Syntax.mlpath -> Prims.string) =
  fun p  ->
    FStar_String.concat ". "
      (FStar_List.append (FStar_Pervasives_Native.fst p)
         [FStar_Pervasives_Native.snd p])
  
let tscheme_to_string :
  'Auu____1360 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1360 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
  =
  fun cm  ->
    fun ts  ->
      FStar_Extraction_ML_Code.string_of_mlty cm
        (FStar_Pervasives_Native.snd ts)
  
let (print_exp_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.exp_binding -> Prims.string)
  =
  fun cm  ->
    fun e  ->
      let uu____1392 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1394 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1396 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1392 uu____1394
        uu____1396
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1414  ->
      match uu____1414 with
      | (fv,exp_binding) ->
          let uu____1422 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1424 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1422 uu____1424
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1439 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1441 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1439 uu____1441
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1459 =
      let uu____1461 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1461 (FStar_String.concat "\n")  in
    let uu____1475 =
      let uu____1477 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1477 (FStar_String.concat "\n")  in
    let uu____1487 =
      let uu____1489 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1489 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1459 uu____1475
      uu____1487
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___2_1522  ->
           match uu___2_1522 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1539 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____1544 =
      let uu____1546 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1546 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1544
  
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env  ->
    fun quals  ->
      fun attrs  ->
        fun lb  ->
          let uu____1606 =
            let uu____1615 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1615 with
            | (tcenv,uu____1633,def_typ) ->
                let uu____1639 = as_pair def_typ  in (tcenv, uu____1639)
             in
          match uu____1606 with
          | (tcenv,(lbdef,lbtyp)) ->
              let lbtyp1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant] tcenv lbtyp
                 in
              let lbdef1 =
                FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef
                  lbtyp1
                 in
              let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let def =
                let uu____1670 =
                  let uu____1671 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1671 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1670 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1679 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1698 -> def  in
              let uu____1699 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1710) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1735 -> ([], def1)  in
              (match uu____1699 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1755  ->
                          match uu___3_1755 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1758 -> false) quals
                      in
                   let uu____1760 = binders_as_mlty_binders env bs  in
                   (match uu____1760 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1787 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1787
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1792 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1799  ->
                                    match uu___4_1799 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1801 -> true
                                    | uu____1807 -> false))
                             in
                          if uu____1792
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1821 = extract_metadata attrs  in
                          let uu____1824 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1821 uu____1824  in
                        let td =
                          let uu____1847 = lident_as_mlsymbol lid  in
                          (assumed, uu____1847, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1859 =
                            let uu____1860 =
                              let uu____1861 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1861
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1860  in
                          [uu____1859;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1862 =
                          let uu____1867 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_1873  ->
                                    match uu___5_1873 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1877 -> false))
                             in
                          if uu____1867
                          then
                            let uu____1884 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____1884, (iface_of_type_names [fv]))
                          else
                            (let uu____1887 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____1887 with
                             | (env2,tydef) ->
                                 let uu____1898 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1898))
                           in
                        (match uu____1862 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_let_rec_type :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env  ->
    fun quals  ->
      fun attrs  ->
        fun lb  ->
          let lbtyp =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.env_tcenv
              lb.FStar_Syntax_Syntax.lbtyp
             in
          let uu____1957 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____1957 with
          | (bs,uu____1973) ->
              let uu____1978 = binders_as_mlty_binders env bs  in
              (match uu____1978 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____2010 = extract_metadata attrs  in
                     let uu____2013 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____2010 uu____2013  in
                   let assumed = false  in
                   let td =
                     let uu____2039 = lident_as_mlsymbol lid  in
                     (assumed, uu____2039, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____2052 =
                       let uu____2053 =
                         let uu____2054 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____2054
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____2053  in
                     [uu____2052; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____2055 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____2055 with
                    | (env2,tydef) ->
                        let iface1 = iface_of_tydefs [tydef]  in
                        (env2, iface1, def)))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____2136 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2136
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2143 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2143 with | (env2,uu____2162,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2201 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2201 with
        | (env_iparams,vars) ->
            let uu____2229 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2229 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2293,t,uu____2295,uu____2296,uu____2297);
            FStar_Syntax_Syntax.sigrng = uu____2298;
            FStar_Syntax_Syntax.sigquals = uu____2299;
            FStar_Syntax_Syntax.sigmeta = uu____2300;
            FStar_Syntax_Syntax.sigattrs = uu____2301;
            FStar_Syntax_Syntax.sigopts = uu____2302;_}::[],uu____2303),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2324 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2324 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2357),quals) ->
          let uu____2371 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____2371
          then (env, empty_iface)
          else
            (let uu____2380 = bundle_as_inductive_families env ses quals  in
             match uu____2380 with
             | (env1,ifams) ->
                 let uu____2397 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____2397 with
                  | (env2,td) ->
                      let uu____2438 =
                        let uu____2439 =
                          let uu____2440 =
                            FStar_List.map (fun x  -> x.ifv) ifams  in
                          iface_of_type_names uu____2440  in
                        iface_union uu____2439
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____2438)))
      | uu____2449 -> failwith "Unexpected signature element"
  
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
  fun g  ->
    fun lid  ->
      fun quals  ->
        fun attrs  ->
          fun univs1  ->
            fun t  ->
              let uu____2524 =
                let uu____2526 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2532  ->
                          match uu___6_2532 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2535 -> false))
                   in
                Prims.op_Negation uu____2526  in
              if uu____2524
              then (g, empty_iface, [])
              else
                (let uu____2550 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2550 with
                 | (bs,uu____2566) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2573 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2573;
                         FStar_Syntax_Syntax.lbattrs = attrs;
                         FStar_Syntax_Syntax.lbpos =
                           (t.FStar_Syntax_Syntax.pos)
                       }  in
                     extract_typ_abbrev g quals attrs lb)
  
let (extract_reifiable_effect :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Extraction_ML_UEnv.uenv * iface *
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun ed  ->
      let extend_env g1 lid ml_name tm tysc =
        let fv =
          FStar_Syntax_Syntax.lid_as_fv lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        let uu____2636 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2636 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2658 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2658
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
                }  in
              (g2, (iface_of_bindings [(fv, exp_binding)]),
                (FStar_Extraction_ML_Syntax.MLM_Let
                   (FStar_Extraction_ML_Syntax.NonRec, [lb])))))
         in
      let rec extract_fv tm =
        (let uu____2694 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2694
         then
           let uu____2699 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2699
         else ());
        (let uu____2704 =
           let uu____2705 = FStar_Syntax_Subst.compress tm  in
           uu____2705.FStar_Syntax_Syntax.n  in
         match uu____2704 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2713) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2720 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2720 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2725;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2726;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2728;_} ->
                  let uu____2731 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2731, tysc))
         | uu____2732 ->
             let uu____2733 =
               let uu____2735 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2737 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2735 uu____2737
                in
             failwith uu____2733)
         in
      let extract_action g1 a =
        (let uu____2765 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2765
         then
           let uu____2770 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2772 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2770
             uu____2772
         else ());
        (let uu____2777 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2777 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2797 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2797  in
             let lb =
               FStar_Syntax_Syntax.mk_lb
                 (lbname, (a.FStar_Syntax_Syntax.action_univs),
                   FStar_Parser_Const.effect_Tot_lid,
                   (a.FStar_Syntax_Syntax.action_typ),
                   (a.FStar_Syntax_Syntax.action_defn), [],
                   ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                in
             let lbs = (false, [lb])  in
             let action_lb =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None
                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                in
             let uu____2827 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2827 with
              | (a_let,uu____2843,ty) ->
                  ((let uu____2846 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2846
                    then
                      let uu____2851 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2851
                    else ());
                   (let uu____2856 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2879,mllb::[]),uu____2881) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____2921 -> failwith "Impossible"  in
                    match uu____2856 with
                    | (exp,tysc) ->
                        ((let uu____2959 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____2959
                          then
                            ((let uu____2965 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____2965);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____2981 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____2981 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____3003 =
        let uu____3010 =
          let uu____3015 =
            let uu____3018 =
              let uu____3027 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr  in
              FStar_All.pipe_right uu____3027 FStar_Util.must  in
            FStar_All.pipe_right uu____3018 FStar_Pervasives_Native.snd  in
          extract_fv uu____3015  in
        match uu____3010 with
        | (return_tm,ty_sc) ->
            let uu____3096 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____3096 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____3003 with
      | (g1,return_iface,return_decl) ->
          let uu____3121 =
            let uu____3128 =
              let uu____3133 =
                let uu____3136 =
                  let uu____3145 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr
                     in
                  FStar_All.pipe_right uu____3145 FStar_Util.must  in
                FStar_All.pipe_right uu____3136 FStar_Pervasives_Native.snd
                 in
              extract_fv uu____3133  in
            match uu____3128 with
            | (bind_tm,ty_sc) ->
                let uu____3214 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____3214 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____3121 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3239 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3239 with
                | (g3,actions) ->
                    let uu____3276 = FStar_List.unzip actions  in
                    (match uu____3276 with
                     | (actions_iface,actions1) ->
                         let uu____3303 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3303, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_let_rec_types :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * iface *
          FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun se  ->
    fun env  ->
      fun lbs  ->
        let uu____3334 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____3339 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____3339) lbs
           in
        if uu____3334
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3362 =
             FStar_List.fold_left
               (fun uu____3397  ->
                  fun lb  ->
                    match uu____3397 with
                    | (env1,iface_opt,impls) ->
                        let uu____3438 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____3438 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3472 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____3472
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____3362 with
           | (env1,iface_opt,impls) ->
               let uu____3512 = FStar_Option.get iface_opt  in
               let uu____3513 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____3512, uu____3513))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3545 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3554 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3571 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3590 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3590 with | (env,iface1,uu____3605) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3611) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3620 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3620 with | (env,iface1,uu____3635) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____3641) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3654 = extract_let_rec_types se g lbs  in
          (match uu____3654 with | (env,iface1,uu____3669) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3680 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3686 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____3686)
             in
          if uu____3680
          then
            let uu____3693 =
              let uu____3704 =
                let uu____3705 =
                  let uu____3708 = always_fail lid t  in [uu____3708]  in
                (false, uu____3705)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3704  in
            (match uu____3693 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3734) ->
          let uu____3739 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3739 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3768 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3769 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3776 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3777 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3790 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3803 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_fail uu____3815 ->
          failwith "impossible: trying to extract Sig_fail"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3834 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____3834
          then
            let uu____3847 = extract_reifiable_effect g ed  in
            (match uu____3847 with | (env,iface1,uu____3862) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3884 = FStar_Options.interactive ()  in
      if uu____3884
      then (g, empty_iface)
      else
        (let uu____3893 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___621_3897 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___621_3897.iface_bindings);
             iface_tydefs = (uu___621_3897.iface_tydefs);
             iface_type_names = (uu___621_3897.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____3915  ->
                fun se  ->
                  match uu____3915 with
                  | (g1,iface2) ->
                      let uu____3927 = extract_sigelt_iface g1 se  in
                      (match uu____3927 with
                       | (g2,iface') ->
                           let uu____3938 = iface_union iface2 iface'  in
                           (g2, uu____3938))) (g, iface1) decls
            in
         (let uu____3940 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____3940);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3957 = FStar_Options.debug_any ()  in
      if uu____3957
      then
        let uu____3964 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____3964
          (fun uu____3972  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let mlident_map =
        FStar_List.fold_left
          (fun acc  ->
             fun uu____4002  ->
               match uu____4002 with
               | (uu____4013,x) ->
                   FStar_Util.psmap_add acc
                     x.FStar_Extraction_ML_UEnv.exp_b_name "")
          g.FStar_Extraction_ML_UEnv.env_mlident_map iface1.iface_bindings
         in
      let uu___644_4017 = g  in
      let uu____4018 =
        let uu____4021 =
          FStar_List.map (fun _4028  -> FStar_Extraction_ML_UEnv.Fv _4028)
            iface1.iface_bindings
           in
        FStar_List.append uu____4021 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___644_4017.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____4018;
        FStar_Extraction_ML_UEnv.env_mlident_map = mlident_map;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___644_4017.FStar_Extraction_ML_UEnv.currentModule)
      }
  
let (extract_bundle :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlmodule1
        Prims.list))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____4106 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4106
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____4114 =
            let uu____4115 =
              let uu____4118 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4118  in
            uu____4115.FStar_Syntax_Syntax.n  in
          match uu____4114 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4123) ->
              FStar_List.map
                (fun uu____4156  ->
                   match uu____4156 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4165;
                        FStar_Syntax_Syntax.sort = uu____4166;_},uu____4167)
                       -> ppname.FStar_Ident.idText) bs
          | uu____4175 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____4183 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____4183 with
        | (env2,uu____4210,uu____4211) ->
            let uu____4214 =
              let uu____4227 = lident_as_mlsymbol ctor.dname  in
              let uu____4229 =
                let uu____4237 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____4237  in
              (uu____4227, uu____4229)  in
            (env2, uu____4214)
         in
      let extract_one_family env1 ind =
        let uu____4298 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4298 with
        | (env_iparams,vars) ->
            let uu____4342 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____4342 with
             | (env2,ctors) ->
                 let uu____4449 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____4449 with
                  | (indices,uu____4483) ->
                      let ml_params =
                        let uu____4492 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____4518  ->
                                    let uu____4526 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____4526))
                           in
                        FStar_List.append vars uu____4492  in
                      let tbody =
                        let uu____4531 =
                          FStar_Util.find_opt
                            (fun uu___7_4536  ->
                               match uu___7_4536 with
                               | FStar_Syntax_Syntax.RecordType uu____4538 ->
                                   true
                               | uu____4548 -> false) ind.iquals
                           in
                        match uu____4531 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____4560 = FStar_List.hd ctors  in
                            (match uu____4560 with
                             | (uu____4585,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____4629  ->
                                          match uu____4629 with
                                          | (uu____4640,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____4645 =
                                                lident_as_mlsymbol lid  in
                                              (uu____4645, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4648 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____4651 =
                        let uu____4674 = lident_as_mlsymbol ind.iname  in
                        (false, uu____4674, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____4651)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____4719,t,uu____4721,uu____4722,uu____4723);
            FStar_Syntax_Syntax.sigrng = uu____4724;
            FStar_Syntax_Syntax.sigquals = uu____4725;
            FStar_Syntax_Syntax.sigmeta = uu____4726;
            FStar_Syntax_Syntax.sigattrs = uu____4727;
            FStar_Syntax_Syntax.sigopts = uu____4728;_}::[],uu____4729),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____4750 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____4750 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____4803),quals) ->
          let uu____4817 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____4817
          then (env, [])
          else
            (let uu____4830 = bundle_as_inductive_families env ses quals  in
             match uu____4830 with
             | (env1,ifams) ->
                 let uu____4849 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____4849 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____4958 -> failwith "Unexpected signature element"
  
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top
         in
      let plugin_with_arity attrs =
        FStar_Util.find_map attrs
          (fun t  ->
             let uu____5016 = FStar_Syntax_Util.head_and_args t  in
             match uu____5016 with
             | (head1,args) ->
                 let uu____5064 =
                   let uu____5066 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____5066  in
                 if uu____5064
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5085));
                         FStar_Syntax_Syntax.pos = uu____5086;
                         FStar_Syntax_Syntax.vars = uu____5087;_},uu____5088)::[]
                        ->
                        let uu____5127 =
                          let uu____5131 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5131  in
                        FStar_Pervasives_Native.Some uu____5127
                    | uu____5137 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5152 =
        let uu____5154 = FStar_Options.codegen ()  in
        uu____5154 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5152
      then []
      else
        (let uu____5164 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5164 with
         | FStar_Pervasives_Native.None  -> []
         | FStar_Pervasives_Native.Some arity_opt ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
                  let mk_registration lb =
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                       in
                    let fv_lid1 =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
                    let ml_name_str =
                      let uu____5206 =
                        let uu____5207 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5207  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5206  in
                    let uu____5209 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____5209 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin) ->
                        let uu____5242 =
                          if plugin
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____5242 with
                         | (register,args) ->
                             let h =
                               let uu____5279 =
                                 let uu____5280 =
                                   let uu____5281 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____5281
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____5280
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____5279
                                in
                             let arity1 =
                               let uu____5283 =
                                 let uu____5284 =
                                   let uu____5296 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____5296, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5284
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5283
                                in
                             let app =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (h,
                                      (FStar_List.append
                                         [w ml_name_str; w arity1] args)))
                                in
                             [FStar_Extraction_ML_Syntax.MLM_Top app])
                    | FStar_Pervasives_Native.None  -> []  in
                  FStar_List.collect mk_registration
                    (FStar_Pervasives_Native.snd lbs)
              | uu____5325 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5353 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5353);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5362 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5371 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5388 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5405 = extract_reifiable_effect g ed  in
           (match uu____5405 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5429 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_fail uu____5443 ->
           failwith "impossible: trying to extract Sig_fail"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5463 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5469 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____5469 with | (env,uu____5485,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5494) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5503 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____5503 with | (env,uu____5519,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____5528) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5541 = extract_let_rec_types se g lbs  in
           (match uu____5541 with | (env,uu____5557,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____5566) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5577 =
             let uu____5586 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____5586 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____5615) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____5577 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___878_5701 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___878_5701.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___878_5701.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___878_5701.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___878_5701.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___878_5701.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___878_5701.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____5710 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____5710)  in
                let uu____5728 =
                  let uu____5735 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5735  in
                (match uu____5728 with
                 | (ml_let,uu____5752,uu____5753) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____5762) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____5779 =
                            FStar_List.fold_left2
                              (fun uu____5805  ->
                                 fun ml_lb  ->
                                   fun uu____5807  ->
                                     match (uu____5805, uu____5807) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____5829;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____5831;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____5832;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____5833;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____5834;_})
                                         ->
                                         let uu____5859 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____5859
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5876 =
                                                let uu____5879 =
                                                  FStar_Util.right lbname  in
                                                uu____5879.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____5876.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____5883 =
                                                let uu____5884 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____5884.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____5883 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5889,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5890;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____5892;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5893;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____5894;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____5895;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____5896;_})
                                                  when
                                                  let uu____5931 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____5931 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____5935 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___926_5940 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___926_5940.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___926_5940.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___926_5940.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___926_5940.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___926_5940.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____5941 =
                                              let uu____5946 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_5953  ->
                                                        match uu___8_5953
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____5955 ->
                                                            true
                                                        | uu____5961 -> false))
                                                 in
                                              if uu____5946
                                              then
                                                let mname =
                                                  let uu____5977 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5977
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____5986 =
                                                  let uu____5994 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____5995 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____5994 mname
                                                    uu____5995
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____5986 with
                                                | (env1,uu____6002,uu____6003)
                                                    ->
                                                    (env1,
                                                      (let uu___939_6007 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___939_6007.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___939_6007.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___939_6007.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___939_6007.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___939_6007.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6014 =
                                                   let uu____6022 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6022
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____6014 with
                                                 | (env1,uu____6029,uu____6030)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____5941 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____5779 with
                           | (g1,ml_lbs') ->
                               let uu____6060 =
                                 let uu____6063 =
                                   let uu____6066 =
                                     let uu____6067 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6067
                                      in
                                   [uu____6066;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____6070 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____6063 uu____6070  in
                               (g1, uu____6060))
                      | uu____6075 ->
                          let uu____6076 =
                            let uu____6078 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6078
                             in
                          failwith uu____6076)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6088,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6093 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6099 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____6099)
              in
           if uu____6093
           then
             let always_fail1 =
               let uu___959_6109 = se  in
               let uu____6110 =
                 let uu____6111 =
                   let uu____6118 =
                     let uu____6119 =
                       let uu____6122 = always_fail lid t  in [uu____6122]
                        in
                     (false, uu____6119)  in
                   (uu____6118, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6111  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6110;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___959_6109.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___959_6109.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___959_6109.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___959_6109.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___959_6109.FStar_Syntax_Syntax.sigopts)
               }  in
             let uu____6129 = extract_sig g always_fail1  in
             (match uu____6129 with
              | (g1,mlm) ->
                  let uu____6148 =
                    FStar_Util.find_map quals
                      (fun uu___9_6153  ->
                         match uu___9_6153 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6157 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6148 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6165 =
                         let uu____6168 =
                           let uu____6169 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6169  in
                         let uu____6170 =
                           let uu____6173 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6173]  in
                         uu____6168 :: uu____6170  in
                       (g1, uu____6165)
                   | uu____6176 ->
                       let uu____6179 =
                         FStar_Util.find_map quals
                           (fun uu___10_6185  ->
                              match uu___10_6185 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6189)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6190 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6179 with
                        | FStar_Pervasives_Native.Some uu____6197 -> (g1, [])
                        | uu____6200 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6210 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____6210 with
            | (ml_main,uu____6224,uu____6225) ->
                let uu____6226 =
                  let uu____6229 =
                    let uu____6230 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6230  in
                  [uu____6229; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____6226))
       | FStar_Syntax_Syntax.Sig_assume uu____6233 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6242 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6245 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6260 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun m  ->
      let uu____6300 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1002_6304 = g  in
        let uu____6305 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____6305;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1002_6304.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.env_mlident_map =
            (uu___1002_6304.FStar_Extraction_ML_UEnv.env_mlident_map);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1002_6304.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1002_6304.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____6306 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____6325 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____6325
               then
                 let nm =
                   let uu____6336 =
                     let uu____6340 = FStar_Syntax_Util.lids_of_sigelt se  in
                     FStar_All.pipe_right uu____6340
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____6336 (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____6356 = FStar_Util.format1 "---Extracted {%s}" nm
                      in
                   FStar_Util.measure_execution_time uu____6356
                     (fun uu____6366  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____6306 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____6388 = FStar_Options.codegen ()  in
            uu____6388 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____6403 =
                let uu____6405 = FStar_Options.silent ()  in
                Prims.op_Negation uu____6405  in
              if uu____6403
              then
                let uu____6408 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____6408
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
  fun g  ->
    fun m  ->
      (let uu____6483 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____6483);
      (let uu____6486 =
         let uu____6488 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____6488  in
       if uu____6486
       then
         let uu____6491 =
           let uu____6493 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6493
            in
         failwith uu____6491
       else ());
      (let uu____6498 = FStar_Options.interactive ()  in
       if uu____6498
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____6518 = FStar_Options.debug_any ()  in
            if uu____6518
            then
              let msg =
                let uu____6529 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s" uu____6529  in
              FStar_Util.measure_execution_time msg
                (fun uu____6539  -> extract' g m)
            else extract' g m  in
          (let uu____6543 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____6543);
          res))
  
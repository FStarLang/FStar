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
              let uu____220 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____220  in
            let uu____228 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____228 FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____265 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____265 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____269 =
          let uu____274 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____274  in
        {
          FStar_Syntax_Syntax.lbname = uu____269;
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
  'Auu____296 . 'Auu____296 Prims.list -> ('Auu____296 * 'Auu____296) =
  fun uu___0_307  ->
    match uu___0_307 with
    | a::b::[] -> (a, b)
    | uu____312 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_327  ->
    match uu___1_327 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____330 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____339 = FStar_Syntax_Subst.compress x  in
    match uu____339 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____343;
        FStar_Syntax_Syntax.vars = uu____344;_} ->
        let uu____347 =
          let uu____349 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____349  in
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
         | "FStar.Pervasives.CMacro" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CMacro
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated "")
         | uu____362 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____365;
             FStar_Syntax_Syntax.vars = uu____366;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____368));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____369;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____370;_},uu____371)::[]);
        FStar_Syntax_Syntax.pos = uu____372;
        FStar_Syntax_Syntax.vars = uu____373;_} ->
        let uu____416 =
          let uu____418 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____418  in
        (match uu____416 with
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
         | uu____428 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____430));
        FStar_Syntax_Syntax.pos = uu____431;
        FStar_Syntax_Syntax.vars = uu____432;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____437));
        FStar_Syntax_Syntax.pos = uu____438;
        FStar_Syntax_Syntax.vars = uu____439;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____444));
        FStar_Syntax_Syntax.pos = uu____445;
        FStar_Syntax_Syntax.vars = uu____446;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____452);
        FStar_Syntax_Syntax.pos = uu____453;
        FStar_Syntax_Syntax.vars = uu____454;_} -> extract_meta x1
    | uu____461 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____481 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____481) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____523  ->
             match uu____523 with
             | (bv,uu____534) ->
                 let uu____535 =
                   let uu____536 =
                     let uu____539 =
                       let uu____540 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____540  in
                     FStar_Pervasives_Native.Some uu____539  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____536  in
                 let uu____542 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____535, uu____542)) env bs
  
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
    let uu____743 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____745 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____748 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____750 =
      let uu____752 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____766 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____768 =
                  let uu____770 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____770  in
                Prims.op_Hat uu____766 uu____768))
         in
      FStar_All.pipe_right uu____752 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____743 uu____745 uu____748
      uu____750
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        let uu____815 =
          FStar_Util.fold_map
            (fun env1  ->
               fun se  ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l,us,bs,t,_mut_i,datas) ->
                     let uu____866 = FStar_Syntax_Subst.open_univ_vars us t
                        in
                     (match uu____866 with
                      | (_us,t1) ->
                          let uu____879 = FStar_Syntax_Subst.open_term bs t1
                             in
                          (match uu____879 with
                           | (bs1,t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1  ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d,us1,t3,l',nparams,uu____925)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____932 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3
                                                in
                                             (match uu____932 with
                                              | (_us1,t4) ->
                                                  let uu____941 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4
                                                     in
                                                  (match uu____941 with
                                                   | (bs',body) ->
                                                       let uu____980 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs'
                                                          in
                                                       (match uu____980 with
                                                        | (bs_params,rest) ->
                                                            let subst1 =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____1071
                                                                    ->
                                                                   fun
                                                                    uu____1072
                                                                     ->
                                                                    match 
                                                                    (uu____1071,
                                                                    uu____1072)
                                                                    with
                                                                    | 
                                                                    ((b',uu____1098),
                                                                    (b,uu____1100))
                                                                    ->
                                                                    let uu____1121
                                                                    =
                                                                    let uu____1128
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                    (b',
                                                                    uu____1128)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____1121)
                                                                bs_params bs1
                                                               in
                                                            let t5 =
                                                              let uu____1134
                                                                =
                                                                let uu____1135
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____1135
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____1134
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1)
                                                               in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____1138 -> []))
                                  in
                               let metadata =
                                 let uu____1142 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs
                                    in
                                 let uu____1145 =
                                   FStar_List.choose flag_of_qual quals  in
                                 FStar_List.append uu____1142 uu____1145  in
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
                 | uu____1152 -> (env1, [])) env ses
           in
        match uu____815 with
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
    let uu___216_1332 = empty_iface  in
    {
      iface_module_name = (uu___216_1332.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___216_1332.iface_tydefs);
      iface_type_names = (uu___216_1332.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___219_1343 = empty_iface  in
    let uu____1344 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___219_1343.iface_module_name);
      iface_bindings = (uu___219_1343.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1344
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___223_1359 = empty_iface  in
    {
      iface_module_name = (uu___223_1359.iface_module_name);
      iface_bindings = (uu___223_1359.iface_bindings);
      iface_tydefs = (uu___223_1359.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1371 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1371;
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
  'Auu____1416 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1416 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____1448 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1450 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1452 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1448 uu____1450
        uu____1452
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1470  ->
      match uu____1470 with
      | (fv,exp_binding) ->
          let uu____1478 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1480 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1478 uu____1480
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1495 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1497 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1495 uu____1497
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1515 =
      let uu____1517 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1517 (FStar_String.concat "\n")  in
    let uu____1531 =
      let uu____1533 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1533 (FStar_String.concat "\n")  in
    let uu____1543 =
      let uu____1545 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1545 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1515 uu____1531
      uu____1543
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
    let gamma =
      let uu____1571 = FStar_Extraction_ML_UEnv.bindings_of_uenv env  in
      FStar_List.collect
        (fun uu___2_1581  ->
           match uu___2_1581 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1598 -> []) uu____1571
       in
    let uu____1603 =
      let uu____1605 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1605 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1603
  
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
          let uu____1665 =
            let uu____1674 =
              let uu____1683 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
              FStar_TypeChecker_Env.open_universes_in uu____1683
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1674 with
            | (tcenv,uu____1693,def_typ) ->
                let uu____1699 = as_pair def_typ  in (tcenv, uu____1699)
             in
          match uu____1665 with
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
                let uu____1730 =
                  let uu____1731 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1731 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1730 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1739 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1758 -> def  in
              let uu____1759 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1770) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1795 -> ([], def1)  in
              (match uu____1759 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1815  ->
                          match uu___3_1815 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1818 -> false) quals
                      in
                   let uu____1820 = binders_as_mlty_binders env bs  in
                   (match uu____1820 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1847 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1847
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1852 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1859  ->
                                    match uu___4_1859 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1861 -> true
                                    | uu____1867 -> false))
                             in
                          if uu____1852
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1881 = extract_metadata attrs  in
                          let uu____1884 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1881 uu____1884  in
                        let td =
                          let uu____1907 = lident_as_mlsymbol lid  in
                          (assumed, uu____1907, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1919 =
                            let uu____1920 =
                              let uu____1921 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1921
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1920  in
                          [uu____1919;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1922 =
                          let uu____1927 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_1933  ->
                                    match uu___5_1933 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1937 -> false))
                             in
                          if uu____1927
                          then
                            let uu____1944 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____1944, (iface_of_type_names [fv]))
                          else
                            (let uu____1947 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____1947 with
                             | (env2,tydef) ->
                                 let uu____1958 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1958))
                           in
                        (match uu____1922 with
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
            let uu____2017 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] uu____2017
              lb.FStar_Syntax_Syntax.lbtyp
             in
          let uu____2018 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____2018 with
          | (bs,uu____2042) ->
              let uu____2063 = binders_as_mlty_binders env bs  in
              (match uu____2063 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____2095 = extract_metadata attrs  in
                     let uu____2098 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____2095 uu____2098  in
                   let assumed = false  in
                   let td =
                     let uu____2124 = lident_as_mlsymbol lid  in
                     (assumed, uu____2124, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____2137 =
                       let uu____2138 =
                         let uu____2139 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____2139
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____2138  in
                     [uu____2137; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____2140 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____2140 with
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
          let uu____2221 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2221
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2228 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2228 with | (env2,uu____2247,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2286 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2286 with
        | (env_iparams,vars) ->
            let uu____2314 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2314 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2378,t,uu____2380,uu____2381,uu____2382);
            FStar_Syntax_Syntax.sigrng = uu____2383;
            FStar_Syntax_Syntax.sigquals = uu____2384;
            FStar_Syntax_Syntax.sigmeta = uu____2385;
            FStar_Syntax_Syntax.sigattrs = uu____2386;
            FStar_Syntax_Syntax.sigopts = uu____2387;_}::[],uu____2388),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2409 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2409 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2442),quals) ->
          let uu____2456 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____2456
          then (env, empty_iface)
          else
            (let uu____2465 = bundle_as_inductive_families env ses quals  in
             match uu____2465 with
             | (env1,ifams) ->
                 let uu____2482 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____2482 with
                  | (env2,td) ->
                      let uu____2523 =
                        let uu____2524 =
                          let uu____2525 =
                            FStar_List.map (fun x  -> x.ifv) ifams  in
                          iface_of_type_names uu____2525  in
                        iface_union uu____2524
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____2523)))
      | uu____2534 -> failwith "Unexpected signature element"
  
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
              let uu____2609 =
                let uu____2611 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2617  ->
                          match uu___6_2617 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2620 -> false))
                   in
                Prims.op_Negation uu____2611  in
              if uu____2609
              then (g, empty_iface, [])
              else
                (let uu____2635 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2635 with
                 | (bs,uu____2659) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2682 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2682;
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
        let uu____2745 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2745 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2767 =
                let uu____2769 =
                  let uu____2775 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g2
                     in
                  FStar_TypeChecker_Env.debug uu____2775  in
                FStar_All.pipe_left uu____2769
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2767
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
        (let uu____2810 =
           let uu____2812 =
             let uu____2818 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.debug uu____2818  in
           FStar_All.pipe_left uu____2812
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2810
         then
           let uu____2822 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2822
         else ());
        (let uu____2827 =
           let uu____2828 = FStar_Syntax_Subst.compress tm  in
           uu____2828.FStar_Syntax_Syntax.n  in
         match uu____2827 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2836) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2843 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2843 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2848;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2849;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2851;_} ->
                  let uu____2854 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2854, tysc))
         | uu____2855 ->
             let uu____2856 =
               let uu____2858 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2860 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2858 uu____2860
                in
             failwith uu____2856)
         in
      let extract_action g1 a =
        (let uu____2888 =
           let uu____2890 =
             let uu____2896 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
             FStar_TypeChecker_Env.debug uu____2896  in
           FStar_All.pipe_left uu____2890
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2888
         then
           let uu____2900 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2902 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2900
             uu____2902
         else ());
        (let uu____2907 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2907 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2927 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2927  in
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
             let uu____2957 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2957 with
              | (a_let,uu____2973,ty) ->
                  ((let uu____2976 =
                      let uu____2978 =
                        let uu____2984 =
                          FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
                        FStar_TypeChecker_Env.debug uu____2984  in
                      FStar_All.pipe_left uu____2978
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2976
                    then
                      let uu____2988 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2988
                    else ());
                   (let uu____2993 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____3016,mllb::[]),uu____3018) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____3058 -> failwith "Impossible"  in
                    match uu____2993 with
                    | (exp,tysc) ->
                        ((let uu____3096 =
                            let uu____3098 =
                              let uu____3104 =
                                FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
                              FStar_TypeChecker_Env.debug uu____3104  in
                            FStar_All.pipe_left uu____3098
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____3096
                          then
                            ((let uu____3109 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____3109);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____3125 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____3125 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____3147 =
        let uu____3154 =
          let uu____3159 =
            let uu____3162 =
              let uu____3171 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr  in
              FStar_All.pipe_right uu____3171 FStar_Util.must  in
            FStar_All.pipe_right uu____3162 FStar_Pervasives_Native.snd  in
          extract_fv uu____3159  in
        match uu____3154 with
        | (return_tm,ty_sc) ->
            let uu____3240 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____3240 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____3147 with
      | (g1,return_iface,return_decl) ->
          let uu____3265 =
            let uu____3272 =
              let uu____3277 =
                let uu____3280 =
                  let uu____3289 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr
                     in
                  FStar_All.pipe_right uu____3289 FStar_Util.must  in
                FStar_All.pipe_right uu____3280 FStar_Pervasives_Native.snd
                 in
              extract_fv uu____3277  in
            match uu____3272 with
            | (bind_tm,ty_sc) ->
                let uu____3358 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____3358 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____3265 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3383 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3383 with
                | (g3,actions) ->
                    let uu____3420 = FStar_List.unzip actions  in
                    (match uu____3420 with
                     | (actions_iface,actions1) ->
                         let uu____3447 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3447, (return_decl :: bind_decl ::
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
        let uu____3478 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____3483 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____3483) lbs
           in
        if uu____3478
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3506 =
             FStar_List.fold_left
               (fun uu____3541  ->
                  fun lb  ->
                    match uu____3541 with
                    | (env1,iface_opt,impls) ->
                        let uu____3582 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____3582 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3616 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____3616
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____3506 with
           | (env1,iface_opt,impls) ->
               let uu____3656 = FStar_Option.get iface_opt  in
               let uu____3657 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____3656, uu____3657))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3689 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3698 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3715 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3734 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3734 with | (env,iface1,uu____3749) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3755) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3764 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3764 with | (env,iface1,uu____3779) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____3785) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3798 = extract_let_rec_types se g lbs  in
          (match uu____3798 with | (env,iface1,uu____3813) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3824 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3830 =
                 let uu____3832 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                    in
                 FStar_TypeChecker_Util.must_erase_for_extraction uu____3832
                   t
                  in
               Prims.op_Negation uu____3830)
             in
          if uu____3824
          then
            let uu____3838 =
              let uu____3849 =
                let uu____3850 =
                  let uu____3853 = always_fail lid t  in [uu____3853]  in
                (false, uu____3850)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3849  in
            (match uu____3838 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3879) ->
          let uu____3884 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3884 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3913 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3914 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3921 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3922 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3935 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3948 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3961 =
            (let uu____3965 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.is_reifiable_effect uu____3965
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____3961
          then
            let uu____3977 = extract_reifiable_effect g ed  in
            (match uu____3977 with | (env,iface1,uu____3992) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4014 = FStar_Options.interactive ()  in
      if uu____4014
      then (g, empty_iface)
      else
        (let uu____4023 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___619_4027 = empty_iface  in
           let uu____4028 = FStar_Extraction_ML_UEnv.current_module_of_uenv g
              in
           {
             iface_module_name = uu____4028;
             iface_bindings = (uu___619_4027.iface_bindings);
             iface_tydefs = (uu___619_4027.iface_tydefs);
             iface_type_names = (uu___619_4027.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____4046  ->
                fun se  ->
                  match uu____4046 with
                  | (g1,iface2) ->
                      let uu____4058 = extract_sigelt_iface g1 se  in
                      (match uu____4058 with
                       | (g2,iface') ->
                           let uu____4069 = iface_union iface2 iface'  in
                           (g2, uu____4069))) (g, iface1) decls
            in
         (let uu____4071 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____4071);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4088 = FStar_Options.debug_any ()  in
      if uu____4088
      then
        let uu____4095 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____4095
          (fun uu____4103  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      FStar_Extraction_ML_UEnv.extend_with_iface g iface1.iface_module_name
        iface1.iface_bindings iface1.iface_tydefs iface1.iface_type_names
  
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
          let uu____4194 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4194
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____4202 =
            let uu____4203 =
              let uu____4206 =
                let uu____4207 =
                  FStar_Extraction_ML_UEnv.tcenv_of_uenv env_iparams  in
                FStar_TypeChecker_Normalize.normalize steps uu____4207
                  ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4206  in
            uu____4203.FStar_Syntax_Syntax.n  in
          match uu____4202 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4212) ->
              FStar_List.map
                (fun uu____4245  ->
                   match uu____4245 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4254;
                        FStar_Syntax_Syntax.sort = uu____4255;_},uu____4256)
                       -> ppname.FStar_Ident.idText) bs
          | uu____4264 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____4272 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____4272 with
        | (env2,uu____4299,uu____4300) ->
            let uu____4303 =
              let uu____4316 = lident_as_mlsymbol ctor.dname  in
              let uu____4318 =
                let uu____4326 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____4326  in
              (uu____4316, uu____4318)  in
            (env2, uu____4303)
         in
      let extract_one_family env1 ind =
        let uu____4387 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4387 with
        | (env_iparams,vars) ->
            let uu____4431 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____4431 with
             | (env2,ctors) ->
                 let uu____4538 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____4538 with
                  | (indices,uu____4580) ->
                      let ml_params =
                        let uu____4605 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____4631  ->
                                    let uu____4639 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____4639))
                           in
                        FStar_List.append vars uu____4605  in
                      let tbody =
                        let uu____4644 =
                          FStar_Util.find_opt
                            (fun uu___7_4649  ->
                               match uu___7_4649 with
                               | FStar_Syntax_Syntax.RecordType uu____4651 ->
                                   true
                               | uu____4661 -> false) ind.iquals
                           in
                        match uu____4644 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____4673 = FStar_List.hd ctors  in
                            (match uu____4673 with
                             | (uu____4698,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____4742  ->
                                          match uu____4742 with
                                          | (uu____4753,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____4758 =
                                                lident_as_mlsymbol lid  in
                                              (uu____4758, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4761 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____4764 =
                        let uu____4787 = lident_as_mlsymbol ind.iname  in
                        (false, uu____4787, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____4764)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____4832,t,uu____4834,uu____4835,uu____4836);
            FStar_Syntax_Syntax.sigrng = uu____4837;
            FStar_Syntax_Syntax.sigquals = uu____4838;
            FStar_Syntax_Syntax.sigmeta = uu____4839;
            FStar_Syntax_Syntax.sigattrs = uu____4840;
            FStar_Syntax_Syntax.sigopts = uu____4841;_}::[],uu____4842),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____4863 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____4863 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____4916),quals) ->
          let uu____4930 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____4930
          then (env, [])
          else
            (let uu____4943 = bundle_as_inductive_families env ses quals  in
             match uu____4943 with
             | (env1,ifams) ->
                 let uu____4962 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____4962 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____5071 -> failwith "Unexpected signature element"
  
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
             let uu____5129 = FStar_Syntax_Util.head_and_args t  in
             match uu____5129 with
             | (head1,args) ->
                 let uu____5177 =
                   let uu____5179 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____5179  in
                 if uu____5177
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5198));
                         FStar_Syntax_Syntax.pos = uu____5199;
                         FStar_Syntax_Syntax.vars = uu____5200;_},uu____5201)::[]
                        ->
                        let uu____5240 =
                          let uu____5244 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5244  in
                        FStar_Pervasives_Native.Some uu____5240
                    | uu____5250 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5265 =
        let uu____5267 = FStar_Options.codegen ()  in
        uu____5267 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5265
      then []
      else
        (let uu____5277 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5277 with
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
                      let uu____5319 =
                        let uu____5320 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5320  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5319  in
                    let uu____5322 =
                      let uu____5335 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        uu____5335 fv fv_t arity_opt ml_name_str
                       in
                    match uu____5322 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____5356 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____5356 with
                         | (register,args) ->
                             let h =
                               let uu____5393 =
                                 let uu____5394 =
                                   let uu____5395 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____5395
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____5394
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____5393
                                in
                             let arity1 =
                               let uu____5397 =
                                 let uu____5398 =
                                   let uu____5410 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____5410, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5398
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5397
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
              | uu____5439 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5467 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5467);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5476 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5485 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5502 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           let uu____5519 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
           FStar_TypeChecker_Env.is_reifiable_effect uu____5519
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5520 = extract_reifiable_effect g ed  in
           (match uu____5520 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5544 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5558 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5564 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____5564 with | (env,uu____5580,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5589) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5598 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____5598 with | (env,uu____5614,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____5623) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5636 = extract_let_rec_types se g lbs  in
           (match uu____5636 with | (env,uu____5652,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____5661) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5672 =
             let uu____5681 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____5681 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____5710) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____5672 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    let uu____5796 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.postprocess uu____5796 tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___867_5797 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___867_5797.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___867_5797.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___867_5797.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___867_5797.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___867_5797.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___867_5797.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____5806 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____5806)  in
                let uu____5824 =
                  let uu____5831 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5831  in
                (match uu____5824 with
                 | (ml_let,uu____5848,uu____5849) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____5858) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____5875 =
                            FStar_List.fold_left2
                              (fun uu____5901  ->
                                 fun ml_lb  ->
                                   fun uu____5903  ->
                                     match (uu____5901, uu____5903) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____5925;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____5927;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____5928;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____5929;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____5930;_})
                                         ->
                                         let uu____5955 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____5955
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5972 =
                                                let uu____5975 =
                                                  FStar_Util.right lbname  in
                                                uu____5975.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____5972.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____5979 =
                                                let uu____5980 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____5980.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____5979 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5985,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5986;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____5988;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5989;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____5990;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____5991;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____5992;_})
                                                  when
                                                  let uu____6027 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____6027 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____6031 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___915_6036 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___915_6036.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___915_6036.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___915_6036.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___915_6036.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___915_6036.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____6037 =
                                              let uu____6042 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_6049  ->
                                                        match uu___8_6049
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____6051 ->
                                                            true
                                                        | uu____6057 -> false))
                                                 in
                                              if uu____6042
                                              then
                                                let mname =
                                                  let uu____6073 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____6073
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____6082 =
                                                  let uu____6090 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____6091 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____6090 mname
                                                    uu____6091
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____6082 with
                                                | (env1,uu____6098,uu____6099)
                                                    ->
                                                    (env1,
                                                      (let uu___928_6103 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___928_6103.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___928_6103.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___928_6103.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___928_6103.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___928_6103.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6110 =
                                                   let uu____6118 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6118
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____6110 with
                                                 | (env1,uu____6125,uu____6126)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____6037 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____5875 with
                           | (g1,ml_lbs') ->
                               let uu____6156 =
                                 let uu____6159 =
                                   let uu____6162 =
                                     let uu____6163 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6163
                                      in
                                   [uu____6162;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____6166 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____6159 uu____6166  in
                               (g1, uu____6156))
                      | uu____6171 ->
                          let uu____6172 =
                            let uu____6174 =
                              let uu____6176 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____6176 ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6174
                             in
                          failwith uu____6172)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6185,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6190 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6196 =
                  let uu____6198 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Util.must_erase_for_extraction uu____6198
                    t
                   in
                Prims.op_Negation uu____6196)
              in
           if uu____6190
           then
             let always_fail1 =
               let uu___948_6207 = se  in
               let uu____6208 =
                 let uu____6209 =
                   let uu____6216 =
                     let uu____6217 =
                       let uu____6220 = always_fail lid t  in [uu____6220]
                        in
                     (false, uu____6217)  in
                   (uu____6216, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6209  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6208;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___948_6207.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___948_6207.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___948_6207.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___948_6207.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___948_6207.FStar_Syntax_Syntax.sigopts)
               }  in
             let uu____6227 = extract_sig g always_fail1  in
             (match uu____6227 with
              | (g1,mlm) ->
                  let uu____6246 =
                    FStar_Util.find_map quals
                      (fun uu___9_6251  ->
                         match uu___9_6251 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6255 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6246 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6263 =
                         let uu____6266 =
                           let uu____6267 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6267  in
                         let uu____6268 =
                           let uu____6271 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6271]  in
                         uu____6266 :: uu____6268  in
                       (g1, uu____6263)
                   | uu____6274 ->
                       let uu____6277 =
                         FStar_Util.find_map quals
                           (fun uu___10_6283  ->
                              match uu___10_6283 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6287)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6288 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6277 with
                        | FStar_Pervasives_Native.Some uu____6295 -> (g1, [])
                        | uu____6298 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6308 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____6308 with
            | (ml_main,uu____6322,uu____6323) ->
                let uu____6324 =
                  let uu____6327 =
                    let uu____6328 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6328  in
                  [uu____6327; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____6324))
       | FStar_Syntax_Syntax.Sig_assume uu____6331 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6340 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6343 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6358 -> (g, [])
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
      let uu____6398 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu____6402 =
          let uu____6403 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
          FStar_TypeChecker_Env.set_current_module uu____6403
            m.FStar_Syntax_Syntax.name
           in
        FStar_Extraction_ML_UEnv.set_tcenv g uu____6402  in
      let g2 = FStar_Extraction_ML_UEnv.set_current_module g1 name  in
      let uu____6405 =
        FStar_Util.fold_map
          (fun g3  ->
             fun se  ->
               let uu____6424 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____6424
               then
                 let nm =
                   let uu____6435 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____6435 (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____6452 = FStar_Util.format1 "---Extracted {%s}" nm
                      in
                   FStar_Util.measure_execution_time uu____6452
                     (fun uu____6462  -> extract_sig g3 se)))
               else extract_sig g3 se) g2 m.FStar_Syntax_Syntax.declarations
         in
      match uu____6405 with
      | (g3,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____6484 = FStar_Options.codegen ()  in
            uu____6484 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____6499 =
                let uu____6501 = FStar_Options.silent ()  in
                Prims.op_Negation uu____6501  in
              if uu____6499
              then
                let uu____6504 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____6504
              else ());
             (g3,
               (FStar_Pervasives_Native.Some
                  (FStar_Extraction_ML_Syntax.MLLib
                     [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                        (FStar_Extraction_ML_Syntax.MLLib []))]))))
          else (g3, FStar_Pervasives_Native.None)
  
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun m  ->
      (let uu____6579 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____6579);
      (let uu____6582 =
         let uu____6584 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____6584  in
       if uu____6582
       then
         let uu____6587 =
           let uu____6589 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6589
            in
         failwith uu____6587
       else ());
      (let uu____6594 = FStar_Options.interactive ()  in
       if uu____6594
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____6614 = FStar_Options.debug_any ()  in
            if uu____6614
            then
              let msg =
                let uu____6625 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____6625  in
              FStar_Util.measure_execution_time msg
                (fun uu____6635  -> extract' g m)
            else extract' g m  in
          (let uu____6639 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____6639);
          res))
  
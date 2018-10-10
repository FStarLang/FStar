open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____13 =
        let uu____20 =
          let uu____21 =
            let uu____38 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____41 =
              let uu____52 = FStar_Syntax_Syntax.iarg t  in
              let uu____61 =
                let uu____72 =
                  let uu____81 =
                    let uu____82 =
                      let uu____89 =
                        let uu____90 =
                          let uu____91 =
                            let uu____97 =
                              let uu____99 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.strcat "Not yet implemented:" uu____99
                               in
                            (uu____97, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____91  in
                        FStar_Syntax_Syntax.Tm_constant uu____90  in
                      FStar_Syntax_Syntax.mk uu____89  in
                    uu____82 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____81  in
                [uu____72]  in
              uu____52 :: uu____61  in
            (uu____38, uu____41)  in
          FStar_Syntax_Syntax.Tm_app uu____21  in
        FStar_Syntax_Syntax.mk uu____20  in
      uu____13 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____171 = FStar_Syntax_Util.arrow_formals t  in
        match uu____171 with
        | ([],t1) ->
            let b =
              let uu____214 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____214  in
            let uu____222 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____222 FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____259 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____259 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____263 =
          let uu____268 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____268  in
        {
          FStar_Syntax_Syntax.lbname = uu____263;
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
  'Auu____290 .
    'Auu____290 Prims.list ->
      ('Auu____290,'Auu____290) FStar_Pervasives_Native.tuple2
  =
  fun uu___403_301  ->
    match uu___403_301 with
    | a::b::[] -> (a, b)
    | uu____306 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___404_321  ->
    match uu___404_321 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____324 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____333 = FStar_Syntax_Subst.compress x  in
    match uu____333 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____337;
        FStar_Syntax_Syntax.vars = uu____338;_} ->
        let uu____341 =
          let uu____343 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____343  in
        (match uu____341 with
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
         | uu____352 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____355;
             FStar_Syntax_Syntax.vars = uu____356;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____358));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____359;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____360;_},uu____361)::[]);
        FStar_Syntax_Syntax.pos = uu____362;
        FStar_Syntax_Syntax.vars = uu____363;_} ->
        let uu____406 =
          let uu____408 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____408  in
        (match uu____406 with
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
         | uu____417 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____419));
        FStar_Syntax_Syntax.pos = uu____420;
        FStar_Syntax_Syntax.vars = uu____421;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____426));
        FStar_Syntax_Syntax.pos = uu____427;
        FStar_Syntax_Syntax.vars = uu____428;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____433));
        FStar_Syntax_Syntax.pos = uu____434;
        FStar_Syntax_Syntax.vars = uu____435;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____441);
        FStar_Syntax_Syntax.pos = uu____442;
        FStar_Syntax_Syntax.vars = uu____443;_} -> extract_meta x1
    | uu____450 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____470 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv,'Auu____470) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____512  ->
             match uu____512 with
             | (bv,uu____523) ->
                 let uu____524 =
                   let uu____525 =
                     let uu____528 =
                       let uu____529 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____529  in
                     FStar_Pervasives_Native.Some uu____528  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____525  in
                 let uu____531 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____524, uu____531)) env bs
  
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
    let uu____732 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____734 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____737 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____739 =
      let uu____741 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____755 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____757 =
                  let uu____759 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____759  in
                Prims.strcat uu____755 uu____757))
         in
      FStar_All.pipe_right uu____741 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____732 uu____734 uu____737
      uu____739
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          (FStar_Extraction_ML_UEnv.uenv,inductive_family Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____813 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____861 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____861 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____900,t2,l',nparams,uu____904)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____911 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____911 with
                                           | (bs',body) ->
                                               let uu____950 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____950 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____1041  ->
                                                           fun uu____1042  ->
                                                             match (uu____1041,
                                                                    uu____1042)
                                                             with
                                                             | ((b',uu____1068),
                                                                (b,uu____1070))
                                                                 ->
                                                                 let uu____1091
                                                                   =
                                                                   let uu____1098
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____1098)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1091)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1104 =
                                                        let uu____1105 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1105
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1104
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1108 -> []))
                               in
                            let metadata =
                              let uu____1112 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____1115 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____1112 uu____1115  in
                            let fv =
                              FStar_Syntax_Syntax.lid_as_fv l
                                FStar_Syntax_Syntax.delta_constant
                                FStar_Pervasives_Native.None
                               in
                            let env2 =
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                fv
                               in
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
                   | uu____1122 -> (env1, [])) env ses
             in
          match uu____813 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type iface =
  {
  iface_module_name: FStar_Extraction_ML_Syntax.mlpath ;
  iface_bindings:
    (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_UEnv.exp_binding)
      FStar_Pervasives_Native.tuple2 Prims.list
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
    (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_UEnv.exp_binding)
      FStar_Pervasives_Native.tuple2 Prims.list)
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
  (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_UEnv.exp_binding)
    FStar_Pervasives_Native.tuple2 Prims.list -> iface)
  =
  fun fvs  ->
    let uu___414_1302 = empty_iface  in
    {
      iface_module_name = (uu___414_1302.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___414_1302.iface_tydefs);
      iface_type_names = (uu___414_1302.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___415_1313 = empty_iface  in
    let uu____1314 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___415_1313.iface_module_name);
      iface_bindings = (uu___415_1313.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1314
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___416_1329 = empty_iface  in
    {
      iface_module_name = (uu___416_1329.iface_module_name);
      iface_bindings = (uu___416_1329.iface_bindings);
      iface_tydefs = (uu___416_1329.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1341 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1341;
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
  'Auu____1386 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1386,FStar_Extraction_ML_Syntax.mlty)
        FStar_Pervasives_Native.tuple2 -> Prims.string
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
      let uu____1418 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1420 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1422 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1418 uu____1420
        uu____1422
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_UEnv.exp_binding)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun cm  ->
    fun uu____1440  ->
      match uu____1440 with
      | (fv,exp_binding) ->
          let uu____1448 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1450 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1448 uu____1450
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1465 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1467 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1465 uu____1467
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1485 =
      let uu____1487 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1487 (FStar_String.concat "\n")  in
    let uu____1501 =
      let uu____1503 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1503 (FStar_String.concat "\n")  in
    let uu____1513 =
      let uu____1515 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1515 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1485 uu____1501
      uu____1513
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___405_1548  ->
           match uu___405_1548 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1565 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____1570 =
      let uu____1572 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1572 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1570
  
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t,iface,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun quals  ->
      fun attrs  ->
        fun lb  ->
          let uu____1632 =
            let uu____1641 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1641 with
            | (tcenv,uu____1659,def_typ) ->
                let uu____1665 = as_pair def_typ  in (tcenv, uu____1665)
             in
          match uu____1632 with
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
                let uu____1696 =
                  let uu____1697 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1697 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1696 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1705 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1724 -> def  in
              let uu____1725 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1736) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1761 -> ([], def1)  in
              (match uu____1725 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___406_1781  ->
                          match uu___406_1781 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1784 -> false) quals
                      in
                   let uu____1786 = binders_as_mlty_binders env bs  in
                   (match uu____1786 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1813 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1813
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1818 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___407_1825  ->
                                    match uu___407_1825 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1827 -> true
                                    | uu____1833 -> false))
                             in
                          if uu____1818
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1847 = extract_metadata attrs  in
                          let uu____1850 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1847 uu____1850  in
                        let td =
                          let uu____1873 = lident_as_mlsymbol lid  in
                          (assumed, uu____1873, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1885 =
                            let uu____1886 =
                              let uu____1887 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1887
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1886  in
                          [uu____1885;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1888 =
                          let uu____1893 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___408_1899  ->
                                    match uu___408_1899 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1903 -> false))
                             in
                          if uu____1893
                          then
                            let uu____1910 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____1910, (iface_of_type_names [fv]))
                          else
                            (let uu____1913 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____1913 with
                             | (env2,tydef) ->
                                 let uu____1924 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1924))
                           in
                        (match uu____1888 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,iface) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____2000 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2000
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2007 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2007 with | (env2,uu____2026,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2065 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2065 with
        | (env_iparams,vars) ->
            let uu____2093 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2093 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2157,t,uu____2159,uu____2160,uu____2161);
            FStar_Syntax_Syntax.sigrng = uu____2162;
            FStar_Syntax_Syntax.sigquals = uu____2163;
            FStar_Syntax_Syntax.sigmeta = uu____2164;
            FStar_Syntax_Syntax.sigattrs = uu____2165;_}::[],uu____2166),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2185 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2185 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2218),quals) ->
          let uu____2232 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____2232 with
           | (env1,ifams) ->
               let uu____2249 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____2249 with
                | (env2,td) ->
                    let uu____2290 =
                      let uu____2291 =
                        let uu____2292 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____2292  in
                      iface_union uu____2291
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____2290)))
      | uu____2301 -> failwith "Unexpected signature element"
  
let (extract_type_declaration :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.univ_name Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              (env_t,iface,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
                FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun lid  ->
      fun quals  ->
        fun attrs  ->
          fun univs1  ->
            fun t  ->
              let uu____2376 =
                let uu____2378 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___409_2384  ->
                          match uu___409_2384 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2387 -> false))
                   in
                Prims.op_Negation uu____2378  in
              if uu____2376
              then (g, empty_iface, [])
              else
                (let uu____2402 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2402 with
                 | (bs,uu____2426) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2449 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2449;
                         FStar_Syntax_Syntax.lbattrs = attrs;
                         FStar_Syntax_Syntax.lbpos =
                           (t.FStar_Syntax_Syntax.pos)
                       }  in
                     extract_typ_abbrev g quals attrs lb)
  
let (extract_reifiable_effect :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Extraction_ML_UEnv.uenv,iface,FStar_Extraction_ML_Syntax.mlmodule1
                                             Prims.list)
        FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun ed  ->
      let extend_env g1 lid ml_name tm tysc =
        let fv =
          FStar_Syntax_Syntax.lid_as_fv lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        let uu____2512 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2512 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2534 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2534
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
        (let uu____2570 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2570
         then
           let uu____2575 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2575
         else ());
        (let uu____2580 =
           let uu____2581 = FStar_Syntax_Subst.compress tm  in
           uu____2581.FStar_Syntax_Syntax.n  in
         match uu____2580 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2589) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2596 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2596 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2601;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2602;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2604;_} ->
                  let uu____2607 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2607, tysc))
         | uu____2608 ->
             let uu____2609 =
               let uu____2611 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2613 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2611 uu____2613
                in
             failwith uu____2609)
         in
      let extract_action g1 a =
        (let uu____2641 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2641
         then
           let uu____2646 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2648 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2646
             uu____2648
         else ());
        (let uu____2653 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2653 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2673 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2673  in
             let lb =
               FStar_Syntax_Syntax.mk_lb
                 (lbname, (a.FStar_Syntax_Syntax.action_univs),
                   FStar_Parser_Const.effect_Tot_lid,
                   (a.FStar_Syntax_Syntax.action_typ),
                   (a.FStar_Syntax_Syntax.action_defn),
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
             let uu____2701 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2701 with
              | (a_let,uu____2717,ty) ->
                  ((let uu____2720 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2720
                    then
                      let uu____2725 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2725
                    else ());
                   (let uu____2730 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2753,mllb::[]),uu____2755) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____2795 -> failwith "Impossible"  in
                    match uu____2730 with
                    | (exp,tysc) ->
                        ((let uu____2833 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____2833
                          then
                            ((let uu____2839 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____2839);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____2855 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____2855 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____2877 =
        let uu____2884 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____2884 with
        | (return_tm,ty_sc) ->
            let uu____2901 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____2901 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____2877 with
      | (g1,return_iface,return_decl) ->
          let uu____2926 =
            let uu____2933 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____2933 with
            | (bind_tm,ty_sc) ->
                let uu____2950 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____2950 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____2926 with
           | (g2,bind_iface,bind_decl) ->
               let uu____2975 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____2975 with
                | (g3,actions) ->
                    let uu____3012 = FStar_List.unzip actions  in
                    (match uu____3012 with
                     | (actions_iface,actions1) ->
                         let uu____3039 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3039, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Extraction_ML_UEnv.uenv,iface) FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3061 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3070 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3087 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3106 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3106 with | (env,iface1,uu____3121) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3127) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3136 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3136 with | (env,iface1,uu____3151) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3162 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3168 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____3168)
             in
          if uu____3162
          then
            let uu____3175 =
              let uu____3186 =
                let uu____3187 =
                  let uu____3190 = always_fail lid t  in [uu____3190]  in
                (false, uu____3187)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3186  in
            (match uu____3175 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3216) ->
          let uu____3221 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3221 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3250 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3251 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3252 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3259 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3260 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3275 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3288 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____3288
          then
            let uu____3301 = extract_reifiable_effect g ed  in
            (match uu____3301 with | (env,iface1,uu____3316) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv,iface) FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun modul  ->
      let uu____3338 = FStar_Options.interactive ()  in
      if uu____3338
      then (g, empty_iface)
      else
        (let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___417_3349 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___417_3349.iface_bindings);
             iface_tydefs = (uu___417_3349.iface_tydefs);
             iface_type_names = (uu___417_3349.iface_type_names)
           }  in
         FStar_List.fold_left
           (fun uu____3362  ->
              fun se  ->
                match uu____3362 with
                | (g1,iface2) ->
                    let uu____3374 = extract_sigelt_iface g1 se  in
                    (match uu____3374 with
                     | (g2,iface') ->
                         let uu____3385 = iface_union iface2 iface'  in
                         (g2, uu____3385))) (g, iface1) decls)
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___418_3397 = g  in
      let uu____3398 =
        let uu____3401 =
          FStar_List.map (fun _0_1  -> FStar_Extraction_ML_UEnv.Fv _0_1)
            iface1.iface_bindings
           in
        FStar_List.append uu____3401 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___418_3397.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____3398;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___418_3397.FStar_Extraction_ML_UEnv.currentModule)
      }
  
let (extract_bundle :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____3480 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____3480
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____3488 =
            let uu____3489 =
              let uu____3492 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____3492  in
            uu____3489.FStar_Syntax_Syntax.n  in
          match uu____3488 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3497) ->
              FStar_List.map
                (fun uu____3530  ->
                   match uu____3530 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____3539;
                        FStar_Syntax_Syntax.sort = uu____3540;_},uu____3541)
                       -> ppname.FStar_Ident.idText) bs
          | uu____3549 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____3557 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____3557 with
        | (env2,uu____3584,uu____3585) ->
            let uu____3588 =
              let uu____3601 = lident_as_mlsymbol ctor.dname  in
              let uu____3603 =
                let uu____3611 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____3611  in
              (uu____3601, uu____3603)  in
            (env2, uu____3588)
         in
      let extract_one_family env1 ind =
        let uu____3672 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____3672 with
        | (env2,vars) ->
            let uu____3716 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____3716 with
             | (env3,ctors) ->
                 let uu____3823 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____3823 with
                  | (indices,uu____3865) ->
                      let ml_params =
                        let uu____3890 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____3916  ->
                                    let uu____3924 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____3924))
                           in
                        FStar_List.append vars uu____3890  in
                      let tbody =
                        let uu____3929 =
                          FStar_Util.find_opt
                            (fun uu___410_3934  ->
                               match uu___410_3934 with
                               | FStar_Syntax_Syntax.RecordType uu____3936 ->
                                   true
                               | uu____3946 -> false) ind.iquals
                           in
                        match uu____3929 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____3958 = FStar_List.hd ctors  in
                            (match uu____3958 with
                             | (uu____3983,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____4027  ->
                                          match uu____4027 with
                                          | (uu____4038,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____4043 =
                                                lident_as_mlsymbol lid  in
                                              (uu____4043, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4046 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____4049 =
                        let uu____4072 = lident_as_mlsymbol ind.iname  in
                        (false, uu____4072, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____4049)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____4117,t,uu____4119,uu____4120,uu____4121);
            FStar_Syntax_Syntax.sigrng = uu____4122;
            FStar_Syntax_Syntax.sigquals = uu____4123;
            FStar_Syntax_Syntax.sigmeta = uu____4124;
            FStar_Syntax_Syntax.sigattrs = uu____4125;_}::[],uu____4126),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____4145 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____4145 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____4198),quals) ->
          let uu____4212 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____4212 with
           | (env1,ifams) ->
               let uu____4231 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____4231 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____4340 -> failwith "Unexpected signature element"
  
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
             let uu____4398 = FStar_Syntax_Util.head_and_args t  in
             match uu____4398 with
             | (head1,args) ->
                 let uu____4446 =
                   let uu____4448 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____4448  in
                 if uu____4446
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____4467));
                         FStar_Syntax_Syntax.pos = uu____4468;
                         FStar_Syntax_Syntax.vars = uu____4469;_},uu____4470)::[]
                        ->
                        let uu____4509 =
                          let uu____4513 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____4513  in
                        FStar_Pervasives_Native.Some uu____4509
                    | uu____4519 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____4534 =
        let uu____4536 = FStar_Options.codegen ()  in
        uu____4536 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____4534
      then []
      else
        (let uu____4546 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____4546 with
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
                      let uu____4588 =
                        let uu____4589 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____4589  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____4588  in
                    let uu____4591 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____4591 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____4624 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____4624 with
                         | (register,args) ->
                             let h =
                               let uu____4661 =
                                 let uu____4662 =
                                   let uu____4663 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____4663
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____4662
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____4661
                                in
                             let arity1 =
                               let uu____4665 =
                                 let uu____4666 =
                                   let uu____4678 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____4678, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____4666
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____4665
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
              | uu____4707 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____4735 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____4735);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____4744 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4753 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____4770 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____4787 = extract_reifiable_effect g ed  in
           (match uu____4787 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____4811 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____4825 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____4831 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____4831 with | (env,uu____4847,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4856) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____4865 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____4865 with | (env,uu____4881,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____4890) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____4901 =
             let uu____4910 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____4910 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____4939) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____4901 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___419_5025 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___419_5025.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___419_5025.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___419_5025.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___419_5025.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___419_5025.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___419_5025.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____5034 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____5034)  in
                let uu____5052 =
                  let uu____5059 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5059  in
                (match uu____5052 with
                 | (ml_let,uu____5076,uu____5077) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____5086) ->
                          let flags1 = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____5103 =
                            FStar_List.fold_left2
                              (fun uu____5129  ->
                                 fun ml_lb  ->
                                   fun uu____5131  ->
                                     match (uu____5129, uu____5131) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____5153;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____5155;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____5156;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____5157;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____5158;_})
                                         ->
                                         let uu____5183 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____5183
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5200 =
                                                let uu____5203 =
                                                  FStar_Util.right lbname  in
                                                uu____5203.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____5200.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____5207 =
                                                let uu____5208 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____5208.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____5207 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5213,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5214;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____5216;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5217;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____5218;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____5219;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____5220;_})
                                                  when
                                                  let uu____5255 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____5255 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____5259 -> []  in
                                            let meta =
                                              FStar_List.append flags1
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___420_5264 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___420_5264.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___420_5264.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___420_5264.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___420_5264.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___420_5264.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____5265 =
                                              let uu____5270 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___411_5277  ->
                                                        match uu___411_5277
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____5279 ->
                                                            true
                                                        | uu____5285 -> false))
                                                 in
                                              if uu____5270
                                              then
                                                let mname =
                                                  let uu____5301 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5301
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____5310 =
                                                  let uu____5318 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____5319 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____5318 mname
                                                    uu____5319
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____5310 with
                                                | (env1,uu____5326,uu____5327)
                                                    ->
                                                    (env1,
                                                      (let uu___421_5331 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___421_5331.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___421_5331.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___421_5331.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___421_5331.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___421_5331.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____5338 =
                                                   let uu____5346 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____5346
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____5338 with
                                                 | (env1,uu____5353,uu____5354)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____5265 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____5103 with
                           | (g1,ml_lbs') ->
                               let uu____5384 =
                                 let uu____5387 =
                                   let uu____5390 =
                                     let uu____5391 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____5391
                                      in
                                   [uu____5390;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____5394 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____5387 uu____5394  in
                               (g1, uu____5384))
                      | uu____5399 ->
                          let uu____5400 =
                            let uu____5402 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____5402
                             in
                          failwith uu____5400)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5412,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5417 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____5423 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____5423)
              in
           if uu____5417
           then
             let always_fail1 =
               let uu___422_5433 = se  in
               let uu____5434 =
                 let uu____5435 =
                   let uu____5442 =
                     let uu____5443 =
                       let uu____5446 = always_fail lid t  in [uu____5446]
                        in
                     (false, uu____5443)  in
                   (uu____5442, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____5435  in
               {
                 FStar_Syntax_Syntax.sigel = uu____5434;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___422_5433.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___422_5433.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___422_5433.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___422_5433.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____5453 = extract_sig g always_fail1  in
             (match uu____5453 with
              | (g1,mlm) ->
                  let uu____5472 =
                    FStar_Util.find_map quals
                      (fun uu___412_5477  ->
                         match uu___412_5477 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____5481 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____5472 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____5489 =
                         let uu____5492 =
                           let uu____5493 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____5493  in
                         let uu____5494 =
                           let uu____5497 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____5497]  in
                         uu____5492 :: uu____5494  in
                       (g1, uu____5489)
                   | uu____5500 ->
                       let uu____5503 =
                         FStar_Util.find_map quals
                           (fun uu___413_5509  ->
                              match uu___413_5509 with
                              | FStar_Syntax_Syntax.Projector (l,uu____5513)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____5514 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____5503 with
                        | FStar_Pervasives_Native.Some uu____5521 -> (g1, [])
                        | uu____5524 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____5534 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____5534 with
            | (ml_main,uu____5548,uu____5549) ->
                let uu____5550 =
                  let uu____5553 =
                    let uu____5554 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____5554  in
                  [uu____5553; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____5550))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5557 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____5565 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____5574 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5577 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv,FStar_Extraction_ML_Syntax.mllib
                                       Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____5620 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___423_5624 = g  in
         let uu____5625 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.env_tcenv = uu____5625;
           FStar_Extraction_ML_UEnv.env_bindings =
             (uu___423_5624.FStar_Extraction_ML_UEnv.env_bindings);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___423_5624.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___423_5624.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____5626 =
         let uu____5628 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____5628  in
       if uu____5626
       then
         let uu____5637 = extract_iface g1 m  in
         match uu____5637 with
         | (g2,iface1) ->
             (FStar_Extraction_ML_UEnv.debug g2
                (fun uu____5653  ->
                   let uu____5654 = iface_to_string iface1  in
                   FStar_Util.print_string uu____5654);
              (g2, []))
       else
         (let uu____5660 =
            FStar_Util.fold_map extract_sig g1
              m.FStar_Syntax_Syntax.declarations
             in
          match uu____5660 with
          | (g2,sigs) ->
              (FStar_Extraction_ML_UEnv.debug g2
                 (fun uu____5690  ->
                    let uu____5691 = gamma_to_string g2  in
                    FStar_Util.print_string uu____5691);
               (let mlm = FStar_List.flatten sigs  in
                let is_kremlin =
                  let uu____5696 = FStar_Options.codegen ()  in
                  uu____5696 =
                    (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                   in
                if
                  ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims")
                    &&
                    (is_kremlin ||
                       (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
                then
                  ((let uu____5711 =
                      FStar_Syntax_Print.lid_to_string
                        m.FStar_Syntax_Syntax.name
                       in
                    FStar_Util.print1 "Extracted module %s\n" uu____5711);
                   (g2,
                     [FStar_Extraction_ML_Syntax.MLLib
                        [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                           (FStar_Extraction_ML_Syntax.MLLib []))]]))
                else (g2, [])))))
  
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv,FStar_Extraction_ML_Syntax.mllib
                                       Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      let uu____5783 = FStar_Options.interactive ()  in
      if uu____5783
      then (g, [])
      else
        (let uu____5796 = FStar_Options.debug_any ()  in
         if uu____5796
         then
           let msg =
             let uu____5807 =
               FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                in
             FStar_Util.format1 "Extracting module %s\n" uu____5807  in
           FStar_Util.measure_execution_time msg
             (fun uu____5817  -> extract' g m)
         else extract' g m)
  
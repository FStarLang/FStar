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
  'Auu____290 . 'Auu____290 Prims.list -> ('Auu____290 * 'Auu____290) =
  fun uu___401_301  ->
    match uu___401_301 with
    | a::b::[] -> (a, b)
    | uu____306 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___402_321  ->
    match uu___402_321 with
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
         | "FStar.Pervasives.CIfDef" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CIfDef
         | uu____353 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____356;
             FStar_Syntax_Syntax.vars = uu____357;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____359));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____360;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____361;_},uu____362)::[]);
        FStar_Syntax_Syntax.pos = uu____363;
        FStar_Syntax_Syntax.vars = uu____364;_} ->
        let uu____407 =
          let uu____409 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____409  in
        (match uu____407 with
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
         | uu____418 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____420));
        FStar_Syntax_Syntax.pos = uu____421;
        FStar_Syntax_Syntax.vars = uu____422;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____427));
        FStar_Syntax_Syntax.pos = uu____428;
        FStar_Syntax_Syntax.vars = uu____429;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____434));
        FStar_Syntax_Syntax.pos = uu____435;
        FStar_Syntax_Syntax.vars = uu____436;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____442);
        FStar_Syntax_Syntax.pos = uu____443;
        FStar_Syntax_Syntax.vars = uu____444;_} -> extract_meta x1
    | uu____451 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____471 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____471) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____513  ->
             match uu____513 with
             | (bv,uu____524) ->
                 let uu____525 =
                   let uu____526 =
                     let uu____529 =
                       let uu____530 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____530  in
                     FStar_Pervasives_Native.Some uu____529  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____526  in
                 let uu____532 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____525, uu____532)) env bs
  
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
    let uu____733 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____735 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____738 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____740 =
      let uu____742 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____756 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____758 =
                  let uu____760 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____760  in
                Prims.strcat uu____756 uu____758))
         in
      FStar_All.pipe_right uu____742 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____733 uu____735 uu____738
      uu____740
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____814 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____862 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____862 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____901,t2,l',nparams,uu____905)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____912 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____912 with
                                           | (bs',body) ->
                                               let uu____951 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____951 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____1042  ->
                                                           fun uu____1043  ->
                                                             match (uu____1042,
                                                                    uu____1043)
                                                             with
                                                             | ((b',uu____1069),
                                                                (b,uu____1071))
                                                                 ->
                                                                 let uu____1092
                                                                   =
                                                                   let uu____1099
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____1099)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1092)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1105 =
                                                        let uu____1106 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1106
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1105
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1109 -> []))
                               in
                            let metadata =
                              let uu____1113 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____1116 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____1113 uu____1116  in
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
                   | uu____1123 -> (env1, [])) env ses
             in
          match uu____814 with
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
    let uu___412_1303 = empty_iface  in
    {
      iface_module_name = (uu___412_1303.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___412_1303.iface_tydefs);
      iface_type_names = (uu___412_1303.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___413_1314 = empty_iface  in
    let uu____1315 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___413_1314.iface_module_name);
      iface_bindings = (uu___413_1314.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1315
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___414_1330 = empty_iface  in
    {
      iface_module_name = (uu___414_1330.iface_module_name);
      iface_bindings = (uu___414_1330.iface_bindings);
      iface_tydefs = (uu___414_1330.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1342 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1342;
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
  'Auu____1387 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1387 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____1419 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1421 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1423 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1419 uu____1421
        uu____1423
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1441  ->
      match uu____1441 with
      | (fv,exp_binding) ->
          let uu____1449 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1451 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1449 uu____1451
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1466 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1468 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1466 uu____1468
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1486 =
      let uu____1488 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1488 (FStar_String.concat "\n")  in
    let uu____1502 =
      let uu____1504 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1504 (FStar_String.concat "\n")  in
    let uu____1514 =
      let uu____1516 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1516 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1486 uu____1502
      uu____1514
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___403_1549  ->
           match uu___403_1549 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1566 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____1571 =
      let uu____1573 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1573 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1571
  
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
          let uu____1633 =
            let uu____1642 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1642 with
            | (tcenv,uu____1660,def_typ) ->
                let uu____1666 = as_pair def_typ  in (tcenv, uu____1666)
             in
          match uu____1633 with
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
                let uu____1697 =
                  let uu____1698 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1698 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1697 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1706 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1725 -> def  in
              let uu____1726 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1737) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1762 -> ([], def1)  in
              (match uu____1726 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___404_1782  ->
                          match uu___404_1782 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1785 -> false) quals
                      in
                   let uu____1787 = binders_as_mlty_binders env bs  in
                   (match uu____1787 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1814 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1814
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1819 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___405_1826  ->
                                    match uu___405_1826 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1828 -> true
                                    | uu____1834 -> false))
                             in
                          if uu____1819
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1848 = extract_metadata attrs  in
                          let uu____1851 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1848 uu____1851  in
                        let td =
                          let uu____1874 = lident_as_mlsymbol lid  in
                          (assumed, uu____1874, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1886 =
                            let uu____1887 =
                              let uu____1888 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1888
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1887  in
                          [uu____1886;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1889 =
                          let uu____1894 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___406_1900  ->
                                    match uu___406_1900 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1904 -> false))
                             in
                          if uu____1894
                          then
                            let uu____1911 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____1911, (iface_of_type_names [fv]))
                          else
                            (let uu____1914 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____1914 with
                             | (env2,tydef) ->
                                 let uu____1925 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1925))
                           in
                        (match uu____1889 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____2001 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2001
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2008 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2008 with | (env2,uu____2027,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2066 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2066 with
        | (env_iparams,vars) ->
            let uu____2094 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2094 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2158,t,uu____2160,uu____2161,uu____2162);
            FStar_Syntax_Syntax.sigrng = uu____2163;
            FStar_Syntax_Syntax.sigquals = uu____2164;
            FStar_Syntax_Syntax.sigmeta = uu____2165;
            FStar_Syntax_Syntax.sigattrs = uu____2166;_}::[],uu____2167),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2186 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2186 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2219),quals) ->
          let uu____2233 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____2233 with
           | (env1,ifams) ->
               let uu____2250 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____2250 with
                | (env2,td) ->
                    let uu____2291 =
                      let uu____2292 =
                        let uu____2293 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____2293  in
                      iface_union uu____2292
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____2291)))
      | uu____2302 -> failwith "Unexpected signature element"
  
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
              let uu____2377 =
                let uu____2379 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___407_2385  ->
                          match uu___407_2385 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2388 -> false))
                   in
                Prims.op_Negation uu____2379  in
              if uu____2377
              then (g, empty_iface, [])
              else
                (let uu____2403 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2403 with
                 | (bs,uu____2427) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2450 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2450;
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
        let uu____2513 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2513 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2535 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2535
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
        (let uu____2571 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2571
         then
           let uu____2576 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2576
         else ());
        (let uu____2581 =
           let uu____2582 = FStar_Syntax_Subst.compress tm  in
           uu____2582.FStar_Syntax_Syntax.n  in
         match uu____2581 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2590) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2597 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2597 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2602;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2603;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2605;_} ->
                  let uu____2608 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2608, tysc))
         | uu____2609 ->
             let uu____2610 =
               let uu____2612 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2614 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2612 uu____2614
                in
             failwith uu____2610)
         in
      let extract_action g1 a =
        (let uu____2642 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2642
         then
           let uu____2647 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2649 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2647
             uu____2649
         else ());
        (let uu____2654 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2654 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2674 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2674  in
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
             let uu____2704 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2704 with
              | (a_let,uu____2720,ty) ->
                  ((let uu____2723 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2723
                    then
                      let uu____2728 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2728
                    else ());
                   (let uu____2733 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2756,mllb::[]),uu____2758) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____2798 -> failwith "Impossible"  in
                    match uu____2733 with
                    | (exp,tysc) ->
                        ((let uu____2836 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____2836
                          then
                            ((let uu____2842 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____2842);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____2858 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____2858 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____2880 =
        let uu____2887 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____2887 with
        | (return_tm,ty_sc) ->
            let uu____2904 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____2904 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____2880 with
      | (g1,return_iface,return_decl) ->
          let uu____2929 =
            let uu____2936 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____2936 with
            | (bind_tm,ty_sc) ->
                let uu____2953 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____2953 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____2929 with
           | (g2,bind_iface,bind_decl) ->
               let uu____2978 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____2978 with
                | (g3,actions) ->
                    let uu____3015 = FStar_List.unzip actions  in
                    (match uu____3015 with
                     | (actions_iface,actions1) ->
                         let uu____3042 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3042, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3064 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3073 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3090 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3109 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3109 with | (env,iface1,uu____3124) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3130) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3139 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3139 with | (env,iface1,uu____3154) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3165 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3171 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____3171)
             in
          if uu____3165
          then
            let uu____3178 =
              let uu____3189 =
                let uu____3190 =
                  let uu____3193 = always_fail lid t  in [uu____3193]  in
                (false, uu____3190)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3189  in
            (match uu____3178 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3219) ->
          let uu____3224 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3224 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3253 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3254 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3255 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3262 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3263 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3278 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3291 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____3291
          then
            let uu____3304 = extract_reifiable_effect g ed  in
            (match uu____3304 with | (env,iface1,uu____3319) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3341 = FStar_Options.interactive ()  in
      if uu____3341
      then (g, empty_iface)
      else
        (let uu____3350 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___415_3354 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___415_3354.iface_bindings);
             iface_tydefs = (uu___415_3354.iface_tydefs);
             iface_type_names = (uu___415_3354.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____3372  ->
                fun se  ->
                  match uu____3372 with
                  | (g1,iface2) ->
                      let uu____3384 = extract_sigelt_iface g1 se  in
                      (match uu____3384 with
                       | (g2,iface') ->
                           let uu____3395 = iface_union iface2 iface'  in
                           (g2, uu____3395))) (g, iface1) decls
            in
         (let uu____3397 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____3397);
         res)
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___416_3410 = g  in
      let uu____3411 =
        let uu____3414 =
          FStar_List.map (fun _0_1  -> FStar_Extraction_ML_UEnv.Fv _0_1)
            iface1.iface_bindings
           in
        FStar_List.append uu____3414 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___416_3410.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____3411;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___416_3410.FStar_Extraction_ML_UEnv.currentModule)
      }
  
let (extract_bundle :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____3498 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____3498
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____3506 =
            let uu____3507 =
              let uu____3510 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____3510  in
            uu____3507.FStar_Syntax_Syntax.n  in
          match uu____3506 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3515) ->
              FStar_List.map
                (fun uu____3548  ->
                   match uu____3548 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____3557;
                        FStar_Syntax_Syntax.sort = uu____3558;_},uu____3559)
                       -> ppname.FStar_Ident.idText) bs
          | uu____3567 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____3575 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____3575 with
        | (env2,uu____3602,uu____3603) ->
            let uu____3606 =
              let uu____3619 = lident_as_mlsymbol ctor.dname  in
              let uu____3621 =
                let uu____3629 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____3629  in
              (uu____3619, uu____3621)  in
            (env2, uu____3606)
         in
      let extract_one_family env1 ind =
        let uu____3690 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____3690 with
        | (env_iparams,vars) ->
            let uu____3734 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____3734 with
             | (env2,ctors) ->
                 let uu____3841 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____3841 with
                  | (indices,uu____3883) ->
                      let ml_params =
                        let uu____3908 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____3934  ->
                                    let uu____3942 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____3942))
                           in
                        FStar_List.append vars uu____3908  in
                      let tbody =
                        let uu____3947 =
                          FStar_Util.find_opt
                            (fun uu___408_3952  ->
                               match uu___408_3952 with
                               | FStar_Syntax_Syntax.RecordType uu____3954 ->
                                   true
                               | uu____3964 -> false) ind.iquals
                           in
                        match uu____3947 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____3976 = FStar_List.hd ctors  in
                            (match uu____3976 with
                             | (uu____4001,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____4045  ->
                                          match uu____4045 with
                                          | (uu____4056,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____4061 =
                                                lident_as_mlsymbol lid  in
                                              (uu____4061, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4064 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____4067 =
                        let uu____4090 = lident_as_mlsymbol ind.iname  in
                        (false, uu____4090, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____4067)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____4135,t,uu____4137,uu____4138,uu____4139);
            FStar_Syntax_Syntax.sigrng = uu____4140;
            FStar_Syntax_Syntax.sigquals = uu____4141;
            FStar_Syntax_Syntax.sigmeta = uu____4142;
            FStar_Syntax_Syntax.sigattrs = uu____4143;_}::[],uu____4144),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____4163 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____4163 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____4216),quals) ->
          let uu____4230 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____4230 with
           | (env1,ifams) ->
               let uu____4249 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____4249 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____4358 -> failwith "Unexpected signature element"
  
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
             let uu____4416 = FStar_Syntax_Util.head_and_args t  in
             match uu____4416 with
             | (head1,args) ->
                 let uu____4464 =
                   let uu____4466 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____4466  in
                 if uu____4464
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____4485));
                         FStar_Syntax_Syntax.pos = uu____4486;
                         FStar_Syntax_Syntax.vars = uu____4487;_},uu____4488)::[]
                        ->
                        let uu____4527 =
                          let uu____4531 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____4531  in
                        FStar_Pervasives_Native.Some uu____4527
                    | uu____4537 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____4552 =
        let uu____4554 = FStar_Options.codegen ()  in
        uu____4554 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____4552
      then []
      else
        (let uu____4564 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____4564 with
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
                      let uu____4606 =
                        let uu____4607 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____4607  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____4606  in
                    let uu____4609 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____4609 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____4642 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____4642 with
                         | (register,args) ->
                             let h =
                               let uu____4679 =
                                 let uu____4680 =
                                   let uu____4681 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____4681
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____4680
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____4679
                                in
                             let arity1 =
                               let uu____4683 =
                                 let uu____4684 =
                                   let uu____4696 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____4696, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____4684
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____4683
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
              | uu____4725 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____4753 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____4753);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____4762 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4771 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____4788 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____4805 = extract_reifiable_effect g ed  in
           (match uu____4805 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____4829 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____4843 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____4849 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____4849 with | (env,uu____4865,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4874) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____4883 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____4883 with | (env,uu____4899,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____4908) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____4919 =
             let uu____4928 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____4928 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____4957) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____4919 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___417_5043 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___417_5043.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___417_5043.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___417_5043.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___417_5043.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___417_5043.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___417_5043.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____5052 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____5052)  in
                let uu____5070 =
                  let uu____5077 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5077  in
                (match uu____5070 with
                 | (ml_let,uu____5094,uu____5095) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____5104) ->
                          let flags1 = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____5121 =
                            FStar_List.fold_left2
                              (fun uu____5147  ->
                                 fun ml_lb  ->
                                   fun uu____5149  ->
                                     match (uu____5147, uu____5149) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____5171;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____5173;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____5174;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____5175;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____5176;_})
                                         ->
                                         let uu____5201 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____5201
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5218 =
                                                let uu____5221 =
                                                  FStar_Util.right lbname  in
                                                uu____5221.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____5218.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____5225 =
                                                let uu____5226 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____5226.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____5225 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5231,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5232;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____5234;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5235;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____5236;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____5237;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____5238;_})
                                                  when
                                                  let uu____5273 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____5273 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____5277 -> []  in
                                            let meta =
                                              FStar_List.append flags1
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___418_5282 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___418_5282.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___418_5282.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___418_5282.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___418_5282.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___418_5282.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____5283 =
                                              let uu____5288 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___409_5295  ->
                                                        match uu___409_5295
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____5297 ->
                                                            true
                                                        | uu____5303 -> false))
                                                 in
                                              if uu____5288
                                              then
                                                let mname =
                                                  let uu____5319 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5319
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____5328 =
                                                  let uu____5336 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____5337 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____5336 mname
                                                    uu____5337
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____5328 with
                                                | (env1,uu____5344,uu____5345)
                                                    ->
                                                    (env1,
                                                      (let uu___419_5349 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___419_5349.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___419_5349.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___419_5349.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___419_5349.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___419_5349.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____5356 =
                                                   let uu____5364 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____5364
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____5356 with
                                                 | (env1,uu____5371,uu____5372)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____5283 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____5121 with
                           | (g1,ml_lbs') ->
                               let uu____5402 =
                                 let uu____5405 =
                                   let uu____5408 =
                                     let uu____5409 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____5409
                                      in
                                   [uu____5408;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____5412 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____5405 uu____5412  in
                               (g1, uu____5402))
                      | uu____5417 ->
                          let uu____5418 =
                            let uu____5420 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____5420
                             in
                          failwith uu____5418)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5430,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5435 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____5441 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____5441)
              in
           if uu____5435
           then
             let always_fail1 =
               let uu___420_5451 = se  in
               let uu____5452 =
                 let uu____5453 =
                   let uu____5460 =
                     let uu____5461 =
                       let uu____5464 = always_fail lid t  in [uu____5464]
                        in
                     (false, uu____5461)  in
                   (uu____5460, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____5453  in
               {
                 FStar_Syntax_Syntax.sigel = uu____5452;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___420_5451.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___420_5451.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___420_5451.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___420_5451.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____5471 = extract_sig g always_fail1  in
             (match uu____5471 with
              | (g1,mlm) ->
                  let uu____5490 =
                    FStar_Util.find_map quals
                      (fun uu___410_5495  ->
                         match uu___410_5495 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____5499 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____5490 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____5507 =
                         let uu____5510 =
                           let uu____5511 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____5511  in
                         let uu____5512 =
                           let uu____5515 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____5515]  in
                         uu____5510 :: uu____5512  in
                       (g1, uu____5507)
                   | uu____5518 ->
                       let uu____5521 =
                         FStar_Util.find_map quals
                           (fun uu___411_5527  ->
                              match uu___411_5527 with
                              | FStar_Syntax_Syntax.Projector (l,uu____5531)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____5532 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____5521 with
                        | FStar_Pervasives_Native.Some uu____5539 -> (g1, [])
                        | uu____5542 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____5552 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____5552 with
            | (ml_main,uu____5566,uu____5567) ->
                let uu____5568 =
                  let uu____5571 =
                    let uu____5572 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____5572  in
                  [uu____5571; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____5568))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5575 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____5583 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____5592 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5595 -> (g, [])
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
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____5638 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___421_5642 = g  in
         let uu____5643 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.env_tcenv = uu____5643;
           FStar_Extraction_ML_UEnv.env_bindings =
             (uu___421_5642.FStar_Extraction_ML_UEnv.env_bindings);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___421_5642.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___421_5642.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____5644 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____5644 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____5674 = FStar_Options.codegen ()  in
             uu____5674 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
              in
           if
             ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
               (is_kremlin ||
                  (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
           then
             ((let uu____5689 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
               FStar_Util.print1 "Extracted module %s\n" uu____5689);
              (g2,
                (FStar_Pervasives_Native.Some
                   (FStar_Extraction_ML_Syntax.MLLib
                      [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                         (FStar_Extraction_ML_Syntax.MLLib []))]))))
           else (g2, FStar_Pervasives_Native.None))
  
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun m  ->
      (let uu____5762 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____5762);
      (let uu____5765 =
         let uu____5767 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____5767  in
       if uu____5765
       then
         let uu____5770 =
           let uu____5772 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____5772
            in
         failwith uu____5770
       else ());
      (let uu____5777 = FStar_Options.interactive ()  in
       if uu____5777
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____5797 = FStar_Options.debug_any ()  in
            if uu____5797
            then
              let msg =
                let uu____5808 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____5808  in
              FStar_Util.measure_execution_time msg
                (fun uu____5818  -> extract' g m)
            else extract' g m  in
          (let uu____5822 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____5822);
          res))
  
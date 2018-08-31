open Prims
type env_t = FStar_Extraction_ML_UEnv.env
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
                            let uu____96 =
                              let uu____97 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.strcat "Not yet implemented:" uu____97
                               in
                            (uu____96, FStar_Range.dummyRange)  in
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
        let uu____165 = FStar_Syntax_Util.arrow_formals t  in
        match uu____165 with
        | ([],t1) ->
            let b =
              let uu____208 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____208  in
            let uu____215 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____215 FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____252 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____252 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____256 =
          let uu____261 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____261  in
        {
          FStar_Syntax_Syntax.lbname = uu____256;
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
  'Auu____278 .
    'Auu____278 Prims.list ->
      ('Auu____278,'Auu____278) FStar_Pervasives_Native.tuple2
  =
  fun uu___394_289  ->
    match uu___394_289 with
    | a::b::[] -> (a, b)
    | uu____294 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___395_307  ->
    match uu___395_307 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____310 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____318 = FStar_Syntax_Subst.compress x  in
    match uu____318 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____322;
        FStar_Syntax_Syntax.vars = uu____323;_} ->
        let uu____326 =
          let uu____327 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____327  in
        (match uu____326 with
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
         | uu____330 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____332;
             FStar_Syntax_Syntax.vars = uu____333;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____335));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____336;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____337;_},uu____338)::[]);
        FStar_Syntax_Syntax.pos = uu____339;
        FStar_Syntax_Syntax.vars = uu____340;_} ->
        let uu____381 =
          let uu____382 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____382  in
        (match uu____381 with
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
         | uu____385 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____386));
        FStar_Syntax_Syntax.pos = uu____387;
        FStar_Syntax_Syntax.vars = uu____388;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____391));
        FStar_Syntax_Syntax.pos = uu____392;
        FStar_Syntax_Syntax.vars = uu____393;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____396));
        FStar_Syntax_Syntax.pos = uu____397;
        FStar_Syntax_Syntax.vars = uu____398;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____402);
        FStar_Syntax_Syntax.pos = uu____403;
        FStar_Syntax_Syntax.vars = uu____404;_} -> extract_meta x1
    | uu____411 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____429 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____429) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____469  ->
             match uu____469 with
             | (bv,uu____479) ->
                 let uu____480 =
                   let uu____481 =
                     let uu____484 =
                       let uu____485 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____485  in
                     FStar_Pervasives_Native.Some uu____484  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____481  in
                 let uu____486 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____480, uu____486)) env bs
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
  
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dtyp
  
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
    | { ifv = __fname__ifv; iname = __fname__iname;
        iparams = __fname__iparams; ityp = __fname__ityp;
        idatas = __fname__idatas; iquals = __fname__iquals;
        imetadata = __fname__imetadata;_} -> __fname__ifv
  
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { ifv = __fname__ifv; iname = __fname__iname;
        iparams = __fname__iparams; ityp = __fname__ityp;
        idatas = __fname__idatas; iquals = __fname__iquals;
        imetadata = __fname__imetadata;_} -> __fname__iname
  
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { ifv = __fname__ifv; iname = __fname__iname;
        iparams = __fname__iparams; ityp = __fname__ityp;
        idatas = __fname__idatas; iquals = __fname__iquals;
        imetadata = __fname__imetadata;_} -> __fname__iparams
  
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { ifv = __fname__ifv; iname = __fname__iname;
        iparams = __fname__iparams; ityp = __fname__ityp;
        idatas = __fname__idatas; iquals = __fname__iquals;
        imetadata = __fname__imetadata;_} -> __fname__ityp
  
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee  ->
    match projectee with
    | { ifv = __fname__ifv; iname = __fname__iname;
        iparams = __fname__iparams; ityp = __fname__ityp;
        idatas = __fname__idatas; iquals = __fname__iquals;
        imetadata = __fname__imetadata;_} -> __fname__idatas
  
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { ifv = __fname__ifv; iname = __fname__iname;
        iparams = __fname__iparams; ityp = __fname__ityp;
        idatas = __fname__idatas; iquals = __fname__iquals;
        imetadata = __fname__imetadata;_} -> __fname__iquals
  
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee  ->
    match projectee with
    | { ifv = __fname__ifv; iname = __fname__iname;
        iparams = __fname__iparams; ityp = __fname__ityp;
        idatas = __fname__idatas; iquals = __fname__iquals;
        imetadata = __fname__imetadata;_} -> __fname__imetadata
  
let (print_ifamily : inductive_family -> unit) =
  fun i  ->
    let uu____675 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____676 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____677 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____678 =
      let uu____679 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____690 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____691 =
                  let uu____692 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____692  in
                Prims.strcat uu____690 uu____691))
         in
      FStar_All.pipe_right uu____679 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____675 uu____676 uu____677
      uu____678
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____739 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____787 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____787 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____826,t2,l',nparams,uu____830)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____835 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____835 with
                                           | (bs',body) ->
                                               let uu____874 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____874 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____965  ->
                                                           fun uu____966  ->
                                                             match (uu____965,
                                                                    uu____966)
                                                             with
                                                             | ((b',uu____992),
                                                                (b,uu____994))
                                                                 ->
                                                                 let uu____1015
                                                                   =
                                                                   let uu____1022
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____1022)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1015)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1028 =
                                                        let uu____1029 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1029
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1028
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1032 -> []))
                               in
                            let metadata =
                              let uu____1036 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____1039 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____1036 uu____1039  in
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
                   | uu____1046 -> (env1, [])) env ses
             in
          match uu____739 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type iface =
  {
  iface_bindings:
    (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_UEnv.exp_binding)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  iface_tydefs: FStar_Extraction_ML_UEnv.tydef Prims.list ;
  iface_type_names: FStar_Syntax_Syntax.fv Prims.list }
let (__proj__Mkiface__item__iface_bindings :
  iface ->
    (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_UEnv.exp_binding)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { iface_bindings = __fname__iface_bindings;
        iface_tydefs = __fname__iface_tydefs;
        iface_type_names = __fname__iface_type_names;_} ->
        __fname__iface_bindings
  
let (__proj__Mkiface__item__iface_tydefs :
  iface -> FStar_Extraction_ML_UEnv.tydef Prims.list) =
  fun projectee  ->
    match projectee with
    | { iface_bindings = __fname__iface_bindings;
        iface_tydefs = __fname__iface_tydefs;
        iface_type_names = __fname__iface_type_names;_} ->
        __fname__iface_tydefs
  
let (__proj__Mkiface__item__iface_type_names :
  iface -> FStar_Syntax_Syntax.fv Prims.list) =
  fun projectee  ->
    match projectee with
    | { iface_bindings = __fname__iface_bindings;
        iface_tydefs = __fname__iface_tydefs;
        iface_type_names = __fname__iface_type_names;_} ->
        __fname__iface_type_names
  
let (empty_iface : iface) =
  { iface_bindings = []; iface_tydefs = []; iface_type_names = [] } 
let (iface_of_bindings :
  (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_UEnv.exp_binding)
    FStar_Pervasives_Native.tuple2 Prims.list -> iface)
  =
  fun fvs  ->
    { iface_bindings = fvs; iface_tydefs = []; iface_type_names = [] }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    { iface_bindings = []; iface_tydefs = tds; iface_type_names = [] }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    { iface_bindings = []; iface_tydefs = []; iface_type_names = fvs }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      {
        iface_bindings =
          (FStar_List.append if1.iface_bindings if2.iface_bindings);
        iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs);
        iface_type_names =
          (FStar_List.append if1.iface_type_names if2.iface_type_names)
      }
  
let (iface_union_l : iface Prims.list -> iface) =
  fun ifs  -> FStar_List.fold_right iface_union ifs empty_iface 
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.env ->
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
          let uu____1280 =
            let uu____1289 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1289 with
            | (tcenv,uu____1307,def_typ) ->
                let uu____1313 = as_pair def_typ  in (tcenv, uu____1313)
             in
          match uu____1280 with
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
                let uu____1344 =
                  let uu____1345 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1345 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1344 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1353 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1372 -> def  in
              let uu____1373 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1384) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1409 -> ([], def1)  in
              (match uu____1373 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___396_1428  ->
                          match uu___396_1428 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1429 -> false) quals
                      in
                   let uu____1430 = binders_as_mlty_binders env bs  in
                   (match uu____1430 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1454 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1454
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1458 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___397_1463  ->
                                    match uu___397_1463 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1464 -> true
                                    | uu____1469 -> false))
                             in
                          if uu____1458
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1477 = extract_metadata attrs  in
                          let uu____1480 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1477 uu____1480  in
                        let td =
                          let uu____1500 = lident_as_mlsymbol lid  in
                          (assumed, uu____1500, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1508 =
                            let uu____1509 =
                              let uu____1510 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1510
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1509  in
                          [uu____1508;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1511 =
                          let uu____1516 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___398_1520  ->
                                    match uu___398_1520 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1521 -> false))
                             in
                          if uu____1516
                          then
                            let uu____1526 =
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                fv
                               in
                            (uu____1526, (iface_of_type_names [fv]))
                          else
                            (let uu____1528 =
                               FStar_Extraction_ML_UEnv.extend_tydef env1 fv
                                 td
                                in
                             match uu____1528 with
                             | (env2,tydef) ->
                                 (env2, (iface_of_tydefs [tydef])))
                           in
                        (match uu____1511 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,iface) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1606 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1606
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1613 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____1613 with | (env2,uu____1629,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____1666 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1666 with
        | (env2,vars) ->
            let uu____1691 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1691 with | (env3,ctors) -> (env3, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1755,t,uu____1757,uu____1758,uu____1759);
            FStar_Syntax_Syntax.sigrng = uu____1760;
            FStar_Syntax_Syntax.sigquals = uu____1761;
            FStar_Syntax_Syntax.sigmeta = uu____1762;
            FStar_Syntax_Syntax.sigattrs = uu____1763;_}::[],uu____1764),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1781 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1781 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1813),quals) ->
          let uu____1827 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1827 with
           | (env1,ifams) ->
               let uu____1844 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1844 with
                | (env2,td) ->
                    let uu____1885 =
                      let uu____1886 =
                        let uu____1887 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____1887  in
                      iface_union uu____1886
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____1885)))
      | uu____1896 -> failwith "Unexpected signature element"
  
let (extract_type_declaration :
  FStar_Extraction_ML_UEnv.env ->
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
              let uu____1969 =
                let uu____1970 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___399_1974  ->
                          match uu___399_1974 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1975 -> false))
                   in
                Prims.op_Negation uu____1970  in
              if uu____1969
              then (g, empty_iface, [])
              else
                (let uu____1987 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____1987 with
                 | (bs,uu____2011) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2034 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2034;
                         FStar_Syntax_Syntax.lbattrs = attrs;
                         FStar_Syntax_Syntax.lbpos =
                           (t.FStar_Syntax_Syntax.pos)
                       }  in
                     extract_typ_abbrev g quals attrs lb)
  
let (extract_reifiable_effect :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Extraction_ML_UEnv.env,iface,FStar_Extraction_ML_Syntax.mlmodule1
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
        let uu____2096 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2096 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2113 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2113
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
        (let uu____2137 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug g.FStar_Extraction_ML_UEnv.tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2137
         then
           let uu____2138 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2138
         else ());
        (let uu____2140 =
           let uu____2141 = FStar_Syntax_Subst.compress tm  in
           uu____2141.FStar_Syntax_Syntax.n  in
         match uu____2140 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2149) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2156 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2156 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2161;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2162;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_isrec = uu____2164;_} ->
                  let uu____2165 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2165, tysc))
         | uu____2166 -> failwith "Not an fv")
         in
      let extract_action g1 a =
        (let uu____2192 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2192
         then
           let uu____2193 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2194 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2193
             uu____2194
         else ());
        (let uu____2196 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2196 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2216 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2216  in
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
             let uu____2240 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2240 with
              | (a_let,uu____2256,ty) ->
                  ((let uu____2259 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2259
                    then
                      let uu____2260 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2260
                    else ());
                   (let uu____2262 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2283,mllb::[]),uu____2285) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____2321 -> failwith "Impossible"  in
                    match uu____2262 with
                    | (exp,tysc) ->
                        ((let uu____2355 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____2355
                          then
                            ((let uu____2357 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____2357);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____2365 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____2365 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____2387 =
        let uu____2394 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____2394 with
        | (return_tm,ty_sc) ->
            let uu____2411 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____2411 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____2387 with
      | (g1,return_iface,return_decl) ->
          let uu____2435 =
            let uu____2442 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____2442 with
            | (bind_tm,ty_sc) ->
                let uu____2459 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____2459 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____2435 with
           | (g2,bind_iface,bind_decl) ->
               let uu____2483 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____2483 with
                | (g3,actions) ->
                    let uu____2520 = FStar_List.unzip actions  in
                    (match uu____2520 with
                     | (actions_iface,actions1) ->
                         let uu____2547 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____2547, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Extraction_ML_UEnv.env,iface) FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____2568 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____2577 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____2594 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____2612 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____2612 with | (env,iface1,uu____2627) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2633) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____2640 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____2640 with | (env,iface1,uu____2655) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____2666 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____2670 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.tcenv t
                  in
               Prims.op_Negation uu____2670)
             in
          if uu____2666
          then
            let uu____2675 =
              let uu____2686 =
                let uu____2687 =
                  let uu____2690 = always_fail lid t  in [uu____2690]  in
                (false, uu____2687)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____2686  in
            (match uu____2675 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____2713) ->
          let uu____2718 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____2718 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____2747 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2748 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____2749 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____2756 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2757 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____2772 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____2784 =
            FStar_TypeChecker_Env.is_reifiable_effect
              g.FStar_Extraction_ML_UEnv.tcenv ed.FStar_Syntax_Syntax.mname
             in
          if uu____2784
          then
            let uu____2789 = extract_reifiable_effect g ed  in
            (match uu____2789 with | (env,iface1,uu____2804) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Extraction_ML_UEnv.env,iface) FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun modul  ->
      FStar_List.fold_left
        (fun uu____2839  ->
           fun se  ->
             match uu____2839 with
             | (g1,iface1) ->
                 let uu____2851 = extract_sigelt_iface g1 se  in
                 (match uu____2851 with
                  | (g2,iface') -> (g2, (iface_union iface1 iface'))))
        (g, empty_iface) modul
  
let (extract_bundle :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____2927 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____2927
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____2934 =
            let uu____2935 =
              let uu____2938 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____2938  in
            uu____2935.FStar_Syntax_Syntax.n  in
          match uu____2934 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____2942) ->
              FStar_List.map
                (fun uu____2974  ->
                   match uu____2974 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____2982;
                        FStar_Syntax_Syntax.sort = uu____2983;_},uu____2984)
                       -> ppname.FStar_Ident.idText) bs
          | uu____2991 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2998 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2998 with
        | (env2,uu____3020,uu____3021) ->
            let uu____3022 =
              let uu____3033 = lident_as_mlsymbol ctor.dname  in
              let uu____3034 =
                let uu____3041 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____3041  in
              (uu____3033, uu____3034)  in
            (env2, uu____3022)
         in
      let extract_one_family env1 ind =
        let uu____3093 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____3093 with
        | (env2,vars) ->
            let uu____3130 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____3130 with
             | (env3,ctors) ->
                 let uu____3223 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____3223 with
                  | (indices,uu____3261) ->
                      let ml_params =
                        let uu____3285 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____3308  ->
                                    let uu____3315 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____3315))
                           in
                        FStar_List.append vars uu____3285  in
                      let tbody =
                        let uu____3317 =
                          FStar_Util.find_opt
                            (fun uu___400_3322  ->
                               match uu___400_3322 with
                               | FStar_Syntax_Syntax.RecordType uu____3323 ->
                                   true
                               | uu____3332 -> false) ind.iquals
                           in
                        match uu____3317 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____3343 = FStar_List.hd ctors  in
                            (match uu____3343 with
                             | (uu____3364,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____3401  ->
                                          match uu____3401 with
                                          | (uu____3410,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____3413 =
                                                lident_as_mlsymbol lid  in
                                              (uu____3413, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____3414 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____3417 =
                        let uu____3436 = lident_as_mlsymbol ind.iname  in
                        (false, uu____3436, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____3417)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____3470,t,uu____3472,uu____3473,uu____3474);
            FStar_Syntax_Syntax.sigrng = uu____3475;
            FStar_Syntax_Syntax.sigquals = uu____3476;
            FStar_Syntax_Syntax.sigmeta = uu____3477;
            FStar_Syntax_Syntax.sigattrs = uu____3478;_}::[],uu____3479),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____3496 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____3496 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____3542),quals) ->
          let uu____3556 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____3556 with
           | (env1,ifams) ->
               let uu____3575 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____3575 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____3668 -> failwith "Unexpected signature element"
  
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
             let uu____3722 = FStar_Syntax_Util.head_and_args t  in
             match uu____3722 with
             | (head1,args) ->
                 let uu____3769 =
                   let uu____3770 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____3770  in
                 if uu____3769
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____3783));
                         FStar_Syntax_Syntax.pos = uu____3784;
                         FStar_Syntax_Syntax.vars = uu____3785;_},uu____3786)::[]
                        ->
                        let uu____3823 =
                          let uu____3826 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____3826  in
                        FStar_Pervasives_Native.Some uu____3823
                    | uu____3829 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____3842 =
        let uu____3843 = FStar_Options.codegen ()  in
        uu____3843 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____3842
      then []
      else
        (let uu____3851 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____3851 with
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
                      let uu____3889 =
                        let uu____3890 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____3890  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____3889  in
                    let uu____3891 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.tcenv fv fv_t arity_opt
                        ml_name_str
                       in
                    match uu____3891 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin) ->
                        let uu____3916 =
                          if plugin
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____3916 with
                         | (register,args) ->
                             let h =
                               let uu____3943 =
                                 let uu____3944 =
                                   let uu____3945 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____3945
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____3944
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____3943
                                in
                             let arity1 =
                               let uu____3947 =
                                 let uu____3948 =
                                   let uu____3959 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____3959, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____3948
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____3947
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
              | uu____3983 -> []))
  
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
           let uu____4010 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____4010);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____4017 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4026 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____4043 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.tcenv ed.FStar_Syntax_Syntax.mname
           ->
           let uu____4059 = extract_reifiable_effect g ed  in
           (match uu____4059 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____4083 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____4096 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____4102 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____4102 with | (env,uu____4118,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4127) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____4134 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____4134 with | (env,uu____4150,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____4159) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____4170 =
             let uu____4177 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
                in
             FStar_Extraction_ML_Term.term_as_mlexpr g uu____4177  in
           (match uu____4170 with
            | (ml_let,uu____4193,uu____4194) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,bindings),uu____4203) ->
                     let flags1 = FStar_List.choose flag_of_qual quals  in
                     let flags' = extract_metadata attrs  in
                     let uu____4220 =
                       FStar_List.fold_left2
                         (fun uu____4246  ->
                            fun ml_lb  ->
                              fun uu____4248  ->
                                match (uu____4246, uu____4248) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____4270;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____4272;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____4273;
                                                  FStar_Syntax_Syntax.lbattrs
                                                    = uu____4274;
                                                  FStar_Syntax_Syntax.lbpos =
                                                    uu____4275;_})
                                    ->
                                    let uu____4300 =
                                      FStar_All.pipe_right
                                        ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                        (FStar_List.contains
                                           FStar_Extraction_ML_Syntax.Erased)
                                       in
                                    if uu____4300
                                    then (env, ml_lbs)
                                    else
                                      (let lb_lid =
                                         let uu____4313 =
                                           let uu____4316 =
                                             FStar_Util.right lbname  in
                                           uu____4316.FStar_Syntax_Syntax.fv_name
                                            in
                                         uu____4313.FStar_Syntax_Syntax.v  in
                                       let flags'' =
                                         let uu____4320 =
                                           let uu____4321 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____4321.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4320 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (uu____4326,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Comp
                                                             {
                                                               FStar_Syntax_Syntax.comp_univs
                                                                 = uu____4327;
                                                               FStar_Syntax_Syntax.effect_name
                                                                 = e;
                                                               FStar_Syntax_Syntax.result_typ
                                                                 = uu____4329;
                                                               FStar_Syntax_Syntax.effect_args
                                                                 = uu____4330;
                                                               FStar_Syntax_Syntax.flags
                                                                 = uu____4331;_};
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____4332;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____4333;_})
                                             when
                                             let uu____4368 =
                                               FStar_Ident.string_of_lid e
                                                in
                                             uu____4368 =
                                               "FStar.HyperStack.ST.StackInline"
                                             ->
                                             [FStar_Extraction_ML_Syntax.StackInline]
                                         | uu____4369 -> []  in
                                       let meta =
                                         FStar_List.append flags1
                                           (FStar_List.append flags' flags'')
                                          in
                                       let ml_lb1 =
                                         let uu___404_4374 = ml_lb  in
                                         {
                                           FStar_Extraction_ML_Syntax.mllb_name
                                             =
                                             (uu___404_4374.FStar_Extraction_ML_Syntax.mllb_name);
                                           FStar_Extraction_ML_Syntax.mllb_tysc
                                             =
                                             (uu___404_4374.FStar_Extraction_ML_Syntax.mllb_tysc);
                                           FStar_Extraction_ML_Syntax.mllb_add_unit
                                             =
                                             (uu___404_4374.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                           FStar_Extraction_ML_Syntax.mllb_def
                                             =
                                             (uu___404_4374.FStar_Extraction_ML_Syntax.mllb_def);
                                           FStar_Extraction_ML_Syntax.mllb_meta
                                             = meta;
                                           FStar_Extraction_ML_Syntax.print_typ
                                             =
                                             (uu___404_4374.FStar_Extraction_ML_Syntax.print_typ)
                                         }  in
                                       let uu____4375 =
                                         let uu____4380 =
                                           FStar_All.pipe_right quals
                                             (FStar_Util.for_some
                                                (fun uu___401_4385  ->
                                                   match uu___401_4385 with
                                                   | FStar_Syntax_Syntax.Projector
                                                       uu____4386 -> true
                                                   | uu____4391 -> false))
                                            in
                                         if uu____4380
                                         then
                                           let mname =
                                             let uu____4403 =
                                               mangle_projector_lid lb_lid
                                                in
                                             FStar_All.pipe_right uu____4403
                                               FStar_Extraction_ML_Syntax.mlpath_of_lident
                                              in
                                           let uu____4410 =
                                             let uu____4417 =
                                               FStar_Util.right lbname  in
                                             let uu____4418 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_fv'
                                               env uu____4417 mname
                                               uu____4418
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           match uu____4410 with
                                           | (env1,uu____4424,uu____4425) ->
                                               (env1,
                                                 (let uu___405_4427 = ml_lb1
                                                     in
                                                  {
                                                    FStar_Extraction_ML_Syntax.mllb_name
                                                      =
                                                      (FStar_Pervasives_Native.snd
                                                         mname);
                                                    FStar_Extraction_ML_Syntax.mllb_tysc
                                                      =
                                                      (uu___405_4427.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                    FStar_Extraction_ML_Syntax.mllb_add_unit
                                                      =
                                                      (uu___405_4427.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                    FStar_Extraction_ML_Syntax.mllb_def
                                                      =
                                                      (uu___405_4427.FStar_Extraction_ML_Syntax.mllb_def);
                                                    FStar_Extraction_ML_Syntax.mllb_meta
                                                      =
                                                      (uu___405_4427.FStar_Extraction_ML_Syntax.mllb_meta);
                                                    FStar_Extraction_ML_Syntax.print_typ
                                                      =
                                                      (uu___405_4427.FStar_Extraction_ML_Syntax.print_typ)
                                                  }))
                                         else
                                           (let uu____4431 =
                                              let uu____4438 =
                                                FStar_Util.must
                                                  ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                 in
                                              FStar_Extraction_ML_UEnv.extend_lb
                                                env lbname t uu____4438
                                                ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                false
                                               in
                                            match uu____4431 with
                                            | (env1,uu____4444,uu____4445) ->
                                                (env1, ml_lb1))
                                          in
                                       match uu____4375 with
                                       | (g1,ml_lb2) ->
                                           (g1, (ml_lb2 :: ml_lbs)))) 
                         (g, []) bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____4220 with
                      | (g1,ml_lbs') ->
                          let uu____4472 =
                            let uu____4475 =
                              let uu____4478 =
                                let uu____4479 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____4479
                                 in
                              [uu____4478;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))]
                               in
                            let uu____4482 = maybe_register_plugin g1 se  in
                            FStar_List.append uu____4475 uu____4482  in
                          (g1, uu____4472))
                 | uu____4487 ->
                     let uu____4488 =
                       let uu____4489 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____4489
                        in
                     failwith uu____4488))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____4497,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____4502 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____4506 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                Prims.op_Negation uu____4506)
              in
           if uu____4502
           then
             let always_fail1 =
               let uu___406_4514 = se  in
               let uu____4515 =
                 let uu____4516 =
                   let uu____4523 =
                     let uu____4524 =
                       let uu____4527 = always_fail lid t  in [uu____4527]
                        in
                     (false, uu____4524)  in
                   (uu____4523, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____4516  in
               {
                 FStar_Syntax_Syntax.sigel = uu____4515;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___406_4514.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___406_4514.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___406_4514.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___406_4514.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____4532 = extract_sig g always_fail1  in
             (match uu____4532 with
              | (g1,mlm) ->
                  let uu____4551 =
                    FStar_Util.find_map quals
                      (fun uu___402_4556  ->
                         match uu___402_4556 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____4560 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____4551 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____4568 =
                         let uu____4571 =
                           let uu____4572 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____4572  in
                         let uu____4573 =
                           let uu____4576 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____4576]  in
                         uu____4571 :: uu____4573  in
                       (g1, uu____4568)
                   | uu____4579 ->
                       let uu____4582 =
                         FStar_Util.find_map quals
                           (fun uu___403_4588  ->
                              match uu___403_4588 with
                              | FStar_Syntax_Syntax.Projector (l,uu____4592)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____4593 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4582 with
                        | FStar_Pervasives_Native.Some uu____4600 -> (g1, [])
                        | uu____4603 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____4612 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____4612 with
            | (ml_main,uu____4626,uu____4627) ->
                let uu____4628 =
                  let uu____4631 =
                    let uu____4632 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____4632  in
                  [uu____4631; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____4628))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4635 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____4642 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____4651 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4654 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____4696 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___407_4699 = g  in
         let uu____4700 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____4700;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___407_4699.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___407_4699.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___407_4699.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____4701 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____4701 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____4730 = FStar_Options.codegen ()  in
             uu____4730 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
              in
           let uu____4735 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____4735
           then
             ((let uu____4743 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____4743);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  
let (extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      let uu____4811 = FStar_Options.debug_any ()  in
      if uu____4811
      then
        let msg =
          let uu____4819 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracting module %s\n" uu____4819  in
        FStar_Util.measure_execution_time msg
          (fun uu____4827  -> extract' g m)
      else extract' g m
  
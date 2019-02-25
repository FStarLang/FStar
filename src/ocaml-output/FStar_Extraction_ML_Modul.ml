open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____68612 =
        let uu____68619 =
          let uu____68620 =
            let uu____68637 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____68640 =
              let uu____68651 = FStar_Syntax_Syntax.iarg t  in
              let uu____68660 =
                let uu____68671 =
                  let uu____68680 =
                    let uu____68681 =
                      let uu____68688 =
                        let uu____68689 =
                          let uu____68690 =
                            let uu____68696 =
                              let uu____68698 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____68698
                               in
                            (uu____68696, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____68690  in
                        FStar_Syntax_Syntax.Tm_constant uu____68689  in
                      FStar_Syntax_Syntax.mk uu____68688  in
                    uu____68681 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____68680
                   in
                [uu____68671]  in
              uu____68651 :: uu____68660  in
            (uu____68637, uu____68640)  in
          FStar_Syntax_Syntax.Tm_app uu____68620  in
        FStar_Syntax_Syntax.mk uu____68619  in
      uu____68612 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____68770 = FStar_Syntax_Util.arrow_formals t  in
        match uu____68770 with
        | ([],t1) ->
            let b =
              let uu____68813 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____68813
               in
            let uu____68821 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____68821
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____68858 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____68858 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____68862 =
          let uu____68867 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____68867  in
        {
          FStar_Syntax_Syntax.lbname = uu____68862;
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
  'Auu____68889 . 'Auu____68889 Prims.list -> ('Auu____68889 * 'Auu____68889)
  =
  fun uu___612_68900  ->
    match uu___612_68900 with
    | a::b::[] -> (a, b)
    | uu____68905 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_68920  ->
    match uu___613_68920 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____68923 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____68932 = FStar_Syntax_Subst.compress x  in
    match uu____68932 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____68936;
        FStar_Syntax_Syntax.vars = uu____68937;_} ->
        let uu____68940 =
          let uu____68942 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____68942  in
        (match uu____68940 with
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
         | uu____68951 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____68954;
             FStar_Syntax_Syntax.vars = uu____68955;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____68957));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____68958;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____68959;_},uu____68960)::[]);
        FStar_Syntax_Syntax.pos = uu____68961;
        FStar_Syntax_Syntax.vars = uu____68962;_} ->
        let uu____69005 =
          let uu____69007 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____69007  in
        (match uu____69005 with
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
         | uu____69016 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____69018));
        FStar_Syntax_Syntax.pos = uu____69019;
        FStar_Syntax_Syntax.vars = uu____69020;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____69025));
        FStar_Syntax_Syntax.pos = uu____69026;
        FStar_Syntax_Syntax.vars = uu____69027;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____69032));
        FStar_Syntax_Syntax.pos = uu____69033;
        FStar_Syntax_Syntax.vars = uu____69034;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____69040);
        FStar_Syntax_Syntax.pos = uu____69041;
        FStar_Syntax_Syntax.vars = uu____69042;_} -> extract_meta x1
    | uu____69049 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____69069 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____69069) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____69111  ->
             match uu____69111 with
             | (bv,uu____69122) ->
                 let uu____69123 =
                   let uu____69124 =
                     let uu____69127 =
                       let uu____69128 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____69128  in
                     FStar_Pervasives_Native.Some uu____69127  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____69124  in
                 let uu____69130 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____69123, uu____69130)) env bs
  
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
    let uu____69331 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____69333 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____69336 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____69338 =
      let uu____69340 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____69354 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____69356 =
                  let uu____69358 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____69358  in
                Prims.op_Hat uu____69354 uu____69356))
         in
      FStar_All.pipe_right uu____69340 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____69331 uu____69333
      uu____69336 uu____69338
  
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
          let uu____69412 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____69460 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____69460 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____69499,t2,l',nparams,uu____69503)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____69510 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____69510 with
                                           | (bs',body) ->
                                               let uu____69549 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____69549 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____69640  ->
                                                           fun uu____69641 
                                                             ->
                                                             match (uu____69640,
                                                                    uu____69641)
                                                             with
                                                             | ((b',uu____69667),
                                                                (b,uu____69669))
                                                                 ->
                                                                 let uu____69690
                                                                   =
                                                                   let uu____69697
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____69697)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____69690)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____69703 =
                                                        let uu____69704 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____69704
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____69703
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____69707 -> []))
                               in
                            let metadata =
                              let uu____69711 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____69714 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____69711 uu____69714  in
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
                   | uu____69721 -> (env1, [])) env ses
             in
          match uu____69412 with
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
    let uu___819_69901 = empty_iface  in
    {
      iface_module_name = (uu___819_69901.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___819_69901.iface_tydefs);
      iface_type_names = (uu___819_69901.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___822_69912 = empty_iface  in
    let uu____69913 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___822_69912.iface_module_name);
      iface_bindings = (uu___822_69912.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____69913
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___826_69928 = empty_iface  in
    {
      iface_module_name = (uu___826_69928.iface_module_name);
      iface_bindings = (uu___826_69928.iface_bindings);
      iface_tydefs = (uu___826_69928.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____69940 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____69940;
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
  'Auu____69985 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____69985 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____70017 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____70019 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____70021 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____70017 uu____70019
        uu____70021
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____70039  ->
      match uu____70039 with
      | (fv,exp_binding) ->
          let uu____70047 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____70049 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____70047 uu____70049
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____70064 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____70066 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____70064 uu____70066
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____70084 =
      let uu____70086 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____70086 (FStar_String.concat "\n")  in
    let uu____70100 =
      let uu____70102 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____70102 (FStar_String.concat "\n")  in
    let uu____70112 =
      let uu____70114 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____70114 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____70084 uu____70100
      uu____70112
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_70147  ->
           match uu___614_70147 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____70164 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____70169 =
      let uu____70171 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____70171 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____70169
  
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
          let uu____70231 =
            let uu____70240 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____70240 with
            | (tcenv,uu____70258,def_typ) ->
                let uu____70264 = as_pair def_typ  in (tcenv, uu____70264)
             in
          match uu____70231 with
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
                let uu____70295 =
                  let uu____70296 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____70296 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____70295 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____70304 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____70323 -> def  in
              let uu____70324 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____70335) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____70360 -> ([], def1)  in
              (match uu____70324 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_70380  ->
                          match uu___615_70380 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____70383 -> false) quals
                      in
                   let uu____70385 = binders_as_mlty_binders env bs  in
                   (match uu____70385 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____70412 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____70412
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____70417 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_70424  ->
                                    match uu___616_70424 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____70426 -> true
                                    | uu____70432 -> false))
                             in
                          if uu____70417
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____70446 = extract_metadata attrs  in
                          let uu____70449 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____70446 uu____70449  in
                        let td =
                          let uu____70472 = lident_as_mlsymbol lid  in
                          (assumed, uu____70472, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____70484 =
                            let uu____70485 =
                              let uu____70486 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____70486
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____70485
                             in
                          [uu____70484;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____70487 =
                          let uu____70492 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_70498  ->
                                    match uu___617_70498 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____70502 -> false))
                             in
                          if uu____70492
                          then
                            let uu____70509 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____70509, (iface_of_type_names [fv]))
                          else
                            (let uu____70512 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____70512 with
                             | (env2,tydef) ->
                                 let uu____70523 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____70523))
                           in
                        (match uu____70487 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____70599 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____70599
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____70606 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____70606 with | (env2,uu____70625,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____70664 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____70664 with
        | (env_iparams,vars) ->
            let uu____70692 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____70692 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____70756,t,uu____70758,uu____70759,uu____70760);
            FStar_Syntax_Syntax.sigrng = uu____70761;
            FStar_Syntax_Syntax.sigquals = uu____70762;
            FStar_Syntax_Syntax.sigmeta = uu____70763;
            FStar_Syntax_Syntax.sigattrs = uu____70764;_}::[],uu____70765),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____70784 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____70784 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____70817),quals) ->
          let uu____70831 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____70831 with
           | (env1,ifams) ->
               let uu____70848 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____70848 with
                | (env2,td) ->
                    let uu____70889 =
                      let uu____70890 =
                        let uu____70891 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____70891  in
                      iface_union uu____70890
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____70889)))
      | uu____70900 -> failwith "Unexpected signature element"
  
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
              let uu____70975 =
                let uu____70977 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_70983  ->
                          match uu___618_70983 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____70986 -> false))
                   in
                Prims.op_Negation uu____70977  in
              if uu____70975
              then (g, empty_iface, [])
              else
                (let uu____71001 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____71001 with
                 | (bs,uu____71025) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____71048 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____71048;
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
        let uu____71111 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____71111 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____71133 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____71133
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
        (let uu____71169 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71169
         then
           let uu____71174 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____71174
         else ());
        (let uu____71179 =
           let uu____71180 = FStar_Syntax_Subst.compress tm  in
           uu____71180.FStar_Syntax_Syntax.n  in
         match uu____71179 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____71188) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____71195 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____71195 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____71200;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____71201;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____71203;_} ->
                  let uu____71206 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____71206, tysc))
         | uu____71207 ->
             let uu____71208 =
               let uu____71210 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____71212 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____71210
                 uu____71212
                in
             failwith uu____71208)
         in
      let extract_action g1 a =
        (let uu____71240 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71240
         then
           let uu____71245 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____71247 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____71245
             uu____71247
         else ());
        (let uu____71252 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____71252 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____71272 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____71272  in
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
             let uu____71302 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____71302 with
              | (a_let,uu____71318,ty) ->
                  ((let uu____71321 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____71321
                    then
                      let uu____71326 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____71326
                    else ());
                   (let uu____71331 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____71354,mllb::[]),uu____71356) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____71396 -> failwith "Impossible"  in
                    match uu____71331 with
                    | (exp,tysc) ->
                        ((let uu____71434 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____71434
                          then
                            ((let uu____71440 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____71440);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____71456 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____71456 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____71478 =
        let uu____71485 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____71485 with
        | (return_tm,ty_sc) ->
            let uu____71502 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____71502 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____71478 with
      | (g1,return_iface,return_decl) ->
          let uu____71527 =
            let uu____71534 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____71534 with
            | (bind_tm,ty_sc) ->
                let uu____71551 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____71551 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____71527 with
           | (g2,bind_iface,bind_decl) ->
               let uu____71576 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____71576 with
                | (g3,actions) ->
                    let uu____71613 = FStar_List.unzip actions  in
                    (match uu____71613 with
                     | (actions_iface,actions1) ->
                         let uu____71640 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____71640, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____71662 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____71671 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____71688 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____71707 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____71707 with | (env,iface1,uu____71722) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____71728) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____71737 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____71737 with | (env,iface1,uu____71752) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____71763 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____71769 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____71769)
             in
          if uu____71763
          then
            let uu____71776 =
              let uu____71787 =
                let uu____71788 =
                  let uu____71791 = always_fail lid t  in [uu____71791]  in
                (false, uu____71788)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____71787  in
            (match uu____71776 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____71817) ->
          let uu____71822 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____71822 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____71851 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____71852 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____71853 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____71860 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____71861 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____71876 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____71889 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____71889
          then
            let uu____71902 = extract_reifiable_effect g ed  in
            (match uu____71902 with
             | (env,iface1,uu____71917) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____71939 = FStar_Options.interactive ()  in
      if uu____71939
      then (g, empty_iface)
      else
        (let uu____71948 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1165_71952 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1165_71952.iface_bindings);
             iface_tydefs = (uu___1165_71952.iface_tydefs);
             iface_type_names = (uu___1165_71952.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____71970  ->
                fun se  ->
                  match uu____71970 with
                  | (g1,iface2) ->
                      let uu____71982 = extract_sigelt_iface g1 se  in
                      (match uu____71982 with
                       | (g2,iface') ->
                           let uu____71993 = iface_union iface2 iface'  in
                           (g2, uu____71993))) (g, iface1) decls
            in
         (let uu____71995 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____71995);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____72012 = FStar_Options.debug_any ()  in
      if uu____72012
      then
        let uu____72019 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____72019
          (fun uu____72027  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1183_72041 = g  in
      let uu____72042 =
        let uu____72045 =
          FStar_List.map (fun _72052  -> FStar_Extraction_ML_UEnv.Fv _72052)
            iface1.iface_bindings
           in
        FStar_List.append uu____72045 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1183_72041.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____72042;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1183_72041.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____72130 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____72130
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____72138 =
            let uu____72139 =
              let uu____72142 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____72142  in
            uu____72139.FStar_Syntax_Syntax.n  in
          match uu____72138 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____72147) ->
              FStar_List.map
                (fun uu____72180  ->
                   match uu____72180 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____72189;
                        FStar_Syntax_Syntax.sort = uu____72190;_},uu____72191)
                       -> ppname.FStar_Ident.idText) bs
          | uu____72199 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____72207 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____72207 with
        | (env2,uu____72234,uu____72235) ->
            let uu____72238 =
              let uu____72251 = lident_as_mlsymbol ctor.dname  in
              let uu____72253 =
                let uu____72261 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____72261  in
              (uu____72251, uu____72253)  in
            (env2, uu____72238)
         in
      let extract_one_family env1 ind =
        let uu____72322 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____72322 with
        | (env_iparams,vars) ->
            let uu____72366 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____72366 with
             | (env2,ctors) ->
                 let uu____72473 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____72473 with
                  | (indices,uu____72515) ->
                      let ml_params =
                        let uu____72540 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____72566  ->
                                    let uu____72574 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____72574))
                           in
                        FStar_List.append vars uu____72540  in
                      let tbody =
                        let uu____72579 =
                          FStar_Util.find_opt
                            (fun uu___619_72584  ->
                               match uu___619_72584 with
                               | FStar_Syntax_Syntax.RecordType uu____72586
                                   -> true
                               | uu____72596 -> false) ind.iquals
                           in
                        match uu____72579 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____72608 = FStar_List.hd ctors  in
                            (match uu____72608 with
                             | (uu____72633,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____72677  ->
                                          match uu____72677 with
                                          | (uu____72688,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____72693 =
                                                lident_as_mlsymbol lid  in
                                              (uu____72693, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____72696 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____72699 =
                        let uu____72722 = lident_as_mlsymbol ind.iname  in
                        (false, uu____72722, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____72699)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____72767,t,uu____72769,uu____72770,uu____72771);
            FStar_Syntax_Syntax.sigrng = uu____72772;
            FStar_Syntax_Syntax.sigquals = uu____72773;
            FStar_Syntax_Syntax.sigmeta = uu____72774;
            FStar_Syntax_Syntax.sigattrs = uu____72775;_}::[],uu____72776),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____72795 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____72795 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____72848),quals) ->
          let uu____72862 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____72862 with
           | (env1,ifams) ->
               let uu____72881 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____72881 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____72990 -> failwith "Unexpected signature element"
  
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
             let uu____73048 = FStar_Syntax_Util.head_and_args t  in
             match uu____73048 with
             | (head1,args) ->
                 let uu____73096 =
                   let uu____73098 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____73098  in
                 if uu____73096
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____73117));
                         FStar_Syntax_Syntax.pos = uu____73118;
                         FStar_Syntax_Syntax.vars = uu____73119;_},uu____73120)::[]
                        ->
                        let uu____73159 =
                          let uu____73163 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____73163  in
                        FStar_Pervasives_Native.Some uu____73159
                    | uu____73169 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____73184 =
        let uu____73186 = FStar_Options.codegen ()  in
        uu____73186 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____73184
      then []
      else
        (let uu____73196 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____73196 with
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
                      let uu____73238 =
                        let uu____73239 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____73239  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____73238  in
                    let uu____73241 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____73241 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____73274 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____73274 with
                         | (register,args) ->
                             let h =
                               let uu____73311 =
                                 let uu____73312 =
                                   let uu____73313 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____73313
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____73312
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____73311
                                in
                             let arity1 =
                               let uu____73315 =
                                 let uu____73316 =
                                   let uu____73328 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____73328,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____73316
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____73315
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
              | uu____73357 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____73385 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____73385);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____73394 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____73403 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____73420 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____73437 = extract_reifiable_effect g ed  in
           (match uu____73437 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____73461 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____73475 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____73481 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____73481 with | (env,uu____73497,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____73506) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____73515 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____73515 with | (env,uu____73531,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____73540) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____73551 =
             let uu____73560 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____73560 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____73589) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____73551 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1402_73675 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1402_73675.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1402_73675.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1402_73675.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1402_73675.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1402_73675.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1402_73675.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____73684 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____73684)  in
                let uu____73702 =
                  let uu____73709 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____73709  in
                (match uu____73702 with
                 | (ml_let,uu____73726,uu____73727) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____73736) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____73753 =
                            FStar_List.fold_left2
                              (fun uu____73779  ->
                                 fun ml_lb  ->
                                   fun uu____73781  ->
                                     match (uu____73779, uu____73781) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____73803;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____73805;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____73806;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____73807;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____73808;_})
                                         ->
                                         let uu____73833 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____73833
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____73850 =
                                                let uu____73853 =
                                                  FStar_Util.right lbname  in
                                                uu____73853.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____73850.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____73857 =
                                                let uu____73858 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____73858.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____73857 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____73863,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____73864;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____73866;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____73867;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____73868;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____73869;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____73870;_})
                                                  when
                                                  let uu____73905 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____73905 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____73909 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1450_73914 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1450_73914.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1450_73914.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1450_73914.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1450_73914.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1450_73914.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____73915 =
                                              let uu____73920 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_73927  ->
                                                        match uu___620_73927
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____73929 ->
                                                            true
                                                        | uu____73935 ->
                                                            false))
                                                 in
                                              if uu____73920
                                              then
                                                let mname =
                                                  let uu____73951 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____73951
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____73960 =
                                                  let uu____73968 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____73969 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____73968 mname
                                                    uu____73969
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____73960 with
                                                | (env1,uu____73976,uu____73977)
                                                    ->
                                                    (env1,
                                                      (let uu___1463_73981 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1463_73981.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1463_73981.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1463_73981.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1463_73981.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1463_73981.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____73988 =
                                                   let uu____73996 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____73996
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____73988 with
                                                 | (env1,uu____74003,uu____74004)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____73915 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____73753 with
                           | (g1,ml_lbs') ->
                               let uu____74034 =
                                 let uu____74037 =
                                   let uu____74040 =
                                     let uu____74041 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____74041
                                      in
                                   [uu____74040;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____74044 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____74037 uu____74044
                                  in
                               (g1, uu____74034))
                      | uu____74049 ->
                          let uu____74050 =
                            let uu____74052 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____74052
                             in
                          failwith uu____74050)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____74062,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____74067 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____74073 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____74073)
              in
           if uu____74067
           then
             let always_fail1 =
               let uu___1483_74083 = se  in
               let uu____74084 =
                 let uu____74085 =
                   let uu____74092 =
                     let uu____74093 =
                       let uu____74096 = always_fail lid t  in [uu____74096]
                        in
                     (false, uu____74093)  in
                   (uu____74092, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____74085  in
               {
                 FStar_Syntax_Syntax.sigel = uu____74084;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1483_74083.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1483_74083.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1483_74083.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1483_74083.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____74103 = extract_sig g always_fail1  in
             (match uu____74103 with
              | (g1,mlm) ->
                  let uu____74122 =
                    FStar_Util.find_map quals
                      (fun uu___621_74127  ->
                         match uu___621_74127 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____74131 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____74122 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____74139 =
                         let uu____74142 =
                           let uu____74143 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____74143  in
                         let uu____74144 =
                           let uu____74147 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____74147]  in
                         uu____74142 :: uu____74144  in
                       (g1, uu____74139)
                   | uu____74150 ->
                       let uu____74153 =
                         FStar_Util.find_map quals
                           (fun uu___622_74159  ->
                              match uu___622_74159 with
                              | FStar_Syntax_Syntax.Projector (l,uu____74163)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____74164 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____74153 with
                        | FStar_Pervasives_Native.Some uu____74171 ->
                            (g1, [])
                        | uu____74174 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____74184 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____74184 with
            | (ml_main,uu____74198,uu____74199) ->
                let uu____74200 =
                  let uu____74203 =
                    let uu____74204 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____74204  in
                  [uu____74203; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____74200))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74207 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____74215 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____74224 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74227 -> (g, [])
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
      let uu____74269 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1526_74273 = g  in
        let uu____74274 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____74274;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1526_74273.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1526_74273.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1526_74273.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____74275 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____74294 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____74294
               then
                 let nm =
                   let uu____74305 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____74305
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____74322 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____74322
                     (fun uu____74332  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____74275 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____74354 = FStar_Options.codegen ()  in
            uu____74354 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____74369 =
                let uu____74371 = FStar_Options.silent ()  in
                Prims.op_Negation uu____74371  in
              if uu____74369
              then
                let uu____74374 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____74374
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
      (let uu____74449 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____74449);
      (let uu____74452 =
         let uu____74454 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____74454  in
       if uu____74452
       then
         let uu____74457 =
           let uu____74459 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____74459
            in
         failwith uu____74457
       else ());
      (let uu____74464 = FStar_Options.interactive ()  in
       if uu____74464
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____74484 = FStar_Options.debug_any ()  in
            if uu____74484
            then
              let msg =
                let uu____74495 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____74495  in
              FStar_Util.measure_execution_time msg
                (fun uu____74505  -> extract' g m)
            else extract' g m  in
          (let uu____74509 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____74509);
          res))
  
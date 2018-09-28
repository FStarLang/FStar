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
  fun uu___403_289  ->
    match uu___403_289 with
    | a::b::[] -> (a, b)
    | uu____294 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___404_307  ->
    match uu___404_307 with
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
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv,'Auu____429) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv,Prims.string Prims.list)
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
    let uu___414_1216 = empty_iface  in
    {
      iface_module_name = (uu___414_1216.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___414_1216.iface_tydefs);
      iface_type_names = (uu___414_1216.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___415_1226 = empty_iface  in
    let uu____1227 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___415_1226.iface_module_name);
      iface_bindings = (uu___415_1226.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1227
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___416_1241 = empty_iface  in
    {
      iface_module_name = (uu___416_1241.iface_module_name);
      iface_bindings = (uu___416_1241.iface_bindings);
      iface_tydefs = (uu___416_1241.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1252 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1252;
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
  'Auu____1282 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1282,FStar_Extraction_ML_Syntax.mlty)
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
      let uu____1311 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1312 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1313 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1311 uu____1312
        uu____1313
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_UEnv.exp_binding)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun cm  ->
    fun uu____1327  ->
      match uu____1327 with
      | (fv,exp_binding) ->
          let uu____1334 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1335 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1334 uu____1335
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1346 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1347 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1346 uu____1347
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1360 =
      let uu____1361 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1361 (FStar_String.concat "\n")  in
    let uu____1370 =
      let uu____1371 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1371 (FStar_String.concat "\n")  in
    let uu____1376 =
      let uu____1377 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1377 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1360 uu____1370
      uu____1376
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___405_1402  ->
           match uu___405_1402 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1419 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____1424 =
      let uu____1425 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1425 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1424
  
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
          let uu____1478 =
            let uu____1487 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1487 with
            | (tcenv,uu____1505,def_typ) ->
                let uu____1511 = as_pair def_typ  in (tcenv, uu____1511)
             in
          match uu____1478 with
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
                let uu____1542 =
                  let uu____1543 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1543 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1542 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1551 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1570 -> def  in
              let uu____1571 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1582) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1607 -> ([], def1)  in
              (match uu____1571 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___406_1626  ->
                          match uu___406_1626 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1627 -> false) quals
                      in
                   let uu____1628 = binders_as_mlty_binders env bs  in
                   (match uu____1628 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1652 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1652
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1656 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___407_1661  ->
                                    match uu___407_1661 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1662 -> true
                                    | uu____1667 -> false))
                             in
                          if uu____1656
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1675 = extract_metadata attrs  in
                          let uu____1678 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1675 uu____1678  in
                        let td =
                          let uu____1698 = lident_as_mlsymbol lid  in
                          (assumed, uu____1698, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1706 =
                            let uu____1707 =
                              let uu____1708 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1708
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1707  in
                          [uu____1706;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1709 =
                          let uu____1714 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___408_1718  ->
                                    match uu___408_1718 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1719 -> false))
                             in
                          if uu____1714
                          then
                            let uu____1724 =
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                fv
                               in
                            (uu____1724, (iface_of_type_names [fv]))
                          else
                            (let uu____1726 =
                               FStar_Extraction_ML_UEnv.extend_tydef env1 fv
                                 td
                                in
                             match uu____1726 with
                             | (env2,tydef) ->
                                 let uu____1737 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1737))
                           in
                        (match uu____1709 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,iface) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1805 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1805
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1812 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____1812 with | (env2,uu____1828,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____1865 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1865 with
        | (env2,vars) ->
            let uu____1890 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1890 with | (env3,ctors) -> (env3, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1954,t,uu____1956,uu____1957,uu____1958);
            FStar_Syntax_Syntax.sigrng = uu____1959;
            FStar_Syntax_Syntax.sigquals = uu____1960;
            FStar_Syntax_Syntax.sigmeta = uu____1961;
            FStar_Syntax_Syntax.sigattrs = uu____1962;_}::[],uu____1963),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1980 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1980 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2012),quals) ->
          let uu____2026 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____2026 with
           | (env1,ifams) ->
               let uu____2043 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____2043 with
                | (env2,td) ->
                    let uu____2084 =
                      let uu____2085 =
                        let uu____2086 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____2086  in
                      iface_union uu____2085
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____2084)))
      | uu____2095 -> failwith "Unexpected signature element"
  
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
              let uu____2168 =
                let uu____2169 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___409_2173  ->
                          match uu___409_2173 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2174 -> false))
                   in
                Prims.op_Negation uu____2169  in
              if uu____2168
              then (g, empty_iface, [])
              else
                (let uu____2186 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2186 with
                 | (bs,uu____2210) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2233 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2233;
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
        let uu____2295 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2295 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2312 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2312
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
        (let uu____2336 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2336
         then
           let uu____2337 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2337
         else ());
        (let uu____2339 =
           let uu____2340 = FStar_Syntax_Subst.compress tm  in
           uu____2340.FStar_Syntax_Syntax.n  in
         match uu____2339 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2348) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2355 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2355 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2360;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2361;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2363;_} ->
                  let uu____2364 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2364, tysc))
         | uu____2365 -> failwith "Not an fv")
         in
      let extract_action g1 a =
        (let uu____2391 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2391
         then
           let uu____2392 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2393 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2392
             uu____2393
         else ());
        (let uu____2395 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2395 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2415 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2415  in
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
             let uu____2439 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2439 with
              | (a_let,uu____2455,ty) ->
                  ((let uu____2458 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2458
                    then
                      let uu____2459 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2459
                    else ());
                   (let uu____2461 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2482,mllb::[]),uu____2484) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____2520 -> failwith "Impossible"  in
                    match uu____2461 with
                    | (exp,tysc) ->
                        ((let uu____2554 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____2554
                          then
                            ((let uu____2556 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____2556);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____2564 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____2564 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____2586 =
        let uu____2593 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____2593 with
        | (return_tm,ty_sc) ->
            let uu____2610 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____2610 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____2586 with
      | (g1,return_iface,return_decl) ->
          let uu____2634 =
            let uu____2641 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____2641 with
            | (bind_tm,ty_sc) ->
                let uu____2658 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____2658 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____2634 with
           | (g2,bind_iface,bind_decl) ->
               let uu____2682 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____2682 with
                | (g3,actions) ->
                    let uu____2719 = FStar_List.unzip actions  in
                    (match uu____2719 with
                     | (actions_iface,actions1) ->
                         let uu____2746 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____2746, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Extraction_ML_UEnv.uenv,iface) FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____2767 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____2776 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____2793 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____2811 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____2811 with | (env,iface1,uu____2826) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2832) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____2839 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____2839 with | (env,iface1,uu____2854) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____2865 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____2869 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____2869)
             in
          if uu____2865
          then
            let uu____2874 =
              let uu____2885 =
                let uu____2886 =
                  let uu____2889 = always_fail lid t  in [uu____2889]  in
                (false, uu____2886)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____2885  in
            (match uu____2874 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____2912) ->
          let uu____2917 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____2917 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____2946 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2947 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____2948 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____2955 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2956 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____2971 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____2983 =
            FStar_TypeChecker_Env.is_reifiable_effect
              g.FStar_Extraction_ML_UEnv.env_tcenv
              ed.FStar_Syntax_Syntax.mname
             in
          if uu____2983
          then
            let uu____2988 = extract_reifiable_effect g ed  in
            (match uu____2988 with | (env,iface1,uu____3003) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv,iface) FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun modul  ->
      let uu____3023 = FStar_Options.interactive ()  in
      if uu____3023
      then (g, empty_iface)
      else
        (let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___417_3031 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___417_3031.iface_bindings);
             iface_tydefs = (uu___417_3031.iface_tydefs);
             iface_type_names = (uu___417_3031.iface_type_names)
           }  in
         FStar_List.fold_left
           (fun uu____3044  ->
              fun se  ->
                match uu____3044 with
                | (g1,iface2) ->
                    let uu____3056 = extract_sigelt_iface g1 se  in
                    (match uu____3056 with
                     | (g2,iface') ->
                         let uu____3067 = iface_union iface2 iface'  in
                         (g2, uu____3067))) (g, iface1) decls)
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___418_3078 = g  in
      let uu____3079 =
        let uu____3082 =
          FStar_List.map (fun _0_1  -> FStar_Extraction_ML_UEnv.Fv _0_1)
            iface1.iface_bindings
           in
        FStar_List.append uu____3082 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___418_3078.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____3079;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___418_3078.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____3154 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____3154
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____3161 =
            let uu____3162 =
              let uu____3165 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____3165  in
            uu____3162.FStar_Syntax_Syntax.n  in
          match uu____3161 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3169) ->
              FStar_List.map
                (fun uu____3201  ->
                   match uu____3201 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____3209;
                        FStar_Syntax_Syntax.sort = uu____3210;_},uu____3211)
                       -> ppname.FStar_Ident.idText) bs
          | uu____3218 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____3225 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____3225 with
        | (env2,uu____3247,uu____3248) ->
            let uu____3249 =
              let uu____3260 = lident_as_mlsymbol ctor.dname  in
              let uu____3261 =
                let uu____3268 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____3268  in
              (uu____3260, uu____3261)  in
            (env2, uu____3249)
         in
      let extract_one_family env1 ind =
        let uu____3320 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____3320 with
        | (env2,vars) ->
            let uu____3357 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____3357 with
             | (env3,ctors) ->
                 let uu____3450 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____3450 with
                  | (indices,uu____3488) ->
                      let ml_params =
                        let uu____3512 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____3535  ->
                                    let uu____3542 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____3542))
                           in
                        FStar_List.append vars uu____3512  in
                      let tbody =
                        let uu____3544 =
                          FStar_Util.find_opt
                            (fun uu___410_3549  ->
                               match uu___410_3549 with
                               | FStar_Syntax_Syntax.RecordType uu____3550 ->
                                   true
                               | uu____3559 -> false) ind.iquals
                           in
                        match uu____3544 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____3570 = FStar_List.hd ctors  in
                            (match uu____3570 with
                             | (uu____3591,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____3628  ->
                                          match uu____3628 with
                                          | (uu____3637,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____3640 =
                                                lident_as_mlsymbol lid  in
                                              (uu____3640, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____3641 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____3644 =
                        let uu____3663 = lident_as_mlsymbol ind.iname  in
                        (false, uu____3663, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____3644)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____3697,t,uu____3699,uu____3700,uu____3701);
            FStar_Syntax_Syntax.sigrng = uu____3702;
            FStar_Syntax_Syntax.sigquals = uu____3703;
            FStar_Syntax_Syntax.sigmeta = uu____3704;
            FStar_Syntax_Syntax.sigattrs = uu____3705;_}::[],uu____3706),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____3723 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____3723 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____3769),quals) ->
          let uu____3783 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____3783 with
           | (env1,ifams) ->
               let uu____3802 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____3802 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____3895 -> failwith "Unexpected signature element"
  
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
             let uu____3949 = FStar_Syntax_Util.head_and_args t  in
             match uu____3949 with
             | (head1,args) ->
                 let uu____3996 =
                   let uu____3997 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____3997  in
                 if uu____3996
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____4010));
                         FStar_Syntax_Syntax.pos = uu____4011;
                         FStar_Syntax_Syntax.vars = uu____4012;_},uu____4013)::[]
                        ->
                        let uu____4050 =
                          let uu____4053 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____4053  in
                        FStar_Pervasives_Native.Some uu____4050
                    | uu____4056 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____4069 =
        let uu____4070 = FStar_Options.codegen ()  in
        uu____4070 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____4069
      then []
      else
        (let uu____4078 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____4078 with
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
                      let uu____4116 =
                        let uu____4117 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____4117  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____4116  in
                    let uu____4118 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____4118 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____4143 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____4143 with
                         | (register,args) ->
                             let h =
                               let uu____4170 =
                                 let uu____4171 =
                                   let uu____4172 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____4172
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____4171
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____4170
                                in
                             let arity1 =
                               let uu____4174 =
                                 let uu____4175 =
                                   let uu____4186 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____4186, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____4175
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____4174
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
              | uu____4210 -> []))
  
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
           let uu____4237 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____4237);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____4244 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4253 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____4270 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____4286 = extract_reifiable_effect g ed  in
           (match uu____4286 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____4310 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____4323 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____4329 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____4329 with | (env,uu____4345,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4354) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____4361 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____4361 with | (env,uu____4377,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____4386) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____4397 =
             let uu____4406 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____4406 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____4435) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____4397 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___419_4519 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___419_4519.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___419_4519.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___419_4519.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___419_4519.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___419_4519.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___419_4519.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____4527 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____4527)  in
                let uu____4541 =
                  let uu____4548 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____4548  in
                (match uu____4541 with
                 | (ml_let,uu____4564,uu____4565) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____4574) ->
                          let flags1 = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____4591 =
                            FStar_List.fold_left2
                              (fun uu____4617  ->
                                 fun ml_lb  ->
                                   fun uu____4619  ->
                                     match (uu____4617, uu____4619) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____4641;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____4643;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____4644;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____4645;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____4646;_})
                                         ->
                                         let uu____4671 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____4671
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____4684 =
                                                let uu____4687 =
                                                  FStar_Util.right lbname  in
                                                uu____4687.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____4684.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____4691 =
                                                let uu____4692 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____4692.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____4691 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____4697,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____4698;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____4700;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____4701;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____4702;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____4703;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____4704;_})
                                                  when
                                                  let uu____4739 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____4739 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____4740 -> []  in
                                            let meta =
                                              FStar_List.append flags1
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___420_4745 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___420_4745.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___420_4745.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___420_4745.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___420_4745.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___420_4745.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____4746 =
                                              let uu____4751 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___411_4756  ->
                                                        match uu___411_4756
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____4757 ->
                                                            true
                                                        | uu____4762 -> false))
                                                 in
                                              if uu____4751
                                              then
                                                let mname =
                                                  let uu____4774 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____4774
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____4781 =
                                                  let uu____4788 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____4789 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____4788 mname
                                                    uu____4789
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____4781 with
                                                | (env1,uu____4795,uu____4796)
                                                    ->
                                                    (env1,
                                                      (let uu___421_4798 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___421_4798.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___421_4798.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___421_4798.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___421_4798.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___421_4798.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____4802 =
                                                   let uu____4809 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____4809
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____4802 with
                                                 | (env1,uu____4815,uu____4816)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____4746 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____4591 with
                           | (g1,ml_lbs') ->
                               let uu____4843 =
                                 let uu____4846 =
                                   let uu____4849 =
                                     let uu____4850 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____4850
                                      in
                                   [uu____4849;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____4853 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____4846 uu____4853  in
                               (g1, uu____4843))
                      | uu____4858 ->
                          let uu____4859 =
                            let uu____4860 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____4860
                             in
                          failwith uu____4859)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____4868,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____4873 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____4877 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____4877)
              in
           if uu____4873
           then
             let always_fail1 =
               let uu___422_4885 = se  in
               let uu____4886 =
                 let uu____4887 =
                   let uu____4894 =
                     let uu____4895 =
                       let uu____4898 = always_fail lid t  in [uu____4898]
                        in
                     (false, uu____4895)  in
                   (uu____4894, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____4887  in
               {
                 FStar_Syntax_Syntax.sigel = uu____4886;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___422_4885.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___422_4885.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___422_4885.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___422_4885.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____4903 = extract_sig g always_fail1  in
             (match uu____4903 with
              | (g1,mlm) ->
                  let uu____4922 =
                    FStar_Util.find_map quals
                      (fun uu___412_4927  ->
                         match uu___412_4927 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____4931 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____4922 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____4939 =
                         let uu____4942 =
                           let uu____4943 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____4943  in
                         let uu____4944 =
                           let uu____4947 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____4947]  in
                         uu____4942 :: uu____4944  in
                       (g1, uu____4939)
                   | uu____4950 ->
                       let uu____4953 =
                         FStar_Util.find_map quals
                           (fun uu___413_4959  ->
                              match uu___413_4959 with
                              | FStar_Syntax_Syntax.Projector (l,uu____4963)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____4964 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4953 with
                        | FStar_Pervasives_Native.Some uu____4971 -> (g1, [])
                        | uu____4974 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____4983 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____4983 with
            | (ml_main,uu____4997,uu____4998) ->
                let uu____4999 =
                  let uu____5002 =
                    let uu____5003 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____5003  in
                  [uu____5002; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____4999))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5006 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____5013 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____5022 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5025 -> (g, [])
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
      (let uu____5067 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___423_5070 = g  in
         let uu____5071 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.env_tcenv = uu____5071;
           FStar_Extraction_ML_UEnv.env_bindings =
             (uu___423_5070.FStar_Extraction_ML_UEnv.env_bindings);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___423_5070.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___423_5070.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____5072 =
         let uu____5073 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____5073  in
       if uu____5072
       then
         let uu____5080 = extract_iface g1 m  in
         match uu____5080 with
         | (g2,iface1) ->
             (FStar_Extraction_ML_UEnv.debug g2
                (fun uu____5096  ->
                   let uu____5097 = iface_to_string iface1  in
                   FStar_Util.print_string uu____5097);
              (g2, []))
       else
         (let uu____5101 =
            FStar_Util.fold_map extract_sig g1
              m.FStar_Syntax_Syntax.declarations
             in
          match uu____5101 with
          | (g2,sigs) ->
              (FStar_Extraction_ML_UEnv.debug g2
                 (fun uu____5131  ->
                    let uu____5132 = gamma_to_string g2  in
                    FStar_Util.print_string uu____5132);
               (let mlm = FStar_List.flatten sigs  in
                let is_kremlin =
                  let uu____5135 = FStar_Options.codegen ()  in
                  uu____5135 =
                    (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                   in
                if
                  ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims")
                    &&
                    (is_kremlin ||
                       (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
                then
                  ((let uu____5147 =
                      FStar_Syntax_Print.lid_to_string
                        m.FStar_Syntax_Syntax.name
                       in
                    FStar_Util.print1 "Extracted module %s\n" uu____5147);
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
      let uu____5215 = FStar_Options.interactive ()  in
      if uu____5215
      then (g, [])
      else
        (let uu____5225 = FStar_Options.debug_any ()  in
         if uu____5225
         then
           let msg =
             let uu____5233 =
               FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                in
             FStar_Util.format1 "Extracting module %s\n" uu____5233  in
           FStar_Util.measure_execution_time msg
             (fun uu____5241  -> extract' g m)
         else extract' g m)
  
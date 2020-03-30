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
        (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlident
          Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____491  ->
             match uu____491 with
             | (bv,uu____502) ->
                 let env2 = FStar_Extraction_ML_UEnv.extend_ty env1 bv false
                    in
                 let name =
                   let uu____507 = FStar_Extraction_ML_UEnv.lookup_bv env2 bv
                      in
                   match uu____507 with
                   | FStar_Util.Inl ty ->
                       ty.FStar_Extraction_ML_UEnv.ty_b_name
                   | uu____510 -> failwith "Impossible"  in
                 (env2, name)) env bs
  
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
    let uu____712 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____714 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____717 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____719 =
      let uu____721 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____735 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____737 =
                  let uu____739 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____739  in
                Prims.op_Hat uu____735 uu____737))
         in
      FStar_All.pipe_right uu____721 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____712 uu____714 uu____717
      uu____719
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        let uu____784 =
          FStar_Util.fold_map
            (fun env1  ->
               fun se  ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l,us,bs,t,_mut_i,datas) ->
                     let uu____835 = FStar_Syntax_Subst.open_univ_vars us t
                        in
                     (match uu____835 with
                      | (_us,t1) ->
                          let uu____848 = FStar_Syntax_Subst.open_term bs t1
                             in
                          (match uu____848 with
                           | (bs1,t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1  ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d,us1,t3,l',nparams,uu____894)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____901 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3
                                                in
                                             (match uu____901 with
                                              | (_us1,t4) ->
                                                  let uu____910 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4
                                                     in
                                                  (match uu____910 with
                                                   | (bs',body) ->
                                                       let uu____925 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs'
                                                          in
                                                       (match uu____925 with
                                                        | (bs_params,rest) ->
                                                            let subst1 =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____1016
                                                                    ->
                                                                   fun
                                                                    uu____1017
                                                                     ->
                                                                    match 
                                                                    (uu____1016,
                                                                    uu____1017)
                                                                    with
                                                                    | 
                                                                    ((b',uu____1043),
                                                                    (b,uu____1045))
                                                                    ->
                                                                    let uu____1066
                                                                    =
                                                                    let uu____1073
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                    (b',
                                                                    uu____1073)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____1066)
                                                                bs_params bs1
                                                               in
                                                            let t5 =
                                                              let uu____1079
                                                                =
                                                                let uu____1080
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____1080
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____1079
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1)
                                                               in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____1083 -> []))
                                  in
                               let metadata =
                                 let uu____1087 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs
                                    in
                                 let uu____1090 =
                                   FStar_List.choose flag_of_qual quals  in
                                 FStar_List.append uu____1087 uu____1090  in
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
                 | uu____1097 -> (env1, [])) env ses
           in
        match uu____784 with
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
    let uu___221_1277 = empty_iface  in
    {
      iface_module_name = (uu___221_1277.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___221_1277.iface_tydefs);
      iface_type_names = (uu___221_1277.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___224_1288 = empty_iface  in
    let uu____1289 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___224_1288.iface_module_name);
      iface_bindings = (uu___224_1288.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1289
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___228_1304 = empty_iface  in
    {
      iface_module_name = (uu___228_1304.iface_module_name);
      iface_bindings = (uu___228_1304.iface_bindings);
      iface_tydefs = (uu___228_1304.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1316 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1316;
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
  'Auu____1361 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1361 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____1393 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1395 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1397 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1393 uu____1395
        uu____1397
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1415  ->
      match uu____1415 with
      | (fv,exp_binding) ->
          let uu____1423 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1425 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1423 uu____1425
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1440 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1442 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1440 uu____1442
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1460 =
      let uu____1462 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1462 (FStar_String.concat "\n")  in
    let uu____1476 =
      let uu____1478 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1478 (FStar_String.concat "\n")  in
    let uu____1488 =
      let uu____1490 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1490 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1460 uu____1476
      uu____1488
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
    let gamma =
      let uu____1516 = FStar_Extraction_ML_UEnv.bindings_of_uenv env  in
      FStar_List.collect
        (fun uu___2_1526  ->
           match uu___2_1526 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1543 -> []) uu____1516
       in
    let uu____1548 =
      let uu____1550 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1550 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1548
  
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
          let uu____1610 =
            let uu____1619 =
              let uu____1628 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
              FStar_TypeChecker_Env.open_universes_in uu____1628
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1619 with
            | (tcenv,uu____1638,def_typ) ->
                let uu____1644 = as_pair def_typ  in (tcenv, uu____1644)
             in
          match uu____1610 with
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
                let uu____1675 =
                  let uu____1676 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1676 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1675 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1684 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1703 -> def  in
              let uu____1704 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1715) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1740 -> ([], def1)  in
              (match uu____1704 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1760  ->
                          match uu___3_1760 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1763 -> false) quals
                      in
                   let uu____1765 = binders_as_mlty_binders env bs  in
                   (match uu____1765 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1792 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1792
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1797 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1804  ->
                                    match uu___4_1804 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1806 -> true
                                    | uu____1812 -> false))
                             in
                          if uu____1797
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1826 = extract_metadata attrs  in
                          let uu____1829 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1826 uu____1829  in
                        let td =
                          let uu____1852 = lident_as_mlsymbol lid  in
                          (assumed, uu____1852, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1864 =
                            let uu____1865 =
                              let uu____1866 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1866
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1865  in
                          [uu____1864;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1867 =
                          let uu____1872 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_1878  ->
                                    match uu___5_1878 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1882 -> false))
                             in
                          if uu____1872
                          then
                            let uu____1889 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____1889, (iface_of_type_names [fv]))
                          else
                            (let uu____1892 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____1892 with
                             | (env2,tydef) ->
                                 let uu____1903 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1903))
                           in
                        (match uu____1867 with
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
            let uu____1962 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] uu____1962
              lb.FStar_Syntax_Syntax.lbtyp
             in
          let uu____1963 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____1963 with
          | (bs,uu____1979) ->
              let uu____1984 = binders_as_mlty_binders env bs  in
              (match uu____1984 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____2016 = extract_metadata attrs  in
                     let uu____2019 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____2016 uu____2019  in
                   let assumed = false  in
                   let td =
                     let uu____2045 = lident_as_mlsymbol lid  in
                     (assumed, uu____2045, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____2058 =
                       let uu____2059 =
                         let uu____2060 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____2060
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____2059  in
                     [uu____2058; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____2061 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____2061 with
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
          let uu____2142 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2142
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2149 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2149 with | (env2,uu____2168,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2207 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2207 with
        | (env_iparams,vars) ->
            let uu____2235 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2235 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2299,t,uu____2301,uu____2302,uu____2303);
            FStar_Syntax_Syntax.sigrng = uu____2304;
            FStar_Syntax_Syntax.sigquals = uu____2305;
            FStar_Syntax_Syntax.sigmeta = uu____2306;
            FStar_Syntax_Syntax.sigattrs = uu____2307;
            FStar_Syntax_Syntax.sigopts = uu____2308;_}::[],uu____2309),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2330 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2330 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2363),quals) ->
          let uu____2377 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____2377
          then (env, empty_iface)
          else
            (let uu____2386 = bundle_as_inductive_families env ses quals  in
             match uu____2386 with
             | (env1,ifams) ->
                 let uu____2403 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____2403 with
                  | (env2,td) ->
                      let uu____2444 =
                        let uu____2445 =
                          let uu____2446 =
                            FStar_List.map (fun x  -> x.ifv) ifams  in
                          iface_of_type_names uu____2446  in
                        iface_union uu____2445
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____2444)))
      | uu____2455 -> failwith "Unexpected signature element"
  
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
              let uu____2530 =
                let uu____2532 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2538  ->
                          match uu___6_2538 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2541 -> false))
                   in
                Prims.op_Negation uu____2532  in
              if uu____2530
              then (g, empty_iface, [])
              else
                (let uu____2556 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2556 with
                 | (bs,uu____2572) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2579 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2579;
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
        let uu____2642 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2642 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2664 =
                let uu____2666 =
                  let uu____2672 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g2
                     in
                  FStar_TypeChecker_Env.debug uu____2672  in
                FStar_All.pipe_left uu____2666
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2664
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
        (let uu____2707 =
           let uu____2709 =
             let uu____2715 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.debug uu____2715  in
           FStar_All.pipe_left uu____2709
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2707
         then
           let uu____2719 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2719
         else ());
        (let uu____2724 =
           let uu____2725 = FStar_Syntax_Subst.compress tm  in
           uu____2725.FStar_Syntax_Syntax.n  in
         match uu____2724 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2733) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2740 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2740 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2745;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2746;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2748;_} ->
                  let uu____2751 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2751, tysc))
         | uu____2752 ->
             let uu____2753 =
               let uu____2755 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2757 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2755 uu____2757
                in
             failwith uu____2753)
         in
      let extract_action g1 a =
        (let uu____2785 =
           let uu____2787 =
             let uu____2793 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
             FStar_TypeChecker_Env.debug uu____2793  in
           FStar_All.pipe_left uu____2787
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2785
         then
           let uu____2797 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2799 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2797
             uu____2799
         else ());
        (let uu____2804 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2804 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2824 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2824  in
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
             let uu____2854 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2854 with
              | (a_let,uu____2870,ty) ->
                  ((let uu____2873 =
                      let uu____2875 =
                        let uu____2881 =
                          FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
                        FStar_TypeChecker_Env.debug uu____2881  in
                      FStar_All.pipe_left uu____2875
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2873
                    then
                      let uu____2885 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2885
                    else ());
                   (let uu____2890 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2913,mllb::[]),uu____2915) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____2955 -> failwith "Impossible"  in
                    match uu____2890 with
                    | (exp,tysc) ->
                        ((let uu____2993 =
                            let uu____2995 =
                              let uu____3001 =
                                FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
                              FStar_TypeChecker_Env.debug uu____3001  in
                            FStar_All.pipe_left uu____2995
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____2993
                          then
                            ((let uu____3006 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____3006);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____3022 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____3022 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____3044 =
        let uu____3051 =
          let uu____3056 =
            let uu____3059 =
              let uu____3068 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr  in
              FStar_All.pipe_right uu____3068 FStar_Util.must  in
            FStar_All.pipe_right uu____3059 FStar_Pervasives_Native.snd  in
          extract_fv uu____3056  in
        match uu____3051 with
        | (return_tm,ty_sc) ->
            let uu____3137 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____3137 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____3044 with
      | (g1,return_iface,return_decl) ->
          let uu____3162 =
            let uu____3169 =
              let uu____3174 =
                let uu____3177 =
                  let uu____3186 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr
                     in
                  FStar_All.pipe_right uu____3186 FStar_Util.must  in
                FStar_All.pipe_right uu____3177 FStar_Pervasives_Native.snd
                 in
              extract_fv uu____3174  in
            match uu____3169 with
            | (bind_tm,ty_sc) ->
                let uu____3255 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____3255 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____3162 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3280 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3280 with
                | (g3,actions) ->
                    let uu____3317 = FStar_List.unzip actions  in
                    (match uu____3317 with
                     | (actions_iface,actions1) ->
                         let uu____3344 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3344, (return_decl :: bind_decl ::
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
        let uu____3375 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____3380 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____3380) lbs
           in
        if uu____3375
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3403 =
             FStar_List.fold_left
               (fun uu____3438  ->
                  fun lb  ->
                    match uu____3438 with
                    | (env1,iface_opt,impls) ->
                        let uu____3479 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____3479 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3513 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____3513
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____3403 with
           | (env1,iface_opt,impls) ->
               let uu____3553 = FStar_Option.get iface_opt  in
               let uu____3554 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____3553, uu____3554))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3586 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3595 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3612 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3631 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3631 with | (env,iface1,uu____3646) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3652) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3661 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3661 with | (env,iface1,uu____3676) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____3682) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3695 = extract_let_rec_types se g lbs  in
          (match uu____3695 with | (env,iface1,uu____3710) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3721 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3727 =
                 let uu____3729 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                    in
                 FStar_TypeChecker_Util.must_erase_for_extraction uu____3729
                   t
                  in
               Prims.op_Negation uu____3727)
             in
          if uu____3721
          then
            let uu____3735 =
              let uu____3746 =
                let uu____3747 =
                  let uu____3750 = always_fail lid t  in [uu____3750]  in
                (false, uu____3747)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3746  in
            (match uu____3735 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3776) ->
          let uu____3781 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3781 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3810 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3811 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3818 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3819 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3832 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3845 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_fail uu____3857 ->
          failwith "impossible: trying to extract Sig_fail"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3876 =
            (let uu____3880 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.is_reifiable_effect uu____3880
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____3876
          then
            let uu____3892 = extract_reifiable_effect g ed  in
            (match uu____3892 with | (env,iface1,uu____3907) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3929 = FStar_Options.interactive ()  in
      if uu____3929
      then (g, empty_iface)
      else
        (let uu____3938 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___626_3942 = empty_iface  in
           let uu____3943 = FStar_Extraction_ML_UEnv.current_module_of_uenv g
              in
           {
             iface_module_name = uu____3943;
             iface_bindings = (uu___626_3942.iface_bindings);
             iface_tydefs = (uu___626_3942.iface_tydefs);
             iface_type_names = (uu___626_3942.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____3961  ->
                fun se  ->
                  match uu____3961 with
                  | (g1,iface2) ->
                      let uu____3973 = extract_sigelt_iface g1 se  in
                      (match uu____3973 with
                       | (g2,iface') ->
                           let uu____3984 = iface_union iface2 iface'  in
                           (g2, uu____3984))) (g, iface1) decls
            in
         (let uu____3986 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____3986);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4003 = FStar_Options.debug_any ()  in
      if uu____4003
      then
        let uu____4010 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____4010
          (fun uu____4018  -> extract_iface' g modul)
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
          let uu____4109 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4109
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____4117 =
            let uu____4118 =
              let uu____4121 =
                let uu____4122 =
                  FStar_Extraction_ML_UEnv.tcenv_of_uenv env_iparams  in
                FStar_TypeChecker_Normalize.normalize steps uu____4122
                  ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4121  in
            uu____4118.FStar_Syntax_Syntax.n  in
          match uu____4117 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4127) ->
              FStar_List.map
                (fun uu____4160  ->
                   match uu____4160 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4169;
                        FStar_Syntax_Syntax.sort = uu____4170;_},uu____4171)
                       -> ppname.FStar_Ident.idText) bs
          | uu____4179 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____4187 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____4187 with
        | (env2,uu____4214,uu____4215) ->
            let uu____4218 =
              let uu____4231 = lident_as_mlsymbol ctor.dname  in
              let uu____4233 =
                let uu____4241 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____4241  in
              (uu____4231, uu____4233)  in
            (env2, uu____4218)
         in
      let extract_one_family env1 ind =
        let uu____4302 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4302 with
        | (env_iparams,vars) ->
            let uu____4346 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____4346 with
             | (env2,ctors) ->
                 let uu____4453 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____4453 with
                  | (indices,uu____4487) ->
                      let ml_params =
                        let uu____4496 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____4522  ->
                                    let uu____4530 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____4530))
                           in
                        FStar_List.append vars uu____4496  in
                      let tbody =
                        let uu____4535 =
                          FStar_Util.find_opt
                            (fun uu___7_4540  ->
                               match uu___7_4540 with
                               | FStar_Syntax_Syntax.RecordType uu____4542 ->
                                   true
                               | uu____4552 -> false) ind.iquals
                           in
                        match uu____4535 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____4564 = FStar_List.hd ctors  in
                            (match uu____4564 with
                             | (uu____4589,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____4633  ->
                                          match uu____4633 with
                                          | (uu____4644,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____4649 =
                                                lident_as_mlsymbol lid  in
                                              (uu____4649, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4652 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____4655 =
                        let uu____4678 = lident_as_mlsymbol ind.iname  in
                        (false, uu____4678, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____4655)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____4723,t,uu____4725,uu____4726,uu____4727);
            FStar_Syntax_Syntax.sigrng = uu____4728;
            FStar_Syntax_Syntax.sigquals = uu____4729;
            FStar_Syntax_Syntax.sigmeta = uu____4730;
            FStar_Syntax_Syntax.sigattrs = uu____4731;
            FStar_Syntax_Syntax.sigopts = uu____4732;_}::[],uu____4733),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____4754 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____4754 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____4807),quals) ->
          let uu____4821 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____4821
          then (env, [])
          else
            (let uu____4834 = bundle_as_inductive_families env ses quals  in
             match uu____4834 with
             | (env1,ifams) ->
                 let uu____4853 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____4853 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____4962 -> failwith "Unexpected signature element"
  
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
             let uu____5020 = FStar_Syntax_Util.head_and_args t  in
             match uu____5020 with
             | (head1,args) ->
                 let uu____5068 =
                   let uu____5070 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____5070  in
                 if uu____5068
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5089));
                         FStar_Syntax_Syntax.pos = uu____5090;
                         FStar_Syntax_Syntax.vars = uu____5091;_},uu____5092)::[]
                        ->
                        let uu____5131 =
                          let uu____5135 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5135  in
                        FStar_Pervasives_Native.Some uu____5131
                    | uu____5141 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5156 =
        let uu____5158 = FStar_Options.codegen ()  in
        uu____5158 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5156
      then []
      else
        (let uu____5168 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5168 with
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
                      let uu____5210 =
                        let uu____5211 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5211  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5210  in
                    let uu____5213 =
                      let uu____5226 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        uu____5226 fv fv_t arity_opt ml_name_str
                       in
                    match uu____5213 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin) ->
                        let uu____5247 =
                          if plugin
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____5247 with
                         | (register,args) ->
                             let h =
                               let uu____5284 =
                                 let uu____5285 =
                                   let uu____5286 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____5286
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____5285
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____5284
                                in
                             let arity1 =
                               let uu____5288 =
                                 let uu____5289 =
                                   let uu____5301 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____5301, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5289
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5288
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
              | uu____5330 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5358 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5358);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5367 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5376 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5393 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           let uu____5410 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
           FStar_TypeChecker_Env.is_reifiable_effect uu____5410
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5411 = extract_reifiable_effect g ed  in
           (match uu____5411 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5435 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_fail uu____5449 ->
           failwith "impossible: trying to extract Sig_fail"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5469 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5475 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____5475 with | (env,uu____5491,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5500) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5509 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____5509 with | (env,uu____5525,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____5534) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5547 = extract_let_rec_types se g lbs  in
           (match uu____5547 with | (env,uu____5563,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____5572) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5583 =
             let uu____5592 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____5592 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____5621) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____5583 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    let uu____5707 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.postprocess uu____5707 tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___876_5708 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___876_5708.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___876_5708.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___876_5708.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___876_5708.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___876_5708.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___876_5708.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____5717 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____5717)  in
                let uu____5735 =
                  let uu____5742 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5742  in
                (match uu____5735 with
                 | (ml_let,uu____5759,uu____5760) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____5769) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____5786 =
                            FStar_List.fold_left2
                              (fun uu____5812  ->
                                 fun ml_lb  ->
                                   fun uu____5814  ->
                                     match (uu____5812, uu____5814) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____5836;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____5838;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____5839;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____5840;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____5841;_})
                                         ->
                                         let uu____5866 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____5866
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5883 =
                                                let uu____5886 =
                                                  FStar_Util.right lbname  in
                                                uu____5886.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____5883.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____5890 =
                                                let uu____5891 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____5891.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____5890 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5896,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5897;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____5899;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5900;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____5901;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____5902;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____5903;_})
                                                  when
                                                  let uu____5938 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____5938 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____5942 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___924_5947 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___924_5947.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___924_5947.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___924_5947.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___924_5947.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___924_5947.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____5948 =
                                              let uu____5953 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_5960  ->
                                                        match uu___8_5960
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____5962 ->
                                                            true
                                                        | uu____5968 -> false))
                                                 in
                                              if uu____5953
                                              then
                                                let mname =
                                                  let uu____5984 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5984
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____5993 =
                                                  let uu____6001 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____6002 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____6001 mname
                                                    uu____6002
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____5993 with
                                                | (env1,uu____6009,uu____6010)
                                                    ->
                                                    (env1,
                                                      (let uu___937_6014 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___937_6014.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___937_6014.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___937_6014.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___937_6014.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___937_6014.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6021 =
                                                   let uu____6029 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6029
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____6021 with
                                                 | (env1,uu____6036,uu____6037)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____5948 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____5786 with
                           | (g1,ml_lbs') ->
                               let uu____6067 =
                                 let uu____6070 =
                                   let uu____6073 =
                                     let uu____6074 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6074
                                      in
                                   [uu____6073;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____6077 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____6070 uu____6077  in
                               (g1, uu____6067))
                      | uu____6082 ->
                          let uu____6083 =
                            let uu____6085 =
                              let uu____6087 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____6087 ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6085
                             in
                          failwith uu____6083)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6096,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6101 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6107 =
                  let uu____6109 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Util.must_erase_for_extraction uu____6109
                    t
                   in
                Prims.op_Negation uu____6107)
              in
           if uu____6101
           then
             let always_fail1 =
               let uu___957_6118 = se  in
               let uu____6119 =
                 let uu____6120 =
                   let uu____6127 =
                     let uu____6128 =
                       let uu____6131 = always_fail lid t  in [uu____6131]
                        in
                     (false, uu____6128)  in
                   (uu____6127, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6120  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6119;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___957_6118.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___957_6118.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___957_6118.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___957_6118.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___957_6118.FStar_Syntax_Syntax.sigopts)
               }  in
             let uu____6138 = extract_sig g always_fail1  in
             (match uu____6138 with
              | (g1,mlm) ->
                  let uu____6157 =
                    FStar_Util.find_map quals
                      (fun uu___9_6162  ->
                         match uu___9_6162 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6166 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6157 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6174 =
                         let uu____6177 =
                           let uu____6178 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6178  in
                         let uu____6179 =
                           let uu____6182 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6182]  in
                         uu____6177 :: uu____6179  in
                       (g1, uu____6174)
                   | uu____6185 ->
                       let uu____6188 =
                         FStar_Util.find_map quals
                           (fun uu___10_6194  ->
                              match uu___10_6194 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6198)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6199 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6188 with
                        | FStar_Pervasives_Native.Some uu____6206 -> (g1, [])
                        | uu____6209 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6219 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____6219 with
            | (ml_main,uu____6233,uu____6234) ->
                let uu____6235 =
                  let uu____6238 =
                    let uu____6239 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6239  in
                  [uu____6238; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____6235))
       | FStar_Syntax_Syntax.Sig_assume uu____6242 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6251 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6254 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6269 -> (g, [])
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
      let uu____6309 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu____6313 =
          let uu____6314 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
          FStar_TypeChecker_Env.set_current_module uu____6314
            m.FStar_Syntax_Syntax.name
           in
        FStar_Extraction_ML_UEnv.set_tcenv g uu____6313  in
      let g2 = FStar_Extraction_ML_UEnv.set_current_module g1 name  in
      let uu____6316 =
        FStar_Util.fold_map
          (fun g3  ->
             fun se  ->
               let uu____6335 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____6335
               then
                 let nm =
                   let uu____6346 =
                     let uu____6350 = FStar_Syntax_Util.lids_of_sigelt se  in
                     FStar_All.pipe_right uu____6350
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____6346 (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____6366 = FStar_Util.format1 "---Extracted {%s}" nm
                      in
                   FStar_Util.measure_execution_time uu____6366
                     (fun uu____6376  -> extract_sig g3 se)))
               else extract_sig g3 se) g2 m.FStar_Syntax_Syntax.declarations
         in
      match uu____6316 with
      | (g3,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____6398 = FStar_Options.codegen ()  in
            uu____6398 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____6413 =
                let uu____6415 = FStar_Options.silent ()  in
                Prims.op_Negation uu____6415  in
              if uu____6413
              then
                let uu____6418 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____6418
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
      (let uu____6493 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____6493);
      (let uu____6496 =
         let uu____6498 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____6498  in
       if uu____6496
       then
         let uu____6501 =
           let uu____6503 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6503
            in
         failwith uu____6501
       else ());
      (let uu____6508 = FStar_Options.interactive ()  in
       if uu____6508
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____6528 = FStar_Options.debug_any ()  in
            if uu____6528
            then
              let msg =
                let uu____6539 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s" uu____6539  in
              FStar_Util.measure_execution_time msg
                (fun uu____6549  -> extract' g m)
            else extract' g m  in
          (let uu____6553 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____6553);
          res))
  
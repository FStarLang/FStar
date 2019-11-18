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
        FStar_Syntax_Syntax.attribute Prims.list ->
          (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____824 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____872 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____872 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____911,t2,l',nparams,uu____915)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____922 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____922 with
                                           | (bs',body) ->
                                               let uu____961 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____961 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____1052  ->
                                                           fun uu____1053  ->
                                                             match (uu____1052,
                                                                    uu____1053)
                                                             with
                                                             | ((b',uu____1079),
                                                                (b,uu____1081))
                                                                 ->
                                                                 let uu____1102
                                                                   =
                                                                   let uu____1109
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____1109)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1102)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1115 =
                                                        let uu____1116 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1116
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1115
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1119 -> []))
                               in
                            let metadata =
                              let uu____1123 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____1126 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____1123 uu____1126  in
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
                   | uu____1133 -> (env1, [])) env ses
             in
          match uu____824 with
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
    let uu___211_1313 = empty_iface  in
    {
      iface_module_name = (uu___211_1313.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___211_1313.iface_tydefs);
      iface_type_names = (uu___211_1313.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___214_1324 = empty_iface  in
    let uu____1325 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___214_1324.iface_module_name);
      iface_bindings = (uu___214_1324.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1325
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___218_1340 = empty_iface  in
    {
      iface_module_name = (uu___218_1340.iface_module_name);
      iface_bindings = (uu___218_1340.iface_bindings);
      iface_tydefs = (uu___218_1340.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1352 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1352;
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
  'Auu____1397 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1397 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____1429 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1431 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1433 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1429 uu____1431
        uu____1433
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1451  ->
      match uu____1451 with
      | (fv,exp_binding) ->
          let uu____1459 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1461 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1459 uu____1461
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1476 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1478 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1476 uu____1478
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1496 =
      let uu____1498 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1498 (FStar_String.concat "\n")  in
    let uu____1512 =
      let uu____1514 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1514 (FStar_String.concat "\n")  in
    let uu____1524 =
      let uu____1526 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1526 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1496 uu____1512
      uu____1524
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___2_1559  ->
           match uu___2_1559 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1576 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____1581 =
      let uu____1583 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1583 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1581
  
let (is_lowstar_union :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Extraction_ML_UEnv.uenv ->
        FStar_Syntax_Syntax.term ->
          (Prims.string * FStar_Extraction_ML_Syntax.mlty) Prims.list
            FStar_Pervasives_Native.option)
  =
  fun range  ->
    fun tcenv  ->
      fun env1  ->
        fun body  ->
          let is_kremlin =
            let uu____1630 = FStar_Options.codegen ()  in
            uu____1630 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          let fix x =
            let uu____1641 =
              let uu____1642 = FStar_Syntax_Util.unmeta x  in
              FStar_Syntax_Util.un_uinst uu____1642  in
            FStar_Syntax_Subst.compress uu____1641  in
          let head_and_args1 e =
            let uu____1661 = FStar_Syntax_Util.head_and_args' e  in
            match uu____1661 with
            | (head1,args) ->
                let uu____1710 = fix head1  in
                let uu____1711 =
                  FStar_List.map
                    (fun uu____1736  ->
                       match uu____1736 with
                       | (x,y) -> let uu____1755 = fix x  in (uu____1755, y))
                    args
                   in
                (uu____1710, uu____1711)
             in
          let uu____1766 = head_and_args1 body  in
          match uu____1766 with
          | ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____1789;
               FStar_Syntax_Syntax.vars = uu____1790;_},uu____1791::(cases,uu____1793)::uu____1794)
              when
              is_kremlin &&
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.union_lid)
              ->
              let cases1 =
                FStar_TypeChecker_Normalize.normalize
                  FStar_Extraction_ML_Term.extraction_norm_steps tcenv cases
                 in
              let uu____1836 = FStar_Syntax_Util.list_elements cases1  in
              (match uu____1836 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1852 =
                     let uu____1858 =
                       let uu____1860 =
                         FStar_Syntax_Print.term_to_string cases1  in
                       FStar_Util.format1
                         "LowStar.Union type definitions must be exactly of the form:\ninline_for_extraction noextract\nlet cases = [ \"case1\", t1; ... ]\nlet t = LowStar.Union.union cases\n\nHere the cases argument is: %s"
                         uu____1860
                        in
                     (FStar_Errors.Fatal_ExtractionUnsupported, uu____1858)
                      in
                   FStar_Errors.raise_error uu____1852 range
               | FStar_Pervasives_Native.Some cases2 ->
                   let cases3 =
                     FStar_List.map
                       (fun case  ->
                          let uu____1912 = head_and_args1 case  in
                          match uu____1912 with
                          | (h,uu____1931::uu____1932::uu____1933::(pair,uu____1935)::[])
                              ->
                              let uu____1996 = head_and_args1 pair  in
                              (match uu____1996 with
                               | (h1,uu____2015::uu____2016::(label1,uu____2018)::
                                  (t,uu____2020)::[]) ->
                                   let t1 =
                                     let uu____2080 =
                                       FStar_Extraction_ML_Term.term_as_mlty
                                         env1 t
                                        in
                                     FStar_Extraction_ML_Util.eraseTypeDeep
                                       (FStar_Extraction_ML_Util.udelta_unfold
                                          env1) uu____2080
                                      in
                                   let uu____2081 =
                                     let uu____2082 = fix label1  in
                                     uu____2082.FStar_Syntax_Syntax.n  in
                                   (match uu____2081 with
                                    | FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_string
                                        (s,uu____2091)) -> (s, t1)
                                    | uu____2095 ->
                                        let uu____2096 =
                                          let uu____2102 =
                                            let uu____2104 =
                                              FStar_Syntax_Print.term_to_string
                                                label1
                                               in
                                            FStar_Util.format1
                                              "The label is this union type is %s which is not a string constant"
                                              uu____2104
                                             in
                                          (FStar_Errors.Fatal_ExtractionUnsupported,
                                            uu____2102)
                                           in
                                        FStar_Errors.raise_error uu____2096
                                          range)
                               | uu____2113 ->
                                   failwith
                                     "impossible: not an inner application")
                          | (h,args) ->
                              let uu____2150 =
                                let uu____2152 =
                                  FStar_Syntax_Print.term_to_string case  in
                                let uu____2154 =
                                  FStar_Syntax_Print.term_to_string h  in
                                let uu____2156 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length args)
                                   in
                                FStar_Util.format3
                                  "%s is not an outer application (head=%s) (length args=%s)"
                                  uu____2152 uu____2154 uu____2156
                                 in
                              failwith uu____2150) cases2
                      in
                   FStar_Pervasives_Native.Some cases3)
          | uu____2177 -> FStar_Pervasives_Native.None
  
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
          let uu____2242 =
            let uu____2251 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____2251 with
            | (tcenv,uu____2269,def_typ) ->
                let uu____2275 = as_pair def_typ  in (tcenv, uu____2275)
             in
          match uu____2242 with
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
                let uu____2306 =
                  let uu____2307 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____2307 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____2306 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____2315 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____2334 -> def  in
              let uu____2335 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____2346) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____2371 -> ([], def1)  in
              (match uu____2335 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_2391  ->
                          match uu___3_2391 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2394 -> false) quals
                      in
                   let uu____2396 = binders_as_mlty_binders env bs  in
                   (match uu____2396 with
                    | (env1,ml_bs) ->
                        let metadata =
                          let uu____2425 = extract_metadata attrs  in
                          let uu____2428 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____2425 uu____2428  in
                        let td =
                          let uu____2432 =
                            let uu____2442 = FStar_Ident.range_of_lid lid  in
                            is_lowstar_union uu____2442 tcenv env1 body  in
                          match uu____2432 with
                          | FStar_Pervasives_Native.Some td_union ->
                              let original_t =
                                let uu____2459 =
                                  FStar_Extraction_ML_Term.term_as_mlty env1
                                    body
                                   in
                                FStar_All.pipe_right uu____2459
                                  (FStar_Extraction_ML_Util.eraseTypeDeep
                                     (FStar_Extraction_ML_Util.udelta_unfold
                                        env1))
                                 in
                              let uu____2460 = lident_as_mlsymbol lid  in
                              (assumed, uu____2460,
                                FStar_Pervasives_Native.None, ml_bs,
                                metadata,
                                (FStar_Pervasives_Native.Some
                                   (FStar_Extraction_ML_Syntax.MLTD_Union
                                      (td_union, original_t))))
                          | FStar_Pervasives_Native.None  ->
                              let body1 =
                                let uu____2485 =
                                  FStar_Extraction_ML_Term.term_as_mlty env1
                                    body
                                   in
                                FStar_All.pipe_right uu____2485
                                  (FStar_Extraction_ML_Util.eraseTypeDeep
                                     (FStar_Extraction_ML_Util.udelta_unfold
                                        env1))
                                 in
                              let mangled_projector =
                                let uu____2490 =
                                  FStar_All.pipe_right quals
                                    (FStar_Util.for_some
                                       (fun uu___4_2497  ->
                                          match uu___4_2497 with
                                          | FStar_Syntax_Syntax.Projector
                                              uu____2499 -> true
                                          | uu____2505 -> false))
                                   in
                                if uu____2490
                                then
                                  let mname = mangle_projector_lid lid  in
                                  FStar_Pervasives_Native.Some
                                    ((mname.FStar_Ident.ident).FStar_Ident.idText)
                                else FStar_Pervasives_Native.None  in
                              let uu____2516 = lident_as_mlsymbol lid  in
                              (assumed, uu____2516, mangled_projector, ml_bs,
                                metadata,
                                (FStar_Pervasives_Native.Some
                                   (FStar_Extraction_ML_Syntax.MLTD_Abbrev
                                      body1)))
                           in
                        let def2 =
                          let uu____2528 =
                            let uu____2529 =
                              let uu____2530 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____2530
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____2529  in
                          [uu____2528;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____2531 =
                          let uu____2536 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_2542  ->
                                    match uu___5_2542 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____2546 -> false))
                             in
                          if uu____2536
                          then
                            let uu____2553 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____2553, (iface_of_type_names [fv]))
                          else
                            (let uu____2556 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____2556 with
                             | (env2,tydef) ->
                                 let uu____2567 = iface_of_tydefs [tydef]  in
                                 (env2, uu____2567))
                           in
                        (match uu____2531 with
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
          let uu____2626 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____2626 with
          | (bs,uu____2650) ->
              let uu____2671 = binders_as_mlty_binders env bs  in
              (match uu____2671 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____2703 = extract_metadata attrs  in
                     let uu____2706 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____2703 uu____2706  in
                   let assumed = false  in
                   let td =
                     let uu____2732 = lident_as_mlsymbol lid  in
                     (assumed, uu____2732, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____2745 =
                       let uu____2746 =
                         let uu____2747 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____2747
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____2746  in
                     [uu____2745; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____2748 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____2748 with
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
          let uu____2829 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2829
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2836 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2836 with | (env2,uu____2855,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2894 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2894 with
        | (env_iparams,vars) ->
            let uu____2922 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2922 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2986,t,uu____2988,uu____2989,uu____2990);
            FStar_Syntax_Syntax.sigrng = uu____2991;
            FStar_Syntax_Syntax.sigquals = uu____2992;
            FStar_Syntax_Syntax.sigmeta = uu____2993;
            FStar_Syntax_Syntax.sigattrs = uu____2994;
            FStar_Syntax_Syntax.sigopts = uu____2995;_}::[],uu____2996),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____3017 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____3017 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____3050),quals) ->
          let uu____3064 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____3064
          then (env, empty_iface)
          else
            (let uu____3073 =
               bundle_as_inductive_families env ses quals
                 se.FStar_Syntax_Syntax.sigattrs
                in
             match uu____3073 with
             | (env1,ifams) ->
                 let uu____3090 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____3090 with
                  | (env2,td) ->
                      let uu____3131 =
                        let uu____3132 =
                          let uu____3133 =
                            FStar_List.map (fun x  -> x.ifv) ifams  in
                          iface_of_type_names uu____3133  in
                        iface_union uu____3132
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____3131)))
      | uu____3142 -> failwith "Unexpected signature element"
  
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
              let uu____3217 =
                let uu____3219 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_3225  ->
                          match uu___6_3225 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____3228 -> false))
                   in
                Prims.op_Negation uu____3219  in
              if uu____3217
              then (g, empty_iface, [])
              else
                (let uu____3243 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____3243 with
                 | (bs,uu____3267) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____3290 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____3290;
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
        let uu____3353 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____3353 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____3375 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____3375
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
        (let uu____3411 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____3411
         then
           let uu____3416 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____3416
         else ());
        (let uu____3421 =
           let uu____3422 = FStar_Syntax_Subst.compress tm  in
           uu____3422.FStar_Syntax_Syntax.n  in
         match uu____3421 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____3430) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____3437 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____3437 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____3442;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____3443;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____3445;_} ->
                  let uu____3448 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____3448, tysc))
         | uu____3449 ->
             let uu____3450 =
               let uu____3452 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____3454 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____3452 uu____3454
                in
             failwith uu____3450)
         in
      let extract_action g1 a =
        (let uu____3482 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____3482
         then
           let uu____3487 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____3489 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____3487
             uu____3489
         else ());
        (let uu____3494 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____3494 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____3514 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____3514  in
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
             let uu____3544 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____3544 with
              | (a_let,uu____3560,ty) ->
                  ((let uu____3563 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____3563
                    then
                      let uu____3568 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____3568
                    else ());
                   (let uu____3573 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____3596,mllb::[]),uu____3598) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____3638 -> failwith "Impossible"  in
                    match uu____3573 with
                    | (exp,tysc) ->
                        ((let uu____3676 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____3676
                          then
                            ((let uu____3682 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____3682);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____3698 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____3698 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____3720 =
        let uu____3727 =
          let uu____3732 =
            let uu____3735 =
              let uu____3744 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr  in
              FStar_All.pipe_right uu____3744 FStar_Util.must  in
            FStar_All.pipe_right uu____3735 FStar_Pervasives_Native.snd  in
          extract_fv uu____3732  in
        match uu____3727 with
        | (return_tm,ty_sc) ->
            let uu____3813 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____3813 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____3720 with
      | (g1,return_iface,return_decl) ->
          let uu____3838 =
            let uu____3845 =
              let uu____3850 =
                let uu____3853 =
                  let uu____3862 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr
                     in
                  FStar_All.pipe_right uu____3862 FStar_Util.must  in
                FStar_All.pipe_right uu____3853 FStar_Pervasives_Native.snd
                 in
              extract_fv uu____3850  in
            match uu____3845 with
            | (bind_tm,ty_sc) ->
                let uu____3931 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____3931 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____3838 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3956 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3956 with
                | (g3,actions) ->
                    let uu____3993 = FStar_List.unzip actions  in
                    (match uu____3993 with
                     | (actions_iface,actions1) ->
                         let uu____4020 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____4020, (return_decl :: bind_decl ::
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
        let uu____4051 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____4056 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____4056) lbs
           in
        if uu____4051
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____4079 =
             FStar_List.fold_left
               (fun uu____4114  ->
                  fun lb  ->
                    match uu____4114 with
                    | (env1,iface_opt,impls) ->
                        let uu____4155 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____4155 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____4189 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____4189
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____4079 with
           | (env1,iface_opt,impls) ->
               let uu____4229 = FStar_Option.get iface_opt  in
               let uu____4230 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____4229, uu____4230))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____4262 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4271 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____4288 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____4307 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____4307 with | (env,iface1,uu____4322) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4328) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____4337 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____4337 with | (env,iface1,uu____4352) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____4358) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____4371 = extract_let_rec_types se g lbs  in
          (match uu____4371 with | (env,iface1,uu____4386) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____4397 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____4403 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____4403)
             in
          if uu____4397
          then
            let uu____4410 =
              let uu____4421 =
                let uu____4422 =
                  let uu____4425 = always_fail lid t  in [uu____4425]  in
                (false, uu____4422)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____4421  in
            (match uu____4410 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4451) ->
          let uu____4456 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____4456 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____4485 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____4486 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4493 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4494 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____4509 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4522 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____4522
          then
            let uu____4535 = extract_reifiable_effect g ed  in
            (match uu____4535 with | (env,iface1,uu____4550) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4572 = FStar_Options.interactive ()  in
      if uu____4572
      then (g, empty_iface)
      else
        (let uu____4581 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___682_4585 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___682_4585.iface_bindings);
             iface_tydefs = (uu___682_4585.iface_tydefs);
             iface_type_names = (uu___682_4585.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____4603  ->
                fun se  ->
                  match uu____4603 with
                  | (g1,iface2) ->
                      let uu____4615 = extract_sigelt_iface g1 se  in
                      (match uu____4615 with
                       | (g2,iface') ->
                           let uu____4626 = iface_union iface2 iface'  in
                           (g2, uu____4626))) (g, iface1) decls
            in
         (let uu____4628 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____4628);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4645 = FStar_Options.debug_any ()  in
      if uu____4645
      then
        let uu____4652 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____4652
          (fun uu____4660  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let mlident_map =
        FStar_List.fold_left
          (fun acc  ->
             fun uu____4690  ->
               match uu____4690 with
               | (uu____4701,x) ->
                   FStar_Util.psmap_add acc
                     x.FStar_Extraction_ML_UEnv.exp_b_name "")
          g.FStar_Extraction_ML_UEnv.env_mlident_map iface1.iface_bindings
         in
      let uu___705_4705 = g  in
      let uu____4706 =
        let uu____4709 =
          FStar_List.map (fun _4716  -> FStar_Extraction_ML_UEnv.Fv _4716)
            iface1.iface_bindings
           in
        FStar_List.append uu____4709 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___705_4705.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____4706;
        FStar_Extraction_ML_UEnv.env_mlident_map = mlident_map;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___705_4705.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____4794 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4794
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____4802 =
            let uu____4803 =
              let uu____4806 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4806  in
            uu____4803.FStar_Syntax_Syntax.n  in
          match uu____4802 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4811) ->
              FStar_List.map
                (fun uu____4844  ->
                   match uu____4844 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4853;
                        FStar_Syntax_Syntax.sort = uu____4854;_},uu____4855)
                       -> ppname.FStar_Ident.idText) bs
          | uu____4863 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____4871 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____4871 with
        | (env2,uu____4898,uu____4899) ->
            let uu____4902 =
              let uu____4915 = lident_as_mlsymbol ctor.dname  in
              let uu____4917 =
                let uu____4925 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____4925  in
              (uu____4915, uu____4917)  in
            (env2, uu____4902)
         in
      let extract_one_family env1 ind =
        let uu____4986 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4986 with
        | (env_iparams,vars) ->
            let uu____5030 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____5030 with
             | (env2,ctors) ->
                 let uu____5137 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____5137 with
                  | (indices,uu____5179) ->
                      let ml_params =
                        let uu____5204 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____5230  ->
                                    let uu____5238 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____5238))
                           in
                        FStar_List.append vars uu____5204  in
                      let tbody =
                        let uu____5243 =
                          FStar_Util.find_opt
                            (fun uu___7_5248  ->
                               match uu___7_5248 with
                               | FStar_Syntax_Syntax.RecordType uu____5250 ->
                                   true
                               | uu____5260 -> false) ind.iquals
                           in
                        match uu____5243 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____5272 = FStar_List.hd ctors  in
                            (match uu____5272 with
                             | (uu____5297,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____5341  ->
                                          match uu____5341 with
                                          | (uu____5352,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____5357 =
                                                lident_as_mlsymbol lid  in
                                              (uu____5357, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____5360 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____5363 =
                        let uu____5386 = lident_as_mlsymbol ind.iname  in
                        (false, uu____5386, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____5363)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____5431,t,uu____5433,uu____5434,uu____5435);
            FStar_Syntax_Syntax.sigrng = uu____5436;
            FStar_Syntax_Syntax.sigquals = uu____5437;
            FStar_Syntax_Syntax.sigmeta = uu____5438;
            FStar_Syntax_Syntax.sigattrs = uu____5439;
            FStar_Syntax_Syntax.sigopts = uu____5440;_}::[],uu____5441),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____5462 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____5462 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____5515),quals) ->
          let uu____5529 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____5529
          then (env, [])
          else
            (let uu____5542 =
               bundle_as_inductive_families env ses quals
                 se.FStar_Syntax_Syntax.sigattrs
                in
             match uu____5542 with
             | (env1,ifams) ->
                 let uu____5561 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____5561 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____5670 -> failwith "Unexpected signature element"
  
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
             let uu____5728 = FStar_Syntax_Util.head_and_args t  in
             match uu____5728 with
             | (head1,args) ->
                 let uu____5776 =
                   let uu____5778 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____5778  in
                 if uu____5776
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5797));
                         FStar_Syntax_Syntax.pos = uu____5798;
                         FStar_Syntax_Syntax.vars = uu____5799;_},uu____5800)::[]
                        ->
                        let uu____5839 =
                          let uu____5843 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5843  in
                        FStar_Pervasives_Native.Some uu____5839
                    | uu____5849 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5864 =
        let uu____5866 = FStar_Options.codegen ()  in
        uu____5866 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5864
      then []
      else
        (let uu____5876 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5876 with
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
                      let uu____5918 =
                        let uu____5919 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5919  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5918  in
                    let uu____5921 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____5921 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____5954 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____5954 with
                         | (register,args) ->
                             let h =
                               let uu____5991 =
                                 let uu____5992 =
                                   let uu____5993 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____5993
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____5992
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____5991
                                in
                             let arity1 =
                               let uu____5995 =
                                 let uu____5996 =
                                   let uu____6008 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____6008, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5996
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5995
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
              | uu____6037 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____6065 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____6065);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____6074 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____6083 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____6100 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____6117 = extract_reifiable_effect g ed  in
           (match uu____6117 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____6141 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____6155 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____6161 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____6161 with | (env,uu____6177,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____6186) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____6195 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____6195 with | (env,uu____6211,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____6220) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____6233 = extract_let_rec_types se g lbs  in
           (match uu____6233 with | (env,uu____6249,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____6258) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6269 =
             let uu____6278 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____6278 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____6307) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____6269 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___937_6393 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___937_6393.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___937_6393.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___937_6393.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___937_6393.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___937_6393.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___937_6393.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____6402 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____6402)  in
                let uu____6420 =
                  let uu____6427 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____6427  in
                (match uu____6420 with
                 | (ml_let,uu____6444,uu____6445) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____6454) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____6471 =
                            FStar_List.fold_left2
                              (fun uu____6497  ->
                                 fun ml_lb  ->
                                   fun uu____6499  ->
                                     match (uu____6497, uu____6499) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____6521;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____6523;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____6524;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____6525;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____6526;_})
                                         ->
                                         let uu____6551 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____6551
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____6568 =
                                                let uu____6571 =
                                                  FStar_Util.right lbname  in
                                                uu____6571.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____6568.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____6575 =
                                                let uu____6576 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____6576.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____6575 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6581,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6582;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____6584;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6585;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____6586;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____6587;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____6588;_})
                                                  when
                                                  let uu____6623 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____6623 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____6627 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___985_6632 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___985_6632.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___985_6632.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___985_6632.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___985_6632.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___985_6632.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____6633 =
                                              let uu____6638 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_6645  ->
                                                        match uu___8_6645
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____6647 ->
                                                            true
                                                        | uu____6653 -> false))
                                                 in
                                              if uu____6638
                                              then
                                                let mname =
                                                  let uu____6669 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____6669
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____6678 =
                                                  let uu____6686 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____6687 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____6686 mname
                                                    uu____6687
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____6678 with
                                                | (env1,uu____6694,uu____6695)
                                                    ->
                                                    (env1,
                                                      (let uu___998_6699 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___998_6699.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___998_6699.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___998_6699.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___998_6699.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___998_6699.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6706 =
                                                   let uu____6714 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6714
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____6706 with
                                                 | (env1,uu____6721,uu____6722)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____6633 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____6471 with
                           | (g1,ml_lbs') ->
                               let uu____6752 =
                                 let uu____6755 =
                                   let uu____6758 =
                                     let uu____6759 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6759
                                      in
                                   [uu____6758;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____6762 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____6755 uu____6762  in
                               (g1, uu____6752))
                      | uu____6767 ->
                          let uu____6768 =
                            let uu____6770 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6770
                             in
                          failwith uu____6768)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6780,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6785 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6791 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____6791)
              in
           if uu____6785
           then
             let always_fail1 =
               let uu___1018_6801 = se  in
               let uu____6802 =
                 let uu____6803 =
                   let uu____6810 =
                     let uu____6811 =
                       let uu____6814 = always_fail lid t  in [uu____6814]
                        in
                     (false, uu____6811)  in
                   (uu____6810, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6803  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6802;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1018_6801.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1018_6801.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1018_6801.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1018_6801.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___1018_6801.FStar_Syntax_Syntax.sigopts)
               }  in
             let uu____6821 = extract_sig g always_fail1  in
             (match uu____6821 with
              | (g1,mlm) ->
                  let uu____6840 =
                    FStar_Util.find_map quals
                      (fun uu___9_6845  ->
                         match uu___9_6845 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6849 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6840 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6857 =
                         let uu____6860 =
                           let uu____6861 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6861  in
                         let uu____6862 =
                           let uu____6865 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6865]  in
                         uu____6860 :: uu____6862  in
                       (g1, uu____6857)
                   | uu____6868 ->
                       let uu____6871 =
                         FStar_Util.find_map quals
                           (fun uu___10_6877  ->
                              match uu___10_6877 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6881)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6882 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6871 with
                        | FStar_Pervasives_Native.Some uu____6889 -> (g1, [])
                        | uu____6892 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6902 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____6902 with
            | (ml_main,uu____6916,uu____6917) ->
                let uu____6918 =
                  let uu____6921 =
                    let uu____6922 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6922  in
                  [uu____6921; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____6918))
       | FStar_Syntax_Syntax.Sig_assume uu____6925 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6934 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6937 -> (g, [])
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
      let uu____6979 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1059_6983 = g  in
        let uu____6984 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____6984;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1059_6983.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.env_mlident_map =
            (uu___1059_6983.FStar_Extraction_ML_UEnv.env_mlident_map);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1059_6983.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1059_6983.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____6985 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____7004 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____7004
               then
                 let nm =
                   let uu____7015 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____7015 (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____7032 = FStar_Util.format1 "---Extracted {%s}" nm
                      in
                   FStar_Util.measure_execution_time uu____7032
                     (fun uu____7042  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____6985 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____7064 = FStar_Options.codegen ()  in
            uu____7064 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____7079 =
                let uu____7081 = FStar_Options.silent ()  in
                Prims.op_Negation uu____7081  in
              if uu____7079
              then
                let uu____7084 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____7084
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
      (let uu____7159 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____7159);
      (let uu____7162 =
         let uu____7164 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____7164  in
       if uu____7162
       then
         let uu____7167 =
           let uu____7169 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____7169
            in
         failwith uu____7167
       else ());
      (let uu____7174 = FStar_Options.interactive ()  in
       if uu____7174
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____7194 = FStar_Options.debug_any ()  in
            if uu____7194
            then
              let msg =
                let uu____7205 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____7205  in
              FStar_Util.measure_execution_time msg
                (fun uu____7215  -> extract' g m)
            else extract' g m  in
          (let uu____7219 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____7219);
          res))
  
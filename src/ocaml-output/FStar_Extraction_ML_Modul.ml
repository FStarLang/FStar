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
          let uu____1643 =
            let uu____1652 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1652 with
            | (tcenv,uu____1670,def_typ) ->
                let uu____1676 = as_pair def_typ  in (tcenv, uu____1676)
             in
          match uu____1643 with
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
                let uu____1707 =
                  let uu____1708 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1708 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1707 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1716 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1735 -> def  in
              let uu____1736 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1747) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1772 -> ([], def1)  in
              (match uu____1736 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1792  ->
                          match uu___3_1792 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1795 -> false) quals
                      in
                   let uu____1797 = binders_as_mlty_binders env bs  in
                   (match uu____1797 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1824 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1824
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1829 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1836  ->
                                    match uu___4_1836 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1838 -> true
                                    | uu____1844 -> false))
                             in
                          if uu____1829
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1858 = extract_metadata attrs  in
                          let uu____1861 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1858 uu____1861  in
                        let td =
                          let uu____1884 = lident_as_mlsymbol lid  in
                          (assumed, uu____1884, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1896 =
                            let uu____1897 =
                              let uu____1898 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1898
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1897  in
                          [uu____1896;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1899 =
                          let uu____1904 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_1910  ->
                                    match uu___5_1910 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1914 -> false))
                             in
                          if uu____1904
                          then
                            let uu____1921 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____1921, (iface_of_type_names [fv]))
                          else
                            (let uu____1924 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____1924 with
                             | (env2,tydef) ->
                                 let uu____1935 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1935))
                           in
                        (match uu____1899 with
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
          let uu____1994 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____1994 with
          | (bs,uu____2018) ->
              let uu____2039 = binders_as_mlty_binders env bs  in
              (match uu____2039 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____2071 = extract_metadata attrs  in
                     let uu____2074 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____2071 uu____2074  in
                   let assumed = false  in
                   let td =
                     let uu____2100 = lident_as_mlsymbol lid  in
                     (assumed, uu____2100, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____2113 =
                       let uu____2114 =
                         let uu____2115 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____2115
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____2114  in
                     [uu____2113; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____2116 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____2116 with
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
          let uu____2197 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2197
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2204 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2204 with | (env2,uu____2223,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2262 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2262 with
        | (env_iparams,vars) ->
            let uu____2290 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2290 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2354,t,uu____2356,uu____2357,uu____2358);
            FStar_Syntax_Syntax.sigrng = uu____2359;
            FStar_Syntax_Syntax.sigquals = uu____2360;
            FStar_Syntax_Syntax.sigmeta = uu____2361;
            FStar_Syntax_Syntax.sigattrs = uu____2362;_}::[],uu____2363),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2382 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2382 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2415),quals) ->
          let uu____2429 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____2429
          then (env, empty_iface)
          else
            (let uu____2438 =
               bundle_as_inductive_families env ses quals
                 se.FStar_Syntax_Syntax.sigattrs
                in
             match uu____2438 with
             | (env1,ifams) ->
                 let uu____2455 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____2455 with
                  | (env2,td) ->
                      let uu____2496 =
                        let uu____2497 =
                          let uu____2498 =
                            FStar_List.map (fun x  -> x.ifv) ifams  in
                          iface_of_type_names uu____2498  in
                        iface_union uu____2497
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____2496)))
      | uu____2507 -> failwith "Unexpected signature element"
  
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
              let uu____2582 =
                let uu____2584 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2590  ->
                          match uu___6_2590 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2593 -> false))
                   in
                Prims.op_Negation uu____2584  in
              if uu____2582
              then (g, empty_iface, [])
              else
                (let uu____2608 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2608 with
                 | (bs,uu____2632) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2655 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2655;
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
        let uu____2718 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2718 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2740 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2740
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
        (let uu____2776 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2776
         then
           let uu____2781 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2781
         else ());
        (let uu____2786 =
           let uu____2787 = FStar_Syntax_Subst.compress tm  in
           uu____2787.FStar_Syntax_Syntax.n  in
         match uu____2786 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2795) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2802 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2802 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2807;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2808;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2810;_} ->
                  let uu____2813 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2813, tysc))
         | uu____2814 ->
             let uu____2815 =
               let uu____2817 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2819 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2817 uu____2819
                in
             failwith uu____2815)
         in
      let extract_action g1 a =
        (let uu____2847 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2847
         then
           let uu____2852 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2854 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2852
             uu____2854
         else ());
        (let uu____2859 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2859 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2879 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2879  in
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
             let uu____2909 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2909 with
              | (a_let,uu____2925,ty) ->
                  ((let uu____2928 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2928
                    then
                      let uu____2933 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2933
                    else ());
                   (let uu____2938 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2961,mllb::[]),uu____2963) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____3003 -> failwith "Impossible"  in
                    match uu____2938 with
                    | (exp,tysc) ->
                        ((let uu____3041 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____3041
                          then
                            ((let uu____3047 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____3047);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____3063 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____3063 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____3085 =
        let uu____3092 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____3092 with
        | (return_tm,ty_sc) ->
            let uu____3109 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____3109 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____3085 with
      | (g1,return_iface,return_decl) ->
          let uu____3134 =
            let uu____3141 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____3141 with
            | (bind_tm,ty_sc) ->
                let uu____3158 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____3158 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____3134 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3183 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3183 with
                | (g3,actions) ->
                    let uu____3220 = FStar_List.unzip actions  in
                    (match uu____3220 with
                     | (actions_iface,actions1) ->
                         let uu____3247 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3247, (return_decl :: bind_decl ::
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
        let uu____3278 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____3283 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____3283) lbs
           in
        if uu____3278
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3306 =
             FStar_List.fold_left
               (fun uu____3341  ->
                  fun lb  ->
                    match uu____3341 with
                    | (env1,iface_opt,impls) ->
                        let uu____3382 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____3382 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3416 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____3416
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____3306 with
           | (env1,iface_opt,impls) ->
               let uu____3456 = FStar_Option.get iface_opt  in
               let uu____3457 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____3456, uu____3457))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3489 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3498 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3515 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3534 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3534 with | (env,iface1,uu____3549) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3555) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3564 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3564 with | (env,iface1,uu____3579) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____3585) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3598 = extract_let_rec_types se g lbs  in
          (match uu____3598 with | (env,iface1,uu____3613) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3624 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3630 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____3630)
             in
          if uu____3624
          then
            let uu____3637 =
              let uu____3648 =
                let uu____3649 =
                  let uu____3652 = always_fail lid t  in [uu____3652]  in
                (false, uu____3649)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3648  in
            (match uu____3637 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3678) ->
          let uu____3683 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3683 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3712 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3713 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3714 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3721 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3722 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3737 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3750 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____3750
          then
            let uu____3763 = extract_reifiable_effect g ed  in
            (match uu____3763 with | (env,iface1,uu____3778) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3800 = FStar_Options.interactive ()  in
      if uu____3800
      then (g, empty_iface)
      else
        (let uu____3809 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___613_3813 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___613_3813.iface_bindings);
             iface_tydefs = (uu___613_3813.iface_tydefs);
             iface_type_names = (uu___613_3813.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____3831  ->
                fun se  ->
                  match uu____3831 with
                  | (g1,iface2) ->
                      let uu____3843 = extract_sigelt_iface g1 se  in
                      (match uu____3843 with
                       | (g2,iface') ->
                           let uu____3854 = iface_union iface2 iface'  in
                           (g2, uu____3854))) (g, iface1) decls
            in
         (let uu____3856 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____3856);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3873 = FStar_Options.debug_any ()  in
      if uu____3873
      then
        let uu____3880 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____3880
          (fun uu____3888  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let mlident_map =
        FStar_List.fold_left
          (fun acc  ->
             fun uu____3918  ->
               match uu____3918 with
               | (uu____3929,x) ->
                   FStar_Util.psmap_add acc
                     x.FStar_Extraction_ML_UEnv.exp_b_name "")
          g.FStar_Extraction_ML_UEnv.env_mlident_map iface1.iface_bindings
         in
      let uu___636_3933 = g  in
      let uu____3934 =
        let uu____3937 =
          FStar_List.map (fun _3944  -> FStar_Extraction_ML_UEnv.Fv _3944)
            iface1.iface_bindings
           in
        FStar_List.append uu____3937 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___636_3933.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____3934;
        FStar_Extraction_ML_UEnv.env_mlident_map = mlident_map;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___636_3933.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____4022 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4022
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____4030 =
            let uu____4031 =
              let uu____4034 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4034  in
            uu____4031.FStar_Syntax_Syntax.n  in
          match uu____4030 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4039) ->
              FStar_List.map
                (fun uu____4072  ->
                   match uu____4072 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4081;
                        FStar_Syntax_Syntax.sort = uu____4082;_},uu____4083)
                       -> ppname.FStar_Ident.idText) bs
          | uu____4091 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____4099 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____4099 with
        | (env2,uu____4126,uu____4127) ->
            let uu____4130 =
              let uu____4143 = lident_as_mlsymbol ctor.dname  in
              let uu____4145 =
                let uu____4153 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____4153  in
              (uu____4143, uu____4145)  in
            (env2, uu____4130)
         in
      let extract_one_family env1 ind =
        let uu____4214 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4214 with
        | (env_iparams,vars) ->
            let uu____4258 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____4258 with
             | (env2,ctors) ->
                 let uu____4365 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____4365 with
                  | (indices,uu____4407) ->
                      let ml_params =
                        let uu____4432 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____4458  ->
                                    let uu____4466 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____4466))
                           in
                        FStar_List.append vars uu____4432  in
                      let tbody =
                        let uu____4471 =
                          FStar_Util.find_opt
                            (fun uu___7_4476  ->
                               match uu___7_4476 with
                               | FStar_Syntax_Syntax.RecordType uu____4478 ->
                                   true
                               | uu____4488 -> false) ind.iquals
                           in
                        match uu____4471 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____4500 = FStar_List.hd ctors  in
                            (match uu____4500 with
                             | (uu____4525,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____4569  ->
                                          match uu____4569 with
                                          | (uu____4580,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____4585 =
                                                lident_as_mlsymbol lid  in
                                              (uu____4585, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4588 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____4591 =
                        let uu____4614 = lident_as_mlsymbol ind.iname  in
                        (false, uu____4614, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____4591)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____4659,t,uu____4661,uu____4662,uu____4663);
            FStar_Syntax_Syntax.sigrng = uu____4664;
            FStar_Syntax_Syntax.sigquals = uu____4665;
            FStar_Syntax_Syntax.sigmeta = uu____4666;
            FStar_Syntax_Syntax.sigattrs = uu____4667;_}::[],uu____4668),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____4687 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____4687 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____4740),quals) ->
          let uu____4754 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____4754
          then (env, [])
          else
            (let uu____4767 =
               bundle_as_inductive_families env ses quals
                 se.FStar_Syntax_Syntax.sigattrs
                in
             match uu____4767 with
             | (env1,ifams) ->
                 let uu____4786 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____4786 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____4895 -> failwith "Unexpected signature element"
  
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
             let uu____4953 = FStar_Syntax_Util.head_and_args t  in
             match uu____4953 with
             | (head1,args) ->
                 let uu____5001 =
                   let uu____5003 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____5003  in
                 if uu____5001
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5022));
                         FStar_Syntax_Syntax.pos = uu____5023;
                         FStar_Syntax_Syntax.vars = uu____5024;_},uu____5025)::[]
                        ->
                        let uu____5064 =
                          let uu____5068 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5068  in
                        FStar_Pervasives_Native.Some uu____5064
                    | uu____5074 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5089 =
        let uu____5091 = FStar_Options.codegen ()  in
        uu____5091 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5089
      then []
      else
        (let uu____5101 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5101 with
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
                      let uu____5143 =
                        let uu____5144 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5144  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5143  in
                    let uu____5146 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____5146 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____5179 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____5179 with
                         | (register,args) ->
                             let h =
                               let uu____5216 =
                                 let uu____5217 =
                                   let uu____5218 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____5218
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____5217
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____5216
                                in
                             let arity1 =
                               let uu____5220 =
                                 let uu____5221 =
                                   let uu____5233 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____5233, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5221
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5220
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
              | uu____5262 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5290 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5290);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5299 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5308 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5325 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5342 = extract_reifiable_effect g ed  in
           (match uu____5342 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5366 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5380 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5386 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____5386 with | (env,uu____5402,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5411) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5420 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____5420 with | (env,uu____5436,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____5445) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5458 = extract_let_rec_types se g lbs  in
           (match uu____5458 with | (env,uu____5474,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____5483) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5494 =
             let uu____5503 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____5503 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____5532) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____5494 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___867_5618 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___867_5618.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___867_5618.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___867_5618.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___867_5618.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___867_5618.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___867_5618.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____5627 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____5627)  in
                let uu____5645 =
                  let uu____5652 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5652  in
                (match uu____5645 with
                 | (ml_let,uu____5669,uu____5670) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____5679) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____5696 =
                            FStar_List.fold_left2
                              (fun uu____5722  ->
                                 fun ml_lb  ->
                                   fun uu____5724  ->
                                     match (uu____5722, uu____5724) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____5746;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____5748;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____5749;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____5750;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____5751;_})
                                         ->
                                         let uu____5776 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____5776
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5793 =
                                                let uu____5796 =
                                                  FStar_Util.right lbname  in
                                                uu____5796.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____5793.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____5800 =
                                                let uu____5801 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____5801.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____5800 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5806,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5807;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____5809;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5810;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____5811;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____5812;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____5813;_})
                                                  when
                                                  let uu____5848 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____5848 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____5852 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___915_5857 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___915_5857.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___915_5857.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___915_5857.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___915_5857.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___915_5857.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____5858 =
                                              let uu____5863 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_5870  ->
                                                        match uu___8_5870
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____5872 ->
                                                            true
                                                        | uu____5878 -> false))
                                                 in
                                              if uu____5863
                                              then
                                                let mname =
                                                  let uu____5894 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5894
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____5903 =
                                                  let uu____5911 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____5912 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____5911 mname
                                                    uu____5912
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____5903 with
                                                | (env1,uu____5919,uu____5920)
                                                    ->
                                                    (env1,
                                                      (let uu___928_5924 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___928_5924.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___928_5924.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___928_5924.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___928_5924.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___928_5924.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____5931 =
                                                   let uu____5939 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____5939
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____5931 with
                                                 | (env1,uu____5946,uu____5947)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____5858 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____5696 with
                           | (g1,ml_lbs') ->
                               let uu____5977 =
                                 let uu____5980 =
                                   let uu____5983 =
                                     let uu____5984 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____5984
                                      in
                                   [uu____5983;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____5987 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____5980 uu____5987  in
                               (g1, uu____5977))
                      | uu____5992 ->
                          let uu____5993 =
                            let uu____5995 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____5995
                             in
                          failwith uu____5993)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6005,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6010 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6016 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____6016)
              in
           if uu____6010
           then
             let always_fail1 =
               let uu___948_6026 = se  in
               let uu____6027 =
                 let uu____6028 =
                   let uu____6035 =
                     let uu____6036 =
                       let uu____6039 = always_fail lid t  in [uu____6039]
                        in
                     (false, uu____6036)  in
                   (uu____6035, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6028  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6027;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___948_6026.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___948_6026.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___948_6026.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___948_6026.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____6046 = extract_sig g always_fail1  in
             (match uu____6046 with
              | (g1,mlm) ->
                  let uu____6065 =
                    FStar_Util.find_map quals
                      (fun uu___9_6070  ->
                         match uu___9_6070 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6074 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6065 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6082 =
                         let uu____6085 =
                           let uu____6086 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6086  in
                         let uu____6087 =
                           let uu____6090 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6090]  in
                         uu____6085 :: uu____6087  in
                       (g1, uu____6082)
                   | uu____6093 ->
                       let uu____6096 =
                         FStar_Util.find_map quals
                           (fun uu___10_6102  ->
                              match uu___10_6102 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6106)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6107 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6096 with
                        | FStar_Pervasives_Native.Some uu____6114 -> (g1, [])
                        | uu____6117 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6127 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____6127 with
            | (ml_main,uu____6141,uu____6142) ->
                let uu____6143 =
                  let uu____6146 =
                    let uu____6147 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6147  in
                  [uu____6146; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____6143))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6150 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____6158 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6167 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6170 -> (g, [])
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
      let uu____6212 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___991_6216 = g  in
        let uu____6217 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____6217;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___991_6216.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.env_mlident_map =
            (uu___991_6216.FStar_Extraction_ML_UEnv.env_mlident_map);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___991_6216.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___991_6216.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____6218 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____6237 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____6237
               then
                 let nm =
                   let uu____6248 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____6248 (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____6265 = FStar_Util.format1 "---Extracted {%s}" nm
                      in
                   FStar_Util.measure_execution_time uu____6265
                     (fun uu____6275  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____6218 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____6297 = FStar_Options.codegen ()  in
            uu____6297 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____6312 =
                let uu____6314 = FStar_Options.silent ()  in
                Prims.op_Negation uu____6314  in
              if uu____6312
              then
                let uu____6317 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____6317
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
      (let uu____6392 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____6392);
      (let uu____6395 =
         let uu____6397 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____6397  in
       if uu____6395
       then
         let uu____6400 =
           let uu____6402 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6402
            in
         failwith uu____6400
       else ());
      (let uu____6407 = FStar_Options.interactive ()  in
       if uu____6407
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____6427 = FStar_Options.debug_any ()  in
            if uu____6427
            then
              let msg =
                let uu____6438 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____6438  in
              FStar_Util.measure_execution_time msg
                (fun uu____6448  -> extract' g m)
            else extract' g m  in
          (let uu____6452 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____6452);
          res))
  
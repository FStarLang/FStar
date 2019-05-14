open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____104 =
        let uu____111 =
          let uu____112 =
            let uu____137 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____148 =
              let uu____163 = FStar_Syntax_Syntax.iarg t  in
              let uu____176 =
                let uu____191 =
                  let uu____204 =
                    let uu____213 =
                      let uu____220 =
                        let uu____221 =
                          let uu____222 =
                            let uu____228 =
                              let uu____230 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____230
                               in
                            (uu____228, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____222  in
                        FStar_Syntax_Syntax.Tm_constant uu____221  in
                      FStar_Syntax_Syntax.mk uu____220  in
                    uu____213 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____204
                   in
                [uu____191]  in
              uu____163 :: uu____176  in
            (uu____137, uu____148)  in
          FStar_Syntax_Syntax.Tm_app uu____112  in
        FStar_Syntax_Syntax.mk uu____111  in
      uu____104 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____355 = FStar_Syntax_Util.arrow_formals t  in
        match uu____355 with
        | ([],t1) ->
            let b =
              let uu____434 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____434  in
            let uu____462 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____462 FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____542 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____542 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____575 =
          let uu____588 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____588  in
        {
          FStar_Syntax_Syntax.lbname = uu____575;
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
  'Auu____654 . 'Auu____654 Prims.list -> ('Auu____654 * 'Auu____654) =
  fun uu___0_665  ->
    match uu___0_665 with
    | a::b::[] -> (a, b)
    | uu____670 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_685  ->
    match uu___1_685 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____688 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____705 = FStar_Syntax_Subst.compress x  in
    match uu____705 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____717;
        FStar_Syntax_Syntax.vars = uu____718;_} ->
        let uu____728 =
          let uu____730 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____730  in
        (match uu____728 with
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
         | uu____749 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____752;
             FStar_Syntax_Syntax.vars = uu____753;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____755));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____756;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____757;_},uu____758)::[]);
        FStar_Syntax_Syntax.pos = uu____759;
        FStar_Syntax_Syntax.vars = uu____760;_} ->
        let uu____838 =
          let uu____840 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____840  in
        (match uu____838 with
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
         | uu____857 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____859));
        FStar_Syntax_Syntax.pos = uu____860;
        FStar_Syntax_Syntax.vars = uu____861;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____870));
        FStar_Syntax_Syntax.pos = uu____871;
        FStar_Syntax_Syntax.vars = uu____872;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____881));
        FStar_Syntax_Syntax.pos = uu____882;
        FStar_Syntax_Syntax.vars = uu____883;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____893);
        FStar_Syntax_Syntax.pos = uu____894;
        FStar_Syntax_Syntax.vars = uu____895;_} -> extract_meta x1
    | uu____914 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____950 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____950) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____1243  ->
             match uu____1243 with
             | (bv,uu____1377) ->
                 let uu____1388 =
                   let uu____1507 =
                     let uu____1510 =
                       let uu____1511 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____1511  in
                     FStar_Pervasives_Native.Some uu____1510  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____1507  in
                 let uu____1513 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____1388, uu____1513)) env bs
  
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
    let uu____2253 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____2255 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____2258 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____2260 =
      let uu____2262 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____2294 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____2296 =
                  let uu____2298 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____2298  in
                Prims.op_Hat uu____2294 uu____2296))
         in
      FStar_All.pipe_right uu____2262 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____2253 uu____2255
      uu____2258 uu____2260
  
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
          let uu____2626 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____2982 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____2982 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____3141,t2,l',nparams,uu____3145)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____3184 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____3184 with
                                           | (bs',body) ->
                                               let uu____3256 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____3256 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____3403  ->
                                                           fun uu____3404  ->
                                                             match (uu____3403,
                                                                    uu____3404)
                                                             with
                                                             | ((b',uu____3450),
                                                                (b,uu____3452))
                                                                 ->
                                                                 let uu____3503
                                                                   =
                                                                   let uu____3519
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____3519)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____3503)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____3550 =
                                                        let uu____3559 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____3559
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3550
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____3590 -> []))
                               in
                            let metadata =
                              let uu____3600 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____3607 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____3600 uu____3607  in
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
                   | uu____3827 -> (env1, [])) env ses
             in
          match uu____2626 with
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
    let uu___209_4594 = empty_iface  in
    {
      iface_module_name = (uu___209_4594.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___209_4594.iface_tydefs);
      iface_type_names = (uu___209_4594.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___212_4633 = empty_iface  in
    let uu____4642 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___212_4633.iface_module_name);
      iface_bindings = (uu___212_4633.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____4642
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___216_4697 = empty_iface  in
    {
      iface_module_name = (uu___216_4697.iface_module_name);
      iface_bindings = (uu___216_4697.iface_bindings);
      iface_tydefs = (uu___216_4697.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____4737 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____4737;
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
  'Auu____4820 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____4820 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____4860 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____4862 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____4864 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____4860 uu____4862
        uu____4864
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____4889  ->
      match uu____4889 with
      | (fv,exp_binding) ->
          let uu____4918 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____4920 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____4918 uu____4920
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____4951 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____4953 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____4951 uu____4953
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____4985 =
      let uu____4987 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____4987 (FStar_String.concat "\n")  in
    let uu____5008 =
      let uu____5010 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____5010 (FStar_String.concat "\n")  in
    let uu____5028 =
      let uu____5030 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____5030 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____4985 uu____5008
      uu____5028
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___2_5198  ->
           match uu___2_5198 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____5257 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____5269 =
      let uu____5271 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____5271 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____5269
  
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
          let uu____5604 =
            let uu____5675 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____5675 with
            | (tcenv,uu____5825,def_typ) ->
                let uu____5947 = as_pair def_typ  in (tcenv, uu____5947)
             in
          match uu____5604 with
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
                let uu____6297 =
                  let uu____6306 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____6306 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____6297 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____6350 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____6385 -> def  in
              let uu____6386 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6405) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____6462 -> ([], def1)  in
              (match uu____6386 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_6562  ->
                          match uu___3_6562 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____6565 -> false) quals
                      in
                   let uu____6567 = binders_as_mlty_binders env bs  in
                   (match uu____6567 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____6834 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____6834
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____6839 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_6846  ->
                                    match uu___4_6846 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____6848 -> true
                                    | uu____6860 -> false))
                             in
                          if uu____6839
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____6882 = extract_metadata attrs  in
                          let uu____6885 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____6882 uu____6885  in
                        let td =
                          let uu____6908 = lident_as_mlsymbol lid  in
                          (assumed, uu____6908, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____6920 =
                            let uu____6921 =
                              let uu____6922 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____6922
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____6921  in
                          [uu____6920;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____6923 =
                          let uu____6991 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_6997  ->
                                    match uu___5_6997 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____7001 -> false))
                             in
                          if uu____6991
                          then
                            let uu____7071 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____7071, (iface_of_type_names [fv]))
                          else
                            (let uu____7261 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____7261 with
                             | (env2,tydef) ->
                                 let uu____7536 = iface_of_tydefs [tydef]  in
                                 (env2, uu____7536))
                           in
                        (match uu____6923 with
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
          let uu____8208 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____8208 with
          | (bs,uu____8304) ->
              let uu____8343 = binders_as_mlty_binders env bs  in
              (match uu____8343 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____8641 = extract_metadata attrs  in
                     let uu____8644 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____8641 uu____8644  in
                   let assumed = false  in
                   let td =
                     let uu____8670 = lident_as_mlsymbol lid  in
                     (assumed, uu____8670, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____8683 =
                       let uu____8684 =
                         let uu____8685 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____8685
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____8684  in
                     [uu____8683; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____8686 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____8686 with
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
          let uu____9752 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____9752
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____9765 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____9765 with | (env2,uu____9913,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____10421 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____10421 with
        | (env_iparams,vars) ->
            let uu____10692 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____10692 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____11293,t,uu____11295,uu____11296,uu____11297);
            FStar_Syntax_Syntax.sigrng = uu____11298;
            FStar_Syntax_Syntax.sigquals = uu____11299;
            FStar_Syntax_Syntax.sigmeta = uu____11300;
            FStar_Syntax_Syntax.sigattrs = uu____11301;_}::[],uu____11302),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____11382 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____11382 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____11753),quals) ->
          let uu____11785 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____11785 with
           | (env1,ifams) ->
               let uu____12072 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____12072 with
                | (env2,td) ->
                    let uu____12450 =
                      let uu____12459 =
                        let uu____12468 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____12468  in
                      iface_union uu____12459
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____12450)))
      | uu____12573 -> failwith "Unexpected signature element"
  
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
              let uu____12983 =
                let uu____12985 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_12991  ->
                          match uu___6_12991 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____12994 -> false))
                   in
                Prims.op_Negation uu____12985  in
              if uu____12983
              then (g, empty_iface, [])
              else
                (let uu____13135 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____13135 with
                 | (bs,uu____13231) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____13292 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____13292;
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
        let uu____13863 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____13863 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____14137 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____14137
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
        (let uu____14298 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____14298
         then
           let uu____14303 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____14303
         else ());
        (let uu____14308 =
           let uu____14309 = FStar_Syntax_Subst.compress tm  in
           uu____14309.FStar_Syntax_Syntax.n  in
         match uu____14308 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____14328) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____14350 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____14350 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____14366;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____14367;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____14369;_} ->
                  let uu____14375 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____14375, tysc))
         | uu____14388 ->
             let uu____14389 =
               let uu____14391 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____14393 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____14391
                 uu____14393
                in
             failwith uu____14389)
         in
      let extract_action g1 a =
        (let uu____14625 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____14625
         then
           let uu____14630 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____14632 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____14630
             uu____14632
         else ());
        (let uu____14637 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____14637 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____14740 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____14740  in
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
             let uu____14871 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____14871 with
              | (a_let,uu____14953,ty) ->
                  ((let uu____14962 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____14962
                    then
                      let uu____14967 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____14967
                    else ());
                   (let uu____14972 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____15001,mllb::[]),uu____15003) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____15088 -> failwith "Impossible"  in
                    match uu____14972 with
                    | (exp,tysc) ->
                        ((let uu____15198 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____15198
                          then
                            ((let uu____15204 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____15204);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____15220 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____15220 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____15561 =
        let uu____15631 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____15631 with
        | (return_tm,ty_sc) ->
            let uu____15726 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____15726 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____15561 with
      | (g1,return_iface,return_decl) ->
          let uu____16015 =
            let uu____16085 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____16085 with
            | (bind_tm,ty_sc) ->
                let uu____16180 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____16180 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____16015 with
           | (g2,bind_iface,bind_decl) ->
               let uu____16469 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____16469 with
                | (g3,actions) ->
                    let uu____16831 = FStar_List.unzip actions  in
                    (match uu____16831 with
                     | (actions_iface,actions1) ->
                         let uu____16937 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____16937, (return_decl :: bind_decl ::
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
        let uu____17252 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____17271 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____17271) lbs
           in
        if uu____17252
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____17420 =
             FStar_List.fold_left
               (fun uu____17588  ->
                  fun lb  ->
                    match uu____17588 with
                    | (env1,iface_opt,impls) ->
                        let uu____17888 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____17888 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____18198 =
                                     iface_union iface' iface1  in
                                   FStar_Pervasives_Native.Some uu____18198
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____17420 with
           | (env1,iface_opt,impls) ->
               let uu____18569 = FStar_Option.get iface_opt  in
               let uu____18582 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____18569, uu____18582))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____18931 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____18949 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____18982 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____19033 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____19033 with | (env,iface1,uu____19174) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____19369) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____19414 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____19414 with | (env,iface1,uu____19555) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____19750) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____19799 = extract_let_rec_types se g lbs  in
          (match uu____19799 with | (env,iface1,uu____19940) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____20156 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____20162 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____20162)
             in
          if uu____20156
          then
            let uu____20232 =
              let uu____20309 =
                let uu____20310 =
                  let uu____20320 = always_fail lid t  in [uu____20320]  in
                (false, uu____20310)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____20309  in
            (match uu____20232 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____20702) ->
          let uu____20715 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____20715 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____21068 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21136 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____21220 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____21298 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21370 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____21519 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21623 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____21623
          then
            let uu____21704 = extract_reifiable_effect g ed  in
            (match uu____21704 with
             | (env,iface1,uu____21845) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____22316 = FStar_Options.interactive ()  in
      if uu____22316
      then (g, empty_iface)
      else
        (let uu____22451 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___610_22463 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___610_22463.iface_bindings);
             iface_tydefs = (uu___610_22463.iface_tydefs);
             iface_type_names = (uu___610_22463.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____22620  ->
                fun se  ->
                  match uu____22620 with
                  | (g1,iface2) ->
                      let uu____22889 = extract_sigelt_iface g1 se  in
                      (match uu____22889 with
                       | (g2,iface') ->
                           let uu____23152 = iface_union iface2 iface'  in
                           (g2, uu____23152))) (g, iface1) decls
            in
         (let uu____23288 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____23288);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____23502 = FStar_Options.debug_any ()  in
      if uu____23502
      then
        let uu____23572 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____23572
          (fun uu____23643  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___628_23842 = g  in
      let uu____23961 =
        let uu____23964 =
          FStar_List.map (fun _23978  -> FStar_Extraction_ML_UEnv.Fv _23978)
            iface1.iface_bindings
           in
        FStar_List.append uu____23964 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___628_23842.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____23961;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___628_23842.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____24620 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____24620
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____24628 =
            let uu____24629 =
              let uu____24640 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____24640  in
            uu____24629.FStar_Syntax_Syntax.n  in
          match uu____24628 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____24653) ->
              FStar_List.map
                (fun uu____24709  ->
                   match uu____24709 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____24723;
                        FStar_Syntax_Syntax.sort = uu____24724;_},uu____24725)
                       -> ppname.FStar_Ident.idText) bs
          | uu____24744 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____24758 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____24758 with
        | (env2,uu____24907,uu____24908) ->
            let uu____25037 =
              let uu____25050 = lident_as_mlsymbol ctor.dname  in
              let uu____25052 =
                let uu____25060 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____25060  in
              (uu____25050, uu____25052)  in
            (env2, uu____25037)
         in
      let extract_one_family env1 ind =
        let uu____25377 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____25377 with
        | (env_iparams,vars) ->
            let uu____25657 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____25657 with
             | (env2,ctors) ->
                 let uu____26130 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____26130 with
                  | (indices,uu____26240) ->
                      let ml_params =
                        let uu____26283 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____26319  ->
                                    let uu____26332 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____26332))
                           in
                        FStar_List.append vars uu____26283  in
                      let tbody =
                        let uu____26337 =
                          FStar_Util.find_opt
                            (fun uu___7_26342  ->
                               match uu___7_26342 with
                               | FStar_Syntax_Syntax.RecordType uu____26344
                                   -> true
                               | uu____26358 -> false) ind.iquals
                           in
                        match uu____26337 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____26378 = FStar_List.hd ctors  in
                            (match uu____26378 with
                             | (uu____26403,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____26449  ->
                                          match uu____26449 with
                                          | (uu____26462,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____26481 =
                                                lident_as_mlsymbol lid  in
                                              (uu____26481, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____26484 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____26487 =
                        let uu____26510 = lident_as_mlsymbol ind.iname  in
                        (false, uu____26510, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____26487)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____26673,t,uu____26675,uu____26676,uu____26677);
            FStar_Syntax_Syntax.sigrng = uu____26678;
            FStar_Syntax_Syntax.sigquals = uu____26679;
            FStar_Syntax_Syntax.sigmeta = uu____26680;
            FStar_Syntax_Syntax.sigattrs = uu____26681;_}::[],uu____26682),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____26762 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____26762 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____27110),quals) ->
          let uu____27142 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____27142 with
           | (env1,ifams) ->
               let uu____27427 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____27427 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____27900 -> failwith "Unexpected signature element"
  
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
             let uu____28170 = FStar_Syntax_Util.head_and_args t  in
             match uu____28170 with
             | (head1,args) ->
                 let uu____28242 =
                   let uu____28244 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____28244  in
                 if uu____28242
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____28263));
                         FStar_Syntax_Syntax.pos = uu____28264;
                         FStar_Syntax_Syntax.vars = uu____28265;_},uu____28266)::[]
                        ->
                        let uu____28321 =
                          let uu____28325 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____28325  in
                        FStar_Pervasives_Native.Some uu____28321
                    | uu____28331 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____28350 =
        let uu____28352 = FStar_Options.codegen ()  in
        uu____28352 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____28350
      then []
      else
        (let uu____28362 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____28362 with
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
                      let uu____28460 =
                        let uu____28461 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____28461  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____28460  in
                    let uu____28463 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____28463 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____28520 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____28520 with
                         | (register,args) ->
                             let h =
                               let uu____28596 =
                                 let uu____28597 =
                                   let uu____28598 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____28598
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____28597
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____28596
                                in
                             let arity1 =
                               let uu____28611 =
                                 let uu____28612 =
                                   let uu____28624 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____28624,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____28612
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____28611
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
              | uu____28700 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____28974 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____28974);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____29042 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____29060 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____29093 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____29146 = extract_reifiable_effect g ed  in
           (match uu____29146 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____29477 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____29558 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____29659 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____29659 with | (env,uu____29797,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____29991) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____30036 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____30036 with | (env,uu____30174,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____30368) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____30417 = extract_let_rec_types se g lbs  in
           (match uu____30417 with | (env,uu____30555,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____30749) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____30772 =
             let uu____30789 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____30789 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____30846) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____30772 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___858_31115 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___858_31115.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___858_31115.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___858_31115.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___858_31115.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___858_31115.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___858_31115.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____31145 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____31145)  in
                let uu____31231 =
                  let uu____31241 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____31241  in
                (match uu____31231 with
                 | (ml_let,uu____31336,uu____31337) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____31411) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____31452 =
                            FStar_List.fold_left2
                              (fun uu____31621  ->
                                 fun ml_lb  ->
                                   fun uu____31623  ->
                                     match (uu____31621, uu____31623) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____31860;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____31862;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____31863;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____31864;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____31865;_})
                                         ->
                                         let uu____32118 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____32118
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____32273 =
                                                let uu____32283 =
                                                  FStar_Util.right lbname  in
                                                uu____32283.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____32273.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____32305 =
                                                let uu____32306 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____32306.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____32305 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____32319,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____32320;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____32322;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____32323;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____32324;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____32325;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____32326;_})
                                                  when
                                                  let uu____32391 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____32391 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____32395 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___906_32412 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___906_32412.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___906_32412.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___906_32412.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___906_32412.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___906_32412.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____32425 =
                                              let uu____32495 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_32502  ->
                                                        match uu___8_32502
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____32504 ->
                                                            true
                                                        | uu____32516 ->
                                                            false))
                                                 in
                                              if uu____32495
                                              then
                                                let mname =
                                                  let uu____32597 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____32597
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____32618 =
                                                  let uu____32689 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____32704 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____32689 mname
                                                    uu____32704
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____32618 with
                                                | (env1,uu____32776,uu____32777)
                                                    ->
                                                    (env1,
                                                      (let uu___919_32972 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___919_32972.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___919_32972.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___919_32972.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___919_32972.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___919_32972.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____32991 =
                                                   let uu____33062 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____33062
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____32991 with
                                                 | (env1,uu____33134,uu____33135)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____32425 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____31452 with
                           | (g1,ml_lbs') ->
                               let uu____33889 =
                                 let uu____33892 =
                                   let uu____33895 =
                                     let uu____33896 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____33896
                                      in
                                   [uu____33895;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____33911 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____33892 uu____33911
                                  in
                               (g1, uu____33889))
                      | uu____33975 ->
                          let uu____33976 =
                            let uu____33978 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____33978
                             in
                          failwith uu____33976)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____34047,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____34068 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____34074 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____34074)
              in
           if uu____34068
           then
             let always_fail1 =
               let uu___939_34153 = se  in
               let uu____34164 =
                 let uu____34165 =
                   let uu____34176 =
                     let uu____34177 =
                       let uu____34187 = always_fail lid t  in [uu____34187]
                        in
                     (false, uu____34177)  in
                   (uu____34176, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____34165  in
               {
                 FStar_Syntax_Syntax.sigel = uu____34164;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___939_34153.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___939_34153.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___939_34153.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___939_34153.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____34237 = extract_sig g always_fail1  in
             (match uu____34237 with
              | (g1,mlm) ->
                  let uu____34492 =
                    FStar_Util.find_map quals
                      (fun uu___9_34505  ->
                         match uu___9_34505 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____34521 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____34492 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____34600 =
                         let uu____34603 =
                           let uu____34604 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____34604  in
                         let uu____34605 =
                           let uu____34608 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____34608]  in
                         uu____34603 :: uu____34605  in
                       (g1, uu____34600)
                   | uu____34670 ->
                       let uu____34677 =
                         FStar_Util.find_map quals
                           (fun uu___10_34691  ->
                              match uu___10_34691 with
                              | FStar_Syntax_Syntax.Projector (l,uu____34699)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____34716 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____34677 with
                        | FStar_Pervasives_Native.Some uu____34786 ->
                            (g1, [])
                        | uu____34856 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____34992 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____34992 with
            | (ml_main,uu____35068,uu____35069) ->
                let uu____35076 =
                  let uu____35079 =
                    let uu____35080 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____35080  in
                  [uu____35079; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____35076))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____35142 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____35229 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____35305 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____35375 -> (g, [])
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
      let uu____35797 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___982_35919 = g  in
        let uu____36038 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____36038;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___982_35919.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___982_35919.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___982_35919.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____36147 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____36353 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____36353
               then
                 let nm =
                   let uu____36423 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____36423
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____36448 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____36448
                     (fun uu____36517  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____36147 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____36717 = FStar_Options.codegen ()  in
            uu____36717 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____36792 =
                let uu____36794 = FStar_Options.silent ()  in
                Prims.op_Negation uu____36794  in
              if uu____36792
              then
                let uu____36797 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____36797
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
      (let uu____37192 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____37192);
      (let uu____37195 =
         let uu____37197 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____37197  in
       if uu____37195
       then
         let uu____37200 =
           let uu____37202 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____37202
            in
         failwith uu____37200
       else ());
      (let uu____37207 = FStar_Options.interactive ()  in
       if uu____37207
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____37408 = FStar_Options.debug_any ()  in
            if uu____37408
            then
              let msg =
                let uu____37479 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____37479  in
              FStar_Util.measure_execution_time msg
                (fun uu____37549  -> extract' g m)
            else extract' g m  in
          (let uu____37553 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____37553);
          res))
  
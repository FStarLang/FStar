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
    let uu____2237 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____2239 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____2242 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____2244 =
      let uu____2246 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____2278 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____2280 =
                  let uu____2282 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____2282  in
                Prims.op_Hat uu____2278 uu____2280))
         in
      FStar_All.pipe_right uu____2246 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____2237 uu____2239
      uu____2242 uu____2244
  
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
          let uu____2610 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____2966 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____2966 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____3125,t2,l',nparams,uu____3129)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____3168 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____3168 with
                                           | (bs',body) ->
                                               let uu____3240 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____3240 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____3387  ->
                                                           fun uu____3388  ->
                                                             match (uu____3387,
                                                                    uu____3388)
                                                             with
                                                             | ((b',uu____3434),
                                                                (b,uu____3436))
                                                                 ->
                                                                 let uu____3487
                                                                   =
                                                                   let uu____3503
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____3503)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____3487)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____3534 =
                                                        let uu____3543 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____3543
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3534
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____3574 -> []))
                               in
                            let metadata =
                              let uu____3584 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____3591 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____3584 uu____3591  in
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
                   | uu____3811 -> (env1, [])) env ses
             in
          match uu____2610 with
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
    let uu___209_4574 = empty_iface  in
    {
      iface_module_name = (uu___209_4574.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___209_4574.iface_tydefs);
      iface_type_names = (uu___209_4574.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___212_4613 = empty_iface  in
    let uu____4622 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___212_4613.iface_module_name);
      iface_bindings = (uu___212_4613.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____4622
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___216_4677 = empty_iface  in
    {
      iface_module_name = (uu___216_4677.iface_module_name);
      iface_bindings = (uu___216_4677.iface_bindings);
      iface_tydefs = (uu___216_4677.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____4717 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____4717;
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
  'Auu____4800 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____4800 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____4840 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____4842 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____4844 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____4840 uu____4842
        uu____4844
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____4869  ->
      match uu____4869 with
      | (fv,exp_binding) ->
          let uu____4898 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____4900 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____4898 uu____4900
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____4931 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____4933 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____4931 uu____4933
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____4965 =
      let uu____4967 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____4967 (FStar_String.concat "\n")  in
    let uu____4988 =
      let uu____4990 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____4990 (FStar_String.concat "\n")  in
    let uu____5008 =
      let uu____5010 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____5010 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____4965 uu____4988
      uu____5008
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___2_5178  ->
           match uu___2_5178 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____5237 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____5249 =
      let uu____5251 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____5251 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____5249
  
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
          let uu____5584 =
            let uu____5655 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____5655 with
            | (tcenv,uu____5805,def_typ) ->
                let uu____5927 = as_pair def_typ  in (tcenv, uu____5927)
             in
          match uu____5584 with
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
                let uu____6277 =
                  let uu____6286 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____6286 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____6277 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____6330 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____6365 -> def  in
              let uu____6366 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6385) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____6442 -> ([], def1)  in
              (match uu____6366 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_6542  ->
                          match uu___3_6542 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____6545 -> false) quals
                      in
                   let uu____6547 = binders_as_mlty_binders env bs  in
                   (match uu____6547 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____6814 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____6814
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____6819 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_6826  ->
                                    match uu___4_6826 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____6828 -> true
                                    | uu____6840 -> false))
                             in
                          if uu____6819
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____6862 = extract_metadata attrs  in
                          let uu____6865 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____6862 uu____6865  in
                        let td =
                          let uu____6888 = lident_as_mlsymbol lid  in
                          (assumed, uu____6888, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____6900 =
                            let uu____6901 =
                              let uu____6902 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____6902
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____6901  in
                          [uu____6900;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____6903 =
                          let uu____6971 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_6977  ->
                                    match uu___5_6977 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____6981 -> false))
                             in
                          if uu____6971
                          then
                            let uu____7051 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____7051, (iface_of_type_names [fv]))
                          else
                            (let uu____7241 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____7241 with
                             | (env2,tydef) ->
                                 let uu____7516 = iface_of_tydefs [tydef]  in
                                 (env2, uu____7516))
                           in
                        (match uu____6903 with
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
          let uu____8188 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____8188 with
          | (bs,uu____8284) ->
              let uu____8323 = binders_as_mlty_binders env bs  in
              (match uu____8323 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____8621 = extract_metadata attrs  in
                     let uu____8624 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____8621 uu____8624  in
                   let assumed = false  in
                   let td =
                     let uu____8650 = lident_as_mlsymbol lid  in
                     (assumed, uu____8650, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____8663 =
                       let uu____8664 =
                         let uu____8665 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____8665
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____8664  in
                     [uu____8663; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____8666 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____8666 with
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
          let uu____9732 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____9732
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____9745 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____9745 with | (env2,uu____9893,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____10401 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____10401 with
        | (env_iparams,vars) ->
            let uu____10672 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____10672 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____11273,t,uu____11275,uu____11276,uu____11277);
            FStar_Syntax_Syntax.sigrng = uu____11278;
            FStar_Syntax_Syntax.sigquals = uu____11279;
            FStar_Syntax_Syntax.sigmeta = uu____11280;
            FStar_Syntax_Syntax.sigattrs = uu____11281;_}::[],uu____11282),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____11362 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____11362 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____11733),quals) ->
          let uu____11765 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____11765 with
           | (env1,ifams) ->
               let uu____12052 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____12052 with
                | (env2,td) ->
                    let uu____12430 =
                      let uu____12439 =
                        let uu____12448 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____12448  in
                      iface_union uu____12439
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____12430)))
      | uu____12553 -> failwith "Unexpected signature element"
  
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
              let uu____12963 =
                let uu____12965 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_12971  ->
                          match uu___6_12971 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____12974 -> false))
                   in
                Prims.op_Negation uu____12965  in
              if uu____12963
              then (g, empty_iface, [])
              else
                (let uu____13115 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____13115 with
                 | (bs,uu____13211) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____13272 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____13272;
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
        let uu____13843 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____13843 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____14117 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____14117
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
        (let uu____14278 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____14278
         then
           let uu____14283 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____14283
         else ());
        (let uu____14288 =
           let uu____14289 = FStar_Syntax_Subst.compress tm  in
           uu____14289.FStar_Syntax_Syntax.n  in
         match uu____14288 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____14308) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____14330 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____14330 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____14346;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____14347;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____14349;_} ->
                  let uu____14355 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____14355, tysc))
         | uu____14368 ->
             let uu____14369 =
               let uu____14371 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____14373 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____14371
                 uu____14373
                in
             failwith uu____14369)
         in
      let extract_action g1 a =
        (let uu____14605 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____14605
         then
           let uu____14610 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____14612 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____14610
             uu____14612
         else ());
        (let uu____14617 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____14617 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____14720 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____14720  in
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
             let uu____14851 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____14851 with
              | (a_let,uu____14933,ty) ->
                  ((let uu____14942 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____14942
                    then
                      let uu____14947 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____14947
                    else ());
                   (let uu____14952 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____14981,mllb::[]),uu____14983) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____15068 -> failwith "Impossible"  in
                    match uu____14952 with
                    | (exp,tysc) ->
                        ((let uu____15178 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____15178
                          then
                            ((let uu____15184 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____15184);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____15200 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____15200 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____15541 =
        let uu____15611 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____15611 with
        | (return_tm,ty_sc) ->
            let uu____15706 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____15706 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____15541 with
      | (g1,return_iface,return_decl) ->
          let uu____15995 =
            let uu____16065 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____16065 with
            | (bind_tm,ty_sc) ->
                let uu____16160 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____16160 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____15995 with
           | (g2,bind_iface,bind_decl) ->
               let uu____16449 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____16449 with
                | (g3,actions) ->
                    let uu____16811 = FStar_List.unzip actions  in
                    (match uu____16811 with
                     | (actions_iface,actions1) ->
                         let uu____16917 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____16917, (return_decl :: bind_decl ::
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
        let uu____17232 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____17251 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____17251) lbs
           in
        if uu____17232
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____17400 =
             FStar_List.fold_left
               (fun uu____17568  ->
                  fun lb  ->
                    match uu____17568 with
                    | (env1,iface_opt,impls) ->
                        let uu____17868 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____17868 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____18178 =
                                     iface_union iface' iface1  in
                                   FStar_Pervasives_Native.Some uu____18178
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____17400 with
           | (env1,iface_opt,impls) ->
               let uu____18549 = FStar_Option.get iface_opt  in
               let uu____18562 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____18549, uu____18562))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____18911 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____18929 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____18962 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____19013 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____19013 with | (env,iface1,uu____19154) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____19349) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____19394 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____19394 with | (env,iface1,uu____19535) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____19730) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____19779 = extract_let_rec_types se g lbs  in
          (match uu____19779 with | (env,iface1,uu____19920) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____20136 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____20142 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____20142)
             in
          if uu____20136
          then
            let uu____20212 =
              let uu____20289 =
                let uu____20290 =
                  let uu____20300 = always_fail lid t  in [uu____20300]  in
                (false, uu____20290)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____20289  in
            (match uu____20212 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____20682) ->
          let uu____20695 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____20695 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____21048 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21116 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____21200 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____21278 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21350 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____21499 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21603 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____21603
          then
            let uu____21684 = extract_reifiable_effect g ed  in
            (match uu____21684 with
             | (env,iface1,uu____21825) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____22296 = FStar_Options.interactive ()  in
      if uu____22296
      then (g, empty_iface)
      else
        (let uu____22431 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___610_22443 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___610_22443.iface_bindings);
             iface_tydefs = (uu___610_22443.iface_tydefs);
             iface_type_names = (uu___610_22443.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____22600  ->
                fun se  ->
                  match uu____22600 with
                  | (g1,iface2) ->
                      let uu____22869 = extract_sigelt_iface g1 se  in
                      (match uu____22869 with
                       | (g2,iface') ->
                           let uu____23132 = iface_union iface2 iface'  in
                           (g2, uu____23132))) (g, iface1) decls
            in
         (let uu____23268 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____23268);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____23482 = FStar_Options.debug_any ()  in
      if uu____23482
      then
        let uu____23552 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____23552
          (fun uu____23623  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___628_23822 = g  in
      let uu____23941 =
        let uu____23944 =
          FStar_List.map (fun _23958  -> FStar_Extraction_ML_UEnv.Fv _23958)
            iface1.iface_bindings
           in
        FStar_List.append uu____23944 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___628_23822.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____23941;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___628_23822.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____24600 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____24600
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____24608 =
            let uu____24609 =
              let uu____24620 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____24620  in
            uu____24609.FStar_Syntax_Syntax.n  in
          match uu____24608 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____24633) ->
              FStar_List.map
                (fun uu____24689  ->
                   match uu____24689 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____24703;
                        FStar_Syntax_Syntax.sort = uu____24704;_},uu____24705)
                       -> ppname.FStar_Ident.idText) bs
          | uu____24724 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____24738 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____24738 with
        | (env2,uu____24887,uu____24888) ->
            let uu____25017 =
              let uu____25030 = lident_as_mlsymbol ctor.dname  in
              let uu____25032 =
                let uu____25040 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____25040  in
              (uu____25030, uu____25032)  in
            (env2, uu____25017)
         in
      let extract_one_family env1 ind =
        let uu____25357 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____25357 with
        | (env_iparams,vars) ->
            let uu____25637 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____25637 with
             | (env2,ctors) ->
                 let uu____26110 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____26110 with
                  | (indices,uu____26220) ->
                      let ml_params =
                        let uu____26263 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____26299  ->
                                    let uu____26312 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____26312))
                           in
                        FStar_List.append vars uu____26263  in
                      let tbody =
                        let uu____26317 =
                          FStar_Util.find_opt
                            (fun uu___7_26322  ->
                               match uu___7_26322 with
                               | FStar_Syntax_Syntax.RecordType uu____26324
                                   -> true
                               | uu____26338 -> false) ind.iquals
                           in
                        match uu____26317 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____26358 = FStar_List.hd ctors  in
                            (match uu____26358 with
                             | (uu____26383,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____26429  ->
                                          match uu____26429 with
                                          | (uu____26442,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____26461 =
                                                lident_as_mlsymbol lid  in
                                              (uu____26461, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____26464 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____26467 =
                        let uu____26490 = lident_as_mlsymbol ind.iname  in
                        (false, uu____26490, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____26467)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____26653,t,uu____26655,uu____26656,uu____26657);
            FStar_Syntax_Syntax.sigrng = uu____26658;
            FStar_Syntax_Syntax.sigquals = uu____26659;
            FStar_Syntax_Syntax.sigmeta = uu____26660;
            FStar_Syntax_Syntax.sigattrs = uu____26661;_}::[],uu____26662),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____26742 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____26742 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____27090),quals) ->
          let uu____27122 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____27122 with
           | (env1,ifams) ->
               let ifams1 =
                 FStar_All.pipe_right ifams
                   (FStar_List.filter
                      (fun fam  ->
                         let t = FStar_Syntax_Syntax.fv_to_tm fam.ifv  in
                         let uu____27477 =
                           FStar_TypeChecker_Util.must_erase_for_extraction
                             env1.FStar_Extraction_ML_UEnv.env_tcenv t
                            in
                         Prims.op_Negation uu____27477))
                  in
               let uu____27479 =
                 FStar_Util.fold_map extract_one_family env1 ifams1  in
               (match uu____27479 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____27952 -> failwith "Unexpected signature element"
  
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
             let uu____28222 = FStar_Syntax_Util.head_and_args t  in
             match uu____28222 with
             | (head1,args) ->
                 let uu____28294 =
                   let uu____28296 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____28296  in
                 if uu____28294
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____28315));
                         FStar_Syntax_Syntax.pos = uu____28316;
                         FStar_Syntax_Syntax.vars = uu____28317;_},uu____28318)::[]
                        ->
                        let uu____28373 =
                          let uu____28377 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____28377  in
                        FStar_Pervasives_Native.Some uu____28373
                    | uu____28383 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____28402 =
        let uu____28404 = FStar_Options.codegen ()  in
        uu____28404 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____28402
      then []
      else
        (let uu____28414 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____28414 with
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
                      let uu____28512 =
                        let uu____28513 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____28513  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____28512  in
                    let uu____28515 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____28515 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____28572 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____28572 with
                         | (register,args) ->
                             let h =
                               let uu____28648 =
                                 let uu____28649 =
                                   let uu____28650 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____28650
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____28649
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____28648
                                in
                             let arity1 =
                               let uu____28663 =
                                 let uu____28664 =
                                   let uu____28676 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____28676,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____28664
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____28663
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
              | uu____28752 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____29026 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____29026);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____29094 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____29112 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____29145 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____29198 = extract_reifiable_effect g ed  in
           (match uu____29198 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____29529 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____29610 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____29711 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____29711 with | (env,uu____29849,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____30043) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____30088 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____30088 with | (env,uu____30226,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____30420) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____30469 = extract_let_rec_types se g lbs  in
           (match uu____30469 with | (env,uu____30607,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____30801) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____30824 =
             let uu____30841 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____30841 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____30898) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____30824 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___861_31167 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___861_31167.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___861_31167.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___861_31167.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___861_31167.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___861_31167.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___861_31167.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____31197 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____31197)  in
                let uu____31283 =
                  let uu____31293 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____31293  in
                (match uu____31283 with
                 | (ml_let,uu____31388,uu____31389) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____31463) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____31504 =
                            FStar_List.fold_left2
                              (fun uu____31673  ->
                                 fun ml_lb  ->
                                   fun uu____31675  ->
                                     match (uu____31673, uu____31675) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____31912;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____31914;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____31915;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____31916;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____31917;_})
                                         ->
                                         let uu____32170 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____32170
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____32325 =
                                                let uu____32335 =
                                                  FStar_Util.right lbname  in
                                                uu____32335.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____32325.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____32357 =
                                                let uu____32358 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____32358.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____32357 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____32371,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____32372;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____32374;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____32375;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____32376;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____32377;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____32378;_})
                                                  when
                                                  let uu____32443 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____32443 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____32447 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___909_32464 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___909_32464.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___909_32464.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___909_32464.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___909_32464.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___909_32464.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____32477 =
                                              let uu____32547 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_32554  ->
                                                        match uu___8_32554
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____32556 ->
                                                            true
                                                        | uu____32568 ->
                                                            false))
                                                 in
                                              if uu____32547
                                              then
                                                let mname =
                                                  let uu____32649 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____32649
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____32670 =
                                                  let uu____32741 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____32756 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____32741 mname
                                                    uu____32756
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____32670 with
                                                | (env1,uu____32828,uu____32829)
                                                    ->
                                                    (env1,
                                                      (let uu___922_33024 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___922_33024.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___922_33024.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___922_33024.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___922_33024.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___922_33024.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____33043 =
                                                   let uu____33114 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____33114
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____33043 with
                                                 | (env1,uu____33186,uu____33187)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____32477 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____31504 with
                           | (g1,ml_lbs') ->
                               let uu____33941 =
                                 let uu____33944 =
                                   let uu____33947 =
                                     let uu____33948 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____33948
                                      in
                                   [uu____33947;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____33963 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____33944 uu____33963
                                  in
                               (g1, uu____33941))
                      | uu____34027 ->
                          let uu____34028 =
                            let uu____34030 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____34030
                             in
                          failwith uu____34028)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____34099,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____34120 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____34126 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____34126)
              in
           if uu____34120
           then
             let always_fail1 =
               let uu___942_34205 = se  in
               let uu____34216 =
                 let uu____34217 =
                   let uu____34228 =
                     let uu____34229 =
                       let uu____34239 = always_fail lid t  in [uu____34239]
                        in
                     (false, uu____34229)  in
                   (uu____34228, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____34217  in
               {
                 FStar_Syntax_Syntax.sigel = uu____34216;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___942_34205.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___942_34205.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___942_34205.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___942_34205.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____34289 = extract_sig g always_fail1  in
             (match uu____34289 with
              | (g1,mlm) ->
                  let uu____34544 =
                    FStar_Util.find_map quals
                      (fun uu___9_34557  ->
                         match uu___9_34557 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____34573 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____34544 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____34652 =
                         let uu____34655 =
                           let uu____34656 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____34656  in
                         let uu____34657 =
                           let uu____34660 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____34660]  in
                         uu____34655 :: uu____34657  in
                       (g1, uu____34652)
                   | uu____34722 ->
                       let uu____34729 =
                         FStar_Util.find_map quals
                           (fun uu___10_34743  ->
                              match uu___10_34743 with
                              | FStar_Syntax_Syntax.Projector (l,uu____34751)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____34768 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____34729 with
                        | FStar_Pervasives_Native.Some uu____34838 ->
                            (g1, [])
                        | uu____34908 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____35044 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____35044 with
            | (ml_main,uu____35120,uu____35121) ->
                let uu____35128 =
                  let uu____35131 =
                    let uu____35132 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____35132  in
                  [uu____35131; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____35128))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____35194 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____35281 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____35357 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____35427 -> (g, [])
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
      let uu____35849 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___985_35971 = g  in
        let uu____36090 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____36090;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___985_35971.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___985_35971.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___985_35971.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____36199 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____36405 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____36405
               then
                 let nm =
                   let uu____36475 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____36475
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____36500 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____36500
                     (fun uu____36569  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____36199 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____36769 = FStar_Options.codegen ()  in
            uu____36769 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____36844 =
                let uu____36846 = FStar_Options.silent ()  in
                Prims.op_Negation uu____36846  in
              if uu____36844
              then
                let uu____36849 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____36849
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
      (let uu____37244 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____37244);
      (let uu____37247 =
         let uu____37249 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____37249  in
       if uu____37247
       then
         let uu____37252 =
           let uu____37254 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____37254
            in
         failwith uu____37252
       else ());
      (let uu____37259 = FStar_Options.interactive ()  in
       if uu____37259
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____37460 = FStar_Options.debug_any ()  in
            if uu____37460
            then
              let msg =
                let uu____37531 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____37531  in
              FStar_Util.measure_execution_time msg
                (fun uu____37601  -> extract' g m)
            else extract' g m  in
          (let uu____37605 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____37605);
          res))
  
open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____68719 =
        let uu____68726 =
          let uu____68727 =
            let uu____68744 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____68747 =
              let uu____68758 = FStar_Syntax_Syntax.iarg t  in
              let uu____68767 =
                let uu____68778 =
                  let uu____68787 =
                    let uu____68788 =
                      let uu____68795 =
                        let uu____68796 =
                          let uu____68797 =
                            let uu____68803 =
                              let uu____68805 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____68805
                               in
                            (uu____68803, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____68797  in
                        FStar_Syntax_Syntax.Tm_constant uu____68796  in
                      FStar_Syntax_Syntax.mk uu____68795  in
                    uu____68788 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____68787
                   in
                [uu____68778]  in
              uu____68758 :: uu____68767  in
            (uu____68744, uu____68747)  in
          FStar_Syntax_Syntax.Tm_app uu____68727  in
        FStar_Syntax_Syntax.mk uu____68726  in
      uu____68719 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____68877 = FStar_Syntax_Util.arrow_formals t  in
        match uu____68877 with
        | ([],t1) ->
            let b =
              let uu____68920 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____68920
               in
            let uu____68928 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____68928
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____68965 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____68965 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____68969 =
          let uu____68974 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____68974  in
        {
          FStar_Syntax_Syntax.lbname = uu____68969;
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
  'Auu____68996 . 'Auu____68996 Prims.list -> ('Auu____68996 * 'Auu____68996)
  =
  fun uu___612_69007  ->
    match uu___612_69007 with
    | a::b::[] -> (a, b)
    | uu____69012 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_69027  ->
    match uu___613_69027 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____69030 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____69039 = FStar_Syntax_Subst.compress x  in
    match uu____69039 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____69043;
        FStar_Syntax_Syntax.vars = uu____69044;_} ->
        let uu____69047 =
          let uu____69049 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____69049  in
        (match uu____69047 with
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
         | uu____69059 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____69062;
             FStar_Syntax_Syntax.vars = uu____69063;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____69065));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____69066;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____69067;_},uu____69068)::[]);
        FStar_Syntax_Syntax.pos = uu____69069;
        FStar_Syntax_Syntax.vars = uu____69070;_} ->
        let uu____69113 =
          let uu____69115 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____69115  in
        (match uu____69113 with
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
         | uu____69124 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____69126));
        FStar_Syntax_Syntax.pos = uu____69127;
        FStar_Syntax_Syntax.vars = uu____69128;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____69133));
        FStar_Syntax_Syntax.pos = uu____69134;
        FStar_Syntax_Syntax.vars = uu____69135;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____69140));
        FStar_Syntax_Syntax.pos = uu____69141;
        FStar_Syntax_Syntax.vars = uu____69142;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____69148);
        FStar_Syntax_Syntax.pos = uu____69149;
        FStar_Syntax_Syntax.vars = uu____69150;_} -> extract_meta x1
    | uu____69157 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____69177 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____69177) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____69219  ->
             match uu____69219 with
             | (bv,uu____69230) ->
                 let uu____69231 =
                   let uu____69232 =
                     let uu____69235 =
                       let uu____69236 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____69236  in
                     FStar_Pervasives_Native.Some uu____69235  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____69232  in
                 let uu____69238 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____69231, uu____69238)) env bs
  
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
    let uu____69439 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____69441 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____69444 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____69446 =
      let uu____69448 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____69462 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____69464 =
                  let uu____69466 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____69466  in
                Prims.op_Hat uu____69462 uu____69464))
         in
      FStar_All.pipe_right uu____69448 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____69439 uu____69441
      uu____69444 uu____69446
  
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
          let uu____69520 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____69568 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____69568 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____69607,t2,l',nparams,uu____69611)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____69618 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____69618 with
                                           | (bs',body) ->
                                               let uu____69657 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____69657 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____69748  ->
                                                           fun uu____69749 
                                                             ->
                                                             match (uu____69748,
                                                                    uu____69749)
                                                             with
                                                             | ((b',uu____69775),
                                                                (b,uu____69777))
                                                                 ->
                                                                 let uu____69798
                                                                   =
                                                                   let uu____69805
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____69805)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____69798)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____69811 =
                                                        let uu____69812 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____69812
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____69811
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____69815 -> []))
                               in
                            let metadata =
                              let uu____69819 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____69822 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____69819 uu____69822  in
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
                   | uu____69829 -> (env1, [])) env ses
             in
          match uu____69520 with
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
    let uu___820_70009 = empty_iface  in
    {
      iface_module_name = (uu___820_70009.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___820_70009.iface_tydefs);
      iface_type_names = (uu___820_70009.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___823_70020 = empty_iface  in
    let uu____70021 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___823_70020.iface_module_name);
      iface_bindings = (uu___823_70020.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____70021
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___827_70036 = empty_iface  in
    {
      iface_module_name = (uu___827_70036.iface_module_name);
      iface_bindings = (uu___827_70036.iface_bindings);
      iface_tydefs = (uu___827_70036.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____70048 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____70048;
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
  'Auu____70093 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____70093 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____70125 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____70127 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____70129 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____70125 uu____70127
        uu____70129
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____70147  ->
      match uu____70147 with
      | (fv,exp_binding) ->
          let uu____70155 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____70157 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____70155 uu____70157
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____70172 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____70174 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____70172 uu____70174
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____70192 =
      let uu____70194 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____70194 (FStar_String.concat "\n")  in
    let uu____70208 =
      let uu____70210 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____70210 (FStar_String.concat "\n")  in
    let uu____70220 =
      let uu____70222 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____70222 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____70192 uu____70208
      uu____70220
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_70255  ->
           match uu___614_70255 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____70272 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____70277 =
      let uu____70279 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____70279 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____70277
  
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
          let uu____70339 =
            let uu____70348 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____70348 with
            | (tcenv,uu____70366,def_typ) ->
                let uu____70372 = as_pair def_typ  in (tcenv, uu____70372)
             in
          match uu____70339 with
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
                let uu____70403 =
                  let uu____70404 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____70404 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____70403 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____70412 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____70431 -> def  in
              let uu____70432 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____70443) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____70468 -> ([], def1)  in
              (match uu____70432 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_70488  ->
                          match uu___615_70488 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____70491 -> false) quals
                      in
                   let uu____70493 = binders_as_mlty_binders env bs  in
                   (match uu____70493 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____70520 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____70520
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____70525 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_70532  ->
                                    match uu___616_70532 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____70534 -> true
                                    | uu____70540 -> false))
                             in
                          if uu____70525
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____70554 = extract_metadata attrs  in
                          let uu____70557 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____70554 uu____70557  in
                        let td =
                          let uu____70580 = lident_as_mlsymbol lid  in
                          (assumed, uu____70580, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____70592 =
                            let uu____70593 =
                              let uu____70594 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____70594
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____70593
                             in
                          [uu____70592;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____70595 =
                          let uu____70600 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_70606  ->
                                    match uu___617_70606 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____70610 -> false))
                             in
                          if uu____70600
                          then
                            let uu____70617 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____70617, (iface_of_type_names [fv]))
                          else
                            (let uu____70620 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____70620 with
                             | (env2,tydef) ->
                                 let uu____70631 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____70631))
                           in
                        (match uu____70595 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____70707 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____70707
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____70714 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____70714 with | (env2,uu____70733,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____70772 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____70772 with
        | (env_iparams,vars) ->
            let uu____70800 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____70800 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____70864,t,uu____70866,uu____70867,uu____70868);
            FStar_Syntax_Syntax.sigrng = uu____70869;
            FStar_Syntax_Syntax.sigquals = uu____70870;
            FStar_Syntax_Syntax.sigmeta = uu____70871;
            FStar_Syntax_Syntax.sigattrs = uu____70872;_}::[],uu____70873),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____70892 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____70892 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____70925),quals) ->
          let uu____70939 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____70939 with
           | (env1,ifams) ->
               let uu____70956 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____70956 with
                | (env2,td) ->
                    let uu____70997 =
                      let uu____70998 =
                        let uu____70999 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____70999  in
                      iface_union uu____70998
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____70997)))
      | uu____71008 -> failwith "Unexpected signature element"
  
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
              let uu____71083 =
                let uu____71085 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_71091  ->
                          match uu___618_71091 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____71094 -> false))
                   in
                Prims.op_Negation uu____71085  in
              if uu____71083
              then (g, empty_iface, [])
              else
                (let uu____71109 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____71109 with
                 | (bs,uu____71133) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____71156 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____71156;
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
        let uu____71219 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____71219 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____71241 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____71241
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
        (let uu____71277 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71277
         then
           let uu____71282 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____71282
         else ());
        (let uu____71287 =
           let uu____71288 = FStar_Syntax_Subst.compress tm  in
           uu____71288.FStar_Syntax_Syntax.n  in
         match uu____71287 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____71296) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____71303 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____71303 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____71308;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____71309;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____71311;_} ->
                  let uu____71314 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____71314, tysc))
         | uu____71315 ->
             let uu____71316 =
               let uu____71318 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____71320 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____71318
                 uu____71320
                in
             failwith uu____71316)
         in
      let extract_action g1 a =
        (let uu____71348 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71348
         then
           let uu____71353 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____71355 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____71353
             uu____71355
         else ());
        (let uu____71360 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____71360 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____71380 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____71380  in
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
             let uu____71410 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____71410 with
              | (a_let,uu____71426,ty) ->
                  ((let uu____71429 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____71429
                    then
                      let uu____71434 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____71434
                    else ());
                   (let uu____71439 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____71462,mllb::[]),uu____71464) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____71504 -> failwith "Impossible"  in
                    match uu____71439 with
                    | (exp,tysc) ->
                        ((let uu____71542 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____71542
                          then
                            ((let uu____71548 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____71548);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____71564 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____71564 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____71586 =
        let uu____71593 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____71593 with
        | (return_tm,ty_sc) ->
            let uu____71610 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____71610 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____71586 with
      | (g1,return_iface,return_decl) ->
          let uu____71635 =
            let uu____71642 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____71642 with
            | (bind_tm,ty_sc) ->
                let uu____71659 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____71659 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____71635 with
           | (g2,bind_iface,bind_decl) ->
               let uu____71684 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____71684 with
                | (g3,actions) ->
                    let uu____71721 = FStar_List.unzip actions  in
                    (match uu____71721 with
                     | (actions_iface,actions1) ->
                         let uu____71748 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____71748, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____71770 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____71779 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____71796 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____71815 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____71815 with | (env,iface1,uu____71830) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____71836) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____71845 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____71845 with | (env,iface1,uu____71860) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____71871 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____71877 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____71877)
             in
          if uu____71871
          then
            let uu____71884 =
              let uu____71895 =
                let uu____71896 =
                  let uu____71899 = always_fail lid t  in [uu____71899]  in
                (false, uu____71896)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____71895  in
            (match uu____71884 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____71925) ->
          let uu____71930 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____71930 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____71959 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____71960 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____71961 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____71968 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____71969 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____71984 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____71997 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____71997
          then
            let uu____72010 = extract_reifiable_effect g ed  in
            (match uu____72010 with
             | (env,iface1,uu____72025) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____72047 = FStar_Options.interactive ()  in
      if uu____72047
      then (g, empty_iface)
      else
        (let uu____72056 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1166_72060 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1166_72060.iface_bindings);
             iface_tydefs = (uu___1166_72060.iface_tydefs);
             iface_type_names = (uu___1166_72060.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____72078  ->
                fun se  ->
                  match uu____72078 with
                  | (g1,iface2) ->
                      let uu____72090 = extract_sigelt_iface g1 se  in
                      (match uu____72090 with
                       | (g2,iface') ->
                           let uu____72101 = iface_union iface2 iface'  in
                           (g2, uu____72101))) (g, iface1) decls
            in
         (let uu____72103 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____72103);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____72120 = FStar_Options.debug_any ()  in
      if uu____72120
      then
        let uu____72127 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____72127
          (fun uu____72135  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1184_72149 = g  in
      let uu____72150 =
        let uu____72153 =
          FStar_List.map (fun _72160  -> FStar_Extraction_ML_UEnv.Fv _72160)
            iface1.iface_bindings
           in
        FStar_List.append uu____72153 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1184_72149.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____72150;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1184_72149.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____72238 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____72238
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____72246 =
            let uu____72247 =
              let uu____72250 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____72250  in
            uu____72247.FStar_Syntax_Syntax.n  in
          match uu____72246 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____72255) ->
              FStar_List.map
                (fun uu____72288  ->
                   match uu____72288 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____72297;
                        FStar_Syntax_Syntax.sort = uu____72298;_},uu____72299)
                       -> ppname.FStar_Ident.idText) bs
          | uu____72307 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____72315 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____72315 with
        | (env2,uu____72342,uu____72343) ->
            let uu____72346 =
              let uu____72359 = lident_as_mlsymbol ctor.dname  in
              let uu____72361 =
                let uu____72369 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____72369  in
              (uu____72359, uu____72361)  in
            (env2, uu____72346)
         in
      let extract_one_family env1 ind =
        let uu____72430 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____72430 with
        | (env_iparams,vars) ->
            let uu____72474 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____72474 with
             | (env2,ctors) ->
                 let uu____72581 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____72581 with
                  | (indices,uu____72623) ->
                      let ml_params =
                        let uu____72648 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____72674  ->
                                    let uu____72682 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____72682))
                           in
                        FStar_List.append vars uu____72648  in
                      let tbody =
                        let uu____72687 =
                          FStar_Util.find_opt
                            (fun uu___619_72692  ->
                               match uu___619_72692 with
                               | FStar_Syntax_Syntax.RecordType uu____72694
                                   -> true
                               | uu____72704 -> false) ind.iquals
                           in
                        match uu____72687 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____72716 = FStar_List.hd ctors  in
                            (match uu____72716 with
                             | (uu____72741,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____72785  ->
                                          match uu____72785 with
                                          | (uu____72796,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____72801 =
                                                lident_as_mlsymbol lid  in
                                              (uu____72801, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____72804 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____72807 =
                        let uu____72830 = lident_as_mlsymbol ind.iname  in
                        (false, uu____72830, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____72807)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____72875,t,uu____72877,uu____72878,uu____72879);
            FStar_Syntax_Syntax.sigrng = uu____72880;
            FStar_Syntax_Syntax.sigquals = uu____72881;
            FStar_Syntax_Syntax.sigmeta = uu____72882;
            FStar_Syntax_Syntax.sigattrs = uu____72883;_}::[],uu____72884),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____72903 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____72903 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____72956),quals) ->
          let uu____72970 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____72970 with
           | (env1,ifams) ->
               let uu____72989 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____72989 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____73098 -> failwith "Unexpected signature element"
  
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
             let uu____73156 = FStar_Syntax_Util.head_and_args t  in
             match uu____73156 with
             | (head1,args) ->
                 let uu____73204 =
                   let uu____73206 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____73206  in
                 if uu____73204
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____73225));
                         FStar_Syntax_Syntax.pos = uu____73226;
                         FStar_Syntax_Syntax.vars = uu____73227;_},uu____73228)::[]
                        ->
                        let uu____73267 =
                          let uu____73271 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____73271  in
                        FStar_Pervasives_Native.Some uu____73267
                    | uu____73277 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____73292 =
        let uu____73294 = FStar_Options.codegen ()  in
        uu____73294 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____73292
      then []
      else
        (let uu____73304 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____73304 with
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
                      let uu____73346 =
                        let uu____73347 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____73347  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____73346  in
                    let uu____73349 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____73349 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____73382 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____73382 with
                         | (register,args) ->
                             let h =
                               let uu____73419 =
                                 let uu____73420 =
                                   let uu____73421 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____73421
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____73420
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____73419
                                in
                             let arity1 =
                               let uu____73423 =
                                 let uu____73424 =
                                   let uu____73436 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____73436,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____73424
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____73423
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
              | uu____73465 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____73493 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____73493);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____73502 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____73511 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____73528 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____73545 = extract_reifiable_effect g ed  in
           (match uu____73545 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____73569 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____73583 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____73589 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____73589 with | (env,uu____73605,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____73614) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____73623 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____73623 with | (env,uu____73639,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____73648) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____73659 =
             let uu____73668 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____73668 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____73697) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____73659 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1403_73783 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1403_73783.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1403_73783.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1403_73783.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1403_73783.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1403_73783.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1403_73783.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____73792 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____73792)  in
                let uu____73810 =
                  let uu____73817 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____73817  in
                (match uu____73810 with
                 | (ml_let,uu____73834,uu____73835) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____73844) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____73861 =
                            FStar_List.fold_left2
                              (fun uu____73887  ->
                                 fun ml_lb  ->
                                   fun uu____73889  ->
                                     match (uu____73887, uu____73889) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____73911;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____73913;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____73914;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____73915;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____73916;_})
                                         ->
                                         let uu____73941 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____73941
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____73958 =
                                                let uu____73961 =
                                                  FStar_Util.right lbname  in
                                                uu____73961.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____73958.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____73965 =
                                                let uu____73966 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____73966.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____73965 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____73971,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____73972;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____73974;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____73975;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____73976;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____73977;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____73978;_})
                                                  when
                                                  let uu____74013 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____74013 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____74017 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1451_74022 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1451_74022.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1451_74022.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1451_74022.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1451_74022.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1451_74022.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____74023 =
                                              let uu____74028 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_74035  ->
                                                        match uu___620_74035
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____74037 ->
                                                            true
                                                        | uu____74043 ->
                                                            false))
                                                 in
                                              if uu____74028
                                              then
                                                let mname =
                                                  let uu____74059 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____74059
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____74068 =
                                                  let uu____74076 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____74077 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____74076 mname
                                                    uu____74077
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____74068 with
                                                | (env1,uu____74084,uu____74085)
                                                    ->
                                                    (env1,
                                                      (let uu___1464_74089 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1464_74089.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1464_74089.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1464_74089.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1464_74089.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1464_74089.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____74096 =
                                                   let uu____74104 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____74104
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____74096 with
                                                 | (env1,uu____74111,uu____74112)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____74023 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____73861 with
                           | (g1,ml_lbs') ->
                               let uu____74142 =
                                 let uu____74145 =
                                   let uu____74148 =
                                     let uu____74149 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____74149
                                      in
                                   [uu____74148;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____74152 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____74145 uu____74152
                                  in
                               (g1, uu____74142))
                      | uu____74157 ->
                          let uu____74158 =
                            let uu____74160 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____74160
                             in
                          failwith uu____74158)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____74170,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____74175 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____74181 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____74181)
              in
           if uu____74175
           then
             let always_fail1 =
               let uu___1484_74191 = se  in
               let uu____74192 =
                 let uu____74193 =
                   let uu____74200 =
                     let uu____74201 =
                       let uu____74204 = always_fail lid t  in [uu____74204]
                        in
                     (false, uu____74201)  in
                   (uu____74200, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____74193  in
               {
                 FStar_Syntax_Syntax.sigel = uu____74192;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1484_74191.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1484_74191.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1484_74191.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1484_74191.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____74211 = extract_sig g always_fail1  in
             (match uu____74211 with
              | (g1,mlm) ->
                  let uu____74230 =
                    FStar_Util.find_map quals
                      (fun uu___621_74235  ->
                         match uu___621_74235 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____74239 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____74230 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____74247 =
                         let uu____74250 =
                           let uu____74251 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____74251  in
                         let uu____74252 =
                           let uu____74255 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____74255]  in
                         uu____74250 :: uu____74252  in
                       (g1, uu____74247)
                   | uu____74258 ->
                       let uu____74261 =
                         FStar_Util.find_map quals
                           (fun uu___622_74267  ->
                              match uu___622_74267 with
                              | FStar_Syntax_Syntax.Projector (l,uu____74271)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____74272 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____74261 with
                        | FStar_Pervasives_Native.Some uu____74279 ->
                            (g1, [])
                        | uu____74282 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____74292 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____74292 with
            | (ml_main,uu____74306,uu____74307) ->
                let uu____74308 =
                  let uu____74311 =
                    let uu____74312 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____74312  in
                  [uu____74311; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____74308))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74315 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____74323 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____74332 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74335 -> (g, [])
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
      let uu____74377 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1527_74381 = g  in
        let uu____74382 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____74382;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1527_74381.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1527_74381.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1527_74381.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____74383 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____74402 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____74402
               then
                 let nm =
                   let uu____74413 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____74413
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____74430 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____74430
                     (fun uu____74440  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____74383 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____74462 = FStar_Options.codegen ()  in
            uu____74462 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____74477 =
                let uu____74479 = FStar_Options.silent ()  in
                Prims.op_Negation uu____74479  in
              if uu____74477
              then
                let uu____74482 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____74482
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
      (let uu____74557 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____74557);
      (let uu____74560 =
         let uu____74562 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____74562  in
       if uu____74560
       then
         let uu____74565 =
           let uu____74567 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____74567
            in
         failwith uu____74565
       else ());
      (let uu____74572 = FStar_Options.interactive ()  in
       if uu____74572
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____74592 = FStar_Options.debug_any ()  in
            if uu____74592
            then
              let msg =
                let uu____74603 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____74603  in
              FStar_Util.measure_execution_time msg
                (fun uu____74613  -> extract' g m)
            else extract' g m  in
          (let uu____74617 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____74617);
          res))
  
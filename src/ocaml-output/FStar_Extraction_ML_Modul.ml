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
        let uu____26 =
          let uu____43 =
            FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          let uu____46 =
            let uu____57 = FStar_Syntax_Syntax.iarg t  in
            let uu____66 =
              let uu____77 =
                let uu____86 =
                  let uu____87 =
                    let uu____88 =
                      let uu____89 =
                        let uu____95 =
                          let uu____97 = FStar_Syntax_Print.lid_to_string lid
                             in
                          Prims.op_Hat "Not yet implemented:" uu____97  in
                        (uu____95, FStar_Range.dummyRange)  in
                      FStar_Const.Const_string uu____89  in
                    FStar_Syntax_Syntax.Tm_constant uu____88  in
                  FStar_Syntax_Syntax.mk uu____87 FStar_Range.dummyRange  in
                FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____86  in
              [uu____77]  in
            uu____57 :: uu____66  in
          (uu____43, uu____46)  in
        FStar_Syntax_Syntax.Tm_app uu____26  in
      FStar_Syntax_Syntax.mk uu____25 FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____163 = FStar_Syntax_Util.arrow_formals t  in
        match uu____163 with
        | ([],t1) ->
            let b =
              let uu____190 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____190  in
            let uu____198 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____198 FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____219 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____219 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____223 =
          let uu____228 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____228  in
        {
          FStar_Syntax_Syntax.lbname = uu____223;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid;
          FStar_Syntax_Syntax.lbdef = imp;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = (imp.FStar_Syntax_Syntax.pos)
        }  in
      lb
  
let as_pair : 'uuuuuu236 . 'uuuuuu236 Prims.list -> ('uuuuuu236 * 'uuuuuu236)
  =
  fun uu___0_247  ->
    match uu___0_247 with
    | a::b::[] -> (a, b)
    | uu____252 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_267  ->
    match uu___1_267 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____270 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____279 = FStar_Syntax_Subst.compress x  in
    match uu____279 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____283;
        FStar_Syntax_Syntax.vars = uu____284;_} ->
        let uu____287 =
          let uu____289 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____289  in
        (match uu____287 with
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
         | uu____302 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____305;
             FStar_Syntax_Syntax.vars = uu____306;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____308));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____309;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____310;_},uu____311)::[]);
        FStar_Syntax_Syntax.pos = uu____312;
        FStar_Syntax_Syntax.vars = uu____313;_} ->
        let uu____356 =
          let uu____358 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____358  in
        (match uu____356 with
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
         | uu____368 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____370));
        FStar_Syntax_Syntax.pos = uu____371;
        FStar_Syntax_Syntax.vars = uu____372;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____377));
        FStar_Syntax_Syntax.pos = uu____378;
        FStar_Syntax_Syntax.vars = uu____379;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____384));
        FStar_Syntax_Syntax.pos = uu____385;
        FStar_Syntax_Syntax.vars = uu____386;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____392);
        FStar_Syntax_Syntax.pos = uu____393;
        FStar_Syntax_Syntax.vars = uu____394;_} -> extract_meta x1
    | uu____401 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'uuuuuu421 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu421) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlident
          Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____463  ->
             match uu____463 with
             | (bv,uu____474) ->
                 let env2 = FStar_Extraction_ML_UEnv.extend_ty env1 bv false
                    in
                 let name =
                   let uu____479 = FStar_Extraction_ML_UEnv.lookup_bv env2 bv
                      in
                   match uu____479 with
                   | FStar_Util.Inl ty ->
                       ty.FStar_Extraction_ML_UEnv.ty_b_name
                   | uu____482 -> failwith "Impossible"  in
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
    let uu____684 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____686 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____689 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____691 =
      let uu____693 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____707 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____709 =
                  let uu____711 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____711  in
                Prims.op_Hat uu____707 uu____709))
         in
      FStar_All.pipe_right uu____693 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____684 uu____686 uu____689
      uu____691
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        let uu____756 =
          FStar_Util.fold_map
            (fun env1  ->
               fun se  ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l,us,bs,t,_mut_i,datas) ->
                     let uu____809 = FStar_Syntax_Subst.open_univ_vars us t
                        in
                     (match uu____809 with
                      | (_us,t1) ->
                          let uu____822 = FStar_Syntax_Subst.open_term bs t1
                             in
                          (match uu____822 with
                           | (bs1,t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1  ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d,us1,t3,l',nparams,uu____868)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____875 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3
                                                in
                                             (match uu____875 with
                                              | (_us1,t4) ->
                                                  let uu____884 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4
                                                     in
                                                  (match uu____884 with
                                                   | (bs',body) ->
                                                       let uu____899 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs'
                                                          in
                                                       (match uu____899 with
                                                        | (bs_params,rest) ->
                                                            let subst =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____990 
                                                                   ->
                                                                   fun
                                                                    uu____991
                                                                     ->
                                                                    match 
                                                                    (uu____990,
                                                                    uu____991)
                                                                    with
                                                                    | 
                                                                    ((b',uu____1017),
                                                                    (b,uu____1019))
                                                                    ->
                                                                    let uu____1040
                                                                    =
                                                                    let uu____1047
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                    (b',
                                                                    uu____1047)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____1040)
                                                                bs_params bs1
                                                               in
                                                            let t5 =
                                                              let uu____1053
                                                                =
                                                                let uu____1054
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____1054
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____1053
                                                                (FStar_Syntax_Subst.subst
                                                                   subst)
                                                               in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____1057 -> []))
                                  in
                               let metadata =
                                 let uu____1061 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs
                                    in
                                 let uu____1064 =
                                   FStar_List.choose flag_of_qual quals  in
                                 FStar_List.append uu____1061 uu____1064  in
                               let fv =
                                 FStar_Syntax_Syntax.lid_as_fv l
                                   FStar_Syntax_Syntax.delta_constant
                                   FStar_Pervasives_Native.None
                                  in
                               let uu____1068 =
                                 FStar_Extraction_ML_UEnv.extend_type_name
                                   env1 fv
                                  in
                               (match uu____1068 with
                                | (uu____1079,env2) ->
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
                                       }]))))
                 | uu____1083 -> (env1, [])) env ses
           in
        match uu____756 with
        | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type iface =
  {
  iface_module_name: FStar_Extraction_ML_Syntax.mlpath ;
  iface_bindings:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list
    ;
  iface_tydefs: FStar_Extraction_ML_UEnv.tydef Prims.list ;
  iface_type_names:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list }
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
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
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
    let uu___221_1295 = empty_iface  in
    {
      iface_module_name = (uu___221_1295.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___221_1295.iface_tydefs);
      iface_type_names = (uu___221_1295.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___224_1306 = empty_iface  in
    let uu____1307 =
      FStar_List.map
        (fun td  ->
           let uu____1322 = FStar_Extraction_ML_UEnv.tydef_fv td  in
           let uu____1323 = FStar_Extraction_ML_UEnv.tydef_mlpath td  in
           (uu____1322, uu____1323)) tds
       in
    {
      iface_module_name = (uu___224_1306.iface_module_name);
      iface_bindings = (uu___224_1306.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1307
    }
  
let (iface_of_type_names :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list ->
    iface)
  =
  fun fvs  ->
    let uu___228_1342 = empty_iface  in
    {
      iface_module_name = (uu___228_1342.iface_module_name);
      iface_bindings = (uu___228_1342.iface_bindings);
      iface_tydefs = (uu___228_1342.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1354 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1354;
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
  'uuuuuu1403 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('uuuuuu1403 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____1435 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1437 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      FStar_Util.format3
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1435 uu____1437
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1455  ->
      match uu____1455 with
      | (fv,exp_binding) ->
          let uu____1463 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1465 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1463 uu____1465
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1480 =
        let uu____1482 = FStar_Extraction_ML_UEnv.tydef_fv tydef  in
        FStar_Syntax_Print.fv_to_string uu____1482  in
      let uu____1483 =
        let uu____1485 = FStar_Extraction_ML_UEnv.tydef_def tydef  in
        tscheme_to_string cm uu____1485  in
      FStar_Util.format2 "(%s, %s)" uu____1480 uu____1483
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name uu____1509 =
      match uu____1509 with
      | (tn,uu____1516) -> FStar_Syntax_Print.fv_to_string tn  in
    let uu____1517 =
      let uu____1519 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1519 (FStar_String.concat "\n")  in
    let uu____1533 =
      let uu____1535 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1535 (FStar_String.concat "\n")  in
    let uu____1545 =
      let uu____1547 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1547 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1517 uu____1533
      uu____1545
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
    let gamma =
      let uu____1577 = FStar_Extraction_ML_UEnv.bindings_of_uenv env  in
      FStar_List.collect
        (fun uu___2_1587  ->
           match uu___2_1587 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1604 -> []) uu____1577
       in
    let uu____1609 =
      let uu____1611 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1611 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1609
  
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
          let uu____1671 =
            let uu____1680 =
              let uu____1689 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
              FStar_TypeChecker_Env.open_universes_in uu____1689
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1680 with
            | (tcenv,uu____1699,def_typ) ->
                let uu____1705 = as_pair def_typ  in (tcenv, uu____1705)
             in
          match uu____1671 with
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
                let uu____1736 =
                  let uu____1737 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1737 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1736 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1745 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1764 -> def  in
              let uu____1765 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1776) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1801 -> ([], def1)  in
              (match uu____1765 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1821  ->
                          match uu___3_1821 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1824 -> false) quals
                      in
                   let uu____1826 = binders_as_mlty_binders env bs  in
                   (match uu____1826 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1853 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1853
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let metadata =
                          let uu____1857 = extract_metadata attrs  in
                          let uu____1860 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1857 uu____1860  in
                        let tyscheme = (ml_bs, body1)  in
                        let uu____1868 =
                          let uu____1883 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1889  ->
                                    match uu___4_1889 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1893 -> false))
                             in
                          if uu____1883
                          then
                            let uu____1910 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            match uu____1910 with
                            | (mlp,env2) ->
                                (mlp, (iface_of_type_names [(fv, mlp)]),
                                  env2)
                          else
                            (let uu____1949 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 tyscheme
                                in
                             match uu____1949 with
                             | (td,mlp,env2) ->
                                 let uu____1973 = iface_of_tydefs [td]  in
                                 (mlp, uu____1973, env2))
                           in
                        (match uu____1868 with
                         | (mlpath,iface1,env2) ->
                             let td =
                               (assumed,
                                 (FStar_Pervasives_Native.snd mlpath),
                                 FStar_Pervasives_Native.None, ml_bs,
                                 metadata,
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Extraction_ML_Syntax.MLTD_Abbrev
                                       body1)))
                                in
                             let def2 =
                               let uu____2044 =
                                 let uu____2045 =
                                   let uu____2046 =
                                     FStar_Ident.range_of_lid lid  in
                                   FStar_Extraction_ML_Util.mlloc_of_range
                                     uu____2046
                                    in
                                 FStar_Extraction_ML_Syntax.MLM_Loc
                                   uu____2045
                                  in
                               [uu____2044;
                               FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                             (env2, iface1, def2))))
  
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
            let uu____2095 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] uu____2095
              lb.FStar_Syntax_Syntax.lbtyp
             in
          let uu____2096 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____2096 with
          | (bs,uu____2112) ->
              let uu____2117 = binders_as_mlty_binders env bs  in
              (match uu____2117 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____2149 = extract_metadata attrs  in
                     let uu____2152 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____2149 uu____2152  in
                   let assumed = false  in
                   let tscheme = (ml_bs, body)  in
                   let uu____2163 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv tscheme  in
                   (match uu____2163 with
                    | (tydef,mlp,env2) ->
                        let td =
                          (assumed, (FStar_Pervasives_Native.snd mlp),
                            FStar_Pervasives_Native.None, ml_bs, metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                           in
                        let def =
                          let uu____2216 =
                            let uu____2217 =
                              let uu____2218 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____2218
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____2217  in
                          [uu____2216;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
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
          let uu____2285 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2285
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____2292 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false  in
        match uu____2292 with | (env2,uu____2310,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2349 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2349 with
        | (env_iparams,vars) ->
            let uu____2377 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2377 with
             | (env2,ctors) ->
                 let env3 =
                   let uu____2429 =
                     FStar_Util.find_opt
                       (fun uu___5_2434  ->
                          match uu___5_2434 with
                          | FStar_Syntax_Syntax.RecordType uu____2436 -> true
                          | uu____2446 -> false) ind.iquals
                      in
                   match uu____2429 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                       let g =
                         FStar_List.fold_right
                           (fun id  ->
                              fun g  ->
                                let uu____2466 =
                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                    g ((ind.iname), id)
                                   in
                                match uu____2466 with | (mlp,g1) -> g1) ids
                           env2
                          in
                       g
                   | uu____2473 -> env2  in
                 (env3, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2489,t,uu____2491,uu____2492,uu____2493);
            FStar_Syntax_Syntax.sigrng = uu____2494;
            FStar_Syntax_Syntax.sigquals = uu____2495;
            FStar_Syntax_Syntax.sigmeta = uu____2496;
            FStar_Syntax_Syntax.sigattrs = uu____2497;
            FStar_Syntax_Syntax.sigopts = uu____2498;_}::[],uu____2499),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2520 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2520 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2553),quals) ->
          let uu____2567 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____2567
          then (env, empty_iface)
          else
            (let uu____2576 = bundle_as_inductive_families env ses quals  in
             match uu____2576 with
             | (env1,ifams) ->
                 let uu____2593 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____2593 with
                  | (env2,td) ->
                      let uu____2634 =
                        let uu____2635 =
                          let uu____2636 =
                            FStar_List.map
                              (fun x  ->
                                 let uu____2650 =
                                   FStar_Extraction_ML_UEnv.mlpath_of_lident
                                     env2 x.iname
                                    in
                                 ((x.ifv), uu____2650)) ifams
                             in
                          iface_of_type_names uu____2636  in
                        iface_union uu____2635
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____2634)))
      | uu____2655 -> failwith "Unexpected signature element"
  
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
          fun univs  ->
            fun t  ->
              let uu____2730 =
                let uu____2732 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2738  ->
                          match uu___6_2738 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2741 -> false))
                   in
                Prims.op_Negation uu____2732  in
              if uu____2730
              then (g, empty_iface, [])
              else
                (let uu____2756 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2756 with
                 | (bs,uu____2772) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2779 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2779;
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
      let extend_iface lid mlp exp exp_binding =
        let fv =
          FStar_Syntax_Syntax.lid_as_fv lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        let lb =
          {
            FStar_Extraction_ML_Syntax.mllb_name =
              (FStar_Pervasives_Native.snd mlp);
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.None;
            FStar_Extraction_ML_Syntax.mllb_add_unit = false;
            FStar_Extraction_ML_Syntax.mllb_def = exp;
            FStar_Extraction_ML_Syntax.mllb_meta = [];
            FStar_Extraction_ML_Syntax.print_typ = false
          }  in
        ((iface_of_bindings [(fv, exp_binding)]),
          (FStar_Extraction_ML_Syntax.MLM_Let
             (FStar_Extraction_ML_Syntax.NonRec, [lb])))
         in
      let rec extract_fv tm =
        (let uu____2883 =
           let uu____2885 =
             let uu____2891 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.debug uu____2891  in
           FStar_All.pipe_left uu____2885
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2883
         then
           let uu____2895 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2895
         else ());
        (let uu____2900 =
           let uu____2901 = FStar_Syntax_Subst.compress tm  in
           uu____2901.FStar_Syntax_Syntax.n  in
         match uu____2900 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2909) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_UEnv.mlpath_of_lident g
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2916 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2916 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2921;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2922;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;_} ->
                  let uu____2925 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2925, tysc))
         | uu____2926 ->
             let uu____2927 =
               let uu____2929 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2931 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2929 uu____2931
                in
             failwith uu____2927)
         in
      let extract_action g1 a =
        (let uu____2959 =
           let uu____2961 =
             let uu____2967 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
             FStar_TypeChecker_Env.debug uu____2967  in
           FStar_All.pipe_left uu____2961
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2959
         then
           let uu____2971 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2973 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2971
             uu____2973
         else ());
        (let lbname =
           let uu____2983 =
             FStar_Syntax_Syntax.new_bv
               (FStar_Pervasives_Native.Some
                  ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
               FStar_Syntax_Syntax.tun
              in
           FStar_Util.Inl uu____2983  in
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
             (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
            in
         let uu____3013 =
           FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
         match uu____3013 with
         | (a_let,uu____3029,ty) ->
             let uu____3031 =
               match a_let.FStar_Extraction_ML_Syntax.expr with
               | FStar_Extraction_ML_Syntax.MLE_Let
                   ((uu____3048,mllb::[]),uu____3050) ->
                   (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc with
                    | FStar_Pervasives_Native.Some tysc ->
                        ((mllb.FStar_Extraction_ML_Syntax.mllb_def), tysc)
                    | FStar_Pervasives_Native.None  ->
                        failwith "No type scheme")
               | uu____3081 -> failwith "Impossible"  in
             (match uu____3031 with
              | (exp,tysc) ->
                  let uu____3109 =
                    FStar_Extraction_ML_UEnv.extend_with_action_name g1 ed a
                      tysc
                     in
                  (match uu____3109 with
                   | (a_nm,a_lid,exp_b,g2) ->
                       ((let uu____3131 =
                           let uu____3133 =
                             let uu____3139 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2  in
                             FStar_TypeChecker_Env.debug uu____3139  in
                           FStar_All.pipe_left uu____3133
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____3131
                         then
                           let uu____3143 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____3143
                         else ());
                        (let uu____3149 =
                           let uu____3151 =
                             let uu____3157 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2  in
                             FStar_TypeChecker_Env.debug uu____3157  in
                           FStar_All.pipe_left uu____3151
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____3149
                         then
                           ((let uu____3162 =
                               FStar_Extraction_ML_Code.string_of_mlty a_nm
                                 (FStar_Pervasives_Native.snd tysc)
                                in
                             FStar_Util.print1 "Extracted action type: %s\n"
                               uu____3162);
                            FStar_List.iter
                              (fun x  ->
                                 FStar_Util.print1 "and binders: %s\n" x)
                              (FStar_Pervasives_Native.fst tysc))
                         else ());
                        (let uu____3172 = extend_iface a_lid a_nm exp exp_b
                            in
                         match uu____3172 with
                         | (iface1,impl) -> (g2, (iface1, impl)))))))
         in
      let uu____3191 =
        let uu____3198 =
          let uu____3203 =
            let uu____3206 =
              let uu____3215 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr  in
              FStar_All.pipe_right uu____3215 FStar_Util.must  in
            FStar_All.pipe_right uu____3206 FStar_Pervasives_Native.snd  in
          extract_fv uu____3203  in
        match uu____3198 with
        | (return_tm,ty_sc) ->
            let uu____3284 =
              FStar_Extraction_ML_UEnv.extend_with_monad_op_name g ed
                "return" ty_sc
               in
            (match uu____3284 with
             | (return_nm,return_lid,return_b,g1) ->
                 let uu____3304 =
                   extend_iface return_lid return_nm return_tm return_b  in
                 (match uu____3304 with | (iface1,impl) -> (g1, iface1, impl)))
         in
      match uu____3191 with
      | (g1,return_iface,return_decl) ->
          let uu____3328 =
            let uu____3335 =
              let uu____3340 =
                let uu____3343 =
                  let uu____3352 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr
                     in
                  FStar_All.pipe_right uu____3352 FStar_Util.must  in
                FStar_All.pipe_right uu____3343 FStar_Pervasives_Native.snd
                 in
              extract_fv uu____3340  in
            match uu____3335 with
            | (bind_tm,ty_sc) ->
                let uu____3421 =
                  FStar_Extraction_ML_UEnv.extend_with_monad_op_name g1 ed
                    "bind" ty_sc
                   in
                (match uu____3421 with
                 | (bind_nm,bind_lid,bind_b,g2) ->
                     let uu____3441 =
                       extend_iface bind_lid bind_nm bind_tm bind_b  in
                     (match uu____3441 with
                      | (iface1,impl) -> (g2, iface1, impl)))
             in
          (match uu____3328 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3465 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3465 with
                | (g3,actions) ->
                    let uu____3502 = FStar_List.unzip actions  in
                    (match uu____3502 with
                     | (actions_iface,actions1) ->
                         let uu____3529 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3529, (return_decl :: bind_decl ::
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
        let uu____3560 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____3565 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____3565) lbs
           in
        if uu____3560
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3588 =
             FStar_List.fold_left
               (fun uu____3623  ->
                  fun lb  ->
                    match uu____3623 with
                    | (env1,iface_opt,impls) ->
                        let uu____3664 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____3664 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3698 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____3698
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____3588 with
           | (env1,iface_opt,impls) ->
               let uu____3738 = FStar_Option.get iface_opt  in
               let uu____3739 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____3738, uu____3739))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3771 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3780 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3797 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3816 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs t
             in
          (match uu____3816 with | (env,iface1,uu____3831) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3837) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3846 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3846 with | (env,iface1,uu____3861) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____3867) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3880 = extract_let_rec_types se g lbs  in
          (match uu____3880 with | (env,iface1,uu____3895) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3906 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3912 =
                 let uu____3914 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                    in
                 FStar_TypeChecker_Util.must_erase_for_extraction uu____3914
                   t
                  in
               Prims.op_Negation uu____3912)
             in
          if uu____3906
          then
            let uu____3920 =
              let uu____3931 =
                let uu____3932 =
                  let uu____3935 = always_fail lid t  in [uu____3935]  in
                (false, uu____3932)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3931  in
            (match uu____3920 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3961) ->
          let uu____3966 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3966 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_assume uu____3995 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4002 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4003 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____4016 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____4029 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_fail uu____4041 ->
          failwith "impossible: trying to extract Sig_fail"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4060 =
            (let uu____4064 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.is_reifiable_effect uu____4064
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____4060
          then
            let uu____4076 = extract_reifiable_effect g ed  in
            (match uu____4076 with | (env,iface1,uu____4091) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4113 = FStar_Options.interactive ()  in
      if uu____4113
      then (g, empty_iface)
      else
        (let uu____4122 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___647_4126 = empty_iface  in
           let uu____4127 = FStar_Extraction_ML_UEnv.current_module_of_uenv g
              in
           {
             iface_module_name = uu____4127;
             iface_bindings = (uu___647_4126.iface_bindings);
             iface_tydefs = (uu___647_4126.iface_tydefs);
             iface_type_names = (uu___647_4126.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____4145  ->
                fun se  ->
                  match uu____4145 with
                  | (g1,iface2) ->
                      let uu____4157 = extract_sigelt_iface g1 se  in
                      (match uu____4157 with
                       | (g2,iface') ->
                           let uu____4168 = iface_union iface2 iface'  in
                           (g2, uu____4168))) (g, iface1) decls
            in
         (let uu____4170 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun uu____4172  -> ()) uu____4170);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4188 =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____4200  ->
             let uu____4201 = FStar_Options.debug_any ()  in
             if uu____4201
             then
               let uu____4208 =
                 let uu____4210 =
                   FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name
                    in
                 FStar_Util.format1 "Extracted interface of %s" uu____4210
                  in
               FStar_Util.measure_execution_time uu____4208
                 (fun uu____4218  -> extract_iface' g modul)
             else extract_iface' g modul)
         in
      match uu____4188 with
      | (g1,iface1) ->
          let uu____4227 = FStar_Extraction_ML_UEnv.exit_module g1  in
          (uu____4227, iface1)
  
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
          let uu____4305 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4305
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names =
          let uu____4313 =
            let uu____4314 =
              let uu____4317 =
                let uu____4318 =
                  FStar_Extraction_ML_UEnv.tcenv_of_uenv env_iparams  in
                FStar_TypeChecker_Normalize.normalize steps uu____4318
                  ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4317  in
            uu____4314.FStar_Syntax_Syntax.n  in
          match uu____4313 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4323) ->
              FStar_List.map
                (fun uu____4356  ->
                   match uu____4356 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4365;
                        FStar_Syntax_Syntax.sort = uu____4366;_},uu____4367)
                       -> FStar_Ident.string_of_id ppname) bs
          | uu____4375 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____4383 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false  in
        match uu____4383 with
        | (env2,mls,uu____4410) ->
            let uu____4413 =
              let uu____4426 =
                let uu____4434 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names uu____4434  in
              (mls, uu____4426)  in
            (env2, uu____4413)
         in
      let extract_one_family env1 ind =
        let uu____4495 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4495 with
        | (env_iparams,vars) ->
            let uu____4539 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____4539 with
             | (env2,ctors) ->
                 let uu____4646 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____4646 with
                  | (indices,uu____4680) ->
                      let ml_params =
                        let uu____4689 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____4715  ->
                                    let uu____4723 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____4723))
                           in
                        FStar_List.append vars uu____4689  in
                      let uu____4727 =
                        let uu____4734 =
                          FStar_Util.find_opt
                            (fun uu___7_4739  ->
                               match uu___7_4739 with
                               | FStar_Syntax_Syntax.RecordType uu____4741 ->
                                   true
                               | uu____4751 -> false) ind.iquals
                           in
                        match uu____4734 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____4769 = FStar_List.hd ctors  in
                            (match uu____4769 with
                             | (uu____4800,c_ty) ->
                                 let uu____4819 =
                                   FStar_List.fold_right2
                                     (fun id  ->
                                        fun uu____4858  ->
                                          fun uu____4859  ->
                                            match (uu____4858, uu____4859)
                                            with
                                            | ((uu____4903,ty),(fields,g)) ->
                                                let uu____4939 =
                                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                                    g ((ind.iname), id)
                                                   in
                                                (match uu____4939 with
                                                 | (mlp,g1) ->
                                                     ((((FStar_Pervasives_Native.snd
                                                           mlp), ty) ::
                                                       fields), g1))) ids
                                     c_ty ([], env2)
                                    in
                                 (match uu____4819 with
                                  | (fields,g) ->
                                      ((FStar_Pervasives_Native.Some
                                          (FStar_Extraction_ML_Syntax.MLTD_Record
                                             fields)), g)))
                        | uu____5010 when
                            (FStar_List.length ctors) = Prims.int_zero ->
                            (FStar_Pervasives_Native.None, env2)
                        | uu____5029 ->
                            ((FStar_Pervasives_Native.Some
                                (FStar_Extraction_ML_Syntax.MLTD_DType ctors)),
                              env2)
                         in
                      (match uu____4727 with
                       | (tbody,env3) ->
                           let uu____5066 =
                             let uu____5089 =
                               let uu____5091 =
                                 FStar_Extraction_ML_UEnv.mlpath_of_lident
                                   env3 ind.iname
                                  in
                               FStar_Pervasives_Native.snd uu____5091  in
                             (false, uu____5089,
                               FStar_Pervasives_Native.None, ml_params,
                               (ind.imetadata), tbody)
                              in
                           (env3, uu____5066))))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____5147,t,uu____5149,uu____5150,uu____5151);
            FStar_Syntax_Syntax.sigrng = uu____5152;
            FStar_Syntax_Syntax.sigquals = uu____5153;
            FStar_Syntax_Syntax.sigmeta = uu____5154;
            FStar_Syntax_Syntax.sigattrs = uu____5155;
            FStar_Syntax_Syntax.sigopts = uu____5156;_}::[],uu____5157),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____5178 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____5178 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____5231),quals) ->
          let uu____5245 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____5245
          then (env, [])
          else
            (let uu____5258 = bundle_as_inductive_families env ses quals  in
             match uu____5258 with
             | (env1,ifams) ->
                 let uu____5277 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____5277 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____5386 -> failwith "Unexpected signature element"
  
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
             let uu____5444 = FStar_Syntax_Util.head_and_args t  in
             match uu____5444 with
             | (head,args) ->
                 let uu____5492 =
                   let uu____5494 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head
                      in
                   Prims.op_Negation uu____5494  in
                 if uu____5492
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5513));
                         FStar_Syntax_Syntax.pos = uu____5514;
                         FStar_Syntax_Syntax.vars = uu____5515;_},uu____5516)::[]
                        ->
                        let uu____5555 =
                          let uu____5559 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5559  in
                        FStar_Pervasives_Native.Some uu____5555
                    | uu____5565 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5580 =
        let uu____5582 = FStar_Options.codegen ()  in
        uu____5582 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5580
      then []
      else
        (let uu____5592 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5592 with
         | FStar_Pervasives_Native.None  -> []
         | FStar_Pervasives_Native.Some arity_opt ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
                  let mk_registration lb =
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                       in
                    let fv_lid =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
                    let ml_name_str =
                      let uu____5634 =
                        let uu____5635 = FStar_Ident.string_of_lid fv_lid  in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5635  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5634  in
                    let uu____5637 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g
                        fv fv_t arity_opt ml_name_str
                       in
                    match uu____5637 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin) ->
                        let uu____5670 =
                          if plugin
                          then
                            ((["FStar_Tactics_Native"], "register_plugin"),
                              [interp; nbe_interp])
                          else
                            ((["FStar_Tactics_Native"], "register_tactic"),
                              [interp])
                           in
                        (match uu____5670 with
                         | (register,args) ->
                             let h =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_Name
                                    register)
                                in
                             let arity1 =
                               let uu____5716 =
                                 let uu____5717 =
                                   let uu____5729 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____5729, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5717
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5716
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
              | uu____5758 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5786 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5786);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5795 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5804 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5821 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           let uu____5838 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
           FStar_TypeChecker_Env.is_reifiable_effect uu____5838
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5839 = extract_reifiable_effect g ed  in
           (match uu____5839 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5863 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_fail uu____5877 ->
           failwith "impossible: trying to extract Sig_fail"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5897 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5903 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs t
              in
           (match uu____5903 with | (env,uu____5919,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5928) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5937 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____5937 with | (env,uu____5953,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____5962) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5975 = extract_let_rec_types se g lbs  in
           (match uu____5975 with | (env,uu____5991,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____6000) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6011 =
             let uu____6020 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____6020 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____6049) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____6011 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    let uu____6135 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.postprocess uu____6135 tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___909_6136 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___909_6136.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___909_6136.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___909_6136.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___909_6136.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___909_6136.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___909_6136.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____6145 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____6145)  in
                let uu____6163 =
                  let uu____6170 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____6170  in
                (match uu____6163 with
                 | (ml_let,uu____6187,uu____6188) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____6197) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____6214 =
                            FStar_List.fold_left2
                              (fun uu____6240  ->
                                 fun ml_lb  ->
                                   fun uu____6242  ->
                                     match (uu____6240, uu____6242) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____6264;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____6266;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____6267;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____6268;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____6269;_})
                                         ->
                                         let uu____6294 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____6294
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____6311 =
                                                let uu____6314 =
                                                  FStar_Util.right lbname  in
                                                uu____6314.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____6311.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____6318 =
                                                let uu____6319 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____6319.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____6318 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6324,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6325;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____6327;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6328;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____6329;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____6330;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____6331;_})
                                                  when
                                                  let uu____6366 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____6366 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____6370 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___957_6375 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___957_6375.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___957_6375.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___957_6375.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___957_6375.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___957_6375.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____6376 =
                                              let uu____6381 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_6388  ->
                                                        match uu___8_6388
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____6390 ->
                                                            true
                                                        | uu____6396 -> false))
                                                 in
                                              if uu____6381
                                              then
                                                let uu____6403 =
                                                  let uu____6411 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____6412 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv
                                                    env uu____6411 uu____6412
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   in
                                                match uu____6403 with
                                                | (env1,mls,uu____6419) ->
                                                    (env1,
                                                      (let uu___969_6423 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           = mls;
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___969_6423.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___969_6423.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___969_6423.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___969_6423.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___969_6423.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6426 =
                                                   let uu____6434 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6434
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    in
                                                 match uu____6426 with
                                                 | (env1,uu____6440,uu____6441)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____6376 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____6214 with
                           | (g1,ml_lbs') ->
                               let uu____6471 =
                                 let uu____6474 =
                                   let uu____6477 =
                                     let uu____6478 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6478
                                      in
                                   [uu____6477;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____6481 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____6474 uu____6481  in
                               (g1, uu____6471))
                      | uu____6486 ->
                          let uu____6487 =
                            let uu____6489 =
                              let uu____6491 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____6491 ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6489
                             in
                          failwith uu____6487)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6500,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6505 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6511 =
                  let uu____6513 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Util.must_erase_for_extraction uu____6513
                    t
                   in
                Prims.op_Negation uu____6511)
              in
           if uu____6505
           then
             let always_fail1 =
               let uu___989_6522 = se  in
               let uu____6523 =
                 let uu____6524 =
                   let uu____6531 =
                     let uu____6532 =
                       let uu____6535 = always_fail lid t  in [uu____6535]
                        in
                     (false, uu____6532)  in
                   (uu____6531, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6524  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6523;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___989_6522.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___989_6522.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___989_6522.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___989_6522.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___989_6522.FStar_Syntax_Syntax.sigopts)
               }  in
             let uu____6542 = extract_sig g always_fail1  in
             (match uu____6542 with
              | (g1,mlm) ->
                  let uu____6561 =
                    FStar_Util.find_map quals
                      (fun uu___9_6566  ->
                         match uu___9_6566 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6570 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6561 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6578 =
                         let uu____6581 =
                           let uu____6582 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6582  in
                         let uu____6583 =
                           let uu____6586 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6586]  in
                         uu____6581 :: uu____6583  in
                       (g1, uu____6578)
                   | uu____6589 ->
                       let uu____6592 =
                         FStar_Util.find_map quals
                           (fun uu___10_6598  ->
                              match uu___10_6598 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6602)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6603 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6592 with
                        | FStar_Pervasives_Native.Some uu____6610 -> (g1, [])
                        | uu____6613 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_assume uu____6622 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6631 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6634 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6649 -> (g, [])
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
      let uu____6689 = FStar_Options.restore_cmd_line_options true  in
      let uu____6691 =
        FStar_Extraction_ML_UEnv.extend_with_module_name g
          m.FStar_Syntax_Syntax.name
         in
      match uu____6691 with
      | (name,g1) ->
          let g2 =
            let uu____6705 =
              let uu____6706 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
              FStar_TypeChecker_Env.set_current_module uu____6706
                m.FStar_Syntax_Syntax.name
               in
            FStar_Extraction_ML_UEnv.set_tcenv g1 uu____6705  in
          let g3 = FStar_Extraction_ML_UEnv.set_current_module g2 name  in
          let uu____6708 =
            FStar_Util.fold_map
              (fun g4  ->
                 fun se  ->
                   let uu____6727 =
                     let uu____6729 =
                       FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                        in
                     FStar_Options.debug_module uu____6729  in
                   if uu____6727
                   then
                     let nm =
                       let uu____6740 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lids_of_sigelt se)
                           (FStar_List.map FStar_Ident.string_of_lid)
                          in
                       FStar_All.pipe_right uu____6740
                         (FStar_String.concat ", ")
                        in
                     (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                      (let uu____6757 =
                         FStar_Util.format1 "---Extracted {%s}" nm  in
                       FStar_Util.measure_execution_time uu____6757
                         (fun uu____6767  -> extract_sig g4 se)))
                   else extract_sig g4 se) g3
              m.FStar_Syntax_Syntax.declarations
             in
          (match uu____6708 with
           | (g4,sigs) ->
               let mlm = FStar_List.flatten sigs  in
               let is_kremlin =
                 let uu____6789 = FStar_Options.codegen ()  in
                 uu____6789 =
                   (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                  in
               let uu____6794 =
                 (let uu____6798 =
                    FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                  uu____6798 <> "Prims") &&
                   (is_kremlin ||
                      (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
                  in
               if uu____6794
               then
                 ((let uu____6810 =
                     let uu____6812 = FStar_Options.silent ()  in
                     Prims.op_Negation uu____6812  in
                   if uu____6810
                   then
                     let uu____6815 =
                       FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                        in
                     FStar_Util.print1 "Extracted module %s\n" uu____6815
                   else ());
                  (g4,
                    (FStar_Pervasives_Native.Some
                       (FStar_Extraction_ML_Syntax.MLLib
                          [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                             (FStar_Extraction_ML_Syntax.MLLib []))]))))
               else (g4, FStar_Pervasives_Native.None))
  
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun m  ->
      (let uu____6890 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun uu____6892  -> ()) uu____6890);
      (let uu____6894 =
         let uu____6896 =
           let uu____6898 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Options.should_extract uu____6898  in
         Prims.op_Negation uu____6896  in
       if uu____6894
       then
         let uu____6901 =
           let uu____6903 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6903
            in
         failwith uu____6901
       else ());
      (let uu____6908 = FStar_Options.interactive ()  in
       if uu____6908
       then (g, FStar_Pervasives_Native.None)
       else
         (let uu____6921 =
            FStar_Syntax_Unionfind.with_uf_enabled
              (fun uu____6937  ->
                 let uu____6938 = FStar_Options.debug_any ()  in
                 if uu____6938
                 then
                   let msg =
                     let uu____6949 =
                       FStar_Syntax_Print.lid_to_string
                         m.FStar_Syntax_Syntax.name
                        in
                     FStar_Util.format1 "Extracting module %s" uu____6949  in
                   FStar_Util.measure_execution_time msg
                     (fun uu____6959  -> extract' g m)
                 else extract' g m)
             in
          match uu____6921 with
          | (g1,mllib) ->
              ((let uu____6975 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_left (fun uu____6977  -> ()) uu____6975);
               (let uu____6978 = FStar_Extraction_ML_UEnv.exit_module g1  in
                (uu____6978, mllib)))))
  
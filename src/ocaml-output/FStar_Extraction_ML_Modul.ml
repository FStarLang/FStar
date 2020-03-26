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
  
let as_pair : 'uuuuuu296 . 'uuuuuu296 Prims.list -> ('uuuuuu296 * 'uuuuuu296)
  =
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
  'uuuuuu481 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu481) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlident
          Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____523  ->
             match uu____523 with
             | (bv,uu____534) ->
                 let env2 = FStar_Extraction_ML_UEnv.extend_ty env1 bv false
                    in
                 let name =
                   let uu____539 = FStar_Extraction_ML_UEnv.lookup_bv env2 bv
                      in
                   match uu____539 with
                   | FStar_Util.Inl ty ->
                       ty.FStar_Extraction_ML_UEnv.ty_b_name
                   | uu____542 -> failwith "Impossible"  in
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
    let uu____744 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____746 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____749 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____751 =
      let uu____753 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____767 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____769 =
                  let uu____771 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____771  in
                Prims.op_Hat uu____767 uu____769))
         in
      FStar_All.pipe_right uu____753 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____744 uu____746 uu____749
      uu____751
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        let uu____816 =
          FStar_Util.fold_map
            (fun env1  ->
               fun se  ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l,us,bs,t,_mut_i,datas) ->
                     let uu____867 = FStar_Syntax_Subst.open_univ_vars us t
                        in
                     (match uu____867 with
                      | (_us,t1) ->
                          let uu____880 = FStar_Syntax_Subst.open_term bs t1
                             in
                          (match uu____880 with
                           | (bs1,t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1  ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d,us1,t3,l',nparams,uu____926)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____933 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3
                                                in
                                             (match uu____933 with
                                              | (_us1,t4) ->
                                                  let uu____942 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4
                                                     in
                                                  (match uu____942 with
                                                   | (bs',body) ->
                                                       let uu____981 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs'
                                                          in
                                                       (match uu____981 with
                                                        | (bs_params,rest) ->
                                                            let subst1 =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____1072
                                                                    ->
                                                                   fun
                                                                    uu____1073
                                                                     ->
                                                                    match 
                                                                    (uu____1072,
                                                                    uu____1073)
                                                                    with
                                                                    | 
                                                                    ((b',uu____1099),
                                                                    (b,uu____1101))
                                                                    ->
                                                                    let uu____1122
                                                                    =
                                                                    let uu____1129
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                    (b',
                                                                    uu____1129)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____1122)
                                                                bs_params bs1
                                                               in
                                                            let t5 =
                                                              let uu____1135
                                                                =
                                                                let uu____1136
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____1136
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____1135
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1)
                                                               in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____1139 -> []))
                                  in
                               let metadata =
                                 let uu____1143 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs
                                    in
                                 let uu____1146 =
                                   FStar_List.choose flag_of_qual quals  in
                                 FStar_List.append uu____1143 uu____1146  in
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
                 | uu____1153 -> (env1, [])) env ses
           in
        match uu____816 with
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
    let uu___221_1333 = empty_iface  in
    {
      iface_module_name = (uu___221_1333.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___221_1333.iface_tydefs);
      iface_type_names = (uu___221_1333.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___224_1344 = empty_iface  in
    let uu____1345 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___224_1344.iface_module_name);
      iface_bindings = (uu___224_1344.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1345
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___228_1360 = empty_iface  in
    {
      iface_module_name = (uu___228_1360.iface_module_name);
      iface_bindings = (uu___228_1360.iface_bindings);
      iface_tydefs = (uu___228_1360.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1372 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1372;
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
  'uuuuuu1417 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('uuuuuu1417 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____1449 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1451 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1453 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1449 uu____1451
        uu____1453
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1471  ->
      match uu____1471 with
      | (fv,exp_binding) ->
          let uu____1479 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1481 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1479 uu____1481
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1496 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1498 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1496 uu____1498
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1516 =
      let uu____1518 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1518 (FStar_String.concat "\n")  in
    let uu____1532 =
      let uu____1534 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1534 (FStar_String.concat "\n")  in
    let uu____1544 =
      let uu____1546 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1546 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1516 uu____1532
      uu____1544
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
    let gamma =
      let uu____1572 = FStar_Extraction_ML_UEnv.bindings_of_uenv env  in
      FStar_List.collect
        (fun uu___2_1582  ->
           match uu___2_1582 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1599 -> []) uu____1572
       in
    let uu____1604 =
      let uu____1606 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1606 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1604
  
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
          let uu____1666 =
            let uu____1675 =
              let uu____1684 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
              FStar_TypeChecker_Env.open_universes_in uu____1684
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1675 with
            | (tcenv,uu____1694,def_typ) ->
                let uu____1700 = as_pair def_typ  in (tcenv, uu____1700)
             in
          match uu____1666 with
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
                let uu____1731 =
                  let uu____1732 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1732 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1731 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1740 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1759 -> def  in
              let uu____1760 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1771) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1796 -> ([], def1)  in
              (match uu____1760 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1816  ->
                          match uu___3_1816 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1819 -> false) quals
                      in
                   let uu____1821 = binders_as_mlty_binders env bs  in
                   (match uu____1821 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1848 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1848
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1853 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1860  ->
                                    match uu___4_1860 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1862 -> true
                                    | uu____1868 -> false))
                             in
                          if uu____1853
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1882 = extract_metadata attrs  in
                          let uu____1885 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1882 uu____1885  in
                        let td =
                          let uu____1908 = lident_as_mlsymbol lid  in
                          (assumed, uu____1908, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1920 =
                            let uu____1921 =
                              let uu____1922 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1922
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1921  in
                          [uu____1920;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1923 =
                          let uu____1928 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_1934  ->
                                    match uu___5_1934 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1938 -> false))
                             in
                          if uu____1928
                          then
                            let uu____1945 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____1945, (iface_of_type_names [fv]))
                          else
                            (let uu____1948 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____1948 with
                             | (env2,tydef) ->
                                 let uu____1959 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1959))
                           in
                        (match uu____1923 with
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
            let uu____2018 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] uu____2018
              lb.FStar_Syntax_Syntax.lbtyp
             in
          let uu____2019 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____2019 with
          | (bs,uu____2043) ->
              let uu____2064 = binders_as_mlty_binders env bs  in
              (match uu____2064 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____2096 = extract_metadata attrs  in
                     let uu____2099 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____2096 uu____2099  in
                   let assumed = false  in
                   let td =
                     let uu____2125 = lident_as_mlsymbol lid  in
                     (assumed, uu____2125, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____2138 =
                       let uu____2139 =
                         let uu____2140 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____2140
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____2139  in
                     [uu____2138; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____2141 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____2141 with
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
          let uu____2222 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2222
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2229 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2229 with | (env2,uu____2248,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2287 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2287 with
        | (env_iparams,vars) ->
            let uu____2315 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2315 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2379,t,uu____2381,uu____2382,uu____2383);
            FStar_Syntax_Syntax.sigrng = uu____2384;
            FStar_Syntax_Syntax.sigquals = uu____2385;
            FStar_Syntax_Syntax.sigmeta = uu____2386;
            FStar_Syntax_Syntax.sigattrs = uu____2387;
            FStar_Syntax_Syntax.sigopts = uu____2388;_}::[],uu____2389),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2410 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2410 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2443),quals) ->
          let uu____2457 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____2457
          then (env, empty_iface)
          else
            (let uu____2466 = bundle_as_inductive_families env ses quals  in
             match uu____2466 with
             | (env1,ifams) ->
                 let uu____2483 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____2483 with
                  | (env2,td) ->
                      let uu____2524 =
                        let uu____2525 =
                          let uu____2526 =
                            FStar_List.map (fun x  -> x.ifv) ifams  in
                          iface_of_type_names uu____2526  in
                        iface_union uu____2525
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____2524)))
      | uu____2535 -> failwith "Unexpected signature element"
  
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
              let uu____2610 =
                let uu____2612 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2618  ->
                          match uu___6_2618 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2621 -> false))
                   in
                Prims.op_Negation uu____2612  in
              if uu____2610
              then (g, empty_iface, [])
              else
                (let uu____2636 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2636 with
                 | (bs,uu____2660) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2683 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2683;
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
        let uu____2746 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2746 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2768 =
                let uu____2770 =
                  let uu____2776 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g2
                     in
                  FStar_TypeChecker_Env.debug uu____2776  in
                FStar_All.pipe_left uu____2770
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2768
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
        (let uu____2811 =
           let uu____2813 =
             let uu____2819 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.debug uu____2819  in
           FStar_All.pipe_left uu____2813
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2811
         then
           let uu____2823 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2823
         else ());
        (let uu____2828 =
           let uu____2829 = FStar_Syntax_Subst.compress tm  in
           uu____2829.FStar_Syntax_Syntax.n  in
         match uu____2828 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2837) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2844 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2844 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2849;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2850;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2852;_} ->
                  let uu____2855 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2855, tysc))
         | uu____2856 ->
             let uu____2857 =
               let uu____2859 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2861 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2859 uu____2861
                in
             failwith uu____2857)
         in
      let extract_action g1 a =
        (let uu____2889 =
           let uu____2891 =
             let uu____2897 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
             FStar_TypeChecker_Env.debug uu____2897  in
           FStar_All.pipe_left uu____2891
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2889
         then
           let uu____2901 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2903 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2901
             uu____2903
         else ());
        (let uu____2908 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2908 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2928 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2928  in
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
             let uu____2958 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2958 with
              | (a_let,uu____2974,ty) ->
                  ((let uu____2977 =
                      let uu____2979 =
                        let uu____2985 =
                          FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
                        FStar_TypeChecker_Env.debug uu____2985  in
                      FStar_All.pipe_left uu____2979
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2977
                    then
                      let uu____2989 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2989
                    else ());
                   (let uu____2994 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____3017,mllb::[]),uu____3019) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____3059 -> failwith "Impossible"  in
                    match uu____2994 with
                    | (exp,tysc) ->
                        ((let uu____3097 =
                            let uu____3099 =
                              let uu____3105 =
                                FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
                              FStar_TypeChecker_Env.debug uu____3105  in
                            FStar_All.pipe_left uu____3099
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____3097
                          then
                            ((let uu____3110 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____3110);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____3126 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____3126 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____3148 =
        let uu____3155 =
          let uu____3160 =
            let uu____3163 =
              let uu____3172 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr  in
              FStar_All.pipe_right uu____3172 FStar_Util.must  in
            FStar_All.pipe_right uu____3163 FStar_Pervasives_Native.snd  in
          extract_fv uu____3160  in
        match uu____3155 with
        | (return_tm,ty_sc) ->
            let uu____3241 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____3241 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____3148 with
      | (g1,return_iface,return_decl) ->
          let uu____3266 =
            let uu____3273 =
              let uu____3278 =
                let uu____3281 =
                  let uu____3290 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr
                     in
                  FStar_All.pipe_right uu____3290 FStar_Util.must  in
                FStar_All.pipe_right uu____3281 FStar_Pervasives_Native.snd
                 in
              extract_fv uu____3278  in
            match uu____3273 with
            | (bind_tm,ty_sc) ->
                let uu____3359 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____3359 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____3266 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3384 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3384 with
                | (g3,actions) ->
                    let uu____3421 = FStar_List.unzip actions  in
                    (match uu____3421 with
                     | (actions_iface,actions1) ->
                         let uu____3448 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3448, (return_decl :: bind_decl ::
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
        let uu____3479 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____3484 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____3484) lbs
           in
        if uu____3479
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3507 =
             FStar_List.fold_left
               (fun uu____3542  ->
                  fun lb  ->
                    match uu____3542 with
                    | (env1,iface_opt,impls) ->
                        let uu____3583 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____3583 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3617 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____3617
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____3507 with
           | (env1,iface_opt,impls) ->
               let uu____3657 = FStar_Option.get iface_opt  in
               let uu____3658 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____3657, uu____3658))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3690 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3699 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3716 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3735 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3735 with | (env,iface1,uu____3750) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3756) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3765 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3765 with | (env,iface1,uu____3780) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____3786) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3799 = extract_let_rec_types se g lbs  in
          (match uu____3799 with | (env,iface1,uu____3814) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3825 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3831 =
                 let uu____3833 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                    in
                 FStar_TypeChecker_Util.must_erase_for_extraction uu____3833
                   t
                  in
               Prims.op_Negation uu____3831)
             in
          if uu____3825
          then
            let uu____3839 =
              let uu____3850 =
                let uu____3851 =
                  let uu____3854 = always_fail lid t  in [uu____3854]  in
                (false, uu____3851)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3850  in
            (match uu____3839 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3880) ->
          let uu____3885 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3885 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3914 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3915 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3922 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3923 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3936 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3949 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_fail uu____3961 ->
          failwith "impossible: trying to extract Sig_fail"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3980 =
            (let uu____3984 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.is_reifiable_effect uu____3984
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____3980
          then
            let uu____3996 = extract_reifiable_effect g ed  in
            (match uu____3996 with | (env,iface1,uu____4011) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4033 = FStar_Options.interactive ()  in
      if uu____4033
      then (g, empty_iface)
      else
        (let uu____4042 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___626_4046 = empty_iface  in
           let uu____4047 = FStar_Extraction_ML_UEnv.current_module_of_uenv g
              in
           {
             iface_module_name = uu____4047;
             iface_bindings = (uu___626_4046.iface_bindings);
             iface_tydefs = (uu___626_4046.iface_tydefs);
             iface_type_names = (uu___626_4046.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____4065  ->
                fun se  ->
                  match uu____4065 with
                  | (g1,iface2) ->
                      let uu____4077 = extract_sigelt_iface g1 se  in
                      (match uu____4077 with
                       | (g2,iface') ->
                           let uu____4088 = iface_union iface2 iface'  in
                           (g2, uu____4088))) (g, iface1) decls
            in
         (let uu____4090 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun uu____4092  -> ()) uu____4090);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4108 = FStar_Options.debug_any ()  in
      if uu____4108
      then
        let uu____4115 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____4115
          (fun uu____4123  -> extract_iface' g modul)
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
          let uu____4214 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4214
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____4222 =
            let uu____4223 =
              let uu____4226 =
                let uu____4227 =
                  FStar_Extraction_ML_UEnv.tcenv_of_uenv env_iparams  in
                FStar_TypeChecker_Normalize.normalize steps uu____4227
                  ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4226  in
            uu____4223.FStar_Syntax_Syntax.n  in
          match uu____4222 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4232) ->
              FStar_List.map
                (fun uu____4265  ->
                   match uu____4265 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4274;
                        FStar_Syntax_Syntax.sort = uu____4275;_},uu____4276)
                       -> ppname.FStar_Ident.idText) bs
          | uu____4284 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____4292 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____4292 with
        | (env2,uu____4319,uu____4320) ->
            let uu____4323 =
              let uu____4336 = lident_as_mlsymbol ctor.dname  in
              let uu____4338 =
                let uu____4346 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____4346  in
              (uu____4336, uu____4338)  in
            (env2, uu____4323)
         in
      let extract_one_family env1 ind =
        let uu____4407 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4407 with
        | (env_iparams,vars) ->
            let uu____4451 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____4451 with
             | (env2,ctors) ->
                 let uu____4558 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____4558 with
                  | (indices,uu____4600) ->
                      let ml_params =
                        let uu____4625 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____4651  ->
                                    let uu____4659 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____4659))
                           in
                        FStar_List.append vars uu____4625  in
                      let tbody =
                        let uu____4664 =
                          FStar_Util.find_opt
                            (fun uu___7_4669  ->
                               match uu___7_4669 with
                               | FStar_Syntax_Syntax.RecordType uu____4671 ->
                                   true
                               | uu____4681 -> false) ind.iquals
                           in
                        match uu____4664 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____4693 = FStar_List.hd ctors  in
                            (match uu____4693 with
                             | (uu____4718,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____4762  ->
                                          match uu____4762 with
                                          | (uu____4773,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____4778 =
                                                lident_as_mlsymbol lid  in
                                              (uu____4778, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4781 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____4784 =
                        let uu____4807 = lident_as_mlsymbol ind.iname  in
                        (false, uu____4807, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____4784)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____4852,t,uu____4854,uu____4855,uu____4856);
            FStar_Syntax_Syntax.sigrng = uu____4857;
            FStar_Syntax_Syntax.sigquals = uu____4858;
            FStar_Syntax_Syntax.sigmeta = uu____4859;
            FStar_Syntax_Syntax.sigattrs = uu____4860;
            FStar_Syntax_Syntax.sigopts = uu____4861;_}::[],uu____4862),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____4883 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____4883 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____4936),quals) ->
          let uu____4950 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____4950
          then (env, [])
          else
            (let uu____4963 = bundle_as_inductive_families env ses quals  in
             match uu____4963 with
             | (env1,ifams) ->
                 let uu____4982 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____4982 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____5091 -> failwith "Unexpected signature element"
  
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
             let uu____5149 = FStar_Syntax_Util.head_and_args t  in
             match uu____5149 with
             | (head1,args) ->
                 let uu____5197 =
                   let uu____5199 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____5199  in
                 if uu____5197
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5218));
                         FStar_Syntax_Syntax.pos = uu____5219;
                         FStar_Syntax_Syntax.vars = uu____5220;_},uu____5221)::[]
                        ->
                        let uu____5260 =
                          let uu____5264 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5264  in
                        FStar_Pervasives_Native.Some uu____5260
                    | uu____5270 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5285 =
        let uu____5287 = FStar_Options.codegen ()  in
        uu____5287 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5285
      then []
      else
        (let uu____5297 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5297 with
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
                      let uu____5339 =
                        let uu____5340 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5340  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5339  in
                    let uu____5342 =
                      let uu____5355 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        uu____5355 fv fv_t arity_opt ml_name_str
                       in
                    match uu____5342 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____5376 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____5376 with
                         | (register,args) ->
                             let h =
                               let uu____5413 =
                                 let uu____5414 =
                                   let uu____5415 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____5415
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____5414
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____5413
                                in
                             let arity1 =
                               let uu____5417 =
                                 let uu____5418 =
                                   let uu____5430 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____5430, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5418
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5417
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
              | uu____5459 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5487 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5487);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5496 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5505 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5522 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           let uu____5539 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
           FStar_TypeChecker_Env.is_reifiable_effect uu____5539
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5540 = extract_reifiable_effect g ed  in
           (match uu____5540 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5564 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_fail uu____5578 ->
           failwith "impossible: trying to extract Sig_fail"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5598 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5604 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____5604 with | (env,uu____5620,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5629) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5638 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____5638 with | (env,uu____5654,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____5663) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5676 = extract_let_rec_types se g lbs  in
           (match uu____5676 with | (env,uu____5692,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____5701) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5712 =
             let uu____5721 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____5721 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____5750) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____5712 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    let uu____5836 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.postprocess uu____5836 tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___876_5837 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___876_5837.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___876_5837.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___876_5837.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___876_5837.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___876_5837.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___876_5837.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____5846 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____5846)  in
                let uu____5864 =
                  let uu____5871 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5871  in
                (match uu____5864 with
                 | (ml_let,uu____5888,uu____5889) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____5898) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____5915 =
                            FStar_List.fold_left2
                              (fun uu____5941  ->
                                 fun ml_lb  ->
                                   fun uu____5943  ->
                                     match (uu____5941, uu____5943) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____5965;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____5967;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____5968;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____5969;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____5970;_})
                                         ->
                                         let uu____5995 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____5995
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____6012 =
                                                let uu____6015 =
                                                  FStar_Util.right lbname  in
                                                uu____6015.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____6012.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____6019 =
                                                let uu____6020 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____6020.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____6019 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6025,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6026;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____6028;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6029;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____6030;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____6031;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____6032;_})
                                                  when
                                                  let uu____6067 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____6067 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____6071 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___924_6076 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___924_6076.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___924_6076.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___924_6076.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___924_6076.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___924_6076.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____6077 =
                                              let uu____6082 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_6089  ->
                                                        match uu___8_6089
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____6091 ->
                                                            true
                                                        | uu____6097 -> false))
                                                 in
                                              if uu____6082
                                              then
                                                let mname =
                                                  let uu____6113 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____6113
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____6122 =
                                                  let uu____6130 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____6131 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____6130 mname
                                                    uu____6131
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____6122 with
                                                | (env1,uu____6138,uu____6139)
                                                    ->
                                                    (env1,
                                                      (let uu___937_6143 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___937_6143.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___937_6143.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___937_6143.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___937_6143.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___937_6143.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6150 =
                                                   let uu____6158 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6158
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____6150 with
                                                 | (env1,uu____6165,uu____6166)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____6077 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____5915 with
                           | (g1,ml_lbs') ->
                               let uu____6196 =
                                 let uu____6199 =
                                   let uu____6202 =
                                     let uu____6203 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6203
                                      in
                                   [uu____6202;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____6206 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____6199 uu____6206  in
                               (g1, uu____6196))
                      | uu____6211 ->
                          let uu____6212 =
                            let uu____6214 =
                              let uu____6216 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____6216 ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6214
                             in
                          failwith uu____6212)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6225,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6230 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6236 =
                  let uu____6238 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Util.must_erase_for_extraction uu____6238
                    t
                   in
                Prims.op_Negation uu____6236)
              in
           if uu____6230
           then
             let always_fail1 =
               let uu___957_6247 = se  in
               let uu____6248 =
                 let uu____6249 =
                   let uu____6256 =
                     let uu____6257 =
                       let uu____6260 = always_fail lid t  in [uu____6260]
                        in
                     (false, uu____6257)  in
                   (uu____6256, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6249  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6248;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___957_6247.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___957_6247.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___957_6247.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___957_6247.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___957_6247.FStar_Syntax_Syntax.sigopts)
               }  in
             let uu____6267 = extract_sig g always_fail1  in
             (match uu____6267 with
              | (g1,mlm) ->
                  let uu____6286 =
                    FStar_Util.find_map quals
                      (fun uu___9_6291  ->
                         match uu___9_6291 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6295 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6286 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6303 =
                         let uu____6306 =
                           let uu____6307 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6307  in
                         let uu____6308 =
                           let uu____6311 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6311]  in
                         uu____6306 :: uu____6308  in
                       (g1, uu____6303)
                   | uu____6314 ->
                       let uu____6317 =
                         FStar_Util.find_map quals
                           (fun uu___10_6323  ->
                              match uu___10_6323 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6327)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6328 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6317 with
                        | FStar_Pervasives_Native.Some uu____6335 -> (g1, [])
                        | uu____6338 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6348 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____6348 with
            | (ml_main,uu____6362,uu____6363) ->
                let uu____6364 =
                  let uu____6367 =
                    let uu____6368 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6368  in
                  [uu____6367; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____6364))
       | FStar_Syntax_Syntax.Sig_assume uu____6371 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6380 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6383 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6398 -> (g, [])
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
      let uu____6438 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu____6442 =
          let uu____6443 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
          FStar_TypeChecker_Env.set_current_module uu____6443
            m.FStar_Syntax_Syntax.name
           in
        FStar_Extraction_ML_UEnv.set_tcenv g uu____6442  in
      let g2 = FStar_Extraction_ML_UEnv.set_current_module g1 name  in
      let uu____6445 =
        FStar_Util.fold_map
          (fun g3  ->
             fun se  ->
               let uu____6464 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____6464
               then
                 let nm =
                   let uu____6475 =
                     let uu____6479 = FStar_Syntax_Util.lids_of_sigelt se  in
                     FStar_All.pipe_right uu____6479
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____6475 (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____6495 = FStar_Util.format1 "---Extracted {%s}" nm
                      in
                   FStar_Util.measure_execution_time uu____6495
                     (fun uu____6505  -> extract_sig g3 se)))
               else extract_sig g3 se) g2 m.FStar_Syntax_Syntax.declarations
         in
      match uu____6445 with
      | (g3,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____6527 = FStar_Options.codegen ()  in
            uu____6527 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____6542 =
                let uu____6544 = FStar_Options.silent ()  in
                Prims.op_Negation uu____6544  in
              if uu____6542
              then
                let uu____6547 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____6547
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
      (let uu____6622 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun uu____6624  -> ()) uu____6622);
      (let uu____6626 =
         let uu____6628 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____6628  in
       if uu____6626
       then
         let uu____6631 =
           let uu____6633 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6633
            in
         failwith uu____6631
       else ());
      (let uu____6638 = FStar_Options.interactive ()  in
       if uu____6638
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____6658 = FStar_Options.debug_any ()  in
            if uu____6658
            then
              let msg =
                let uu____6669 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____6669  in
              FStar_Util.measure_execution_time msg
                (fun uu____6679  -> extract' g m)
            else extract' g m  in
          (let uu____6683 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun uu____6685  -> ()) uu____6683);
          res))
  
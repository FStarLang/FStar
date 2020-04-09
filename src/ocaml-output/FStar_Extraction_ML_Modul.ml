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
  
let as_pair :
  'Auu____250 . 'Auu____250 Prims.list -> ('Auu____250 * 'Auu____250) =
  fun uu___0_261  ->
    match uu___0_261 with
    | a::b::[] -> (a, b)
    | uu____266 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_281  ->
    match uu___1_281 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____284 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____293 = FStar_Syntax_Subst.compress x  in
    match uu____293 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____297;
        FStar_Syntax_Syntax.vars = uu____298;_} ->
        let uu____301 =
          let uu____303 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____303  in
        (match uu____301 with
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
         | uu____316 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____319;
             FStar_Syntax_Syntax.vars = uu____320;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____322));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____323;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____324;_},uu____325)::[]);
        FStar_Syntax_Syntax.pos = uu____326;
        FStar_Syntax_Syntax.vars = uu____327;_} ->
        let uu____370 =
          let uu____372 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____372  in
        (match uu____370 with
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
         | uu____382 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____384));
        FStar_Syntax_Syntax.pos = uu____385;
        FStar_Syntax_Syntax.vars = uu____386;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____391));
        FStar_Syntax_Syntax.pos = uu____392;
        FStar_Syntax_Syntax.vars = uu____393;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____398));
        FStar_Syntax_Syntax.pos = uu____399;
        FStar_Syntax_Syntax.vars = uu____400;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____406);
        FStar_Syntax_Syntax.pos = uu____407;
        FStar_Syntax_Syntax.vars = uu____408;_} -> extract_meta x1
    | uu____415 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____435 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____435) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlident
          Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____477  ->
             match uu____477 with
             | (bv,uu____488) ->
                 let env2 = FStar_Extraction_ML_UEnv.extend_ty env1 bv false
                    in
                 let name =
                   let uu____493 = FStar_Extraction_ML_UEnv.lookup_bv env2 bv
                      in
                   match uu____493 with
                   | FStar_Util.Inl ty ->
                       ty.FStar_Extraction_ML_UEnv.ty_b_name
                   | uu____496 -> failwith "Impossible"  in
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
    let uu____698 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____700 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____703 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____705 =
      let uu____707 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____721 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____723 =
                  let uu____725 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____725  in
                Prims.op_Hat uu____721 uu____723))
         in
      FStar_All.pipe_right uu____707 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____698 uu____700 uu____703
      uu____705
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        let uu____770 =
          FStar_Util.fold_map
            (fun env1  ->
               fun se  ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l,us,bs,t,_mut_i,datas) ->
                     let uu____823 = FStar_Syntax_Subst.open_univ_vars us t
                        in
                     (match uu____823 with
                      | (_us,t1) ->
                          let uu____836 = FStar_Syntax_Subst.open_term bs t1
                             in
                          (match uu____836 with
                           | (bs1,t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1  ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d,us1,t3,l',nparams,uu____882)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____889 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3
                                                in
                                             (match uu____889 with
                                              | (_us1,t4) ->
                                                  let uu____898 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4
                                                     in
                                                  (match uu____898 with
                                                   | (bs',body) ->
                                                       let uu____913 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs'
                                                          in
                                                       (match uu____913 with
                                                        | (bs_params,rest) ->
                                                            let subst1 =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____1004
                                                                    ->
                                                                   fun
                                                                    uu____1005
                                                                     ->
                                                                    match 
                                                                    (uu____1004,
                                                                    uu____1005)
                                                                    with
                                                                    | 
                                                                    ((b',uu____1031),
                                                                    (b,uu____1033))
                                                                    ->
                                                                    let uu____1054
                                                                    =
                                                                    let uu____1061
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                    (b',
                                                                    uu____1061)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____1054)
                                                                bs_params bs1
                                                               in
                                                            let t5 =
                                                              let uu____1067
                                                                =
                                                                let uu____1068
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____1068
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____1067
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1)
                                                               in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____1071 -> []))
                                  in
                               let metadata =
                                 let uu____1075 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs
                                    in
                                 let uu____1078 =
                                   FStar_List.choose flag_of_qual quals  in
                                 FStar_List.append uu____1075 uu____1078  in
                               let fv =
                                 FStar_Syntax_Syntax.lid_as_fv l
                                   FStar_Syntax_Syntax.delta_constant
                                   FStar_Pervasives_Native.None
                                  in
                               let uu____1082 =
                                 FStar_Extraction_ML_UEnv.extend_type_name
                                   env1 fv
                                  in
                               (match uu____1082 with
                                | (uu____1093,env2) ->
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
                 | uu____1097 -> (env1, [])) env ses
           in
        match uu____770 with
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
    let uu___221_1309 = empty_iface  in
    {
      iface_module_name = (uu___221_1309.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___221_1309.iface_tydefs);
      iface_type_names = (uu___221_1309.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___224_1320 = empty_iface  in
    let uu____1321 =
      FStar_List.map
        (fun td  ->
           let uu____1336 = FStar_Extraction_ML_UEnv.tydef_fv td  in
           let uu____1337 = FStar_Extraction_ML_UEnv.tydef_mlpath td  in
           (uu____1336, uu____1337)) tds
       in
    {
      iface_module_name = (uu___224_1320.iface_module_name);
      iface_bindings = (uu___224_1320.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1321
    }
  
let (iface_of_type_names :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list ->
    iface)
  =
  fun fvs  ->
    let uu___228_1356 = empty_iface  in
    {
      iface_module_name = (uu___228_1356.iface_module_name);
      iface_bindings = (uu___228_1356.iface_bindings);
      iface_tydefs = (uu___228_1356.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1368 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1368;
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
  'Auu____1417 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1417 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      FStar_Util.format3
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1449 uu____1451
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1469  ->
      match uu____1469 with
      | (fv,exp_binding) ->
          let uu____1477 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1479 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1477 uu____1479
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1494 =
        let uu____1496 = FStar_Extraction_ML_UEnv.tydef_fv tydef  in
        FStar_Syntax_Print.fv_to_string uu____1496  in
      let uu____1497 =
        let uu____1499 = FStar_Extraction_ML_UEnv.tydef_def tydef  in
        tscheme_to_string cm uu____1499  in
      FStar_Util.format2 "(%s, %s)" uu____1494 uu____1497
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name uu____1523 =
      match uu____1523 with
      | (tn,uu____1530) -> FStar_Syntax_Print.fv_to_string tn  in
    let uu____1531 =
      let uu____1533 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1533 (FStar_String.concat "\n")  in
    let uu____1547 =
      let uu____1549 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1549 (FStar_String.concat "\n")  in
    let uu____1559 =
      let uu____1561 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1561 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1531 uu____1547
      uu____1559
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
    let gamma =
      let uu____1591 = FStar_Extraction_ML_UEnv.bindings_of_uenv env  in
      FStar_List.collect
        (fun uu___2_1601  ->
           match uu___2_1601 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1618 -> []) uu____1591
       in
    let uu____1623 =
      let uu____1625 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1625 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1623
  
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
          let uu____1685 =
            let uu____1694 =
              let uu____1703 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
              FStar_TypeChecker_Env.open_universes_in uu____1703
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1694 with
            | (tcenv,uu____1713,def_typ) ->
                let uu____1719 = as_pair def_typ  in (tcenv, uu____1719)
             in
          match uu____1685 with
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
                let uu____1750 =
                  let uu____1751 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1751 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1750 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1759 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1778 -> def  in
              let uu____1779 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1790) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1815 -> ([], def1)  in
              (match uu____1779 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1835  ->
                          match uu___3_1835 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1838 -> false) quals
                      in
                   let uu____1840 = binders_as_mlty_binders env bs  in
                   (match uu____1840 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1867 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1867
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let metadata =
                          let uu____1871 = extract_metadata attrs  in
                          let uu____1874 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1871 uu____1874  in
                        let tyscheme = (ml_bs, body1)  in
                        let uu____1882 =
                          let uu____1897 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1903  ->
                                    match uu___4_1903 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1907 -> false))
                             in
                          if uu____1897
                          then
                            let uu____1924 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            match uu____1924 with
                            | (mlp,env2) ->
                                (mlp, (iface_of_type_names [(fv, mlp)]),
                                  env2)
                          else
                            (let uu____1963 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 tyscheme
                                in
                             match uu____1963 with
                             | (td,mlp,env2) ->
                                 let uu____1987 = iface_of_tydefs [td]  in
                                 (mlp, uu____1987, env2))
                           in
                        (match uu____1882 with
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
                               let uu____2058 =
                                 let uu____2059 =
                                   let uu____2060 =
                                     FStar_Ident.range_of_lid lid  in
                                   FStar_Extraction_ML_Util.mlloc_of_range
                                     uu____2060
                                    in
                                 FStar_Extraction_ML_Syntax.MLM_Loc
                                   uu____2059
                                  in
                               [uu____2058;
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
            let uu____2109 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] uu____2109
              lb.FStar_Syntax_Syntax.lbtyp
             in
          let uu____2110 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____2110 with
          | (bs,uu____2126) ->
              let uu____2131 = binders_as_mlty_binders env bs  in
              (match uu____2131 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____2163 = extract_metadata attrs  in
                     let uu____2166 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____2163 uu____2166  in
                   let assumed = false  in
                   let tscheme = (ml_bs, body)  in
                   let uu____2177 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv tscheme  in
                   (match uu____2177 with
                    | (tydef,mlp,env2) ->
                        let td =
                          (assumed, (FStar_Pervasives_Native.snd mlp),
                            FStar_Pervasives_Native.None, ml_bs, metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                           in
                        let def =
                          let uu____2230 =
                            let uu____2231 =
                              let uu____2232 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____2232
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____2231  in
                          [uu____2230;
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
          let uu____2299 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2299
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____2306 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false  in
        match uu____2306 with | (env2,uu____2324,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2363 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2363 with
        | (env_iparams,vars) ->
            let uu____2391 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2391 with
             | (env2,ctors) ->
                 let env3 =
                   let uu____2443 =
                     FStar_Util.find_opt
                       (fun uu___5_2448  ->
                          match uu___5_2448 with
                          | FStar_Syntax_Syntax.RecordType uu____2450 -> true
                          | uu____2460 -> false) ind.iquals
                      in
                   match uu____2443 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                       let g =
                         FStar_List.fold_right
                           (fun id1  ->
                              fun g  ->
                                let uu____2480 =
                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                    g ((ind.iname), id1)
                                   in
                                match uu____2480 with | (mlp,g1) -> g1) ids
                           env2
                          in
                       g
                   | uu____2487 -> env2  in
                 (env3, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2503,t,uu____2505,uu____2506,uu____2507);
            FStar_Syntax_Syntax.sigrng = uu____2508;
            FStar_Syntax_Syntax.sigquals = uu____2509;
            FStar_Syntax_Syntax.sigmeta = uu____2510;
            FStar_Syntax_Syntax.sigattrs = uu____2511;
            FStar_Syntax_Syntax.sigopts = uu____2512;_}::[],uu____2513),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2534 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2534 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2567),quals) ->
          let uu____2581 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____2581
          then (env, empty_iface)
          else
            (let uu____2590 = bundle_as_inductive_families env ses quals  in
             match uu____2590 with
             | (env1,ifams) ->
                 let uu____2607 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____2607 with
                  | (env2,td) ->
                      let uu____2648 =
                        let uu____2649 =
                          let uu____2650 =
                            FStar_List.map
                              (fun x  ->
                                 let uu____2664 =
                                   FStar_Extraction_ML_UEnv.mlpath_of_lident
                                     env2 x.iname
                                    in
                                 ((x.ifv), uu____2664)) ifams
                             in
                          iface_of_type_names uu____2650  in
                        iface_union uu____2649
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____2648)))
      | uu____2669 -> failwith "Unexpected signature element"
  
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
              let uu____2744 =
                let uu____2746 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2752  ->
                          match uu___6_2752 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2755 -> false))
                   in
                Prims.op_Negation uu____2746  in
              if uu____2744
              then (g, empty_iface, [])
              else
                (let uu____2770 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2770 with
                 | (bs,uu____2786) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2793 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2793;
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
        (let uu____2897 =
           let uu____2899 =
             let uu____2905 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.debug uu____2905  in
           FStar_All.pipe_left uu____2899
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2897
         then
           let uu____2909 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2909
         else ());
        (let uu____2914 =
           let uu____2915 = FStar_Syntax_Subst.compress tm  in
           uu____2915.FStar_Syntax_Syntax.n  in
         match uu____2914 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2923) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_UEnv.mlpath_of_lident g
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2930 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2930 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2935;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2936;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;_} ->
                  let uu____2939 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2939, tysc))
         | uu____2940 ->
             let uu____2941 =
               let uu____2943 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2945 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2943 uu____2945
                in
             failwith uu____2941)
         in
      let extract_action g1 a =
        (let uu____2973 =
           let uu____2975 =
             let uu____2981 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
             FStar_TypeChecker_Env.debug uu____2981  in
           FStar_All.pipe_left uu____2975
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2973
         then
           let uu____2985 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2987 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2985
             uu____2987
         else ());
        (let lbname =
           let uu____2997 =
             FStar_Syntax_Syntax.new_bv
               (FStar_Pervasives_Native.Some
                  ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
               FStar_Syntax_Syntax.tun
              in
           FStar_Util.Inl uu____2997  in
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
         let uu____3027 =
           FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
         match uu____3027 with
         | (a_let,uu____3043,ty) ->
             let uu____3045 =
               match a_let.FStar_Extraction_ML_Syntax.expr with
               | FStar_Extraction_ML_Syntax.MLE_Let
                   ((uu____3062,mllb::[]),uu____3064) ->
                   (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc with
                    | FStar_Pervasives_Native.Some tysc ->
                        ((mllb.FStar_Extraction_ML_Syntax.mllb_def), tysc)
                    | FStar_Pervasives_Native.None  ->
                        failwith "No type scheme")
               | uu____3095 -> failwith "Impossible"  in
             (match uu____3045 with
              | (exp,tysc) ->
                  let uu____3123 =
                    FStar_Extraction_ML_UEnv.extend_with_action_name g1 ed a
                      tysc
                     in
                  (match uu____3123 with
                   | (a_nm,a_lid,exp_b,g2) ->
                       ((let uu____3145 =
                           let uu____3147 =
                             let uu____3153 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2  in
                             FStar_TypeChecker_Env.debug uu____3153  in
                           FStar_All.pipe_left uu____3147
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____3145
                         then
                           let uu____3157 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____3157
                         else ());
                        (let uu____3163 =
                           let uu____3165 =
                             let uu____3171 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2  in
                             FStar_TypeChecker_Env.debug uu____3171  in
                           FStar_All.pipe_left uu____3165
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____3163
                         then
                           ((let uu____3176 =
                               FStar_Extraction_ML_Code.string_of_mlty a_nm
                                 (FStar_Pervasives_Native.snd tysc)
                                in
                             FStar_Util.print1 "Extracted action type: %s\n"
                               uu____3176);
                            FStar_List.iter
                              (fun x  ->
                                 FStar_Util.print1 "and binders: %s\n" x)
                              (FStar_Pervasives_Native.fst tysc))
                         else ());
                        (let uu____3186 = extend_iface a_lid a_nm exp exp_b
                            in
                         match uu____3186 with
                         | (iface1,impl) -> (g2, (iface1, impl)))))))
         in
      let uu____3205 =
        let uu____3212 =
          let uu____3217 =
            let uu____3220 =
              let uu____3229 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr  in
              FStar_All.pipe_right uu____3229 FStar_Util.must  in
            FStar_All.pipe_right uu____3220 FStar_Pervasives_Native.snd  in
          extract_fv uu____3217  in
        match uu____3212 with
        | (return_tm,ty_sc) ->
            let uu____3298 =
              FStar_Extraction_ML_UEnv.extend_with_monad_op_name g ed
                "return" ty_sc
               in
            (match uu____3298 with
             | (return_nm,return_lid,return_b,g1) ->
                 let uu____3318 =
                   extend_iface return_lid return_nm return_tm return_b  in
                 (match uu____3318 with | (iface1,impl) -> (g1, iface1, impl)))
         in
      match uu____3205 with
      | (g1,return_iface,return_decl) ->
          let uu____3342 =
            let uu____3349 =
              let uu____3354 =
                let uu____3357 =
                  let uu____3366 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr
                     in
                  FStar_All.pipe_right uu____3366 FStar_Util.must  in
                FStar_All.pipe_right uu____3357 FStar_Pervasives_Native.snd
                 in
              extract_fv uu____3354  in
            match uu____3349 with
            | (bind_tm,ty_sc) ->
                let uu____3435 =
                  FStar_Extraction_ML_UEnv.extend_with_monad_op_name g1 ed
                    "bind" ty_sc
                   in
                (match uu____3435 with
                 | (bind_nm,bind_lid,bind_b,g2) ->
                     let uu____3455 =
                       extend_iface bind_lid bind_nm bind_tm bind_b  in
                     (match uu____3455 with
                      | (iface1,impl) -> (g2, iface1, impl)))
             in
          (match uu____3342 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3479 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3479 with
                | (g3,actions) ->
                    let uu____3516 = FStar_List.unzip actions  in
                    (match uu____3516 with
                     | (actions_iface,actions1) ->
                         let uu____3543 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3543, (return_decl :: bind_decl ::
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
        let uu____3574 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____3579 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____3579) lbs
           in
        if uu____3574
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3602 =
             FStar_List.fold_left
               (fun uu____3637  ->
                  fun lb  ->
                    match uu____3637 with
                    | (env1,iface_opt,impls) ->
                        let uu____3678 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____3678 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3712 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____3712
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____3602 with
           | (env1,iface_opt,impls) ->
               let uu____3752 = FStar_Option.get iface_opt  in
               let uu____3753 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____3752, uu____3753))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3785 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3794 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3811 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3830 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3830 with | (env,iface1,uu____3845) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3851) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3860 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3860 with | (env,iface1,uu____3875) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____3881) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3894 = extract_let_rec_types se g lbs  in
          (match uu____3894 with | (env,iface1,uu____3909) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3920 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3926 =
                 let uu____3928 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                    in
                 FStar_TypeChecker_Util.must_erase_for_extraction uu____3928
                   t
                  in
               Prims.op_Negation uu____3926)
             in
          if uu____3920
          then
            let uu____3934 =
              let uu____3945 =
                let uu____3946 =
                  let uu____3949 = always_fail lid t  in [uu____3949]  in
                (false, uu____3946)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3945  in
            (match uu____3934 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3975) ->
          let uu____3980 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3980 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____4009 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____4010 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4017 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4018 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____4031 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____4044 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_fail uu____4056 ->
          failwith "impossible: trying to extract Sig_fail"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4075 =
            (let uu____4079 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_Env.is_reifiable_effect uu____4079
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____4075
          then
            let uu____4091 = extract_reifiable_effect g ed  in
            (match uu____4091 with | (env,iface1,uu____4106) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4128 = FStar_Options.interactive ()  in
      if uu____4128
      then (g, empty_iface)
      else
        (let uu____4137 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___649_4141 = empty_iface  in
           let uu____4142 = FStar_Extraction_ML_UEnv.current_module_of_uenv g
              in
           {
             iface_module_name = uu____4142;
             iface_bindings = (uu___649_4141.iface_bindings);
             iface_tydefs = (uu___649_4141.iface_tydefs);
             iface_type_names = (uu___649_4141.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____4160  ->
                fun se  ->
                  match uu____4160 with
                  | (g1,iface2) ->
                      let uu____4172 = extract_sigelt_iface g1 se  in
                      (match uu____4172 with
                       | (g2,iface') ->
                           let uu____4183 = iface_union iface2 iface'  in
                           (g2, uu____4183))) (g, iface1) decls
            in
         (let uu____4185 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____4185);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____4202 =
        let uu____4207 = FStar_Options.debug_any ()  in
        if uu____4207
        then
          let uu____4214 =
            FStar_Util.format1 "Extracted interface of %s"
              (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
             in
          FStar_Util.measure_execution_time uu____4214
            (fun uu____4222  -> extract_iface' g modul)
        else extract_iface' g modul  in
      match uu____4202 with
      | (g1,iface1) ->
          let uu____4231 = FStar_Extraction_ML_UEnv.exit_module g1  in
          (uu____4231, iface1)
  
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
          let uu____4309 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4309
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____4317 =
            let uu____4318 =
              let uu____4321 =
                let uu____4322 =
                  FStar_Extraction_ML_UEnv.tcenv_of_uenv env_iparams  in
                FStar_TypeChecker_Normalize.normalize steps uu____4322
                  ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4321  in
            uu____4318.FStar_Syntax_Syntax.n  in
          match uu____4317 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4327) ->
              FStar_List.map
                (fun uu____4360  ->
                   match uu____4360 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4369;
                        FStar_Syntax_Syntax.sort = uu____4370;_},uu____4371)
                       -> ppname.FStar_Ident.idText) bs
          | uu____4379 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____4387 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false  in
        match uu____4387 with
        | (env2,mls,uu____4414) ->
            let uu____4417 =
              let uu____4430 =
                let uu____4438 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____4438  in
              (mls, uu____4430)  in
            (env2, uu____4417)
         in
      let extract_one_family env1 ind =
        let uu____4499 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4499 with
        | (env_iparams,vars) ->
            let uu____4543 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____4543 with
             | (env2,ctors) ->
                 let uu____4650 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____4650 with
                  | (indices,uu____4684) ->
                      let ml_params =
                        let uu____4693 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____4719  ->
                                    let uu____4727 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____4727))
                           in
                        FStar_List.append vars uu____4693  in
                      let uu____4731 =
                        let uu____4736 =
                          FStar_Util.find_opt
                            (fun uu___7_4741  ->
                               match uu___7_4741 with
                               | FStar_Syntax_Syntax.RecordType uu____4743 ->
                                   true
                               | uu____4753 -> false) ind.iquals
                           in
                        match uu____4736 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____4769 = FStar_List.hd ctors  in
                            (match uu____4769 with
                             | (uu____4798,c_ty) ->
                                 let uu____4817 =
                                   FStar_List.fold_right2
                                     (fun id1  ->
                                        fun uu____4856  ->
                                          fun uu____4857  ->
                                            match (uu____4856, uu____4857)
                                            with
                                            | ((uu____4901,ty),(fields,g)) ->
                                                let uu____4937 =
                                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                                    g ((ind.iname), id1)
                                                   in
                                                (match uu____4937 with
                                                 | (mlp,g1) ->
                                                     ((((FStar_Pervasives_Native.snd
                                                           mlp), ty) ::
                                                       fields), g1))) ids
                                     c_ty ([], env2)
                                    in
                                 (match uu____4817 with
                                  | (fields,g) ->
                                      ((FStar_Extraction_ML_Syntax.MLTD_Record
                                          fields), g)))
                        | uu____5004 ->
                            ((FStar_Extraction_ML_Syntax.MLTD_DType ctors),
                              env2)
                         in
                      (match uu____4731 with
                       | (tbody,env3) ->
                           let uu____5035 =
                             let uu____5058 =
                               let uu____5060 =
                                 FStar_Extraction_ML_UEnv.mlpath_of_lident
                                   env3 ind.iname
                                  in
                               FStar_Pervasives_Native.snd uu____5060  in
                             (false, uu____5058,
                               FStar_Pervasives_Native.None, ml_params,
                               (ind.imetadata),
                               (FStar_Pervasives_Native.Some tbody))
                              in
                           (env3, uu____5035))))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____5116,t,uu____5118,uu____5119,uu____5120);
            FStar_Syntax_Syntax.sigrng = uu____5121;
            FStar_Syntax_Syntax.sigquals = uu____5122;
            FStar_Syntax_Syntax.sigmeta = uu____5123;
            FStar_Syntax_Syntax.sigattrs = uu____5124;
            FStar_Syntax_Syntax.sigopts = uu____5125;_}::[],uu____5126),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____5147 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____5147 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____5200),quals) ->
          let uu____5214 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____5214
          then (env, [])
          else
            (let uu____5227 = bundle_as_inductive_families env ses quals  in
             match uu____5227 with
             | (env1,ifams) ->
                 let uu____5246 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____5246 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____5355 -> failwith "Unexpected signature element"
  
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
             let uu____5413 = FStar_Syntax_Util.head_and_args t  in
             match uu____5413 with
             | (head1,args) ->
                 let uu____5461 =
                   let uu____5463 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____5463  in
                 if uu____5461
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5482));
                         FStar_Syntax_Syntax.pos = uu____5483;
                         FStar_Syntax_Syntax.vars = uu____5484;_},uu____5485)::[]
                        ->
                        let uu____5524 =
                          let uu____5528 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5528  in
                        FStar_Pervasives_Native.Some uu____5524
                    | uu____5534 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5549 =
        let uu____5551 = FStar_Options.codegen ()  in
        uu____5551 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5549
      then []
      else
        (let uu____5561 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5561 with
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
                      let uu____5603 =
                        let uu____5604 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5604  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5603  in
                    let uu____5606 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g
                        fv fv_t arity_opt ml_name_str
                       in
                    match uu____5606 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin) ->
                        let uu____5639 =
                          if plugin
                          then
                            ((["FStar_Tactics_Native"], "register_plugin"),
                              [interp; nbe_interp])
                          else
                            ((["FStar_Tactics_Native"], "register_tactic"),
                              [interp])
                           in
                        (match uu____5639 with
                         | (register,args) ->
                             let h =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_Name
                                    register)
                                in
                             let arity1 =
                               let uu____5685 =
                                 let uu____5686 =
                                   let uu____5698 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____5698, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5686
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5685
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
              | uu____5727 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5755 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5755);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5764 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5773 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5790 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           let uu____5807 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
           FStar_TypeChecker_Env.is_reifiable_effect uu____5807
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5808 = extract_reifiable_effect g ed  in
           (match uu____5808 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5832 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_fail uu____5846 ->
           failwith "impossible: trying to extract Sig_fail"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5866 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5872 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____5872 with | (env,uu____5888,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5897) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5906 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____5906 with | (env,uu____5922,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____5931) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5944 = extract_let_rec_types se g lbs  in
           (match uu____5944 with | (env,uu____5960,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____5969) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5980 =
             let uu____5989 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____5989 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____6018) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____5980 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    let uu____6104 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.postprocess uu____6104 tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___909_6105 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___909_6105.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___909_6105.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___909_6105.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___909_6105.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___909_6105.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___909_6105.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____6114 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____6114)  in
                let uu____6132 =
                  let uu____6139 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____6139  in
                (match uu____6132 with
                 | (ml_let,uu____6156,uu____6157) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____6166) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____6183 =
                            FStar_List.fold_left2
                              (fun uu____6209  ->
                                 fun ml_lb  ->
                                   fun uu____6211  ->
                                     match (uu____6209, uu____6211) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____6233;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____6235;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____6236;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____6237;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____6238;_})
                                         ->
                                         let uu____6263 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____6263
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____6280 =
                                                let uu____6283 =
                                                  FStar_Util.right lbname  in
                                                uu____6283.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____6280.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____6287 =
                                                let uu____6288 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____6288.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____6287 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6293,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6294;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____6296;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6297;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____6298;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____6299;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____6300;_})
                                                  when
                                                  let uu____6335 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____6335 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____6339 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___957_6344 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___957_6344.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___957_6344.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___957_6344.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___957_6344.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___957_6344.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____6345 =
                                              let uu____6350 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_6357  ->
                                                        match uu___8_6357
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____6359 ->
                                                            true
                                                        | uu____6365 -> false))
                                                 in
                                              if uu____6350
                                              then
                                                let uu____6372 =
                                                  let uu____6380 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____6381 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv
                                                    env uu____6380 uu____6381
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   in
                                                match uu____6372 with
                                                | (env1,mls,uu____6388) ->
                                                    (env1,
                                                      (let uu___969_6392 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           = mls;
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___969_6392.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___969_6392.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___969_6392.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___969_6392.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___969_6392.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6395 =
                                                   let uu____6403 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6403
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    in
                                                 match uu____6395 with
                                                 | (env1,uu____6409,uu____6410)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____6345 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____6183 with
                           | (g1,ml_lbs') ->
                               let uu____6440 =
                                 let uu____6443 =
                                   let uu____6446 =
                                     let uu____6447 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6447
                                      in
                                   [uu____6446;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____6450 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____6443 uu____6450  in
                               (g1, uu____6440))
                      | uu____6455 ->
                          let uu____6456 =
                            let uu____6458 =
                              let uu____6460 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____6460 ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6458
                             in
                          failwith uu____6456)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6469,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6474 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6480 =
                  let uu____6482 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Util.must_erase_for_extraction uu____6482
                    t
                   in
                Prims.op_Negation uu____6480)
              in
           if uu____6474
           then
             let always_fail1 =
               let uu___989_6491 = se  in
               let uu____6492 =
                 let uu____6493 =
                   let uu____6500 =
                     let uu____6501 =
                       let uu____6504 = always_fail lid t  in [uu____6504]
                        in
                     (false, uu____6501)  in
                   (uu____6500, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6493  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6492;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___989_6491.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___989_6491.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___989_6491.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___989_6491.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___989_6491.FStar_Syntax_Syntax.sigopts)
               }  in
             let uu____6511 = extract_sig g always_fail1  in
             (match uu____6511 with
              | (g1,mlm) ->
                  let uu____6530 =
                    FStar_Util.find_map quals
                      (fun uu___9_6535  ->
                         match uu___9_6535 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6539 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6530 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6547 =
                         let uu____6550 =
                           let uu____6551 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6551  in
                         let uu____6552 =
                           let uu____6555 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6555]  in
                         uu____6550 :: uu____6552  in
                       (g1, uu____6547)
                   | uu____6558 ->
                       let uu____6561 =
                         FStar_Util.find_map quals
                           (fun uu___10_6567  ->
                              match uu___10_6567 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6571)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6572 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6561 with
                        | FStar_Pervasives_Native.Some uu____6579 -> (g1, [])
                        | uu____6582 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6592 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____6592 with
            | (ml_main,uu____6606,uu____6607) ->
                let uu____6608 =
                  let uu____6611 =
                    let uu____6612 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6612  in
                  [uu____6611; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____6608))
       | FStar_Syntax_Syntax.Sig_assume uu____6615 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6624 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6627 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6642 -> (g, [])
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
      let uu____6682 = FStar_Options.restore_cmd_line_options true  in
      let uu____6684 =
        FStar_Extraction_ML_UEnv.extend_with_module_name g
          m.FStar_Syntax_Syntax.name
         in
      match uu____6684 with
      | (name,g1) ->
          let g2 =
            let uu____6698 =
              let uu____6699 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
              FStar_TypeChecker_Env.set_current_module uu____6699
                m.FStar_Syntax_Syntax.name
               in
            FStar_Extraction_ML_UEnv.set_tcenv g1 uu____6698  in
          let g3 = FStar_Extraction_ML_UEnv.set_current_module g2 name  in
          let uu____6701 =
            FStar_Util.fold_map
              (fun g4  ->
                 fun se  ->
                   let uu____6720 =
                     FStar_Options.debug_module
                       (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____6720
                   then
                     let nm =
                       let uu____6731 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lids_of_sigelt se)
                           (FStar_List.map FStar_Ident.string_of_lid)
                          in
                       FStar_All.pipe_right uu____6731
                         (FStar_String.concat ", ")
                        in
                     (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                      (let uu____6748 =
                         FStar_Util.format1 "---Extracted {%s}" nm  in
                       FStar_Util.measure_execution_time uu____6748
                         (fun uu____6758  -> extract_sig g4 se)))
                   else extract_sig g4 se) g3
              m.FStar_Syntax_Syntax.declarations
             in
          (match uu____6701 with
           | (g4,sigs) ->
               let mlm = FStar_List.flatten sigs  in
               let is_kremlin =
                 let uu____6780 = FStar_Options.codegen ()  in
                 uu____6780 =
                   (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                  in
               if
                 ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                   (is_kremlin ||
                      (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
               then
                 ((let uu____6795 =
                     let uu____6797 = FStar_Options.silent ()  in
                     Prims.op_Negation uu____6797  in
                   if uu____6795
                   then
                     let uu____6800 =
                       FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                        in
                     FStar_Util.print1 "Extracted module %s\n" uu____6800
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
      (let uu____6875 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____6875);
      (let uu____6878 =
         let uu____6880 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____6880  in
       if uu____6878
       then
         let uu____6883 =
           let uu____6885 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6885
            in
         failwith uu____6883
       else ());
      (let uu____6890 = FStar_Options.interactive ()  in
       if uu____6890
       then (g, FStar_Pervasives_Native.None)
       else
         (let uu____6903 =
            let uu____6910 = FStar_Options.debug_any ()  in
            if uu____6910
            then
              let msg =
                let uu____6921 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s" uu____6921  in
              FStar_Util.measure_execution_time msg
                (fun uu____6931  -> extract' g m)
            else extract' g m  in
          match uu____6903 with
          | (g1,mllib) ->
              ((let uu____6947 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_left (fun a3  -> ()) uu____6947);
               (let uu____6949 = FStar_Extraction_ML_UEnv.exit_module g1  in
                (uu____6949, mllib)))))
  
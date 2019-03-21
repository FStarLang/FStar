open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____63800 =
        let uu____63807 =
          let uu____63808 =
            let uu____63825 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____63828 =
              let uu____63839 = FStar_Syntax_Syntax.iarg t  in
              let uu____63848 =
                let uu____63859 =
                  let uu____63868 =
                    let uu____63869 =
                      let uu____63876 =
                        let uu____63877 =
                          let uu____63878 =
                            let uu____63884 =
                              let uu____63886 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____63886
                               in
                            (uu____63884, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____63878  in
                        FStar_Syntax_Syntax.Tm_constant uu____63877  in
                      FStar_Syntax_Syntax.mk uu____63876  in
                    uu____63869 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____63868
                   in
                [uu____63859]  in
              uu____63839 :: uu____63848  in
            (uu____63825, uu____63828)  in
          FStar_Syntax_Syntax.Tm_app uu____63808  in
        FStar_Syntax_Syntax.mk uu____63807  in
      uu____63800 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____63952 = FStar_Syntax_Util.arrow_formals t  in
        match uu____63952 with
        | ([],t1) ->
            let b =
              let uu____63995 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____63995
               in
            let uu____64003 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____64003
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____64040 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____64040 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____64044 =
          let uu____64049 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____64049  in
        {
          FStar_Syntax_Syntax.lbname = uu____64044;
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
  'Auu____64071 . 'Auu____64071 Prims.list -> ('Auu____64071 * 'Auu____64071)
  =
  fun uu___612_64082  ->
    match uu___612_64082 with
    | a::b::[] -> (a, b)
    | uu____64087 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_64102  ->
    match uu___613_64102 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____64105 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____64114 = FStar_Syntax_Subst.compress x  in
    match uu____64114 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____64118;
        FStar_Syntax_Syntax.vars = uu____64119;_} ->
        let uu____64122 =
          let uu____64124 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64124  in
        (match uu____64122 with
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
         | uu____64134 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____64137;
             FStar_Syntax_Syntax.vars = uu____64138;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____64140));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____64141;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____64142;_},uu____64143)::[]);
        FStar_Syntax_Syntax.pos = uu____64144;
        FStar_Syntax_Syntax.vars = uu____64145;_} ->
        let uu____64188 =
          let uu____64190 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64190  in
        (match uu____64188 with
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
         | uu____64199 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____64201));
        FStar_Syntax_Syntax.pos = uu____64202;
        FStar_Syntax_Syntax.vars = uu____64203;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____64208));
        FStar_Syntax_Syntax.pos = uu____64209;
        FStar_Syntax_Syntax.vars = uu____64210;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____64215));
        FStar_Syntax_Syntax.pos = uu____64216;
        FStar_Syntax_Syntax.vars = uu____64217;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____64223);
        FStar_Syntax_Syntax.pos = uu____64224;
        FStar_Syntax_Syntax.vars = uu____64225;_} -> extract_meta x1
    | uu____64232 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____64252 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____64252) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____64294  ->
             match uu____64294 with
             | (bv,uu____64305) ->
                 let uu____64306 =
                   let uu____64307 =
                     let uu____64310 =
                       let uu____64311 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____64311  in
                     FStar_Pervasives_Native.Some uu____64310  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____64307  in
                 let uu____64313 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____64306, uu____64313)) env bs
  
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
    let uu____64514 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____64516 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____64519 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____64521 =
      let uu____64523 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____64537 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____64539 =
                  let uu____64541 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____64541  in
                Prims.op_Hat uu____64537 uu____64539))
         in
      FStar_All.pipe_right uu____64523 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____64514 uu____64516
      uu____64519 uu____64521
  
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
          let uu____64595 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____64643 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____64643 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____64682,t2,l',nparams,uu____64686)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____64693 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____64693 with
                                           | (bs',body) ->
                                               let uu____64732 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____64732 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____64823  ->
                                                           fun uu____64824 
                                                             ->
                                                             match (uu____64823,
                                                                    uu____64824)
                                                             with
                                                             | ((b',uu____64850),
                                                                (b,uu____64852))
                                                                 ->
                                                                 let uu____64873
                                                                   =
                                                                   let uu____64880
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____64880)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____64873)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____64886 =
                                                        let uu____64887 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____64887
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____64886
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____64890 -> []))
                               in
                            let metadata =
                              let uu____64894 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____64897 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____64894 uu____64897  in
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
                   | uu____64904 -> (env1, [])) env ses
             in
          match uu____64595 with
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
    let uu___820_65084 = empty_iface  in
    {
      iface_module_name = (uu___820_65084.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___820_65084.iface_tydefs);
      iface_type_names = (uu___820_65084.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___823_65095 = empty_iface  in
    let uu____65096 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___823_65095.iface_module_name);
      iface_bindings = (uu___823_65095.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____65096
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___827_65111 = empty_iface  in
    {
      iface_module_name = (uu___827_65111.iface_module_name);
      iface_bindings = (uu___827_65111.iface_bindings);
      iface_tydefs = (uu___827_65111.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____65123 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____65123;
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
  'Auu____65168 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____65168 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____65200 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____65202 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____65204 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____65200 uu____65202
        uu____65204
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____65222  ->
      match uu____65222 with
      | (fv,exp_binding) ->
          let uu____65230 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____65232 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____65230 uu____65232
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____65247 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____65249 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____65247 uu____65249
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____65267 =
      let uu____65269 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____65269 (FStar_String.concat "\n")  in
    let uu____65283 =
      let uu____65285 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____65285 (FStar_String.concat "\n")  in
    let uu____65295 =
      let uu____65297 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____65297 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____65267 uu____65283
      uu____65295
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_65330  ->
           match uu___614_65330 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____65347 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____65352 =
      let uu____65354 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____65354 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____65352
  
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
          let uu____65414 =
            let uu____65423 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____65423 with
            | (tcenv,uu____65441,def_typ) ->
                let uu____65447 = as_pair def_typ  in (tcenv, uu____65447)
             in
          match uu____65414 with
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
                let uu____65478 =
                  let uu____65479 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____65479 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____65478 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____65487 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____65506 -> def  in
              let uu____65507 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____65518) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____65543 -> ([], def1)  in
              (match uu____65507 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_65563  ->
                          match uu___615_65563 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____65566 -> false) quals
                      in
                   let uu____65568 = binders_as_mlty_binders env bs  in
                   (match uu____65568 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____65595 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____65595
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____65600 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_65607  ->
                                    match uu___616_65607 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____65609 -> true
                                    | uu____65615 -> false))
                             in
                          if uu____65600
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____65629 = extract_metadata attrs  in
                          let uu____65632 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____65629 uu____65632  in
                        let td =
                          let uu____65655 = lident_as_mlsymbol lid  in
                          (assumed, uu____65655, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____65667 =
                            let uu____65668 =
                              let uu____65669 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____65669
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____65668
                             in
                          [uu____65667;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____65670 =
                          let uu____65675 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_65681  ->
                                    match uu___617_65681 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____65685 -> false))
                             in
                          if uu____65675
                          then
                            let uu____65692 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____65692, (iface_of_type_names [fv]))
                          else
                            (let uu____65695 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____65695 with
                             | (env2,tydef) ->
                                 let uu____65706 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____65706))
                           in
                        (match uu____65670 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____65782 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____65782
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____65789 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____65789 with | (env2,uu____65808,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____65847 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____65847 with
        | (env_iparams,vars) ->
            let uu____65875 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____65875 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____65939,t,uu____65941,uu____65942,uu____65943);
            FStar_Syntax_Syntax.sigrng = uu____65944;
            FStar_Syntax_Syntax.sigquals = uu____65945;
            FStar_Syntax_Syntax.sigmeta = uu____65946;
            FStar_Syntax_Syntax.sigattrs = uu____65947;_}::[],uu____65948),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____65967 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____65967 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____66000),quals) ->
          let uu____66014 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____66014 with
           | (env1,ifams) ->
               let uu____66031 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____66031 with
                | (env2,td) ->
                    let uu____66072 =
                      let uu____66073 =
                        let uu____66074 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____66074  in
                      iface_union uu____66073
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____66072)))
      | uu____66083 -> failwith "Unexpected signature element"
  
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
              let uu____66158 =
                let uu____66160 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_66166  ->
                          match uu___618_66166 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____66169 -> false))
                   in
                Prims.op_Negation uu____66160  in
              if uu____66158
              then (g, empty_iface, [])
              else
                (let uu____66184 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____66184 with
                 | (bs,uu____66208) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____66231 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____66231;
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
        let uu____66294 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____66294 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____66316 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____66316
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
        (let uu____66352 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66352
         then
           let uu____66357 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____66357
         else ());
        (let uu____66362 =
           let uu____66363 = FStar_Syntax_Subst.compress tm  in
           uu____66363.FStar_Syntax_Syntax.n  in
         match uu____66362 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____66371) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____66378 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____66378 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____66383;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____66384;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____66386;_} ->
                  let uu____66389 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____66389, tysc))
         | uu____66390 ->
             let uu____66391 =
               let uu____66393 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____66395 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____66393
                 uu____66395
                in
             failwith uu____66391)
         in
      let extract_action g1 a =
        (let uu____66423 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66423
         then
           let uu____66428 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____66430 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____66428
             uu____66430
         else ());
        (let uu____66435 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____66435 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____66455 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____66455  in
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
             let uu____66485 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____66485 with
              | (a_let,uu____66501,ty) ->
                  ((let uu____66504 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____66504
                    then
                      let uu____66509 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____66509
                    else ());
                   (let uu____66514 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____66537,mllb::[]),uu____66539) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____66579 -> failwith "Impossible"  in
                    match uu____66514 with
                    | (exp,tysc) ->
                        ((let uu____66617 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____66617
                          then
                            ((let uu____66623 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____66623);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____66639 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____66639 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____66661 =
        let uu____66668 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____66668 with
        | (return_tm,ty_sc) ->
            let uu____66685 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____66685 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____66661 with
      | (g1,return_iface,return_decl) ->
          let uu____66710 =
            let uu____66717 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____66717 with
            | (bind_tm,ty_sc) ->
                let uu____66734 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____66734 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____66710 with
           | (g2,bind_iface,bind_decl) ->
               let uu____66759 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____66759 with
                | (g3,actions) ->
                    let uu____66796 = FStar_List.unzip actions  in
                    (match uu____66796 with
                     | (actions_iface,actions1) ->
                         let uu____66823 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____66823, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____66845 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____66854 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____66871 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____66890 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____66890 with | (env,iface1,uu____66905) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____66911) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____66920 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____66920 with | (env,iface1,uu____66935) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____66946 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____66952 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____66952)
             in
          if uu____66946
          then
            let uu____66959 =
              let uu____66970 =
                let uu____66971 =
                  let uu____66974 = always_fail lid t  in [uu____66974]  in
                (false, uu____66971)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____66970  in
            (match uu____66959 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____67000) ->
          let uu____67005 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____67005 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____67034 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____67035 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____67036 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____67043 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____67044 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____67059 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____67072 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____67072
          then
            let uu____67085 = extract_reifiable_effect g ed  in
            (match uu____67085 with
             | (env,iface1,uu____67100) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67122 = FStar_Options.interactive ()  in
      if uu____67122
      then (g, empty_iface)
      else
        (let uu____67131 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1166_67135 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1166_67135.iface_bindings);
             iface_tydefs = (uu___1166_67135.iface_tydefs);
             iface_type_names = (uu___1166_67135.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____67153  ->
                fun se  ->
                  match uu____67153 with
                  | (g1,iface2) ->
                      let uu____67165 = extract_sigelt_iface g1 se  in
                      (match uu____67165 with
                       | (g2,iface') ->
                           let uu____67176 = iface_union iface2 iface'  in
                           (g2, uu____67176))) (g, iface1) decls
            in
         (let uu____67178 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____67178);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67195 = FStar_Options.debug_any ()  in
      if uu____67195
      then
        let uu____67202 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____67202
          (fun uu____67210  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1184_67224 = g  in
      let uu____67225 =
        let uu____67228 =
          FStar_List.map (fun _67235  -> FStar_Extraction_ML_UEnv.Fv _67235)
            iface1.iface_bindings
           in
        FStar_List.append uu____67228 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1184_67224.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____67225;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1184_67224.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____67313 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____67313
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____67321 =
            let uu____67322 =
              let uu____67325 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____67325  in
            uu____67322.FStar_Syntax_Syntax.n  in
          match uu____67321 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____67330) ->
              FStar_List.map
                (fun uu____67363  ->
                   match uu____67363 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____67372;
                        FStar_Syntax_Syntax.sort = uu____67373;_},uu____67374)
                       -> ppname.FStar_Ident.idText) bs
          | uu____67382 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____67390 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____67390 with
        | (env2,uu____67417,uu____67418) ->
            let uu____67421 =
              let uu____67434 = lident_as_mlsymbol ctor.dname  in
              let uu____67436 =
                let uu____67444 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____67444  in
              (uu____67434, uu____67436)  in
            (env2, uu____67421)
         in
      let extract_one_family env1 ind =
        let uu____67505 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____67505 with
        | (env_iparams,vars) ->
            let uu____67549 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____67549 with
             | (env2,ctors) ->
                 let uu____67656 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____67656 with
                  | (indices,uu____67698) ->
                      let ml_params =
                        let uu____67723 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____67749  ->
                                    let uu____67757 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____67757))
                           in
                        FStar_List.append vars uu____67723  in
                      let tbody =
                        let uu____67762 =
                          FStar_Util.find_opt
                            (fun uu___619_67767  ->
                               match uu___619_67767 with
                               | FStar_Syntax_Syntax.RecordType uu____67769
                                   -> true
                               | uu____67779 -> false) ind.iquals
                           in
                        match uu____67762 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____67791 = FStar_List.hd ctors  in
                            (match uu____67791 with
                             | (uu____67816,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____67860  ->
                                          match uu____67860 with
                                          | (uu____67871,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____67876 =
                                                lident_as_mlsymbol lid  in
                                              (uu____67876, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____67879 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____67882 =
                        let uu____67905 = lident_as_mlsymbol ind.iname  in
                        (false, uu____67905, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____67882)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____67950,t,uu____67952,uu____67953,uu____67954);
            FStar_Syntax_Syntax.sigrng = uu____67955;
            FStar_Syntax_Syntax.sigquals = uu____67956;
            FStar_Syntax_Syntax.sigmeta = uu____67957;
            FStar_Syntax_Syntax.sigattrs = uu____67958;_}::[],uu____67959),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____67978 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____67978 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____68031),quals) ->
          let uu____68045 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____68045 with
           | (env1,ifams) ->
               let uu____68064 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____68064 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____68173 -> failwith "Unexpected signature element"
  
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
             let uu____68231 = FStar_Syntax_Util.head_and_args t  in
             match uu____68231 with
             | (head1,args) ->
                 let uu____68279 =
                   let uu____68281 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____68281  in
                 if uu____68279
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____68300));
                         FStar_Syntax_Syntax.pos = uu____68301;
                         FStar_Syntax_Syntax.vars = uu____68302;_},uu____68303)::[]
                        ->
                        let uu____68342 =
                          let uu____68346 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____68346  in
                        FStar_Pervasives_Native.Some uu____68342
                    | uu____68352 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____68367 =
        let uu____68369 = FStar_Options.codegen ()  in
        uu____68369 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____68367
      then []
      else
        (let uu____68379 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____68379 with
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
                      let uu____68421 =
                        let uu____68422 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____68422  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____68421  in
                    let uu____68424 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____68424 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____68457 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____68457 with
                         | (register,args) ->
                             let h =
                               let uu____68494 =
                                 let uu____68495 =
                                   let uu____68496 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____68496
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____68495
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____68494
                                in
                             let arity1 =
                               let uu____68498 =
                                 let uu____68499 =
                                   let uu____68511 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____68511,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____68499
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____68498
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
              | uu____68540 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____68568 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____68568);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____68577 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____68586 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____68603 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____68620 = extract_reifiable_effect g ed  in
           (match uu____68620 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____68644 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____68658 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____68664 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____68664 with | (env,uu____68680,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____68689) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____68698 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____68698 with | (env,uu____68714,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____68723) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____68734 =
             let uu____68743 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____68743 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____68772) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____68734 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1403_68858 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1403_68858.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1403_68858.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1403_68858.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1403_68858.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1403_68858.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1403_68858.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____68867 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____68867)  in
                let uu____68885 =
                  let uu____68892 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____68892  in
                (match uu____68885 with
                 | (ml_let,uu____68909,uu____68910) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____68919) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____68936 =
                            FStar_List.fold_left2
                              (fun uu____68962  ->
                                 fun ml_lb  ->
                                   fun uu____68964  ->
                                     match (uu____68962, uu____68964) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____68986;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____68988;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____68989;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____68990;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____68991;_})
                                         ->
                                         let uu____69016 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____69016
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____69033 =
                                                let uu____69036 =
                                                  FStar_Util.right lbname  in
                                                uu____69036.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____69033.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____69040 =
                                                let uu____69041 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____69041.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____69040 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____69046,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____69047;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____69049;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____69050;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____69051;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____69052;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____69053;_})
                                                  when
                                                  let uu____69088 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____69088 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____69092 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1451_69097 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1451_69097.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1451_69097.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1451_69097.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1451_69097.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1451_69097.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____69098 =
                                              let uu____69103 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_69110  ->
                                                        match uu___620_69110
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____69112 ->
                                                            true
                                                        | uu____69118 ->
                                                            false))
                                                 in
                                              if uu____69103
                                              then
                                                let mname =
                                                  let uu____69134 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____69134
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____69143 =
                                                  let uu____69151 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____69152 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____69151 mname
                                                    uu____69152
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____69143 with
                                                | (env1,uu____69159,uu____69160)
                                                    ->
                                                    (env1,
                                                      (let uu___1464_69164 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1464_69164.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1464_69164.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1464_69164.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1464_69164.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1464_69164.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____69171 =
                                                   let uu____69179 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____69179
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____69171 with
                                                 | (env1,uu____69186,uu____69187)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____69098 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____68936 with
                           | (g1,ml_lbs') ->
                               let uu____69217 =
                                 let uu____69220 =
                                   let uu____69223 =
                                     let uu____69224 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____69224
                                      in
                                   [uu____69223;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____69227 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____69220 uu____69227
                                  in
                               (g1, uu____69217))
                      | uu____69232 ->
                          let uu____69233 =
                            let uu____69235 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____69235
                             in
                          failwith uu____69233)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____69245,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____69250 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____69256 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____69256)
              in
           if uu____69250
           then
             let always_fail1 =
               let uu___1484_69266 = se  in
               let uu____69267 =
                 let uu____69268 =
                   let uu____69275 =
                     let uu____69276 =
                       let uu____69279 = always_fail lid t  in [uu____69279]
                        in
                     (false, uu____69276)  in
                   (uu____69275, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____69268  in
               {
                 FStar_Syntax_Syntax.sigel = uu____69267;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1484_69266.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1484_69266.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1484_69266.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1484_69266.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____69286 = extract_sig g always_fail1  in
             (match uu____69286 with
              | (g1,mlm) ->
                  let uu____69305 =
                    FStar_Util.find_map quals
                      (fun uu___621_69310  ->
                         match uu___621_69310 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____69314 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____69305 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____69322 =
                         let uu____69325 =
                           let uu____69326 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____69326  in
                         let uu____69327 =
                           let uu____69330 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____69330]  in
                         uu____69325 :: uu____69327  in
                       (g1, uu____69322)
                   | uu____69333 ->
                       let uu____69336 =
                         FStar_Util.find_map quals
                           (fun uu___622_69342  ->
                              match uu___622_69342 with
                              | FStar_Syntax_Syntax.Projector (l,uu____69346)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____69347 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____69336 with
                        | FStar_Pervasives_Native.Some uu____69354 ->
                            (g1, [])
                        | uu____69357 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____69367 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____69367 with
            | (ml_main,uu____69381,uu____69382) ->
                let uu____69383 =
                  let uu____69386 =
                    let uu____69387 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____69387  in
                  [uu____69386; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____69383))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69390 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____69398 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____69407 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69410 -> (g, [])
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
      let uu____69452 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1527_69456 = g  in
        let uu____69457 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____69457;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1527_69456.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1527_69456.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1527_69456.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____69458 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____69477 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____69477
               then
                 let nm =
                   let uu____69488 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____69488
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____69505 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____69505
                     (fun uu____69515  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____69458 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____69537 = FStar_Options.codegen ()  in
            uu____69537 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____69552 =
                let uu____69554 = FStar_Options.silent ()  in
                Prims.op_Negation uu____69554  in
              if uu____69552
              then
                let uu____69557 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____69557
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
      (let uu____69632 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____69632);
      (let uu____69635 =
         let uu____69637 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____69637  in
       if uu____69635
       then
         let uu____69640 =
           let uu____69642 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____69642
            in
         failwith uu____69640
       else ());
      (let uu____69647 = FStar_Options.interactive ()  in
       if uu____69647
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____69667 = FStar_Options.debug_any ()  in
            if uu____69667
            then
              let msg =
                let uu____69678 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____69678  in
              FStar_Util.measure_execution_time msg
                (fun uu____69688  -> extract' g m)
            else extract' g m  in
          (let uu____69692 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____69692);
          res))
  
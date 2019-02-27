open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____68622 =
        let uu____68629 =
          let uu____68630 =
            let uu____68647 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____68650 =
              let uu____68661 = FStar_Syntax_Syntax.iarg t  in
              let uu____68670 =
                let uu____68681 =
                  let uu____68690 =
                    let uu____68691 =
                      let uu____68698 =
                        let uu____68699 =
                          let uu____68700 =
                            let uu____68706 =
                              let uu____68708 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____68708
                               in
                            (uu____68706, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____68700  in
                        FStar_Syntax_Syntax.Tm_constant uu____68699  in
                      FStar_Syntax_Syntax.mk uu____68698  in
                    uu____68691 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____68690
                   in
                [uu____68681]  in
              uu____68661 :: uu____68670  in
            (uu____68647, uu____68650)  in
          FStar_Syntax_Syntax.Tm_app uu____68630  in
        FStar_Syntax_Syntax.mk uu____68629  in
      uu____68622 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____68780 = FStar_Syntax_Util.arrow_formals t  in
        match uu____68780 with
        | ([],t1) ->
            let b =
              let uu____68823 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____68823
               in
            let uu____68831 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____68831
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____68868 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____68868 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____68872 =
          let uu____68877 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____68877  in
        {
          FStar_Syntax_Syntax.lbname = uu____68872;
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
  'Auu____68899 . 'Auu____68899 Prims.list -> ('Auu____68899 * 'Auu____68899)
  =
  fun uu___612_68910  ->
    match uu___612_68910 with
    | a::b::[] -> (a, b)
    | uu____68915 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_68930  ->
    match uu___613_68930 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____68933 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____68942 = FStar_Syntax_Subst.compress x  in
    match uu____68942 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____68946;
        FStar_Syntax_Syntax.vars = uu____68947;_} ->
        let uu____68950 =
          let uu____68952 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____68952  in
        (match uu____68950 with
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
         | uu____68962 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____68965;
             FStar_Syntax_Syntax.vars = uu____68966;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____68968));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____68969;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____68970;_},uu____68971)::[]);
        FStar_Syntax_Syntax.pos = uu____68972;
        FStar_Syntax_Syntax.vars = uu____68973;_} ->
        let uu____69016 =
          let uu____69018 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____69018  in
        (match uu____69016 with
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
         | uu____69027 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____69029));
        FStar_Syntax_Syntax.pos = uu____69030;
        FStar_Syntax_Syntax.vars = uu____69031;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____69036));
        FStar_Syntax_Syntax.pos = uu____69037;
        FStar_Syntax_Syntax.vars = uu____69038;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____69043));
        FStar_Syntax_Syntax.pos = uu____69044;
        FStar_Syntax_Syntax.vars = uu____69045;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____69051);
        FStar_Syntax_Syntax.pos = uu____69052;
        FStar_Syntax_Syntax.vars = uu____69053;_} -> extract_meta x1
    | uu____69060 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____69080 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____69080) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____69122  ->
             match uu____69122 with
             | (bv,uu____69133) ->
                 let uu____69134 =
                   let uu____69135 =
                     let uu____69138 =
                       let uu____69139 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____69139  in
                     FStar_Pervasives_Native.Some uu____69138  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____69135  in
                 let uu____69141 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____69134, uu____69141)) env bs
  
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
    let uu____69342 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____69344 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____69347 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____69349 =
      let uu____69351 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____69365 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____69367 =
                  let uu____69369 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____69369  in
                Prims.op_Hat uu____69365 uu____69367))
         in
      FStar_All.pipe_right uu____69351 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____69342 uu____69344
      uu____69347 uu____69349
  
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
          let uu____69423 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____69471 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____69471 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____69510,t2,l',nparams,uu____69514)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____69521 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____69521 with
                                           | (bs',body) ->
                                               let uu____69560 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____69560 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____69651  ->
                                                           fun uu____69652 
                                                             ->
                                                             match (uu____69651,
                                                                    uu____69652)
                                                             with
                                                             | ((b',uu____69678),
                                                                (b,uu____69680))
                                                                 ->
                                                                 let uu____69701
                                                                   =
                                                                   let uu____69708
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____69708)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____69701)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____69714 =
                                                        let uu____69715 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____69715
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____69714
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____69718 -> []))
                               in
                            let metadata =
                              let uu____69722 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____69725 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____69722 uu____69725  in
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
                   | uu____69732 -> (env1, [])) env ses
             in
          match uu____69423 with
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
    let uu___820_69912 = empty_iface  in
    {
      iface_module_name = (uu___820_69912.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___820_69912.iface_tydefs);
      iface_type_names = (uu___820_69912.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___823_69923 = empty_iface  in
    let uu____69924 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___823_69923.iface_module_name);
      iface_bindings = (uu___823_69923.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____69924
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___827_69939 = empty_iface  in
    {
      iface_module_name = (uu___827_69939.iface_module_name);
      iface_bindings = (uu___827_69939.iface_bindings);
      iface_tydefs = (uu___827_69939.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____69951 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____69951;
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
  'Auu____69996 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____69996 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____70028 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____70030 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____70032 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____70028 uu____70030
        uu____70032
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____70050  ->
      match uu____70050 with
      | (fv,exp_binding) ->
          let uu____70058 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____70060 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____70058 uu____70060
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____70075 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____70077 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____70075 uu____70077
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____70095 =
      let uu____70097 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____70097 (FStar_String.concat "\n")  in
    let uu____70111 =
      let uu____70113 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____70113 (FStar_String.concat "\n")  in
    let uu____70123 =
      let uu____70125 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____70125 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____70095 uu____70111
      uu____70123
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_70158  ->
           match uu___614_70158 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____70175 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____70180 =
      let uu____70182 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____70182 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____70180
  
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
          let uu____70242 =
            let uu____70251 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____70251 with
            | (tcenv,uu____70269,def_typ) ->
                let uu____70275 = as_pair def_typ  in (tcenv, uu____70275)
             in
          match uu____70242 with
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
                let uu____70306 =
                  let uu____70307 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____70307 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____70306 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____70315 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____70334 -> def  in
              let uu____70335 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____70346) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____70371 -> ([], def1)  in
              (match uu____70335 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_70391  ->
                          match uu___615_70391 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____70394 -> false) quals
                      in
                   let uu____70396 = binders_as_mlty_binders env bs  in
                   (match uu____70396 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____70423 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____70423
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____70428 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_70435  ->
                                    match uu___616_70435 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____70437 -> true
                                    | uu____70443 -> false))
                             in
                          if uu____70428
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____70457 = extract_metadata attrs  in
                          let uu____70460 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____70457 uu____70460  in
                        let td =
                          let uu____70483 = lident_as_mlsymbol lid  in
                          (assumed, uu____70483, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____70495 =
                            let uu____70496 =
                              let uu____70497 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____70497
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____70496
                             in
                          [uu____70495;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____70498 =
                          let uu____70503 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_70509  ->
                                    match uu___617_70509 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____70513 -> false))
                             in
                          if uu____70503
                          then
                            let uu____70520 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____70520, (iface_of_type_names [fv]))
                          else
                            (let uu____70523 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____70523 with
                             | (env2,tydef) ->
                                 let uu____70534 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____70534))
                           in
                        (match uu____70498 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____70610 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____70610
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____70617 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____70617 with | (env2,uu____70636,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____70675 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____70675 with
        | (env_iparams,vars) ->
            let uu____70703 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____70703 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____70767,t,uu____70769,uu____70770,uu____70771);
            FStar_Syntax_Syntax.sigrng = uu____70772;
            FStar_Syntax_Syntax.sigquals = uu____70773;
            FStar_Syntax_Syntax.sigmeta = uu____70774;
            FStar_Syntax_Syntax.sigattrs = uu____70775;_}::[],uu____70776),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____70795 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____70795 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____70828),quals) ->
          let uu____70842 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____70842 with
           | (env1,ifams) ->
               let uu____70859 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____70859 with
                | (env2,td) ->
                    let uu____70900 =
                      let uu____70901 =
                        let uu____70902 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____70902  in
                      iface_union uu____70901
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____70900)))
      | uu____70911 -> failwith "Unexpected signature element"
  
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
              let uu____70986 =
                let uu____70988 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_70994  ->
                          match uu___618_70994 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____70997 -> false))
                   in
                Prims.op_Negation uu____70988  in
              if uu____70986
              then (g, empty_iface, [])
              else
                (let uu____71012 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____71012 with
                 | (bs,uu____71036) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____71059 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____71059;
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
        let uu____71122 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____71122 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____71144 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____71144
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
        (let uu____71180 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71180
         then
           let uu____71185 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____71185
         else ());
        (let uu____71190 =
           let uu____71191 = FStar_Syntax_Subst.compress tm  in
           uu____71191.FStar_Syntax_Syntax.n  in
         match uu____71190 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____71199) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____71206 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____71206 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____71211;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____71212;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____71214;_} ->
                  let uu____71217 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____71217, tysc))
         | uu____71218 ->
             let uu____71219 =
               let uu____71221 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____71223 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____71221
                 uu____71223
                in
             failwith uu____71219)
         in
      let extract_action g1 a =
        (let uu____71251 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71251
         then
           let uu____71256 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____71258 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____71256
             uu____71258
         else ());
        (let uu____71263 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____71263 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____71283 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____71283  in
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
             let uu____71313 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____71313 with
              | (a_let,uu____71329,ty) ->
                  ((let uu____71332 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____71332
                    then
                      let uu____71337 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____71337
                    else ());
                   (let uu____71342 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____71365,mllb::[]),uu____71367) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____71407 -> failwith "Impossible"  in
                    match uu____71342 with
                    | (exp,tysc) ->
                        ((let uu____71445 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____71445
                          then
                            ((let uu____71451 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____71451);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____71467 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____71467 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____71489 =
        let uu____71496 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____71496 with
        | (return_tm,ty_sc) ->
            let uu____71513 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____71513 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____71489 with
      | (g1,return_iface,return_decl) ->
          let uu____71538 =
            let uu____71545 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____71545 with
            | (bind_tm,ty_sc) ->
                let uu____71562 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____71562 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____71538 with
           | (g2,bind_iface,bind_decl) ->
               let uu____71587 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____71587 with
                | (g3,actions) ->
                    let uu____71624 = FStar_List.unzip actions  in
                    (match uu____71624 with
                     | (actions_iface,actions1) ->
                         let uu____71651 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____71651, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____71673 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____71682 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____71699 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____71718 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____71718 with | (env,iface1,uu____71733) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____71739) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____71748 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____71748 with | (env,iface1,uu____71763) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____71774 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____71780 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____71780)
             in
          if uu____71774
          then
            let uu____71787 =
              let uu____71798 =
                let uu____71799 =
                  let uu____71802 = always_fail lid t  in [uu____71802]  in
                (false, uu____71799)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____71798  in
            (match uu____71787 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____71828) ->
          let uu____71833 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____71833 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____71862 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____71863 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____71864 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____71871 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____71872 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____71887 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____71900 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____71900
          then
            let uu____71913 = extract_reifiable_effect g ed  in
            (match uu____71913 with
             | (env,iface1,uu____71928) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____71950 = FStar_Options.interactive ()  in
      if uu____71950
      then (g, empty_iface)
      else
        (let uu____71959 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1166_71963 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1166_71963.iface_bindings);
             iface_tydefs = (uu___1166_71963.iface_tydefs);
             iface_type_names = (uu___1166_71963.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____71981  ->
                fun se  ->
                  match uu____71981 with
                  | (g1,iface2) ->
                      let uu____71993 = extract_sigelt_iface g1 se  in
                      (match uu____71993 with
                       | (g2,iface') ->
                           let uu____72004 = iface_union iface2 iface'  in
                           (g2, uu____72004))) (g, iface1) decls
            in
         (let uu____72006 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____72006);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____72023 = FStar_Options.debug_any ()  in
      if uu____72023
      then
        let uu____72030 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____72030
          (fun uu____72038  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1184_72052 = g  in
      let uu____72053 =
        let uu____72056 =
          FStar_List.map (fun _72063  -> FStar_Extraction_ML_UEnv.Fv _72063)
            iface1.iface_bindings
           in
        FStar_List.append uu____72056 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1184_72052.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____72053;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1184_72052.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____72141 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____72141
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____72149 =
            let uu____72150 =
              let uu____72153 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____72153  in
            uu____72150.FStar_Syntax_Syntax.n  in
          match uu____72149 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____72158) ->
              FStar_List.map
                (fun uu____72191  ->
                   match uu____72191 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____72200;
                        FStar_Syntax_Syntax.sort = uu____72201;_},uu____72202)
                       -> ppname.FStar_Ident.idText) bs
          | uu____72210 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____72218 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____72218 with
        | (env2,uu____72245,uu____72246) ->
            let uu____72249 =
              let uu____72262 = lident_as_mlsymbol ctor.dname  in
              let uu____72264 =
                let uu____72272 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____72272  in
              (uu____72262, uu____72264)  in
            (env2, uu____72249)
         in
      let extract_one_family env1 ind =
        let uu____72333 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____72333 with
        | (env_iparams,vars) ->
            let uu____72377 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____72377 with
             | (env2,ctors) ->
                 let uu____72484 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____72484 with
                  | (indices,uu____72526) ->
                      let ml_params =
                        let uu____72551 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____72577  ->
                                    let uu____72585 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____72585))
                           in
                        FStar_List.append vars uu____72551  in
                      let tbody =
                        let uu____72590 =
                          FStar_Util.find_opt
                            (fun uu___619_72595  ->
                               match uu___619_72595 with
                               | FStar_Syntax_Syntax.RecordType uu____72597
                                   -> true
                               | uu____72607 -> false) ind.iquals
                           in
                        match uu____72590 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____72619 = FStar_List.hd ctors  in
                            (match uu____72619 with
                             | (uu____72644,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____72688  ->
                                          match uu____72688 with
                                          | (uu____72699,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____72704 =
                                                lident_as_mlsymbol lid  in
                                              (uu____72704, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____72707 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____72710 =
                        let uu____72733 = lident_as_mlsymbol ind.iname  in
                        (false, uu____72733, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____72710)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____72778,t,uu____72780,uu____72781,uu____72782);
            FStar_Syntax_Syntax.sigrng = uu____72783;
            FStar_Syntax_Syntax.sigquals = uu____72784;
            FStar_Syntax_Syntax.sigmeta = uu____72785;
            FStar_Syntax_Syntax.sigattrs = uu____72786;_}::[],uu____72787),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____72806 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____72806 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____72859),quals) ->
          let uu____72873 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____72873 with
           | (env1,ifams) ->
               let uu____72892 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____72892 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____73001 -> failwith "Unexpected signature element"
  
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
             let uu____73059 = FStar_Syntax_Util.head_and_args t  in
             match uu____73059 with
             | (head1,args) ->
                 let uu____73107 =
                   let uu____73109 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____73109  in
                 if uu____73107
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____73128));
                         FStar_Syntax_Syntax.pos = uu____73129;
                         FStar_Syntax_Syntax.vars = uu____73130;_},uu____73131)::[]
                        ->
                        let uu____73170 =
                          let uu____73174 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____73174  in
                        FStar_Pervasives_Native.Some uu____73170
                    | uu____73180 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____73195 =
        let uu____73197 = FStar_Options.codegen ()  in
        uu____73197 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____73195
      then []
      else
        (let uu____73207 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____73207 with
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
                      let uu____73249 =
                        let uu____73250 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____73250  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____73249  in
                    let uu____73252 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____73252 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____73285 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____73285 with
                         | (register,args) ->
                             let h =
                               let uu____73322 =
                                 let uu____73323 =
                                   let uu____73324 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____73324
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____73323
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____73322
                                in
                             let arity1 =
                               let uu____73326 =
                                 let uu____73327 =
                                   let uu____73339 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____73339,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____73327
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____73326
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
              | uu____73368 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____73396 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____73396);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____73405 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____73414 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____73431 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____73448 = extract_reifiable_effect g ed  in
           (match uu____73448 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____73472 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____73486 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____73492 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____73492 with | (env,uu____73508,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____73517) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____73526 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____73526 with | (env,uu____73542,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____73551) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____73562 =
             let uu____73571 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____73571 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____73600) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____73562 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1403_73686 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1403_73686.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1403_73686.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1403_73686.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1403_73686.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1403_73686.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1403_73686.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____73695 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____73695)  in
                let uu____73713 =
                  let uu____73720 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____73720  in
                (match uu____73713 with
                 | (ml_let,uu____73737,uu____73738) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____73747) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____73764 =
                            FStar_List.fold_left2
                              (fun uu____73790  ->
                                 fun ml_lb  ->
                                   fun uu____73792  ->
                                     match (uu____73790, uu____73792) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____73814;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____73816;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____73817;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____73818;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____73819;_})
                                         ->
                                         let uu____73844 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____73844
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____73861 =
                                                let uu____73864 =
                                                  FStar_Util.right lbname  in
                                                uu____73864.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____73861.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____73868 =
                                                let uu____73869 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____73869.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____73868 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____73874,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____73875;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____73877;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____73878;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____73879;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____73880;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____73881;_})
                                                  when
                                                  let uu____73916 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____73916 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____73920 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1451_73925 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1451_73925.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1451_73925.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1451_73925.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1451_73925.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1451_73925.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____73926 =
                                              let uu____73931 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_73938  ->
                                                        match uu___620_73938
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____73940 ->
                                                            true
                                                        | uu____73946 ->
                                                            false))
                                                 in
                                              if uu____73931
                                              then
                                                let mname =
                                                  let uu____73962 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____73962
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____73971 =
                                                  let uu____73979 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____73980 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____73979 mname
                                                    uu____73980
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____73971 with
                                                | (env1,uu____73987,uu____73988)
                                                    ->
                                                    (env1,
                                                      (let uu___1464_73992 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1464_73992.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1464_73992.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1464_73992.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1464_73992.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1464_73992.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____73999 =
                                                   let uu____74007 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____74007
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____73999 with
                                                 | (env1,uu____74014,uu____74015)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____73926 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____73764 with
                           | (g1,ml_lbs') ->
                               let uu____74045 =
                                 let uu____74048 =
                                   let uu____74051 =
                                     let uu____74052 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____74052
                                      in
                                   [uu____74051;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____74055 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____74048 uu____74055
                                  in
                               (g1, uu____74045))
                      | uu____74060 ->
                          let uu____74061 =
                            let uu____74063 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____74063
                             in
                          failwith uu____74061)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____74073,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____74078 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____74084 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____74084)
              in
           if uu____74078
           then
             let always_fail1 =
               let uu___1484_74094 = se  in
               let uu____74095 =
                 let uu____74096 =
                   let uu____74103 =
                     let uu____74104 =
                       let uu____74107 = always_fail lid t  in [uu____74107]
                        in
                     (false, uu____74104)  in
                   (uu____74103, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____74096  in
               {
                 FStar_Syntax_Syntax.sigel = uu____74095;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1484_74094.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1484_74094.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1484_74094.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1484_74094.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____74114 = extract_sig g always_fail1  in
             (match uu____74114 with
              | (g1,mlm) ->
                  let uu____74133 =
                    FStar_Util.find_map quals
                      (fun uu___621_74138  ->
                         match uu___621_74138 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____74142 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____74133 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____74150 =
                         let uu____74153 =
                           let uu____74154 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____74154  in
                         let uu____74155 =
                           let uu____74158 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____74158]  in
                         uu____74153 :: uu____74155  in
                       (g1, uu____74150)
                   | uu____74161 ->
                       let uu____74164 =
                         FStar_Util.find_map quals
                           (fun uu___622_74170  ->
                              match uu___622_74170 with
                              | FStar_Syntax_Syntax.Projector (l,uu____74174)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____74175 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____74164 with
                        | FStar_Pervasives_Native.Some uu____74182 ->
                            (g1, [])
                        | uu____74185 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____74195 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____74195 with
            | (ml_main,uu____74209,uu____74210) ->
                let uu____74211 =
                  let uu____74214 =
                    let uu____74215 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____74215  in
                  [uu____74214; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____74211))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74218 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____74226 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____74235 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74238 -> (g, [])
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
      let uu____74280 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1527_74284 = g  in
        let uu____74285 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____74285;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1527_74284.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1527_74284.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1527_74284.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____74286 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____74305 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____74305
               then
                 let nm =
                   let uu____74316 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____74316
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____74333 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____74333
                     (fun uu____74343  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____74286 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____74365 = FStar_Options.codegen ()  in
            uu____74365 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____74380 =
                let uu____74382 = FStar_Options.silent ()  in
                Prims.op_Negation uu____74382  in
              if uu____74380
              then
                let uu____74385 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____74385
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
      (let uu____74460 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____74460);
      (let uu____74463 =
         let uu____74465 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____74465  in
       if uu____74463
       then
         let uu____74468 =
           let uu____74470 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____74470
            in
         failwith uu____74468
       else ());
      (let uu____74475 = FStar_Options.interactive ()  in
       if uu____74475
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____74495 = FStar_Options.debug_any ()  in
            if uu____74495
            then
              let msg =
                let uu____74506 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____74506  in
              FStar_Util.measure_execution_time msg
                (fun uu____74516  -> extract' g m)
            else extract' g m  in
          (let uu____74520 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____74520);
          res))
  